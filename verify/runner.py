#!/usr/bin/env python3
"""CLI driver for the 4-tier opaque-box E2E verification suite (orchestrated by run_e2e.sh).

Exit codes:
  0 — All selected tests PASSED (or --list / --help succeeded)
  1 — One or more selected tests FAILED
  2 — Invalid CLI usage / zero tests matched filter
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import sys
import time
from typing import Sequence

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(100000)

# Ensure verify/ is importable regardless of current working directory
_VERIFY_DIR = Path(__file__).resolve().parent
if str(_VERIFY_DIR) not in sys.path:
    sys.path.insert(0, str(_VERIFY_DIR))

from common import (
    SuiteContext,
    TestCase,
    TestResult,
    build_json_report,
    execute_test,
    format_result_line,
)
from self_test import get_self_tests
from tiers.tier1 import get_tier1_tests
from tiers.tier2 import get_tier2_tests
from tiers.tier3 import get_tier3_tests
from tiers.tier4 import get_tier4_tests


class _StrictArgumentParser(argparse.ArgumentParser):
    def error(self, message: str) -> None:
        self.print_usage(sys.stderr)
        sys.stderr.write(f"error: {message}\n")
        raise SystemExit(2)


def _parse_tiers(raw_tiers: Sequence[str]) -> list[int]:
    tiers: list[int] = []
    for item in raw_tiers:
        for part in item.split(","):
            part = part.strip()
            if not part:
                continue
            if part not in ("1", "2", "3", "4"):
                sys.stderr.write(f"error: invalid tier {part!r} (expected 1, 2, 3, or 4)\n")
                raise SystemExit(2)
            t = int(part)
            if t not in tiers:
                tiers.append(t)
    if not tiers:
        sys.stderr.write("error: empty --tier specification (expected 1, 2, 3, or 4)\n")
        raise SystemExit(2)
    return tiers


def _build_parser() -> argparse.ArgumentParser:
    p = _StrictArgumentParser(
        prog="verify/run_e2e.sh",
        description="Opaque-Box 4-Tier E2E Verification Suite for Shannon Capacity of C_7 (Lean 4)",
    )
    p.add_argument("--tier", action="append", default=[], help="Run tier(s) 1..4 (repeatable or comma-separated)")
    p.add_argument("--all", action="store_true", help="Run Tiers 1, 2, 3, and 4 sequentially (164 tests)")
    p.add_argument("--self-test", action="store_true", help="Run isolated mktemp -d mutation/control suite (18 suites)")
    p.add_argument("--list", action="store_true", help="List all 164 E2E tests and 18 self-tests without running")
    p.add_argument("--project-dir", type=Path, default=None, help="Target Lean project root (default: parent of verify/)")
    p.add_argument("--json-out", type=Path, default=None, help="Write structured JSON report to this path")
    p.add_argument("-v", "--verbose", action="store_true", help="Show detailed diagnostics for PASS as well as FAIL")
    p.add_argument("--filter", type=str, default=None, help="Case-insensitive substring filter on test ID / feature / title")
    p.add_argument("--lean-timeout", type=int, default=180, help="Timeout in seconds for `lake env lean` (default: 180)")
    p.add_argument("--no-build", action="store_true", help="Never invoke `lake build`; audit pre-built .oleans only")
    # Internal plumbing flags passed by run_e2e.sh
    p.add_argument("--default-project-dir", type=Path, default=_VERIFY_DIR.parent, help=argparse.SUPPRESS)
    p.add_argument("--verify-dir", type=Path, default=_VERIFY_DIR, help=argparse.SUPPRESS)
    return p


def _all_tier_map() -> dict[int, list[TestCase]]:
    return {
        1: get_tier1_tests(),
        2: get_tier2_tests(),
        3: get_tier3_tests(),
        4: get_tier4_tests(),
    }


def _apply_filter(cases: list[TestCase], substr: str | None) -> list[TestCase]:
    if not substr:
        return cases
    needle = substr.lower()
    return [
        c
        for c in cases
        if needle in c.test_id.lower()
        or needle in c.feature.lower()
        or needle in c.title.lower()
    ]


def _run_main(argv: Sequence[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)

    tier_map = _all_tier_map()
    self_tests = get_self_tests()

    # Validate mutually exclusive / required mode flags
    has_tiers = bool(args.tier)
    mode_count = int(bool(args.all)) + int(has_tiers) + int(bool(args.self_test)) + int(bool(args.list))
    if mode_count == 0:
        sys.stderr.write("error: must specify one mode: --tier <1..4>, --all, --self-test, or --list\n")
        return 2
    if args.self_test and (args.all or has_tiers or args.list):
        sys.stderr.write("error: --self-test cannot be combined with --tier, --all, or --list\n")
        return 2
    if args.list and (args.all or has_tiers):
        sys.stderr.write("error: --list cannot be combined with --tier or --all\n")
        return 2
    if args.all and has_tiers:
        sys.stderr.write("error: --all cannot be combined with --tier\n")
        return 2
    if mode_count > 1:
        sys.stderr.write("error: mutually exclusive mode flags specified\n")
        return 2
    if args.lean_timeout <= 0:
        sys.stderr.write("error: --lean-timeout must be a positive integer\n")
        return 2

    if args.list:
        all_e2e = tier_map[1] + tier_map[2] + tier_map[3] + tier_map[4]
        for c in all_e2e:
            print(f"{c.test_id}\t{c.tier}\t{c.feature}\t{c.title}")
        for c in self_tests:
            print(f"{c.test_id}\t{c.tier}\t{c.feature}\t{c.title}")
        print(
            f"\nSummary: T1={len(tier_map[1])}, T2={len(tier_map[2])}, "
            f"T3={len(tier_map[3])}, T4={len(tier_map[4])}, "
            f"Total_E2E={len(all_e2e)}, SelfTests={len(self_tests)}"
        )
        return 0

    project_dir = (args.project_dir if args.project_dir is not None else args.default_project_dir).resolve()
    verify_dir = args.verify_dir.resolve()
    ctx = SuiteContext(
        project_dir=project_dir,
        verify_dir=verify_dir,
        lean_timeout=args.lean_timeout,
        build_timeout=max(300, args.lean_timeout),
        no_build=args.no_build,
        verbose=args.verbose,
    )

    if args.self_test:
        mode = "self-test"
        tiers_run = ["SELF_TEST"]
        selected = _apply_filter(self_tests, args.filter)
    elif args.all:
        mode = "all"
        tiers_run = ["T1", "T2", "T3", "T4"]
        selected = _apply_filter(tier_map[1] + tier_map[2] + tier_map[3] + tier_map[4], args.filter)
    else:
        parsed_tiers = _parse_tiers(args.tier)
        mode = "tier"
        tiers_run = [f"T{t}" for t in parsed_tiers]
        combined: list[TestCase] = []
        for t in parsed_tiers:
            combined.extend(tier_map[t])
        selected = _apply_filter(combined, args.filter)

    if not selected:
        sys.stderr.write(f"error: no tests matched filter {args.filter!r}\n")
        return 2

    t0 = time.monotonic()
    results: list[TestResult] = []
    for case in selected:
        res = execute_test(case, ctx)
        results.append(res)
        print(format_result_line(res, verbose=args.verbose))

    elapsed_s = time.monotonic() - t0
    passed = sum(1 for r in results if r.status == "PASS")
    failed = len(results) - passed
    exit_code = 0 if failed == 0 else 1

    print(
        f"\n=== E2E Summary ({mode}) ===\n"
        f"Project: {project_dir}\n"
        f"Total: {len(results)} | PASS: {passed} | FAIL: {failed} | Elapsed: {elapsed_s:.2f}s | Exit: {exit_code}"
    )

    if args.json_out is not None:
        report = build_json_report(mode, tiers_run, project_dir, results, exit_code)
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    return exit_code


def main() -> int:
    try:
        return _run_main()
    except SystemExit as exc:
        code = exc.code
        return code if isinstance(code, int) else 1
    except Exception as exc:
        if os.environ.get("SHANNON_C7_E2E_DEBUG") == "1":
            raise
        sys.stderr.write(f"error: unexpected runner failure ({type(exc).__name__}): {exc}\n")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
