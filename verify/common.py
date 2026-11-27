#!/usr/bin/env python3
"""Shared E2E test infrastructure: data model, single-invocation caching,
hardware/Mathlib-cache guardrails, zero-traceback execution boundary, and JSON/text formatters.

Stdlib Python 3.12 ONLY.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import sys
import time
from typing import Any, Callable, Sequence

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(100000)

from cross_check import (
    ALLOWED_AXIOMS,
    REQUIRED_AUDIT_AXIOM_DECLS,
    HygieneViolation,
    extract_main_bounds,
    parse_e2e_consts,
    parse_print_axioms,
    read_lean_source_strict,
    scan_lean_hygiene,
    verify_axiom_whitelist,
)

# Max safe physical RAM ceiling on 7.8 GiB VM (in KiB)
MAX_RSS_LIMIT_KB = 7800 * 1024

_LEAN_ERROR_LINE_RE = re.compile(
    r"^[^\n]*:\d+:\d+(?:-\d+:\d+)?:\s*error(?:\([^)\n]+\))?:",
    re.MULTILINE,
)
_LEAN_SORRY_WARN_RE = re.compile(
    r"declaration uses\s+['`]@?(?:sorry|sorryAx)\b",
    re.IGNORECASE,
)


@dataclass(frozen=True)
class TestResult:
    test_id: str
    tier: str
    feature: str
    title: str
    status: str  # "PASS" | "FAIL" (NEVER "SKIP"!)
    code: str
    message: str
    details: dict[str, Any] = field(default_factory=dict)
    elapsed_ms: float = 0.0

    def to_dict(self) -> dict[str, Any]:
        return {
            "test_id": self.test_id,
            "tier": self.tier,
            "feature": self.feature,
            "title": self.title,
            "status": self.status,
            "code": self.code,
            "message": self.message,
            "details": self.details,
            "elapsed_ms": round(self.elapsed_ms, 2),
        }


TestFn = Callable[["SuiteContext"], tuple[bool, str, str, dict[str, Any]]]


@dataclass(frozen=True)
class TestCase:
    test_id: str
    tier: str
    feature: str
    title: str
    fn: TestFn


@dataclass
class SubprocessOutcome:
    ok: bool
    code: str
    returncode: int
    stdout: str
    stderr: str
    timed_out: bool
    elapsed_s: float
    max_rss_kb: int


@dataclass
class LeanBuildRun:
    ok: bool
    code: str
    message: str
    returncode: int = -1
    stdout: str = ""
    stderr: str = ""
    timed_out: bool = False
    elapsed_s: float = 0.0
    max_rss_kb: int = 0
    used_cached_olean: bool = False


@dataclass
class LeanAuditRun:
    ok: bool
    code: str
    message: str
    returncode: int = -1
    stdout: str = ""
    stderr: str = ""
    combined: str = ""
    timed_out: bool = False
    elapsed_s: float = 0.0
    max_rss_kb: int = 0
    parsed_axioms: dict[str, set[str]] = field(default_factory=dict)
    eval_consts: dict[str, int] = field(default_factory=dict)
    built_first: bool = False


def build_clean_env(extra: dict[str, str] | None = None) -> dict[str, str]:
    """Return process environment with ~/.elan/bin prepended (if present) and bytecode disabled."""
    env = dict(os.environ)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    elan_bin = Path(env.get("ELAN_HOME") or (Path.home() / ".elan")) / "bin"
    if elan_bin.is_dir():
        cur = env.get("PATH", "")
        parts = cur.split(os.pathsep) if cur else []
        if str(elan_bin) not in parts:
            env["PATH"] = str(elan_bin) + (os.pathsep + cur if cur else "")
    if extra:
        env.update(extra)
    return env


def run_subprocess_safe(
    cmd: Sequence[str | os.PathLike[str]],
    cwd: Path | None = None,
    timeout: int | float = 120,
    extra_env: dict[str, str] | None = None,
) -> SubprocessOutcome:
    """Execute a subprocess safely with timeout, timing, and child RSS telemetry (no /usr/bin/time)."""
    t0 = time.monotonic()
    cmd_list: list[Any] = []
    try:
        env = build_clean_env(extra_env)
        cmd_list = list(cmd)
        proc = subprocess.run(
            cmd_list,
            cwd=os.fspath(cwd) if cwd is not None else None,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout,
            env=env,
        )
        elapsed = time.monotonic() - t0
        rss_kb = int(resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
        return SubprocessOutcome(
            ok=proc.returncode == 0,
            code="OK" if proc.returncode == 0 else "SUBPROCESS_FAILED",
            returncode=proc.returncode,
            stdout=proc.stdout,
            stderr=proc.stderr,
            timed_out=False,
            elapsed_s=elapsed,
            max_rss_kb=rss_kb,
        )
    except FileNotFoundError as exc:
        elapsed = time.monotonic() - t0
        prog = _safe_str_obj(cmd_list[0]) if cmd_list else "<empty>"
        return SubprocessOutcome(
            ok=False,
            code="MISSING_TOOL",
            returncode=127,
            stdout="",
            stderr=f"Executable not found: {prog} ({_safe_str_obj(exc)})",
            timed_out=False,
            elapsed_s=elapsed,
            max_rss_kb=0,
        )
    except subprocess.TimeoutExpired as exc:
        elapsed = time.monotonic() - t0
        out = exc.stdout if type(exc.stdout) is str else ""
        err = exc.stderr if type(exc.stderr) is str else ""
        cmd_desc = " ".join(_safe_str_obj(c) for c in cmd_list)
        return SubprocessOutcome(
            ok=False,
            code="TIMEOUT",
            returncode=124,
            stdout=out,
            stderr=err + f"\nCommand timed out after {_safe_str_obj(timeout)}s: {cmd_desc}",
            timed_out=True,
            elapsed_s=elapsed,
            max_rss_kb=int(resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss),
        )
    except Exception as exc:
        elapsed = time.monotonic() - t0
        return SubprocessOutcome(
            ok=False,
            code="INTERNAL_EXCEPTION",
            returncode=1,
            stdout="",
            stderr=f"Subprocess error ({type(exc).__name__}): {_safe_str_obj(exc)}",
            timed_out=False,
            elapsed_s=elapsed,
            max_rss_kb=0,
        )


def _find_first_olean(root: Path) -> Path | None:
    """Bounded O(1)-best-case recursive scan stopping on the first `.olean` found."""
    if not root.is_dir():
        return None
    stack = [root]
    while stack:
        cur = stack.pop()
        try:
            with os.scandir(cur) as it:
                for entry in it:
                    if entry.is_file(follow_symlinks=False) and entry.name.endswith(".olean"):
                        return Path(entry.path)
                    if entry.is_dir(follow_symlinks=False):
                        stack.append(Path(entry.path))
        except OSError:
            continue
    return None


class SuiteContext:
    """Per-run shared state with single-invocation caching and hardware/TCB guardrails."""

    def __init__(
        self,
        project_dir: Path,
        verify_dir: Path,
        lean_timeout: int = 180,
        build_timeout: int = 300,
        no_build: bool = False,
        verbose: bool = False,
    ) -> None:
        self.project_dir = project_dir.resolve()
        self.verify_dir = verify_dir.resolve()
        self.lean_timeout = lean_timeout
        self.build_timeout = build_timeout
        self.no_build = no_build
        self.verbose = verbose

        self._tool_cache: dict[str, Path | None] = {}
        self._mathlib_cache_result: tuple[bool, str, str, dict[str, Any]] | None = None
        self._build_result: LeanBuildRun | None = None
        self._audit_result: LeanAuditRun | None = None
        self._hygiene_result: tuple[bool, str, str, dict[str, Any]] | None = None
        self._audit_hygiene_result: tuple[bool, str, str, dict[str, Any]] | None = None
        self._bounds_result: tuple[bool, str, dict[str, Any]] | None = None
        self._tool_version_cache: dict[str, SubprocessOutcome] = {}
        self._verify_axioms_result: tuple[bool, str, str, dict[str, Any]] | None = None

    def find_tool(self, name: str) -> Path | None:
        if name in self._tool_cache:
            return self._tool_cache[name]
        env = build_clean_env()
        found = shutil.which(name, path=env.get("PATH"))
        res = Path(found) if found else None
        self._tool_cache[name] = res
        return res

    def get_tool_version(self, name: str) -> SubprocessOutcome:
        if name in self._tool_version_cache:
            return self._tool_version_cache[name]
        tool = self.find_tool(name)
        if tool is None:
            out = SubprocessOutcome(
                ok=False,
                code="MISSING_TOOL",
                returncode=127,
                stdout="",
                stderr=f"Tool `{name}` not found on PATH or in ~/.elan/bin",
                timed_out=False,
                elapsed_s=0.0,
                max_rss_kb=0,
            )
        else:
            out = run_subprocess_safe([str(tool), "--version"], timeout=15)
        self._tool_version_cache[name] = out
        return out

    def lakefile_requires_mathlib(self) -> bool:
        for fname in ("lakefile.toml", "lakefile.lean"):
            p = self.project_dir / fname
            if p.is_file():
                try:
                    txt = p.read_text(encoding="utf-8", errors="replace").lower()
                    if "mathlib" in txt:
                        return True
                except OSError:
                    pass
        return False

    def check_mathlib_cache(self) -> tuple[bool, str, str, dict[str, Any]]:
        """Verify precompiled Mathlib `.olean`s exist before ever invoking `lake` (prevents source build)."""
        if self._mathlib_cache_result is not None:
            return self._mathlib_cache_result

        if not self.project_dir.is_dir():
            res = (
                False,
                "MISSING_DIR",
                f"Project directory does not exist: {self.project_dir}",
                {"project_dir": str(self.project_dir)},
            )
            self._mathlib_cache_result = res
            return res

        pkg_dir = self.project_dir / ".lake" / "packages" / "mathlib"
        if not pkg_dir.is_dir():
            res = (
                False,
                "MATHLIB_CACHE_MISSING",
                f"Mathlib package directory missing ({pkg_dir}); refusing to trigger source build on 2 vCPUs",
                {"pkg_dir": str(pkg_dir)},
            )
            self._mathlib_cache_result = res
            return res

        candidates = (
            pkg_dir / ".lake" / "build" / "lib" / "lean" / "Mathlib",
            pkg_dir / ".lake" / "build" / "lib" / "Mathlib",
            pkg_dir / ".lake" / "build" / "lib" / "lean",
        )
        sample: Path | None = None
        for cand in candidates:
            sample = _find_first_olean(cand)
            if sample is not None:
                break

        if sample is None:
            res = (
                False,
                "MATHLIB_CACHE_MISSING",
                "Precompiled Mathlib .olean cache absent; refusing to compile Mathlib from source on 2 vCPUs",
                {"pkg_dir": str(pkg_dir)},
            )
        else:
            res = (
                True,
                "OK",
                f"Precompiled Mathlib .olean cache verified ({sample.name})",
                {"sample_olean": str(sample)},
            )
        self._mathlib_cache_result = res
        return res

    def _preflight_lean(self) -> tuple[bool, str, str]:
        if not self.project_dir.is_dir():
            return False, "MISSING_DIR", f"Project directory missing: {self.project_dir}"
        lake = self.find_tool("lake")
        lean = self.find_tool("lean")
        if lake is None or lean is None:
            missing = [t for t, p in (("lake", lake), ("lean", lean)) if p is None]
            return False, "MISSING_TOOL", f"Required Lean toolchain executable(s) missing: {', '.join(missing)}"
        if not (self.project_dir / "lean-toolchain").is_file():
            return False, "MISSING_FILE", f"Missing lean-toolchain in {self.project_dir}"
        if not ((self.project_dir / "lakefile.toml").is_file() or (self.project_dir / "lakefile.lean").is_file()):
            return False, "MISSING_FILE", f"Missing lakefile.toml / lakefile.lean in {self.project_dir}"
        if not (self.project_dir / "ShannonC7" / "Main.lean").is_file():
            return False, "MISSING_FILE", f"Missing ShannonC7/Main.lean in {self.project_dir}"
        if self.lakefile_requires_mathlib():
            ok_m, code_m, msg_m, _ = self.check_mathlib_cache()
            if not ok_m:
                return False, code_m, msg_m
        return True, "OK", "Pre-flight OK"

    def run_lean_build(self) -> LeanBuildRun:
        """Build `ShannonC7.Main` safely (`LEAN_NUM_THREADS=2 lake build ShannonC7.Main`) once per run."""
        if self._build_result is not None:
            return self._build_result

        ok_pre, code_pre, msg_pre = self._preflight_lean()
        if not ok_pre:
            self._build_result = LeanBuildRun(ok=False, code=code_pre, message=msg_pre)
            return self._build_result

        main_olean = self.project_dir / ".lake" / "build" / "lib" / "lean" / "ShannonC7" / "Main.olean"
        if self.no_build:
            if main_olean.is_file():
                self._build_result = LeanBuildRun(
                    ok=True,
                    code="OK",
                    message=f"Using pre-built Main.olean (--no-build): {main_olean}",
                    returncode=0,
                    used_cached_olean=True,
                )
            else:
                self._build_result = LeanBuildRun(
                    ok=False,
                    code="MISSING_FILE",
                    message=f"Main.olean missing under --no-build: {main_olean}",
                )
            return self._build_result

        lake = self.find_tool("lake")
        assert lake is not None
        out = run_subprocess_safe(
            [str(lake), "build", "ShannonC7.Main"],
            cwd=self.project_dir,
            timeout=self.build_timeout,
            extra_env={"LEAN_NUM_THREADS": "2"},
        )
        combined = out.stdout + ("\n" + out.stderr if out.stderr else "")
        has_err = bool(_LEAN_ERROR_LINE_RE.search(combined))
        if out.timed_out:
            res = LeanBuildRun(
                ok=False,
                code="TIMEOUT",
                message=f"`LEAN_NUM_THREADS=2 lake build ShannonC7.Main` timed out after {self.build_timeout}s",
                returncode=out.returncode,
                stdout=out.stdout,
                stderr=out.stderr,
                timed_out=True,
                elapsed_s=out.elapsed_s,
                max_rss_kb=out.max_rss_kb,
            )
        elif not out.ok or has_err:
            tail = (out.stderr or out.stdout).strip().splitlines()[-3:]
            res = LeanBuildRun(
                ok=False,
                code="LEAN_BUILD_FAILED",
                message=f"`LEAN_NUM_THREADS=2 lake build ShannonC7.Main` failed (rc={out.returncode}): {' | '.join(tail)}",
                returncode=out.returncode,
                stdout=out.stdout,
                stderr=out.stderr,
                elapsed_s=out.elapsed_s,
                max_rss_kb=out.max_rss_kb,
            )
        elif out.max_rss_kb > MAX_RSS_LIMIT_KB:
            res = LeanBuildRun(
                ok=False,
                code="LEAN_BUILD_FAILED",
                message=f"Build RSS {out.max_rss_kb // 1024} MiB exceeded 7800 MiB guardrail",
                returncode=out.returncode,
                stdout=out.stdout,
                stderr=out.stderr,
                elapsed_s=out.elapsed_s,
                max_rss_kb=out.max_rss_kb,
            )
        else:
            res = LeanBuildRun(
                ok=True,
                code="OK",
                message=f"`LEAN_NUM_THREADS=2 lake build ShannonC7.Main` succeeded in {out.elapsed_s:.2f}s (max_rss={out.max_rss_kb // 1024} MiB)",
                returncode=0,
                stdout=out.stdout,
                stderr=out.stderr,
                elapsed_s=out.elapsed_s,
                max_rss_kb=out.max_rss_kb,
            )
        self._build_result = res
        return res

    def run_lean_audit(self) -> LeanAuditRun:
        """Run `lake env lean verify/e2e_audit.lean` once per run and cache output, axioms & eval constants."""
        if self._audit_result is not None:
            return self._audit_result

        audit_file = self.verify_dir / "e2e_audit.lean"
        if not audit_file.is_file():
            self._audit_result = LeanAuditRun(
                ok=False,
                code="MISSING_FILE",
                message=f"Missing opaque-box audit file: {audit_file}",
            )
            return self._audit_result

        ok_pre, code_pre, msg_pre = self._preflight_lean()
        if not ok_pre:
            self._audit_result = LeanAuditRun(ok=False, code=code_pre, message=msg_pre)
            return self._audit_result

        lake = self.find_tool("lake")
        assert lake is not None

        # Step A: Attempt read-only `lake env lean` first (writes zero .olean files)
        out = run_subprocess_safe(
            [str(lake), "env", "lean", str(audit_file)],
            cwd=self.project_dir,
            timeout=self.lean_timeout,
        )
        combined = out.stdout + ("\n" + out.stderr if out.stderr else "")
        built_first = False

        # Step B: If ShannonC7.Main .olean is missing/stale and build is allowed, build once and re-run
        missing_olean_hint = any(
            pat in combined
            for pat in (
                "object file",
                "unknown module prefix 'ShannonC7'",
                "unknown module prefix `ShannonC7`",
                "unknown package 'ShannonC7'",
                "unknown package `ShannonC7`",
                "does not exist",
            )
        )
        if not out.ok and not out.timed_out and missing_olean_hint and not self.no_build:
            bres = self.run_lean_build()
            if not bres.ok:
                self._audit_result = LeanAuditRun(
                    ok=False,
                    code=bres.code,
                    message=f"Pre-audit build failed: {bres.message}",
                    returncode=bres.returncode,
                    stdout=bres.stdout,
                    stderr=bres.stderr,
                    combined=bres.stdout + "\n" + bres.stderr,
                    timed_out=bres.timed_out,
                    elapsed_s=bres.elapsed_s,
                    max_rss_kb=bres.max_rss_kb,
                    built_first=True,
                )
                return self._audit_result
            built_first = True
            out = run_subprocess_safe(
                [str(lake), "env", "lean", str(audit_file)],
                cwd=self.project_dir,
                timeout=self.lean_timeout,
            )
            combined = out.stdout + ("\n" + out.stderr if out.stderr else "")

        parsed_axioms = parse_print_axioms(combined)
        eval_consts = parse_e2e_consts(combined)
        has_err = bool(_LEAN_ERROR_LINE_RE.search(combined))
        has_sorry_warn = bool(_LEAN_SORRY_WARN_RE.search(combined))

        if out.timed_out:
            res = LeanAuditRun(
                ok=False,
                code="TIMEOUT",
                message=f"`lake env lean e2e_audit.lean` timed out after {self.lean_timeout}s",
                returncode=out.returncode,
                stdout=out.stdout,
                stderr=out.stderr,
                combined=combined,
                timed_out=True,
                elapsed_s=out.elapsed_s,
                max_rss_kb=out.max_rss_kb,
                parsed_axioms=parsed_axioms,
                eval_consts=eval_consts,
                built_first=built_first,
            )
        elif not out.ok or has_err:
            tail = [ln for ln in combined.splitlines() if ln.strip()][-4:]
            res = LeanAuditRun(
                ok=False,
                code="LEAN_AUDIT_FAILED",
                message=f"`e2e_audit.lean` failed (rc={out.returncode}): {' | '.join(tail)}",
                returncode=out.returncode,
                stdout=out.stdout,
                stderr=out.stderr,
                combined=combined,
                elapsed_s=out.elapsed_s,
                max_rss_kb=out.max_rss_kb,
                parsed_axioms=parsed_axioms,
                eval_consts=eval_consts,
                built_first=built_first,
            )
        elif has_sorry_warn:
            res = LeanAuditRun(
                ok=False,
                code="HYGIENE_VIOLATION",
                message="`e2e_audit.lean` emitted a `declaration uses sorry` warning",
                returncode=out.returncode,
                stdout=out.stdout,
                stderr=out.stderr,
                combined=combined,
                elapsed_s=out.elapsed_s,
                max_rss_kb=out.max_rss_kb,
                parsed_axioms=parsed_axioms,
                eval_consts=eval_consts,
                built_first=built_first,
            )
        else:
            res = LeanAuditRun(
                ok=True,
                code="OK",
                message=(
                    f"`e2e_audit.lean` passed in {out.elapsed_s:.2f}s "
                    f"({len(parsed_axioms)} axiom reports, {len(eval_consts)} constants)"
                ),
                returncode=0,
                stdout=out.stdout,
                stderr=out.stderr,
                combined=combined,
                elapsed_s=out.elapsed_s,
                max_rss_kb=out.max_rss_kb,
                parsed_axioms=parsed_axioms,
                eval_consts=eval_consts,
                built_first=built_first,
            )

        self._audit_result = res
        return res

    def scan_all_lean_files(self) -> tuple[bool, str, str, dict[str, Any]]:
        """Scan every `.lean` file under `ShannonC7/` once per run (UTF-8, zero NUL, full hygiene)."""
        if self._hygiene_result is not None:
            return self._hygiene_result

        src_root = self.project_dir / "ShannonC7"
        if not src_root.is_dir():
            res = (
                False,
                "MISSING_DIR",
                f"Source directory missing: {src_root}",
                {"src_root": str(src_root)},
            )
            self._hygiene_result = res
            return res

        lean_files = sorted(src_root.rglob("*.lean"))
        if not lean_files:
            res = (
                False,
                "MISSING_FILE",
                f"No .lean source files found under {src_root}",
                {"src_root": str(src_root)},
            )
            self._hygiene_result = res
            return res

        per_file: dict[str, list[HygieneViolation]] = {}
        all_violations: list[HygieneViolation] = []
        encoding_errors: list[str] = []

        for path in lean_files:
            rel = str(path.relative_to(self.project_dir))
            try:
                raw_bytes = path.read_bytes()
            except OSError as exc:
                encoding_errors.append(f"{rel}: read error {exc}")
                continue
            if b"\x00" in raw_bytes:
                encoding_errors.append(f"{rel}: contains NUL byte")
                continue
            try:
                src = raw_bytes.decode("utf-8")
            except UnicodeDecodeError as exc:
                encoding_errors.append(f"{rel}: invalid UTF-8 ({exc})")
                continue
            viols = scan_lean_hygiene(src, path=rel, mode="impl")
            per_file[rel] = viols
            all_violations.extend(viols)

        if encoding_errors:
            res = (
                False,
                "HYGIENE_VIOLATION",
                f"UTF-8/NUL errors in Lean sources: {encoding_errors[0]}",
                {
                    "files_scanned": len(lean_files),
                    "encoding_errors": encoding_errors,
                    "per_file": per_file,
                    "violations": [v.to_dict() for v in all_violations],
                },
            )
        elif all_violations:
            first = all_violations[0]
            code = (
                "WHOLESALE_IMPORT"
                if first.rule == "WHOLESALE_MATHLIB_IMPORT"
                else (
                    "UNCLOSED_BLOCK_COMMENT"
                    if first.rule == "UNCLOSED_BLOCK_COMMENT"
                    else "HYGIENE_VIOLATION"
                )
            )
            res = (
                False,
                code,
                f"{len(all_violations)} hygiene violation(s); first at {first.path}:{first.line} [{first.rule}] `{first.token}`",
                {
                    "files_scanned": len(lean_files),
                    "per_file": per_file,
                    "violations": [v.to_dict() for v in all_violations],
                },
            )
        else:
            res = (
                True,
                "OK",
                f"All {len(lean_files)} .lean files under ShannonC7/ passed static hygiene scan",
                {
                    "files_scanned": len(lean_files),
                    "per_file": per_file,
                    "violations": [],
                },
            )

        self._hygiene_result = res
        return res

    def scan_audit_file(self) -> tuple[bool, str, str, dict[str, Any]]:
        if self._audit_hygiene_result is not None:
            return self._audit_hygiene_result
        audit_file = self.verify_dir / "e2e_audit.lean"
        if not audit_file.is_file():
            res = (False, "MISSING_FILE", f"Missing {audit_file}", {"path": str(audit_file)})
            self._audit_hygiene_result = res
            return res
        src, enc_viols = read_lean_source_strict(audit_file, display_path=str(audit_file))
        if src is None:
            first = enc_viols[0]
            res = (
                False,
                "HYGIENE_VIOLATION",
                f"e2e_audit.lean encoding/NUL error at line {first.line}: [{first.rule}] {first.message}",
                {"violations": [v.to_dict() for v in enc_viols]},
            )
            self._audit_hygiene_result = res
            return res
        viols = scan_lean_hygiene(src, path=str(audit_file), mode="audit")
        if viols:
            first = viols[0]
            code = "OPAQUE_BOX_VIOLATION" if "OPAQUE_BOX" in first.rule or "MAIN_IMPORT" in first.rule else "HYGIENE_VIOLATION"
            res = (
                False,
                code,
                f"e2e_audit.lean violation at line {first.line}: [{first.rule}] {first.message}",
                {"violations": [v.to_dict() for v in viols]},
            )
        else:
            res = (True, "OK", "verify/e2e_audit.lean passed opaque-box & hygiene audit", {"violations": []})
        self._audit_hygiene_result = res
        return res

    def run_verify_axioms_script(self) -> tuple[bool, str, str, dict[str, Any]]:
        """Execute `scripts/verify_axioms.sh` once per run (guarded by Mathlib cache pre-flight)."""
        if self._verify_axioms_result is not None:
            return self._verify_axioms_result
        script = self.project_dir / "scripts" / "verify_axioms.sh"
        if not script.is_file():
            res = (False, "MISSING_FILE", f"Missing {script}", {"path": str(script)})
            self._verify_axioms_result = res
            return res
        ok_m, code_m, msg_m, info_m = self.check_mathlib_cache()
        if not ok_m:
            res = (False, code_m, msg_m, info_m)
            self._verify_axioms_result = res
            return res
        out = run_subprocess_safe(["bash", str(script)], cwd=self.project_dir, timeout=self.lean_timeout)
        if not out.ok:
            tail = (out.stderr or out.stdout).strip().splitlines()[-3:]
            res = (
                False,
                out.code,
                f"scripts/verify_axioms.sh failed (rc={out.returncode}): {' | '.join(tail)}",
                {"rc": out.returncode, "stderr": out.stderr[-300:]},
            )
        else:
            res = (
                True,
                "OK",
                f"scripts/verify_axioms.sh exited 0 in {out.elapsed_s:.2f}s",
                {"elapsed_s": round(out.elapsed_s, 2)},
            )
        self._verify_axioms_result = res
        return res

    def get_main_bounds(self) -> tuple[bool, str, dict[str, Any]]:
        """Retrieve exact `(c7_lower_num, c7_lower_den)` via Lean `#eval` primary or static Main.lean fallback."""
        if self._bounds_result is not None:
            return self._bounds_result
        eval_consts: dict[str, int] | None = None
        # Only use Lean eval constants if Lean audit already ran or can run cleanly
        audit = self.run_lean_audit()
        if audit.ok and audit.eval_consts:
            eval_consts = audit.eval_consts
        res = extract_main_bounds(self.project_dir / "ShannonC7" / "Main.lean", eval_consts=eval_consts)
        self._bounds_result = res
        return res


def check_decl_axioms(
    ctx: SuiteContext, decls: Sequence[str]
) -> tuple[bool, str, str, dict[str, Any]]:
    """Helper verifying Lean audit succeeded AND specified declarations pass `#print axioms` whitelist."""
    audit = ctx.run_lean_audit()
    if not audit.ok:
        return False, audit.code, audit.message, {"returncode": audit.returncode}
    subset = {k: v for k, v in audit.parsed_axioms.items() if k in set(decls)}
    ok, code, info = verify_axiom_whitelist(
        subset, required_decls=decls, whitelist=ALLOWED_AXIOMS, raw_output=audit.combined
    )
    if not ok:
        return False, code, f"Axiom whitelist check failed ({code}) for {len(decls)} decl(s)", info
    return True, "OK", f"All {len(decls)} declaration(s) strictly within {{propext, Classical.choice, Quot.sound}}", info


def execute_test(case: TestCase, ctx: SuiteContext) -> TestResult:
    """Run a single TestCase under a zero-traceback exception boundary."""
    t0 = time.monotonic()
    try:
        passed, code, message, details = case.fn(ctx)
        elapsed_ms = (time.monotonic() - t0) * 1000.0
        passed_b = bool(passed)
        raw_code = _safe_str_obj(code) if code is not None else ""
        safe_code = raw_code if raw_code else ("OK" if passed_b else "FAIL")
        safe_message = _safe_str_obj(message) if message is not None else ""
        # Strip non-JSON-serializable objects (like HygieneViolation instances in per_file) from details
        safe_details = _sanitize_details(details)
        return TestResult(
            test_id=case.test_id,
            tier=case.tier,
            feature=case.feature,
            title=case.title,
            status="PASS" if passed_b else "FAIL",
            code=safe_code,
            message=safe_message,
            details=safe_details,
            elapsed_ms=elapsed_ms,
        )
    except Exception as exc:
        elapsed_ms = (time.monotonic() - t0) * 1000.0
        return TestResult(
            test_id=case.test_id,
            tier=case.tier,
            feature=case.feature,
            title=case.title,
            status="FAIL",
            code="INTERNAL_EXCEPTION",
            message=f"Caught unexpected {type(exc).__name__}: {_safe_str_obj(exc)}",
            details={"exception_type": type(exc).__name__},
            elapsed_ms=elapsed_ms,
        )


def _safe_str_obj(x: Any) -> str:
    if type(x) is str:
        return x
    try:
        s = str(x)
        return s if type(s) is str else str.__str__(s)
    except Exception:
        if isinstance(x, str):
            try:
                return str.__str__(x)
            except Exception:
                pass
        return f"<{type(x).__name__} unprintable>"


def _sanitize_int(obj: Any) -> int | str:
    if type(obj) is int:
        val = obj
    else:
        try:
            val = int.__int__(obj)
            if type(val) is not int:
                return _safe_str_obj(obj)
        except Exception:
            return _safe_str_obj(obj)
    bl = val.bit_length()
    if bl > 300000:
        sign = "-" if val < 0 else ""
        return f"{sign}<int bit_length={bl}>"
    return val


def _sanitize_details(obj: Any) -> Any:
    if obj is None or type(obj) in (bool, float, str):
        return obj
    if type(obj) is int:
        bl = obj.bit_length()
        if bl > 300000:
            sign = "-" if obj < 0 else ""
            return f"{sign}<int bit_length={bl}>"
        return obj
    if isinstance(obj, str):
        return str.__str__(obj)
    if isinstance(obj, float):
        try:
            fval = float.__float__(obj)
            return fval if type(fval) is float else _safe_str_obj(obj)
        except Exception:
            return _safe_str_obj(obj)
    if isinstance(obj, int):
        return _sanitize_int(obj)
    if isinstance(obj, Path):
        return _safe_str_obj(obj)
    if isinstance(obj, HygieneViolation):
        try:
            return _sanitize_details(obj.to_dict())
        except Exception:
            return _safe_str_obj(obj)
    if isinstance(obj, (set, frozenset)):
        items = [_sanitize_details(x) for x in obj]
        try:
            return sorted(items)
        except Exception:
            return sorted(items, key=_safe_str_obj)
    if isinstance(obj, (list, tuple)):
        return [_sanitize_details(x) for x in obj]
    if isinstance(obj, dict):
        out: dict[str, Any] = {}
        for k, v in obj.items():
            if type(k) is str and k == "per_file":
                continue
            if type(k) is str:
                key_str = k
            elif isinstance(k, int) and not isinstance(k, bool):
                k_san = _sanitize_int(k)
                key_str = k_san if type(k_san) is str else str(k_san)
            elif isinstance(k, float) and type(k) is not float:
                try:
                    kf = float.__float__(k)
                    key_str = str(kf) if type(kf) is float else _safe_str_obj(k)
                except Exception:
                    key_str = _safe_str_obj(k)
            else:
                key_str = _safe_str_obj(k)
            out[key_str] = _sanitize_details(v)
        return out
    return _safe_str_obj(obj)


def format_result_line(res: TestResult, verbose: bool = False) -> str:
    base = f"[{res.status}] {res.test_id} ({res.feature}) [{res.code}] {res.title}"
    if res.status == "FAIL" or verbose:
        return f"{base}\n       -> {res.message} ({res.elapsed_ms:.1f}ms)"
    return base


def build_json_report(
    mode: str,
    tiers_run: Sequence[str],
    project_dir: Path,
    results: Sequence[TestResult],
    exit_code: int,
) -> dict[str, Any]:
    by_tier: dict[str, dict[str, int]] = {}
    for r in results:
        entry = by_tier.setdefault(r.tier, {"total": 0, "passed": 0, "failed": 0})
        entry["total"] += 1
        if r.status == "PASS":
            entry["passed"] += 1
        else:
            entry["failed"] += 1

    passed = sum(1 for r in results if r.status == "PASS")
    failed = len(results) - passed
    return {
        "schema_version": "1.0",
        "project_dir": str(project_dir),
        "mode": mode,
        "tiers_run": list(tiers_run),
        "exit_code": exit_code,
        "summary": {
            "total": len(results),
            "passed": passed,
            "failed": failed,
            "by_tier": by_tier,
        },
        "results": [r.to_dict() for r in results],
    }
