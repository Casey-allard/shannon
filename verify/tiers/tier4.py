#!/usr/bin/env python3
"""Tier 4 — Real-World End-to-End Workloads (8 workloads: T4-W01 .. T4-W08)."""

from __future__ import annotations

import ast
import json
import os
from pathlib import Path
import shutil
import tempfile

from common import SuiteContext, TestCase, check_decl_axioms, run_subprocess_safe
from cross_check import (
    REQUIRED_AUDIT_AXIOM_DECLS,
    WITNESS_C5_POW2,
    WITNESS_C7_COMPL_POW4,
    WITNESS_C7_POW1,
    WITNESS_C7_POW2,
    WITNESS_C7_POW3,
    Trie7,
    build_c7_pow5_linear_343,
    build_polak_schrijver_clean_327,
    build_synthetic_c7_valid_tuple,
    c5_adj,
    c7_adj,
    c7_compl_adj,
    check_frontier_rational_bounds,
    verify_c7_compl_psd,
    verify_c7_fourier_psd,
    verify_cubic_irreducibility_and_roots,
    verify_obstruction_graphs,
    verify_odd_cycle_lovasz_table,
    verify_profile_dp,
    verify_research_report,
    verify_results_md,
    verify_strong_power_independent_set,
    verify_valid_tuple,
)

EXPECTED_PROJECT_DELIVERABLES = (
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
    "RESULTS.md",
    "scripts/verify_axioms.sh",
    "ShannonC7/Defs.lean",
    "ShannonC7/Fekete.lean",
    "ShannonC7/CycleC7.lean",
    "ShannonC7/Lovasz.lean",
    "ShannonC7/LovaszC7.lean",
    "ShannonC7/CubicBounds.lean",
    "ShannonC7/Haemers.lean",
    "ShannonC7/TrieVerifier.lean",
    "ShannonC7/Decimal.lean",
    "ShannonC7/SmallPowers.lean",
    "ShannonC7/ValidTuple.lean",
    "ShannonC7/HeteroLayered.lean",
    "ShannonC7/FrontierLower.lean",
    "ShannonC7/AlphaC7Cube.lean",
    "ShannonC7/FinitePowerUpper.lean",
    "ShannonC7/Main.lean",
    "search/lower/LOWER_RESEARCH_REPORT.md",
    "search/upper/UPPER_RESEARCH_REPORT.md",
    "search/upper/obstruction_testbed.py",
)


def _t4_w01(ctx: SuiteContext):
    """Workload 1: Clean Lean 4 Project Build & Resource Audit."""
    for req in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        if not (ctx.project_dir / req).is_file():
            return False, "MISSING_FILE", f"Missing required build config `{req}`", {"missing": req}
    tc = (ctx.project_dir / "lean-toolchain").read_text(encoding="utf-8", errors="replace").strip()
    if tc != "leanprover/lean4:v4.32.2":
        return False, "MATH_MISMATCH", f"lean-toolchain is {tc!r}, expected leanprover/lean4:v4.32.2", {}
    ok_m, code_m, msg_m, info_m = ctx.check_mathlib_cache()
    if not ok_m:
        return False, code_m, msg_m, info_m
    bres = ctx.run_lean_build()
    if not bres.ok:
        return False, bres.code, bres.message, {"rc": bres.returncode, "max_rss_kb": bres.max_rss_kb}
    return (
        True,
        "OK",
        bres.message,
        {"elapsed_s": round(bres.elapsed_s, 2), "max_rss_mb": round(bres.max_rss_kb / 1024.0, 1)},
    )


def _t4_w02(ctx: SuiteContext):
    """Workload 2: Opaque-Box `verify/e2e_audit.lean` Compilation & Textbook-Equivalence Audit."""
    ok_a, code_a, msg_a, info_a = ctx.scan_audit_file()
    if not ok_a:
        return False, code_a, msg_a, info_a
    audit = ctx.run_lean_audit()
    if not audit.ok:
        return False, audit.code, audit.message, {"rc": audit.returncode}
    if "c7_lower_num" not in audit.eval_consts or "c7_lower_den" not in audit.eval_consts:
        return False, "LEAN_AUDIT_FAILED", "e2e_audit.lean did not emit E2E_CONST c7_lower_num / c7_lower_den", {}
    return (
        True,
        "OK",
        audit.message,
        {"eval_consts": audit.eval_consts, "elapsed_s": round(audit.elapsed_s, 2)},
    )


def _t4_w03(ctx: SuiteContext):
    """Workload 3: Exhaustive `#print axioms` TCB Whitelist Audit across all 24 declarations."""
    return check_decl_axioms(ctx, REQUIRED_AUDIT_AXIOM_DECLS)


def _t4_w04(ctx: SuiteContext):
    """Workload 4: Repository-Wide Comment/String-Aware Static Hygiene Audit."""
    ok_a, code_a, msg_a, info_a = ctx.scan_audit_file()
    if not ok_a:
        return False, code_a, msg_a, info_a
    return ctx.scan_all_lean_files()


def _t4_w05(ctx: SuiteContext):
    """Workload 5: Independent Stdlib Python Exact-Math, Witness, Trie7/ValidTuple & Obstruction Cross-Check."""
    checks = (
        ("cubic_irreducibility", verify_cubic_irreducibility_and_roots),
        ("c7_fourier_psd", verify_c7_fourier_psd),
        ("c7_compl_psd", verify_c7_compl_psd),
        ("odd_cycles", verify_odd_cycle_lovasz_table),
        ("profile_dp", verify_profile_dp),
        ("obstructions", verify_obstruction_graphs),
    )
    for name, fn in checks:
        ok, code, info = fn()
        if not ok:
            return False, code, f"Independent math check `{name}` failed ({code})", info

    # Verify all canonical small-power witnesses + Trie7 + ValidTuple
    lin343 = build_c7_pow5_linear_343()
    ps327 = build_polak_schrijver_clean_327()
    for label, verts, adj, d, dom, exp_n in (
        ("C5^2", WITNESS_C5_POW2, c5_adj, 2, 5, 5),
        ("C7^1", WITNESS_C7_POW1, c7_adj, 1, 7, 3),
        ("C7^2", WITNESS_C7_POW2, c7_adj, 2, 7, 10),
        ("C7^3", WITNESS_C7_POW3, c7_adj, 3, 7, 33),
        ("C7^5_lin", lin343, c7_adj, 5, 7, 343),
        ("C7^5_PS", ps327, c7_adj, 5, 7, 327),
        ("C7c^4", WITNESS_C7_COMPL_POW4, c7_compl_adj, 4, 7, 17),
    ):
        ok_w, code_w, info_w = verify_strong_power_independent_set(verts, adj, d, domain_size=dom)
        if not ok_w or info_w["card"] != exp_n:
            return False, code_w, f"Witness `{label}` failed", info_w

    t33, c33, _ = Trie7.from_vertices(WITNESS_C7_POW3, 3)
    if t33 is None or not t33.is_indep() or t33.card() != 33:
        return False, c33, "Trie7 check failed on C_7^3", {}

    I_v, S_v, X_v, f0, f1 = build_synthetic_c7_valid_tuple()
    ok_vt, code_vt, _ = verify_valid_tuple(c7_adj, I_v, S_v, X_v, f0, f1)
    if not ok_vt:
        return False, code_vt, "ValidTuple check failed", {}

    # Cross-check project Main.lean frontier rational bounds
    ok_b, code_b, info_b = ctx.get_main_bounds()
    if not ok_b:
        return False, code_b, info_b.get("reason", f"Main.lean bounds unavailable ({code_b})"), info_b
    ok_r, code_r, info_r = check_frontier_rational_bounds(info_b["c7_lower_num"], info_b["c7_lower_den"])
    if not ok_r:
        return False, code_r, info_r.get("reason", "Frontier rational check failed"), info_r
    return (
        True,
        "OK",
        f"All independent math/PSD/DP/witness/Trie7/ValidTuple/5-obstruction checks & frontier {info_r['decimal_20']} verified",
        info_r,
    )


def _t4_w06(ctx: SuiteContext):
    """Workload 6: Research Reports & Cross-Artifact Scientific Honesty Audit."""
    ok_b, code_b, info_b = ctx.get_main_bounds()
    if not ok_b:
        return False, code_b, info_b.get("reason", f"Main.lean bounds unavailable ({code_b})"), info_b
    lnum, lden = info_b["c7_lower_num"], info_b["c7_lower_den"]

    ok1, c1, i1 = verify_results_md(ctx.project_dir / "RESULTS.md", lnum, lden)
    if not ok1:
        return False, c1, f"RESULTS.md failed: {i1.get('reason', c1)}", i1
    ok2, c2, i2 = verify_research_report(
        ctx.project_dir / "search" / "lower" / "LOWER_RESEARCH_REPORT.md", "lower", lnum, lden
    )
    if not ok2:
        return False, c2, f"LOWER_RESEARCH_REPORT.md failed: {i2.get('reason', c2)}", i2
    ok3, c3, i3 = verify_research_report(
        ctx.project_dir / "search" / "upper" / "UPPER_RESEARCH_REPORT.md", "upper"
    )
    if not ok3:
        return False, c3, f"UPPER_RESEARCH_REPORT.md failed: {i3.get('reason', c3)}", i3
    return True, "OK", "RESULTS.md, LOWER_RESEARCH_REPORT.md, and UPPER_RESEARCH_REPORT.md passed full honesty & consistency audit", info_b


def _t4_w07(ctx: SuiteContext):
    """Workload 7: Project Verification & Search Tooling Reproducibility Audit."""
    verify_sh = ctx.project_dir / "scripts" / "verify_axioms.sh"
    if not verify_sh.is_file():
        return False, "MISSING_FILE", f"Missing {verify_sh}", {}
    testbed = ctx.project_dir / "search" / "upper" / "obstruction_testbed.py"
    if not testbed.is_file():
        return False, "MISSING_FILE", f"Missing {testbed}", {}
    lower_dir = ctx.project_dir / "search" / "lower"
    if not lower_dir.is_dir():
        return False, "MISSING_DIR", f"Missing {lower_dir}", {}

    # Syntax-check all Python scripts in search/lower/ and search/upper/
    py_scripts = sorted(lower_dir.rglob("*.py")) + sorted((ctx.project_dir / "search" / "upper").rglob("*.py"))
    if not py_scripts:
        return False, "MISSING_FILE", "No Python scripts found under search/lower/ or search/upper/", {}
    for p in py_scripts:
        try:
            ast.parse(p.read_text(encoding="utf-8"), filename=str(p))
        except SyntaxError as exc:
            return False, "SUBPROCESS_FAILED", f"SyntaxError in {p}: {exc}", {}

    # Run obstruction_testbed.py cleanly (preferring project .venv/bin/python if provisioned by F1)
    venv_py = ctx.project_dir / ".venv" / "bin" / "python"
    py_exe = str(venv_py) if venv_py.is_file() else "python3"
    out_obs = run_subprocess_safe([py_exe, "-B", str(testbed)], cwd=ctx.project_dir, timeout=60)
    if not out_obs.ok:
        return False, out_obs.code, f"obstruction_testbed.py failed (rc={out_obs.returncode})", {"stderr": out_obs.stderr[-300:], "python": py_exe}

    # Execute scripts/verify_axioms.sh via single-invocation cache
    ok_ax, code_ax, msg_ax, info_ax = ctx.run_verify_axioms_script()
    if not ok_ax:
        return False, code_ax, msg_ax, info_ax

    return True, "OK", f"verify_axioms.sh, obstruction_testbed.py & {len(py_scripts)} search script(s) reproduced cleanly", {"scripts": len(py_scripts), "python": py_exe}


def _t4_w08(ctx: SuiteContext):
    """Workload 8: Unified Deliverable Completeness, Zero-Pollution & Missing-Fixture Graceful Degradation."""
    # 1. Zero __pycache__ / .pyc pollution inside verify/
    pycache_hits = [str(p) for p in ctx.verify_dir.rglob("__pycache__")] + [
        str(p) for p in ctx.verify_dir.rglob("*.pyc")
    ]
    if pycache_hits:
        return False, "HYGIENE_VIOLATION", f"Bytecode pollution found under verify/: {pycache_hits[:3]}", {"hits": pycache_hits}

    # 2. Verify graceful structured FAIL (exit 1, zero Traceback, valid JSON) on an empty mktemp dir.
    # Guarded against recursion via SHANNON_C7_E2E_NESTED=1 and narrow --tier 1 --filter T1-F01.
    if os.environ.get("SHANNON_C7_E2E_NESTED") != "1":
        tmp_dir = Path(tempfile.mkdtemp(prefix="shannon_c7_w08_empty_"))
        try:
            os.chmod(tmp_dir, 0o700)
            empty_proj = tmp_dir / "empty_proj"
            empty_proj.mkdir()
            json_out = tmp_dir / "degraded.json"
            run_sh = ctx.verify_dir / "run_e2e.sh"
            out = run_subprocess_safe(
                [
                    str(run_sh),
                    "--tier",
                    "1",
                    "--filter",
                    "T1-F01",
                    "--project-dir",
                    str(empty_proj),
                    "--json-out",
                    str(json_out),
                ],
                cwd=ctx.verify_dir,
                timeout=30,
                extra_env={"SHANNON_C7_E2E_NESTED": "1"},
            )
            combined = out.stdout + "\n" + out.stderr
            if out.returncode != 1 or "Traceback" in combined or not json_out.is_file():
                return (
                    False,
                    "SUBPROCESS_FAILED",
                    f"Missing-fixture graceful degradation failed (rc={out.returncode}, has_traceback={'Traceback' in combined})",
                    {},
                )
            rep = json.loads(json_out.read_text(encoding="utf-8"))
            if rep.get("summary", {}).get("total") != 5 or rep.get("summary", {}).get("failed") != 5:
                return False, "REPORT_MISMATCH", f"Unexpected empty-fixture JSON summary: {rep.get('summary')}", {}
        finally:
            shutil.rmtree(tmp_dir, ignore_errors=True)

    # 3. Verify all PROJECT.md § 5 deliverables exist in target project_dir
    missing = [rel for rel in EXPECTED_PROJECT_DELIVERABLES if not (ctx.project_dir / rel).is_file()]
    if missing:
        return (
            False,
            "MISSING_FILE",
            f"Missing {len(missing)} PROJECT.md § 5 deliverable(s); first 5: {', '.join(missing[:5])}",
            {"missing_count": len(missing), "missing": missing},
        )

    return (
        True,
        "OK",
        f"All {len(EXPECTED_PROJECT_DELIVERABLES)} PROJECT.md § 5 deliverables present, zero verify/ pollution & graceful degradation verified",
        {"deliverables": len(EXPECTED_PROJECT_DELIVERABLES)},
    )


def get_tier4_tests() -> list[TestCase]:
    return [
        TestCase("T4-W01", "T4", "WORKLOAD", "Clean Lean 4 project build (LEAN_NUM_THREADS=2) & RAM resource audit", _t4_w01),
        TestCase("T4-W02", "T4", "WORKLOAD", "Opaque-box verify/e2e_audit.lean compilation & textbook-equivalence audit", _t4_w02),
        TestCase("T4-W03", "T4", "WORKLOAD", "Exhaustive #print axioms TCB whitelist audit (all 24 declarations)", _t4_w03),
        TestCase("T4-W04", "T4", "WORKLOAD", "Repository-wide comment/string-aware static hygiene audit", _t4_w04),
        TestCase("T4-W05", "T4", "WORKLOAD", "Independent Python exact-math, witness, Trie7/ValidTuple & 5-obstruction cross-check", _t4_w05),
        TestCase("T4-W06", "T4", "WORKLOAD", "Research reports & cross-artifact scientific honesty audit", _t4_w06),
        TestCase("T4-W07", "T4", "WORKLOAD", "Project verification & search tooling reproducibility audit", _t4_w07),
        TestCase("T4-W08", "T4", "WORKLOAD", "Unified deliverable completeness, zero-pollution & missing-fixture degradation audit", _t4_w08),
    ]
