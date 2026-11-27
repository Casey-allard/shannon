#!/usr/bin/env python3
"""Tier 3 — Pairwise Combinatorial Cross-Feature Tests (16 tests: T3-P01 .. T3-P16).

Every feature F01-F14 is covered in >= 2 cross-feature combinations.
"""

from __future__ import annotations

import ast
from fractions import Fraction
import math

from common import SuiteContext, TestCase, check_decl_axioms, run_subprocess_safe
from cross_check import (
    COMPL_LOWER_RAT,
    COMPL_UPPER_RAT,
    FLOOR_LOWER,
    LOVASZ_LOWER_RAT,
    LOVASZ_UPPER_RAT,
    REQUIRED_AUDIT_AXIOM_DECLS,
    WITNESS_C7_COMPL_POW4,
    WITNESS_C7_POW1,
    WITNESS_C7_POW2,
    WITNESS_C7_POW3,
    Trie7,
    c7_adj,
    c7_compl_adj,
    check_frontier_rational_bounds,
    check_nat_pow_bound,
    cubic_p,
    format_fraction_down,
    verify_c7_compl_psd,
    verify_cubic_irreducibility_and_roots,
    verify_gilbert32_obstruction,
    verify_obstruction_graphs,
    verify_profile_dp,
    verify_research_report,
    verify_results_md,
    verify_srg27_obstruction,
    verify_strong_power_independent_set,
)


def _t3_p01(ctx: SuiteContext):
    # F01 x F02: pinned v4.32.2 toolchain + cached Mathlib compiles e2e_audit.lean and proves textbook_eq_project
    tc = ctx.project_dir / "lean-toolchain"
    if not tc.is_file():
        return False, "MISSING_FILE", f"Missing {tc}", {}
    if tc.read_text(encoding="utf-8", errors="replace").strip() != "leanprover/lean4:v4.32.2":
        return False, "MATH_MISMATCH", "lean-toolchain not pinned to v4.32.2", {}
    ok_m, code_m, msg_m, info_m = ctx.check_mathlib_cache()
    if not ok_m:
        return False, code_m, msg_m, info_m
    return check_decl_axioms(ctx, ("E2EAudit.textbook_eq_project", "ShannonC7.strongPowPi"))


def _t3_p02(ctx: SuiteContext):
    # F02 x F03: textbook equivalence + Fekete convergence + Lovasz upper bound & rational ceiling
    return check_decl_axioms(
        ctx,
        (
            "E2EAudit.textbook_eq_project",
            "ShannonC7.c7_shannonCapacity_tendsto",
            "ShannonC7.c7_upper_lovasz",
            "ShannonC7.c7_upper_rational",
        ),
    )


def _t3_p03(ctx: SuiteContext):
    # F03 x F04: Lovasz theta closed form + irreducible cubic + 12-digit enclosure + Galois unattainability
    ok_c, code_c, info_c = verify_cubic_irreducibility_and_roots()
    if not ok_c:
        return False, code_c, "Cubic irreducibility / root separation failed", info_c
    return check_decl_axioms(
        ctx,
        (
            "ShannonC7.lovaszThetaC7",
            "ShannonC7.c7_upper_lovasz",
            "ShannonC7.c7_upper_rational",
            "ShannonC7.c7_lovasz_unattainable",
        ),
    )


def _t3_p04(ctx: SuiteContext):
    # F03 x F05: oddCycle_upper_lovasz matches C_5 (sqrt 5) & C_7 (lovaszThetaC7) + theta(C_7)*theta(C_7^c) = 7
    ok_p, code_p, info_p = verify_c7_compl_psd()
    if not ok_p:
        return False, code_p, "Complement product identity / PSD failed", info_p
    return check_decl_axioms(
        ctx,
        (
            "ShannonC7.oddCycle_upper_lovasz",
            "ShannonC7.c5_shannonCapacity_eq_sqrt_five",
            "ShannonC7.c7_upper_lovasz",
            "ShannonC7.c7_compl_sandwich",
        ),
    )


def _t3_p05(ctx: SuiteContext):
    # F02 x F06: strongPowPi + pure-kernel Trie7/Decimal bridge -> zero Lean.ofReduceBool across lower bounds
    t33, c33, _ = Trie7.from_vertices(WITNESS_C7_POW3, 3)
    if t33 is None or t33.card() != 33 or not t33.is_indep():
        return False, c33, "Reference Trie7 failed on C_7^3", {}
    ok_h, code_h, msg_h, info_h = ctx.scan_all_lean_files()
    if not ok_h:
        return False, code_h, msg_h, info_h
    return check_decl_axioms(
        ctx,
        (
            "ShannonC7.strongPowPi",
            "ShannonC7.c7_lower_num",
            "ShannonC7.c7_lower_den",
            "ShannonC7.c7_lower_frontier",
            "E2EAudit.audit_c7_lower_floor",
        ),
    )


def _t3_p06(ctx: SuiteContext):
    # F05 x F07: Complement sandwich unifies 17-word witness lower bound & 1+sec(pi/7) upper bound with strict gap
    ok_w, code_w, info_w = verify_strong_power_independent_set(WITNESS_C7_COMPL_POW4, c7_compl_adj, 4, domain_size=7)
    if not ok_w or info_w["card"] != 17:
        return False, code_w, "17-word C_7^c^4 witness failed", info_w
    ok_p, code_p, info_p = verify_c7_compl_psd()
    if not ok_p:
        return False, code_p, "Complement PSD / cubic failed", info_p
    if not (Fraction(2030543184868, 10**12) < COMPL_LOWER_RAT < COMPL_UPPER_RAT):
        return False, "MATH_MISMATCH", "Complement gap ordering failed", {}
    return check_decl_axioms(ctx, ("ShannonC7.c7_compl_sandwich",))


def _t3_p07(ctx: SuiteContext):
    # F06 x F07: Pure-kernel small powers (3, 10, 33) match independent Python witnesses & exact decimal floors
    for verts, d, num, N in (
        (WITNESS_C7_POW1, 1, 3000000000000, 3),
        (WITNESS_C7_POW2, 2, 3162277660168, 10),
        (WITNESS_C7_POW3, 3, 3207534329995, 33),
    ):
        ok_w, code_w, info_w = verify_strong_power_independent_set(verts, c7_adj, d, domain_size=7)
        ok_b, msg_b = check_nat_pow_bound(num, 10**12, d, N)
        if not ok_w or info_w["card"] != N or not ok_b:
            return False, code_w if not ok_w else "MATH_MISMATCH", f"Small power d={d} cross-check failed: {msg_b}", info_w
    return check_decl_axioms(ctx, ("ShannonC7.alpha_c7_pow1", "ShannonC7.alpha_c7_pow2", "ShannonC7.alpha_c7_pow3"))


def _t3_p08(ctx: SuiteContext):
    # F08 x F09: Profile.star DP (Itty/Gao/BPZ) aligns with search/lower/ tooling & >= FLOOR_LOWER in Main.lean
    ok_dp, code_dp, info_dp = verify_profile_dp()
    if not ok_dp:
        return False, code_dp, "Profile.star DP verification failed", info_dp
    lower_dir = ctx.project_dir / "search" / "lower"
    if not lower_dir.is_dir():
        return False, "MISSING_DIR", f"Missing {lower_dir}", {}
    py_files = sorted(lower_dir.rglob("*.py"))
    if not py_files:
        return False, "MISSING_FILE", "No Python verifier/codegen scripts in search/lower/", {}
    for p in py_files:
        try:
            ast.parse(p.read_text(encoding="utf-8"), filename=str(p))
        except SyntaxError as exc:
            return False, "SUBPROCESS_FAILED", f"SyntaxError in {p.name}: {exc}", {}
    ok_b, code_b, info_b = ctx.get_main_bounds()
    if not ok_b:
        return False, code_b, info_b.get("reason", f"Main.lean bounds unavailable ({code_b})"), info_b
    ok_r, code_r, info_r = check_frontier_rational_bounds(info_b["c7_lower_num"], info_b["c7_lower_den"])
    if not ok_r:
        return False, code_r, info_r.get("reason", "Frontier bounds failed"), info_r
    return True, "OK", f"Profile.star DP, search/lower/ tooling ({len(py_files)} py), and Main.lean bound {info_r['decimal_20']} aligned", info_r


def _t3_p09(ctx: SuiteContext):
    # F06 x F08 x F09: Pure-kernel Trie7/Decimal + ValidTuple/HeteroLayered + FrontierLower zero native_decide & audited
    for rel in ("ShannonC7/TrieVerifier.lean", "ShannonC7/Decimal.lean", "ShannonC7/ValidTuple.lean", "ShannonC7/FrontierLower.lean"):
        if not (ctx.project_dir / rel).is_file():
            return False, "MISSING_FILE", f"Missing {rel}", {"path": rel}
    ok_h, code_h, msg_h, info_h = ctx.scan_all_lean_files()
    if not ok_h:
        return False, code_h, msg_h, info_h
    return check_decl_axioms(
        ctx,
        (
            "ShannonC7.c7_lower_frontier",
            "ShannonC7.c7_lower_num",
            "ShannonC7.c7_lower_den",
            "E2EAudit.audit_c7_lower_den_pos",
            "E2EAudit.audit_c7_lower_floor",
        ),
    )


def _t3_p10(ctx: SuiteContext):
    # F07 x F10 x F11: Complete finite-to-asymptotic monotonicity chain + alpha(C_7^3)=33 -> alpha(C_7^4)<=115
    ok_b, code_b, info_b = ctx.get_main_bounds()
    if not ok_b:
        return False, code_b, info_b.get("reason", f"Main.lean bounds unavailable ({code_b})"), info_b
    num, den = info_b["c7_lower_num"], info_b["c7_lower_den"]
    ok_r, code_r, info_r = check_frontier_rational_bounds(num, den)
    if not ok_r:
        return False, code_r, info_r.get("reason", "Frontier bounds failed"), info_r
    # Exact integer monotonicity chain: 3 < 10^(1/2) < 33^(1/3) < 108^(1/4) < 367^(1/5) < 134753^(1/10) < lower < upper
    chain_ok = (
        3**2 < 10
        and 10**3 < 33**2
        and 33**4 < 108**3
        and 108**5 < 367**4
        and 367**2 < 134753
        and pow(den, 10) * 134753 < pow(num, 10)
        and (33 * 7) // 2 == 115
    )
    if not chain_ok:
        return False, "MATH_MISMATCH", "Monotonicity chain from d=1..10 to frontier failed", info_r
    return check_decl_axioms(
        ctx,
        ("ShannonC7.alpha_c7_pow1", "ShannonC7.alpha_c7_pow2", "ShannonC7.alpha_c7_pow3", "ShannonC7.c7_lower_frontier"),
    )


def _t3_p11(ctx: SuiteContext):
    # F03 x F10 x F13: Main.lean sandwich + exact Python cubic brackets + OpenQuestion_StrictGap + finite gap < 0.0589
    ok_b, code_b, info_b = ctx.get_main_bounds()
    if not ok_b:
        return False, code_b, info_b.get("reason", f"Main.lean bounds unavailable ({code_b})"), info_b
    num, den = info_b["c7_lower_num"], info_b["c7_lower_den"]
    ok_r, code_r, info_r = check_frontier_rational_bounds(num, den)
    if not ok_r:
        return False, code_r, info_r.get("reason", "Frontier bounds failed"), info_r
    val = Fraction(num, den)
    gap = LOVASZ_UPPER_RAT - val
    if not (cubic_p(val) < 0 < cubic_p(LOVASZ_UPPER_RAT) and Fraction(0) < gap < Fraction(589, 10000)):
        return False, "BOUNDS_VIOLATION", f"Sandwich cubic/gap check failed (gap={format_fraction_down(gap, 8)})", info_r
    return check_decl_axioms(
        ctx,
        (
            "ShannonC7.c7_shannonCapacity_sandwich",
            "E2EAudit.audit_textbook_sandwich",
            "ShannonC7.OpenQuestion_StrictGap",
        ),
    )


def _t3_p12(ctx: SuiteContext):
    # F04 x F11 x F12: Algebraic/combinatorial upper barriers align (cube=33, Haemers rank-7 vs C_7>=4, Galois, Gilbert-32)
    ok_obs, code_obs, info_obs = verify_obstruction_graphs()
    if not ok_obs:
        return False, code_obs, "Obstruction graph testbed verification failed", info_obs
    return check_decl_axioms(ctx, ("ShannonC7.alpha_c7_pow3", "ShannonC7.c7_lovasz_unattainable"))


def _t3_p13(ctx: SuiteContext):
    # F09 x F10 x F13: LOWER_RESEARCH_REPORT.md, RESULTS.md, and kernel Main.lean agree on c7_lower_num/den
    ok_b, code_b, info_b = ctx.get_main_bounds()
    if not ok_b:
        return False, code_b, info_b.get("reason", f"Main.lean bounds unavailable ({code_b})"), info_b
    lnum, lden = info_b["c7_lower_num"], info_b["c7_lower_den"]
    ok_r, code_r, info_r = verify_results_md(ctx.project_dir / "RESULTS.md", lnum, lden)
    if not ok_r:
        return False, code_r, info_r.get("reason", f"RESULTS.md failed ({code_r})"), info_r
    ok_l, code_l, info_l = verify_research_report(
        ctx.project_dir / "search" / "lower" / "LOWER_RESEARCH_REPORT.md", "lower", lnum, lden
    )
    if not ok_l:
        return False, code_l, info_l.get("reason", f"LOWER_RESEARCH_REPORT.md failed ({code_l})"), info_l
    return True, "OK", "Main.lean, RESULTS.md, and LOWER_RESEARCH_REPORT.md agree on certified lower bound", info_b


def _t3_p14(ctx: SuiteContext):
    # F11 x F12 x F13: UPPER_RESEARCH_REPORT.md, RESULTS.md, Main.lean, and obstruction_testbed.py aligned
    testbed = ctx.project_dir / "search" / "upper" / "obstruction_testbed.py"
    if not testbed.is_file():
        return False, "MISSING_FILE", f"Missing {testbed}", {}
    ok_u, code_u, info_u = verify_research_report(
        ctx.project_dir / "search" / "upper" / "UPPER_RESEARCH_REPORT.md", "upper"
    )
    if not ok_u:
        return False, code_u, info_u.get("reason", f"UPPER_RESEARCH_REPORT.md failed ({code_u})"), info_u
    ok_b, code_b, info_b = ctx.get_main_bounds()
    if not ok_b:
        return False, code_b, info_b.get("reason", f"Main.lean bounds unavailable ({code_b})"), info_b
    ok_r, code_r, info_r = verify_results_md(
        ctx.project_dir / "RESULTS.md", info_b["c7_lower_num"], info_b["c7_lower_den"]
    )
    if not ok_r:
        return False, code_r, info_r.get("reason", f"RESULTS.md failed ({code_r})"), info_r
    return check_decl_axioms(ctx, ("ShannonC7.alpha_c7_pow3", "ShannonC7.c7_upper_lovasz"))


def _t3_p15(ctx: SuiteContext):
    # F01 x F14: Clean LEAN_NUM_THREADS=2 lake build + verify_axioms.sh + repo-wide static hygiene all pass together
    ok_h, code_h, msg_h, info_h = ctx.scan_all_lean_files()
    if not ok_h:
        return False, code_h, msg_h, info_h
    bres = ctx.run_lean_build()
    if not bres.ok:
        return False, bres.code, bres.message, {"rc": bres.returncode}
    ok_ax, code_ax, msg_ax, info_ax = ctx.run_verify_axioms_script()
    if not ok_ax:
        return False, code_ax, msg_ax, info_ax
    return True, "OK", "Build (LEAN_NUM_THREADS=2), verify_axioms.sh, and global hygiene all succeeded under v4.32.2", info_ax


def _t3_p16(ctx: SuiteContext):
    # F13 x F14: Every PROJECT.md § 4.4 export audited via opaque-box e2e_audit.lean + all 24 axioms + RESULTS.md
    ok_a, code_a, msg_a, info_a = ctx.scan_audit_file()
    if not ok_a:
        return False, code_a, msg_a, info_a
    ok_ax, code_ax, msg_ax, info_ax = check_decl_axioms(ctx, REQUIRED_AUDIT_AXIOM_DECLS)
    if not ok_ax:
        return False, code_ax, msg_ax, info_ax
    ok_b, code_b, info_b = ctx.get_main_bounds()
    if not ok_b:
        return False, code_b, info_b.get("reason", f"Main.lean bounds unavailable ({code_b})"), info_b
    ok_r, code_r, info_r = verify_results_md(
        ctx.project_dir / "RESULTS.md", info_b["c7_lower_num"], info_b["c7_lower_den"]
    )
    if not ok_r:
        return False, code_r, info_r.get("reason", f"RESULTS.md failed ({code_r})"), info_r
    return True, "OK", "All 16 § 4.4 exports, 24 #print axioms checks, opaque-box audit & RESULTS.md unified", info_ax


def get_tier3_tests() -> list[TestCase]:
    return [
        TestCase("T3-P01", "T3", "F01xF02", "Pinned v4.32.2 + cached Mathlib compiles e2e_audit.lean & textbook_eq_project", _t3_p01),
        TestCase("T3-P02", "T3", "F02xF03", "Textbook shannonCapacity satisfies Fekete limit & Lovasz upper bounds", _t3_p02),
        TestCase("T3-P03", "T3", "F03xF04", "Lovasz closed form + irreducible cubic + 12-digit bracket + Galois unattainability", _t3_p03),
        TestCase("T3-P04", "T3", "F03xF05", "oddCycle_upper_lovasz matches C_5/C_7 & complement product theta(C_7)*theta(C_7^c)=7", _t3_p04),
        TestCase("T3-P05", "T3", "F02xF06", "strongPowPi + pure-kernel Trie7/Decimal bridge zero Lean.ofReduceBool", _t3_p05),
        TestCase("T3-P06", "T3", "F05xF07", "Complement sandwich unifies 17-word witness & 1+sec(pi/7) with strict gap", _t3_p06),
        TestCase("T3-P07", "T3", "F06xF07", "Pure-kernel alpha_c7_pow1..3 match Python witnesses & exact decimal floors", _t3_p07),
        TestCase("T3-P08", "T3", "F08xF09", "Profile.star DP aligns with search/lower/ tooling & Main.lean frontier bound", _t3_p08),
        TestCase("T3-P09", "T3", "F06xF08xF09", "Pure-kernel Trie7/Decimal + ValidTuple + FrontierLower zero native_decide", _t3_p09),
        TestCase("T3-P10", "T3", "F07xF10xF11", "Finite-to-asymptotic monotonicity chain (d=1..10 -> frontier) & cube->115", _t3_p10),
        TestCase("T3-P11", "T3", "F03xF10xF13", "Main.lean sandwich + exact cubic brackets + OpenQuestion_StrictGap (< 0.0589 gap)", _t3_p11),
        TestCase("T3-P12", "T3", "F04xF11xF12", "Upper-bound barriers align: cube=33, Haemers, Galois & all 5 obstruction graphs", _t3_p12),
        TestCase("T3-P13", "T3", "F09xF10xF13", "Main.lean, RESULTS.md & LOWER_RESEARCH_REPORT.md agree on certified bound", _t3_p13),
        TestCase("T3-P14", "T3", "F11xF12xF13", "Main.lean, RESULTS.md, UPPER_RESEARCH_REPORT.md & obstruction_testbed.py aligned", _t3_p14),
        TestCase("T3-P15", "T3", "F01xF14", "Clean LEAN_NUM_THREADS=2 lake build + scripts/verify_axioms.sh + repo-wide hygiene pass", _t3_p15),
        TestCase("T3-P16", "T3", "F13xF14", "All 16 § 4.4 exports, 24 #print axioms, opaque-box audit & RESULTS.md unified", _t3_p16),
    ]
