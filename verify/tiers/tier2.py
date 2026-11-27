#!/usr/bin/env python3
"""Tier 2 — Boundary Value Analysis, Corner Cases & Negative Robustness (70 tests: T2-F01-01 .. T2-F14-05).

5 sharp BVA/corner/negative tests per feature area across F01-F14.
Tests inspecting project artifacts FAIL cleanly if project artifacts are absent.
"""

from __future__ import annotations

from fractions import Fraction
import itertools
import os
from pathlib import Path
import shutil
import tempfile

from common import SuiteContext, TestCase, check_decl_axioms
from cross_check import (
    ALLOWED_AXIOMS,
    BPZ_D200_EXACT_N,
    COMPL_LOWER_RAT,
    COMPL_UPPER_RAT,
    FLOOR_LOWER,
    GAO_D200_EXACT_N,
    LOVASZ_8_LOWER,
    LOVASZ_8_UPPER,
    LOVASZ_15_LOWER,
    LOVASZ_15_UPPER,
    LOVASZ_CUBIC_TRAP,
    LOVASZ_LOWER_RAT,
    LOVASZ_UPPER_RAT,
    THETA_C7_30DIGITS,
    WITNESS_C7_COMPL_POW4,
    WITNESS_C7_POW1,
    WITNESS_C7_POW2,
    WITNESS_C7_POW3,
    Profile,
    Trie7,
    bisect_theta_c7,
    build_c7_pow5_linear_343,
    build_synthetic_c7_valid_tuple,
    c7_adj,
    c7_compl_adj,
    check_frontier_rational_bounds,
    check_nat_pow_bound,
    cubic_compl_q,
    cubic_p,
    cubic_p_deriv,
    exact_rational_rank,
    parse_print_axioms,
    profile_star,
    read_lean_source_strict,
    safe_int_preview,
    scan_lean_hygiene,
    split_tree_pow,
    validate_upper_bound_claim,
    verify_axiom_whitelist,
    verify_c7_fourier_psd,
    verify_research_report,
    verify_results_md,
    verify_srg27_obstruction,
    verify_strong_power_independent_set,
    verify_valid_tuple,
)

# ---------------------------------------------------------------------------
# F01 — Toolchain & Guardrails BVA / Negative
# ---------------------------------------------------------------------------


def _t2_f01_01(ctx: SuiteContext):
    p = ctx.project_dir / "lean-toolchain"
    if not p.is_file():
        return False, "MISSING_FILE", f"Missing {p}", {"path": str(p)}
    lines = [ln for ln in p.read_text(encoding="utf-8", errors="replace").splitlines() if ln.strip()]
    if len(lines) != 1 or lines[0].strip() != "leanprover/lean4:v4.32.2":
        return False, "MATH_MISMATCH", f"lean-toolchain must be single-line exact v4.32.2, got {lines!r}", {"lines": lines}
    # Negative sanity: wrong version strings must fail exact comparison
    for bad in ("leanprover/lean4:v4.32.1", "leanprover/lean4:v4.33.0", "leanprover/lean4:nightly"):
        if bad == lines[0].strip():
            return False, "MATH_MISMATCH", "Unexpected toolchain match", {}
    return True, "OK", "lean-toolchain is exact single-line leanprover/lean4:v4.32.2", {"toolchain": lines[0]}


def _t2_f01_02(ctx: SuiteContext):
    p = ctx.project_dir / "lakefile.toml"
    if not p.is_file():
        return False, "MISSING_FILE", f"Missing {p}", {"path": str(p)}
    txt = p.read_text(encoding="utf-8", errors="replace")
    if "blob.core.windows.net" in txt:
        return False, "REPORT_MISMATCH", "lakefile.toml references retired Azure blob URL", {}
    if 'rev = "master"' in txt or 'rev = "main"' in txt:
        return False, "REPORT_MISMATCH", "lakefile.toml uses unpinned main/master mathlib rev", {}
    return True, "OK", "lakefile.toml free of retired Azure URLs and unpinned main/master branches", {}


def _t2_f01_03(ctx: SuiteContext):
    ok, code, msg, info = ctx.scan_all_lean_files()
    if code in ("MISSING_DIR", "MISSING_FILE"):
        return False, code, msg, info
    enc_errs = info.get("encoding_errors", [])
    if enc_errs:
        return False, "HYGIENE_VIOLATION", f"Encoding/NUL error: {enc_errs[0]}", {"encoding_errors": enc_errs}
    return True, "OK", f"All {info.get('files_scanned', 0)} .lean files are valid UTF-8 with zero NUL bytes", {}


def _t2_f01_04(ctx: SuiteContext):
    bad_src = "import Mathlib   -- trailing comment\ndef x := 1\n"
    good_src = "import Mathlib.Data.ZMod.Basic\ndef x := 1\n"
    v_bad = scan_lean_hygiene(bad_src, mode="impl")
    v_good = scan_lean_hygiene(good_src, mode="impl")
    if not any(v.rule == "WHOLESALE_MATHLIB_IMPORT" for v in v_bad):
        return False, "HYGIENE_VIOLATION", "Hygiene scanner failed to reject wholesale `import Mathlib`", {}
    if v_good:
        return False, "HYGIENE_VIOLATION", f"False positive on leaf import: {v_good}", {}
    return True, "OK", "Wholesale `import Mathlib` rejected while leaf import accepted", {}


def _t2_f01_05(ctx: SuiteContext):
    comment_only = "/- /- import Mathlib -/ -/\nimport Mathlib.Combinatorics.SimpleGraph.Basic\n"
    if scan_lean_hygiene(comment_only, mode="impl"):
        return False, "HYGIENE_VIOLATION", "Nested block comment /- import Mathlib -/ triggered false positive", {}
    ok, code, msg, info = ctx.scan_all_lean_files()
    if code in ("MISSING_DIR", "MISSING_FILE"):
        return False, code, msg, info
    enc_errs = info.get("encoding_errors", [])
    if enc_errs:
        return (
            False,
            "HYGIENE_VIOLATION",
            f"Encoding/NUL error prevented comment scan: {enc_errs[0]}",
            {"encoding_errors": enc_errs},
        )
    unclosed = [v for v in info.get("violations", []) if v.get("rule") == "UNCLOSED_BLOCK_COMMENT"]
    if unclosed:
        return False, "UNCLOSED_BLOCK_COMMENT", f"Unclosed block comment in {unclosed[0]['path']}", {"unclosed": unclosed}
    return True, "OK", "Nested commented import ignored and zero unclosed block comments in ShannonC7/", {}


# ---------------------------------------------------------------------------
# F02 — Core Shannon Capacity & Fekete BVA / Negative
# ---------------------------------------------------------------------------


def _t2_f02_01(ctx: SuiteContext):
    ok_pow, _ = check_nat_pow_bound(1, 1, 0, 1)
    ok_ind, _, _ = verify_strong_power_independent_set([()], c7_adj, 0, domain_size=7)
    if ok_pow or ok_ind:
        return False, "MATH_MISMATCH", "d=0 boundary must be rejected by power and witness validators", {}
    audit_src = (ctx.verify_dir / "e2e_audit.lean").read_text(encoding="utf-8")
    if "0 < d" not in audit_src:
        return False, "HYGIENE_VIOLATION", "e2e_audit.lean missing explicit `0 < d` guard in shannonSetTextbook", {}
    return True, "OK", "d=0 boundary strictly excluded in e2e_audit.lean and rejected by Python verifiers", {}


def _t2_f02_02(ctx: SuiteContext):
    return check_decl_axioms(ctx, ("ShannonC7.alpha_c7_pow1", "E2EAudit.textbook_eq_project"))


def _t2_f02_03(ctx: SuiteContext):
    if not (c7_adj(0, 1) and c7_adj(0, 6) and c7_adj(6, 0)):
        return False, "MATH_MISMATCH", "C_7 cyclic wrap-around adjacency 0~1, 0~6 failed", {}
    if any(c7_adj(0, v) for v in (0, 2, 3, 4, 5)):
        return False, "MATH_MISMATCH", "C_7 non-adjacency at distance 0,2,3,4,5 failed", {}
    if any(c7_adj(u, u) for u in range(7)):
        return False, "MATH_MISMATCH", "C_7 looplessness failed", {}
    return True, "OK", "C_7 cyclic wrap-around 0~6, non-adjacency 0!~{2..5}, and looplessness verified", {}


def _t2_f02_04(ctx: SuiteContext):
    ok1, c1, _ = verify_strong_power_independent_set([(0, 0, 0), (0, 0, 1)], c7_adj, 3, domain_size=7)
    ok2, c2, _ = verify_strong_power_independent_set([(0, 0, 0), (0, 0, 6)], c7_adj, 3, domain_size=7)
    if ok1 or c1 != "CONFLICT_EDGE" or ok2 or c2 != "CONFLICT_EDGE":
        return False, "MATH_MISMATCH", f"Failed to detect strong-power conflict edges (c1={c1}, c2={c2})", {}
    return True, "OK", "Strong-power conflict edges (0,0,0)~(0,0,1) and wrap-around (0,0,0)~(0,0,6) caught", {}


def _t2_f02_05(ctx: SuiteContext):
    ok, code, info = verify_strong_power_independent_set([(0, 0, 0), (2, 0, 0)], c7_adj, 3, domain_size=7)
    if not ok:
        return False, code, "Pair differing by cyclic distance 2 in one coord must be independent", info
    return True, "OK", "Pair (0,0,0) vs (2,0,0) verified independent in C_7^3", info


# ---------------------------------------------------------------------------
# F03 — Lovasz Upper Bound & Cubic BVA / Negative
# ---------------------------------------------------------------------------


def _t2_f03_01(ctx: SuiteContext):
    if not (cubic_p(LOVASZ_8_LOWER) < 0 < cubic_p(LOVASZ_8_UPPER)):
        return False, "MATH_MISMATCH", "8-digit cubic boundary failed", {}
    return True, "OK", "Exact 8-digit cubic boundary: p(331766720/10^8) < 0 < p(331766721/10^8)", {}


def _t2_f03_02(ctx: SuiteContext):
    if not (cubic_p(LOVASZ_LOWER_RAT) < 0 < cubic_p(LOVASZ_UPPER_RAT)):
        return False, "MATH_MISMATCH", "12-digit cubic boundary failed", {}
    return True, "OK", "Exact 12-digit cubic boundary: p(3317667207394/10^12) < 0 < p(3317667207395/10^12)", {}


def _t2_f03_03(ctx: SuiteContext):
    ok15 = cubic_p(LOVASZ_15_LOWER) < 0 < cubic_p(LOVASZ_15_UPPER)
    _, _, digits30 = bisect_theta_c7(150)
    if not (ok15 and digits30 == THETA_C7_30DIGITS):
        return False, "MATH_MISMATCH", f"15/30-digit bisection mismatch: {digits30}", {}
    return True, "OK", f"Exact 15-digit bracket (...095 < theta < ...096) & 30-digit bisection {digits30} verified", {}


def _t2_f03_04(ctx: SuiteContext):
    ok_nonadj, _, _ = verify_c7_fourier_psd(perturb_nonadj=1e-6)
    ok_beta, _, _ = verify_c7_fourier_psd(perturb_beta=1e-6)
    if ok_nonadj or ok_beta:
        return False, "MATH_MISMATCH", f"Perturbed PSD certificate should fail (nonadj={ok_nonadj}, beta={ok_beta})", {}
    return True, "OK", "Negative PSD perturbation (non-edge +1e-6 and beta +1e-6) cleanly rejected", {}


def _t2_f03_05(ctx: SuiteContext):
    if not (LOVASZ_UPPER_RAT < Fraction(7, 2)):
        return False, "MATH_MISMATCH", "Upper bound not < 7/2", {}
    return check_decl_axioms(ctx, ("ShannonC7.c7_upper_lovasz", "ShannonC7.c7_upper_rational"))


# ---------------------------------------------------------------------------
# F04 — Galois Unattainability & Haemers BVA / Negative
# ---------------------------------------------------------------------------


def _t2_f04_01(ctx: SuiteContext):
    crit = Fraction(7, 3)
    ok = (
        cubic_p_deriv(crit) == 0
        and cubic_p(crit) == Fraction(-392, 27)
        and cubic_p_deriv(crit + Fraction(1, 10**6)) > 0
        and cubic_p_deriv(Fraction(3)) > 0
    )
    if not ok:
        return False, "MATH_MISMATCH", "Critical point / strict monotonicity check failed", {}
    return True, "OK", "p'(7/3)=0, p(7/3)=-392/27 < 0, and p'(t) > 0 strictly past 7/3", {}


def _t2_f04_02(ctx: SuiteContext):
    expected = {1: 8, -1: 104, 7: 392, -7: 392, 49: 132104, -49: -98392}
    actual = {r: int(cubic_p(Fraction(r))) for r in expected}
    if actual != expected or any(v == 0 for v in actual.values()):
        return False, "MATH_MISMATCH", f"Rational root evaluations mismatch: {actual}", {"actual": actual}
    return True, "OK", "All 6 rational-root candidates +/-1,+/-7,+/-49 verified exact nonzero", {"evals": actual}


def _t2_f04_03(ctx: SuiteContext):
    # `e2e_audit.lean` instantiates c7_lovasz_unattainable explicitly at d=1,2,3
    audit = ctx.run_lean_audit()
    if not audit.ok:
        return False, audit.code, audit.message, {"returncode": audit.returncode}
    return check_decl_axioms(ctx, ("ShannonC7.c7_lovasz_unattainable",))


def _t2_f04_04(ctx: SuiteContext):
    # Haemers bound: minrank >= Theta(C_7) >= sqrt(10) > 3 => integer minrank >= 4
    # Also verify a rank-3 matrix on C_7 cannot fit (3 cliques cover at most 6 < 7 vertices)
    if not (3 * 3 < 10 and Fraction(7, 2) < Fraction(4, 1) and LOVASZ_UPPER_RAT < Fraction(7, 2)):
        return False, "MATH_MISMATCH", "Haemers boundary inequality failed", {}
    # Verify rank-3 3-clique matrix leaves vertex 6 with diagonal 0 (breaks fitting property)
    M3 = [[0] * 7 for _ in range(7)]
    for blk in ((0, 1), (2, 3), (4, 5)):
        for u in blk:
            for v in blk:
                M3[u][v] = 1
    if exact_rational_rank(M3) != 3 or M3[6][6] != 0:
        return False, "MATH_MISMATCH", "Rank-3 clique-cover counterexample check failed", {}
    return True, "OK", "Haemers minrank boundary (> sqrt(10) > 3 => >= 4; 3-clique fails vertex 6) verified", {}


def _t2_f04_05(ctx: SuiteContext):
    ok, code, info = verify_srg27_obstruction()
    if not ok:
        return False, code, "srg(27,10,1,5) complement check failed", info
    if info.get("compl_I_minus_A_rank") != 27 or info.get("compl_4I_minus_A_rank") != 21:
        return False, "MATH_MISMATCH", f"Unexpected complement ranks: {info}", info
    return True, "OK", "Complement srg(27,16,10,8) has rank_Q(I-A_bar)=27 and rank_Q(4I-A_bar)=21 (> 3 = alpha)", info


# ---------------------------------------------------------------------------
# F05 — Odd Cycles & C_7^c BVA / Negative
# ---------------------------------------------------------------------------


def _t2_f05_01(ctx: SuiteContext):
    # C_3 boundary k=1: theta(C_3) = 3*(1/2)/(3/2) = 1
    if Fraction(3, 2) / Fraction(3, 2) != Fraction(1, 1):
        return False, "MATH_MISMATCH", "C_3 boundary failed", {}
    return check_decl_axioms(ctx, ("ShannonC7.oddCycle_upper_lovasz",))


def _t2_f05_02(ctx: SuiteContext):
    return check_decl_axioms(ctx, ("ShannonC7.c5_shannonCapacity_eq_sqrt_five",))


def _t2_f05_03(ctx: SuiteContext):
    if not (cubic_compl_q(COMPL_LOWER_RAT) > 0 > cubic_compl_q(COMPL_UPPER_RAT)):
        return False, "MATH_MISMATCH", "Decreasing complement cubic bracket failed", {}
    return True, "OK", "Decreasing complement cubic: q(2109916264174/10^12) > 0 > q(2109916264175/10^12)", {}


def _t2_f05_04(ctx: SuiteContext):
    ok_lo, _ = check_nat_pow_bound(2030543184868, 10**12, 4, 17)
    ok_hi, _ = check_nat_pow_bound(2030543184869, 10**12, 4, 17)
    strict_gap = 2**4 < 17 and 17 * (10**12) ** 4 < 2109916264174**4
    if not (ok_lo and not ok_hi and strict_gap):
        return False, "MATH_MISMATCH", "Complement 17^(1/4) exact integer bracket failed", {}
    return True, "OK", "Exact complement bracket 2.030543184868 <= 17^(1/4) < 2.030543184869 < 2.109916264174", {}


def _t2_f05_05(ctx: SuiteContext):
    mutated = list(WITNESS_C7_COMPL_POW4)
    mutated[0] = (0, 0, 0, 2)  # Distance 2 from (0,0,1,3) etc. -> adjacent in C_7^c^4!
    ok, code, info = verify_strong_power_independent_set(mutated, c7_compl_adj, 4, domain_size=7)
    if ok or code != "CONFLICT_EDGE":
        return False, "MATH_MISMATCH", f"Mutated C_7^c^4 witness should fail CONFLICT_EDGE, got ok={ok} code={code}", info
    return True, "OK", "Single cyclic-dist-2 mutation in C_7^c^4 witness rejected (CONFLICT_EDGE)", info


# ---------------------------------------------------------------------------
# F06 — Trie7 & Exact Decimal Bridge BVA / Negative
# ---------------------------------------------------------------------------


def _t2_f06_01(ctx: SuiteContext):
    ok_lo, _ = check_nat_pow_bound(3258789153908, 10**12, 200, GAO_D200_EXACT_N)
    ok_hi, _ = check_nat_pow_bound(3258789153909, 10**12, 200, GAO_D200_EXACT_N)
    if not (ok_lo and not ok_hi):
        return False, "MATH_MISMATCH", f"Gao rounded-up BVA failed (lo={ok_lo}, hi={ok_hi})", {}
    return True, "OK", "Gao d=200: truncated ...908 PASSES while rounded-up ...909 REJECTED", {}


def _t2_f06_02(ctx: SuiteContext):
    ps_lo, _ = check_nat_pow_bound(3257865966783, 10**12, 5, 367)
    ps_hi, _ = check_nat_pow_bound(3257865966784, 10**12, 5, 367)
    bpz_lo, _ = check_nat_pow_bound(3258805369885, 10**12, 200, BPZ_D200_EXACT_N)
    bpz_hi, _ = check_nat_pow_bound(3258805369886, 10**12, 200, BPZ_D200_EXACT_N)
    if not (ps_lo and not ps_hi and bpz_lo and not bpz_hi):
        return False, "MATH_MISMATCH", "Polak-Schrijver / BPZ +/-1 ULP boundary check failed", {}
    return True, "OK", "Polak-Schrijver (...783 vs ...784) & BPZ (...885 vs ...886) exact +/-1 ULP verified", {}


def _t2_f06_03(ctx: SuiteContext):
    ok_eq, _ = check_nat_pow_bound(3, 1, 3, 27)
    ok_den0, _ = check_nat_pow_bound(3, 0, 5, 367)
    ok_d0, _ = check_nat_pow_bound(3, 1, 0, 367)
    ok_neg, _ = check_nat_pow_bound(-1, 1, 5, 367)
    if not (ok_eq and not ok_den0 and not ok_d0 and not ok_neg):
        return False, "MATH_MISMATCH", "Exact equality / zero-den / zero-d / negative-num boundary failed", {}
    return True, "OK", "Exact equality 3^3 == 1^3 * 27 accepted; den=0, d=0, num<0 cleanly rejected", {}


def _t2_f06_04(ctx: SuiteContext):
    # d=500 with 15-digit num produces ~7756-digit integer (exceeds Python 3.12 default 4300 limit)
    num = 3258827985920007
    den = 10**15
    N_pass = (pow(num, 500) + pow(den, 500) - 1) // pow(den, 500)
    N_fail = N_pass - 1
    ok_p, msg_p = check_nat_pow_bound(num, den, 500, N_pass)
    ok_f, msg_f = check_nat_pow_bound(num, den, 500, N_fail)
    if not (ok_p and not ok_f):
        return False, "MATH_MISMATCH", f"d=500 big-int check failed (pass={ok_p}, fail={ok_f})", {}
    return True, "OK", f"d=500 >7500-digit exact power verified safely under Python 3.12 ({msg_p})", {}


def _t2_f06_05(ctx: SuiteContext):
    dup_verts = list(WITNESS_C7_POW3) + [WITNESS_C7_POW3[0]]
    t_dup, c_dup, _ = Trie7.from_vertices(dup_verts, 3)
    if t_dup is not None or c_dup != "DUPLICATE_VERTEX":
        return False, "MATH_MISMATCH", f"Trie7 failed to reject duplicate vertex (code={c_dup})", {}
    bad_verts = list(WITNESS_C7_POW3)
    bad_verts[0] = (0, 1, 4)  # adjacent to (1,1,4)
    t_bad, _, _ = Trie7.from_vertices(bad_verts, 3)
    if t_bad is None or t_bad.is_indep():
        return False, "MATH_MISMATCH", "Trie7 failed to detect single conflict edge in C_7^3", {}
    return True, "OK", "Trie7 rejected both duplicate vertex and single cyclic-distance-1 conflict", {}


# ---------------------------------------------------------------------------
# F07 — Small Powers d=1..5 & C_7^c BVA / Negative
# ---------------------------------------------------------------------------


def _t2_f07_01(ctx: SuiteContext):
    for comb in itertools.combinations(range(7), 4):
        ok, code, _ = verify_strong_power_independent_set([(x,) for x in comb], c7_adj, 1, domain_size=7)
        if ok or code != "CONFLICT_EDGE":
            return False, "MATH_MISMATCH", f"4-subset {comb} unexpectedly passed C_7^1 independence", {}
    return True, "OK", "All C(7,4)=35 four-vertex subsets of C_7 rejected (pigeonhole alpha(C_7) < 4)", {}


def _t2_f07_02(ctx: SuiteContext):
    existing = set(WITNESS_C7_POW2)
    tested = 0
    for u in range(7):
        for v in range(7):
            if (u, v) in existing:
                continue
            tested += 1
            ok, code, _ = verify_strong_power_independent_set(
                list(WITNESS_C7_POW2) + [(u, v)], c7_adj, 2, domain_size=7
            )
            if ok or code != "CONFLICT_EDGE":
                return False, "MATH_MISMATCH", f"Extending WITNESS_C7_POW2 with {(u,v)} unexpectedly passed", {}
    return True, "OK", f"All {tested} single-vertex extensions of 10-set in C_7^2 rejected (maximality)", {"tested": tested}


def _t2_f07_03(ctx: SuiteContext):
    mut = list(WITNESS_C7_POW3)
    mut[0] = (0, 1, 4)  # adjacent to (1,1,4)
    ok, code, info = verify_strong_power_independent_set(mut, c7_adj, 3, domain_size=7)
    if ok or code != "CONFLICT_EDGE":
        return False, "MATH_MISMATCH", f"Single coordinate mutation in C_7^3 not caught (code={code})", info
    return True, "OK", "Single coordinate mutation (0,1,1)->(0,1,4) in C_7^3 caught as CONFLICT_EDGE", info


def _t2_f07_04(ctx: SuiteContext):
    lin = build_c7_pow5_linear_343()
    ok_add, c_add, _ = verify_strong_power_independent_set(lin + [(1, 0, 0, 0, 0)], c7_adj, 5, domain_size=7)
    ok_dup, c_dup, _ = verify_strong_power_independent_set(list(WITNESS_C7_POW3) + [(0, 1, 1)], c7_adj, 3, domain_size=7)
    if ok_add or c_add != "CONFLICT_EDGE" or ok_dup or c_dup != "DUPLICATE_VERTEX":
        return False, "MATH_MISMATCH", f"Mutation checks failed (add={c_add}, dup={c_dup})", {}
    return True, "OK", "C_7^5 linear 343+1 conflict caught & C_7^3 duplicate vertex caught", {}


def _t2_f07_05(ctx: SuiteContext):
    a1 = len(WITNESS_C7_POW1)
    a2 = len(WITNESS_C7_POW2)
    a3 = len(WITNESS_C7_POW3)
    a4, a5 = 108, 367
    mono = (
        a1 == 3
        and a2 == 10
        and a3 == 33
        and a1**2 < a2
        and a1 * a2 < a3
        and a2**3 < a3**2
        and a3**4 < a4**3
        and a4**5 < a5**4
    )
    ok1, _ = check_nat_pow_bound(3000000000000, 10**12, 1, a1)
    ok2, _ = check_nat_pow_bound(3162277660168, 10**12, 2, a2)
    ok3, _ = check_nat_pow_bound(3207534329995, 10**12, 3, a3)
    ok4, _ = check_nat_pow_bound(3223709795470, 10**12, 4, a4)
    ok5, _ = check_nat_pow_bound(3257865966783, 10**12, 5, a5)
    if not (mono and ok1 and ok2 and ok3 and ok4 and ok5):
        return False, "MATH_MISMATCH", "Computed small-power monotonicity / check_nat_pow_bound check failed", {}
    return (
        True,
        "OK",
        f"Computed strict progression from witnesses ({a1},{a2},{a3},{a4},{a5}) & verified 12-digit power floors",
        {"cards": [a1, a2, a3, a4, a5]},
    )


# ---------------------------------------------------------------------------
# F08 — ValidTuple.star & Heterogeneous/Layered BVA / Negative
# ---------------------------------------------------------------------------


def _t2_f08_01(ctx: SuiteContext):
    deg = Profile(367, 0, 367, 367)
    res = profile_star(deg, deg)
    if res != Profile(367**2, 0, 367**2, 367**2):
        return False, "MATH_MISMATCH", f"Degenerate b=0 profile_star mismatch: {res}", {}
    return True, "OK", "Degenerate b=0 profile reduces cleanly to Cartesian product (367^2, 0, 367^2, 367^2)", {}


def _t2_f08_02(ctx: SuiteContext):
    edge = Profile(10, 10, 10, 10)
    res = profile_star(edge, edge)
    ok, msg = res.validate()
    if not ok or res.a != 200 or res.b != 200 or res.c != 100 or res.d != 100:
        return False, "MATH_MISMATCH", f"Boundary b==a, d==c failed: {res} ({msg})", {}
    return True, "OK", "Boundary profile b==a, d==c preserves invariants cleanly without underflow", {}


def _t2_f08_03(ctx: SuiteContext):
    bad1 = Profile(10, 11, 10, 5)
    bad2 = Profile(10, 5, 10, 11)
    ok1, _ = bad1.validate()
    ok2, _ = bad2.validate()
    raised1 = raised2 = False
    try:
        profile_star(bad1, Profile(10, 5, 10, 5))
    except ValueError:
        raised1 = True
    try:
        profile_star(Profile(10, 5, 10, 5), bad2)
    except ValueError:
        raised2 = True
    if ok1 or ok2 or not (raised1 and raised2):
        return False, "MATH_MISMATCH", "Invalid profiles b>a / d>c not cleanly rejected", {}
    return True, "OK", "Invalid profiles (b>a and d>c) rejected by both validate() and profile_star()", {}


def _t2_f08_04(ctx: SuiteContext):
    bpz = Profile(367, 8, 367, 322)
    p20 = split_tree_pow(bpz, 20)
    p40 = split_tree_pow(bpz, 40)
    p60 = split_tree_pow(bpz, 60)
    p100 = split_tree_pow(bpz, 100)
    itty_gain = profile_star(Profile(367, 8, 367, 321), Profile(367, 8, 367, 321)).a - 367**2
    if not (p40.a > p20.a**2 and p40.a**3 > p60.a**2 and p40.a**5 > p100.a**2 and itty_gain == 64):
        return False, "MATH_MISMATCH", "Homogeneous turnover or Itty +64 gain failed", {}
    return True, "OK", "Verified exact integer peak at k=40 (a_40 > a_20^2, a_40^3 > a_60^2, a_40^5 > a_100^2) & Itty +64", {}


def _t2_f08_05(ctx: SuiteContext):
    I_v, S_v, X_v, f0, f1 = build_synthetic_c7_valid_tuple()
    # Mutate f1(0) = 1: N[1] = {0,1,2} hits BOTH 0 and 2 in I -> PRIVACY_VIOLATION
    ok_priv, c_priv, _ = verify_valid_tuple(c7_adj, I_v, S_v, X_v, f0, {0: 1})
    # Mutate X = [0, 2, 4]: 0 in N[f0(0)] cap N[f1(0)] -> DISJOINTNESS_VIOLATION
    ok_disj, c_disj, _ = verify_valid_tuple(c7_adj, I_v, S_v, [0, 2, 4], f0, f1)
    # Mutate f0 == f1 == {0: 0} -> toggle_S / f0 != f1 violated
    ok_eq, c_eq, _ = verify_valid_tuple(c7_adj, I_v, S_v, X_v, f0, f0)
    # C_7^2 tuple violating toggle_S (neither f0[s] nor f1[s] equals s)
    c7_2 = lambda u, v: u != v and all(u[k] == v[k] or c7_adj(u[k], v[k]) for k in range(2))
    ok_tog, c_tog, _ = verify_valid_tuple(c7_2, [(0, 0)], [(0, 0)], [(0, 6)], {(0, 0): (1, 1)}, {(0, 0): (6, 1)})
    if (
        ok_priv
        or c_priv != "PRIVACY_VIOLATION"
        or ok_disj
        or c_disj != "DISJOINTNESS_VIOLATION"
        or ok_eq
        or c_eq != "MATH_MISMATCH"
        or ok_tog
        or c_tog != "MATH_MISMATCH"
    ):
        return False, "MATH_MISMATCH", f"ValidTuple negative checks failed (priv={c_priv}, disj={c_disj}, eq={c_eq}, tog={c_tog})", {}
    return True, "OK", "ValidTuple verifier caught privacy, disjointness, identical-toggle & toggle_S violations", {}


# ---------------------------------------------------------------------------
# F09 — Dual Verifier & Codegen BVA / Negative
# ---------------------------------------------------------------------------


def _t2_f09_01(ctx: SuiteContext):
    ok, code, _ = verify_strong_power_independent_set([(0, 0, 0, 0, 0), (2, 2, 2, 2)], c7_adj, 5, domain_size=7)
    if ok or code != "MATH_MISMATCH":
        return False, "MATH_MISMATCH", "Mismatched tuple length (4 in d=5) was not rejected", {}
    return True, "OK", "Mismatched tuple dimension (4-tuple in d=5) cleanly rejected", {}


def _t2_f09_02(ctx: SuiteContext):
    ok1, c1, _ = verify_strong_power_independent_set([(-1, 0, 0)], c7_adj, 3, domain_size=7)
    ok2, c2, _ = verify_strong_power_independent_set([(7, 0, 0)], c7_adj, 3, domain_size=7)
    if ok1 or ok2 or c1 != "MATH_MISMATCH" or c2 != "MATH_MISMATCH":
        return False, "MATH_MISMATCH", "Out-of-range coordinates (-1, 7) not rejected", {}
    return True, "OK", "Out-of-range ZMod 7 coordinates (-1 and 7) cleanly rejected", {}


def _t2_f09_03(ctx: SuiteContext):
    ok1, _, i1 = verify_strong_power_independent_set([(0,)], c7_adj, 1, domain_size=7)
    ok_empty, _ = check_nat_pow_bound(1, 1, 1, 0)
    if not (ok1 and i1["card"] == 1 and not ok_empty):
        return False, "MATH_MISMATCH", "Single-word / empty-witness boundary failed", {}
    return True, "OK", "Single-word witness (N=1,d=1) accepted and empty witness (N=0) rejected for lower bound", {}


def _t2_f09_04(ctx: SuiteContext):
    ok, code, info = ctx.get_main_bounds()
    if not ok:
        return False, code, info.get("reason", f"Main.lean bounds unavailable ({code})"), info
    if info["c7_lower_num"] <= 0 or info["c7_lower_den"] <= 0:
        return (
            False,
            "BOUNDS_VIOLATION",
            f"Non-positive Main.lean bounds: num={safe_int_preview(info['c7_lower_num'])}, den={safe_int_preview(info['c7_lower_den'])}",
            info,
        )
    return True, "OK", f"Main.lean exports positive c7_lower_num and c7_lower_den ({info['source']})", info


def _t2_f09_05(ctx: SuiteContext):
    tmp = Path(tempfile.mkdtemp(prefix="shannon_c7_t2_f09_"))
    try:
        os.chmod(tmp, 0o700)
        res_md = tmp / "RESULTS.md"
        res_md.write_text(
            "# Results\n"
            "The exact Shannon capacity of C_7 remains an open problem with strict gap below Lovasz 3.317667207395.\n"
            "Exact small powers: alpha(C_7)=3, alpha(C_7^2)=10, alpha(C_7^3)=33.\n"
            "Verified in pure Lean kernel using {propext, Classical.choice, Quot.sound}.\n"
            "Our certified Lean 4 lower bound is 3.258832620353 (and 3.258805369885).\n",
            encoding="utf-8",
        )
        ok, code, info = verify_results_md(res_md, lower_num=3258805369885, lower_den=10**12)
        if ok or code != "REPORT_MISMATCH":
            return False, "MATH_MISMATCH", f"Inflated RESULTS.md bound not caught (ok={ok}, code={code})", info
        return True, "OK", "Cross-checker rejected inflated RESULTS.md bound (3.258832620353 > 3.258805369885)", {}
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


# ---------------------------------------------------------------------------
# F10 — Frontier Lower-Bound BVA / Negative
# ---------------------------------------------------------------------------


def _t2_f10_01(ctx: SuiteContext):
    ok, code, _ = check_frontier_rational_bounds(3258805369885, 0)
    if ok or code != "BOUNDS_VIOLATION":
        return False, "MATH_MISMATCH", "den=0 must be rejected with BOUNDS_VIOLATION", {}
    return True, "OK", "Vacuous c7_lower_den = 0 cleanly rejected (BOUNDS_VIOLATION, zero ZeroDivisionError)", {}


def _t2_f10_02(ctx: SuiteContext):
    ok_below, c_below, _ = check_frontier_rational_bounds(3258805369884, 10**12)
    ok_exact, _, _ = check_frontier_rational_bounds(3258805369885, 10**12)
    if ok_below or c_below != "BOUNDS_VIOLATION" or not ok_exact:
        return False, "MATH_MISMATCH", f"Floor +/-1 ULP check failed (below={ok_below}, exact={ok_exact})", {}
    return True, "OK", "BPZ v1 floor boundary: ...884/10^12 REJECTED while ...885/10^12 ACCEPTED", {}


def _t2_f10_03(ctx: SuiteContext):
    ok_trap, c_trap, _ = check_frontier_rational_bounds(33176672073945, 10**13)
    ok_eq, c_eq, _ = check_frontier_rational_bounds(3317667207395, 10**12)
    if ok_trap or c_trap != "BOUNDS_VIOLATION" or ok_eq or c_eq != "BOUNDS_VIOLATION":
        return False, "MATH_MISMATCH", "Cubic trap or upper-ceiling collision not rejected", {}
    return True, "OK", "Cubic trap 33176672073945/10^13 (> theta(C_7)) and >= 3317667207395/10^12 rejected", {}


def _t2_f10_04(ctx: SuiteContext):
    # Exact reduced fraction: 3258805369885 / 10^12 == 651761073977 / 200000000000
    ok, code, info = check_frontier_rational_bounds(651761073977, 200000000000)
    if not ok:
        return False, code, "Reduced non-power-of-10 fraction failed cross-multiplied check", info
    return True, "OK", "Non-power-of-10 reduced fraction 651761073977/200000000000 accepted via exact cross-multiplication", {}


def _t2_f10_05(ctx: SuiteContext):
    ok, code, info = ctx.get_main_bounds()
    if not ok:
        return False, code, info.get("reason", f"Main.lean bounds unavailable ({code})"), info
    num, den = info["c7_lower_num"], info["c7_lower_den"]
    ok_r, code_r, info_r = check_frontier_rational_bounds(num, den)
    if not ok_r:
        return False, code_r, info_r.get("reason", "Frontier bounds failed"), info_r
    gap = LOVASZ_UPPER_RAT - Fraction(num, den)
    if not (Fraction(0) < gap < Fraction(6, 100)):
        return False, "BOUNDS_VIOLATION", f"Unexpected gap width {float(gap):.6f}", info_r
    return True, "OK", f"Project frontier gap width verified in (0, 0.06): {info_r['gap_to_upper_rat_20']}", info_r


# ---------------------------------------------------------------------------
# F11 — Exact alpha(C_7^3)=33 & alpha(C_7^4) Audit BVA / Negative
# ---------------------------------------------------------------------------


def _t2_f11_01(ctx: SuiteContext):
    audit_src = (ctx.verify_dir / "e2e_audit.lean").read_text(encoding="utf-8")
    if "audit_alpha_pow3_not_34" not in audit_src:
        return False, "HYGIENE_VIOLATION", "e2e_audit.lean missing audit_alpha_pow3_not_34 check", {}
    audit = ctx.run_lean_audit()
    if not audit.ok:
        return False, audit.code, audit.message, {"returncode": audit.returncode}
    return True, "OK", "e2e_audit.lean proved ¬ (34 ≤ (strongPowC7Textbook 3).indepNum) from alpha_c7_pow3 = 33", {}


def _t2_f11_02(ctx: SuiteContext):
    a3 = len(WITNESS_C7_POW3)
    s4 = (a3 * 7) // 2
    s5_cond = (112 * 7) // 2
    s5_uncond = (s4 * 7) // 2
    lov5 = int(LOVASZ_UPPER_RAT**5)
    ok_p3_lo, _ = check_nat_pow_bound(3207534329995, 10**12, 3, a3)
    ok_p3_hi, _ = check_nat_pow_bound(3207534329996, 10**12, 3, a3)
    ok = (
        a3 == 33
        and s4 == 115
        and 2 * s4 <= 7 * a3 < 2 * (s4 + 1)
        and s5_cond == 392
        and 2 * s5_cond == 7 * 112
        and s5_uncond == 402
        and lov5 == 401
        and lov5 < s5_uncond
        and ok_p3_lo
        and not ok_p3_hi
    )
    if not ok:
        return False, "MATH_MISMATCH", "Computed slice double-counting odd/even floor boundaries failed", {}
    return (
        True,
        "OK",
        f"Computed from |C_7^3|={a3}: floor(7*{a3}/2)={s4}, 7*112/2={s5_cond}, floor(theta^5)={lov5} < {s5_uncond}",
        {"a3": a3, "s4": s4, "s5_cond": s5_cond, "s5_uncond": s5_uncond, "lov5": lov5},
    )


def _t2_f11_03(ctx: SuiteContext):
    a3 = len(WITNESS_C7_POW3)
    s4 = (a3 * 7) // 2
    s5_cond = (112 * 7) // 2
    lov4_lo, lov4_hi = int(LOVASZ_LOWER_RAT**4), int(LOVASZ_UPPER_RAT**4)
    lov5_lo, lov5_hi = int(LOVASZ_LOWER_RAT**5), int(LOVASZ_UPPER_RAT**5)
    ok = (
        a3 == 33
        and lov4_lo == 121
        and lov4_hi == 121
        and lov5_lo == 401
        and lov5_hi == 401
        and 108 <= 112 <= s4 <= lov4_lo
        and 367 <= s5_cond <= lov5_lo
    )
    if not ok:
        return False, "MATH_MISMATCH", "Computed finite-power interval / Lovasz floor ordering failed", {}
    return (
        True,
        "OK",
        f"Computed exact floors: 108 <= 112 <= {s4} <= {lov4_lo}=floor(theta^4) and 367 <= {s5_cond} <= {lov5_lo}=floor(theta^5)",
        {"a3": a3, "s4": s4, "lov4": lov4_lo, "s5_cond": s5_cond, "lov5": lov5_lo},
    )


def _t2_f11_04(ctx: SuiteContext):
    tmp = Path(tempfile.mkdtemp(prefix="shannon_c7_t2_f11_"))
    try:
        os.chmod(tmp, 0o700)
        bad_rep = tmp / "UPPER_RESEARCH_REPORT.md"
        bad_rep.write_text(
            "# Upper Research Report\n"
            "We proved alpha(C_7^3) = 33 and audited Bukh-Cox / Bi-Tang / Sason obstructions.\n"
            "Bogus claim: α(C_7^4) <= 107 contradicts known 108-vertex lower bound.\n"
            + ("padding text for length " * 10),
            encoding="utf-8",
        )
        ok, code, info = verify_research_report(bad_rep, kind="upper")
        if ok or code != "REPORT_MISMATCH":
            return False, "MATH_MISMATCH", f"Impossible alpha(C_7^4)<=107 claim not rejected (ok={ok}, code={code})", info
        return True, "OK", "Upper report verifier rejected impossible alpha(C_7^4) <= 107 (< 108)", {}
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def _t2_f11_05(ctx: SuiteContext):
    mock_out = "'ShannonC7.alpha_c7_pow3' depends on axioms: [Lean.ofReduceBool, propext]\n"
    parsed = parse_print_axioms(mock_out)
    ok, code, info = verify_axiom_whitelist(parsed, required_decls=("ShannonC7.alpha_c7_pow3",))
    if ok or code != "AXIOM_VIOLATION":
        return False, "MATH_MISMATCH", f"native_decide axiom Lean.ofReduceBool not rejected (code={code})", info
    return True, "OK", "Axiom verifier rejected alpha_c7_pow3 depending on Lean.ofReduceBool", {}


# ---------------------------------------------------------------------------
# F12 — Obstruction Testbed BVA / Negative
# ---------------------------------------------------------------------------


def _t2_f12_01(ctx: SuiteContext):
    ok_sos, _ = validate_upper_bound_claim("C5", Fraction(2, 1))
    ok_lo, _ = validate_upper_bound_claim("C5", Fraction(22360679, 10**7))
    ok_hi, _ = validate_upper_bound_claim("C5", Fraction(22360680, 10**7))
    if ok_sos or ok_lo or not ok_hi:
        return False, "OBSTRUCTION_VIOLATION", f"C_5 boundary check failed (sos={ok_sos}, lo={ok_lo}, hi={ok_hi})", {}
    return True, "OK", "C_5 obstruction: 2 (SoS) & 2.2360679 REJECTED; 2.2360680 (> sqrt(5)) ACCEPTED", {}


def _t2_f12_02(ctx: SuiteContext):
    ok_sch, _ = validate_upper_bound_claim("SasonGilbert32", Fraction(4, 1))
    ok_lo, _ = validate_upper_bound_claim("SasonGilbert32", Fraction(44721359, 10**7))
    ok_lov, _ = validate_upper_bound_claim("SasonGilbert32", Fraction(16, 3))
    if ok_sch or ok_lo or not ok_lov:
        return False, "OBSTRUCTION_VIOLATION", f"Gilbert-32 check failed (sch={ok_sch}, lo={ok_lo}, lov={ok_lov})", {}
    return True, "OK", "Sason Gilbert-32: Schrijver 4 & 4.4721359 REJECTED; Lovasz 16/3 ACCEPTED", {}


def _t2_f12_03(ctx: SuiteContext):
    ok_bad, _ = validate_upper_bound_claim("SRG27", Fraction(59, 10))
    ok_haem, _ = validate_upper_bound_claim("SRG27", Fraction(7, 1))
    if ok_bad or not ok_haem:
        return False, "OBSTRUCTION_VIOLATION", f"SRG27 check failed (bad={ok_bad}, haem={ok_haem})", {}
    return True, "OK", "srg(27,10,1,5): 5.9 (< alpha=6) REJECTED; Haemers 7 (< Lovasz 9) ACCEPTED", {}


def _t2_f12_04(ctx: SuiteContext):
    ok_c7, _ = validate_upper_bound_claim("C7", Fraction(325, 100))
    ok_c7c, _ = validate_upper_bound_claim("C7_compl", Fraction(2, 1))
    if ok_c7 or ok_c7c:
        return False, "OBSTRUCTION_VIOLATION", f"C_7 / C_7^c invalid bounds not rejected (c7={ok_c7}, c7c={ok_c7c})", {}
    return True, "OK", "Invalid claims 3.25 on C_7 and 2.0 on C_7^c cleanly rejected", {}


def _t2_f12_05(ctx: SuiteContext):
    lovasz_bounds = (
        ("C5", Fraction(22360680, 10**7)),
        ("SasonGilbert32", Fraction(16, 3)),
        ("SRG27", Fraction(9, 1)),
        ("C7", LOVASZ_UPPER_RAT),
        ("C7_compl", COMPL_UPPER_RAT),
    )
    for g, b in lovasz_bounds:
        ok, msg = validate_upper_bound_claim(g, b)
        if not ok:
            return False, "OBSTRUCTION_VIOLATION", f"Lovasz theta ceiling failed on {g}: {msg}", {}
    return True, "OK", "Lovasz theta ceilings pass all 5 obstruction graphs with zero violations", {}


# ---------------------------------------------------------------------------
# F13 — Main.lean, Open-Problem Props & RESULTS.md BVA / Negative
# ---------------------------------------------------------------------------


def _t2_f13_01(ctx: SuiteContext):
    main_p = ctx.project_dir / "ShannonC7" / "Main.lean"
    if not main_p.is_file():
        return False, "MISSING_FILE", f"Missing {main_p}", {"path": str(main_p)}
    src, enc_viols = read_lean_source_strict(main_p, display_path="ShannonC7/Main.lean")
    if src is None:
        return (
            False,
            "HYGIENE_VIOLATION",
            f"Main.lean encoding/NUL violation: {enc_viols[0].message}",
            {"violations": [v.to_dict() for v in enc_viols]},
        )
    viols = scan_lean_hygiene(src, path="ShannonC7/Main.lean", mode="impl")
    if viols:
        return False, "HYGIENE_VIOLATION", f"Main.lean hygiene violation: {viols[0].message}", {"violations": [v.to_dict() for v in viols]}
    # Opaque-box kernel check via e2e_audit.lean (supports clean submodule re-exports in Main.lean)
    return check_decl_axioms(ctx, ("ShannonC7.strongPowPi", "E2EAudit.textbook_eq_project"))


def _t2_f13_02(ctx: SuiteContext):
    tmp = Path(tempfile.mkdtemp(prefix="shannon_c7_t2_f13_"))
    try:
        os.chmod(tmp, 0o700)
        p = tmp / "RESULTS.md"
        p.write_text(
            "# Results\n"
            "We proved Theta(C_7) = 3.258805369885 exactly! Exact solution proven in Lean.\n"
            "Small powers 3, 10, 33. Lovasz 3.317667207395. Open gap closed. Axioms: propext, Classical.choice, Quot.sound.\n"
            + ("additional summary content " * 8),
            encoding="utf-8",
        )
        ok, code, info = verify_results_md(p, lower_num=3258805369885, lower_den=10**12)
        if ok or code != "HONESTY_VIOLATION":
            return False, "MATH_MISMATCH", f"False exact-solution claim not caught (ok={ok}, code={code})", info
        return True, "OK", "Report honesty verifier rejected false exact-solution claim (HONESTY_VIOLATION)", {}
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def _t2_f13_03(ctx: SuiteContext):
    tmp = Path(tempfile.mkdtemp(prefix="shannon_c7_t2_f13p_"))
    try:
        os.chmod(tmp, 0o700)
        p = tmp / "RESULTS.md"
        p.write_text(
            "# Results\n"
            "Open problem gap remains below Lovasz 3.317667207395. Small powers 3, 10, 33.\n"
            "Axioms: propext, Classical.choice, Quot.sound. Certified 3.258805369885.\n"
            "TODO: fill in final benchmark table.\n" + ("context " * 25),
            encoding="utf-8",
        )
        ok, code, info = verify_results_md(p, lower_num=3258805369885, lower_den=10**12)
        if ok or code != "REPORT_MISMATCH":
            return False, "MATH_MISMATCH", f"Unresolved TODO placeholder not caught (ok={ok}, code={code})", info
        return True, "OK", "Report verifier rejected unresolved TODO/TBD/FIXME placeholder", {}
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def _t2_f13_04(ctx: SuiteContext):
    ok_b, code_b, info_b = ctx.get_main_bounds()
    if not ok_b:
        return False, code_b, info_b.get("reason", f"Main.lean bounds unavailable ({code_b})"), info_b
    ok, code, info = verify_results_md(
        ctx.project_dir / "RESULTS.md",
        lower_num=info_b["c7_lower_num"],
        lower_den=info_b["c7_lower_den"],
    )
    if not ok:
        return False, code, info.get("reason", f"RESULTS.md audit failed ({code})"), info
    return True, "OK", "Project RESULTS.md passed honesty, placeholder, and downward-truncation audit", info


def _t2_f13_05(ctx: SuiteContext):
    # `e2e_audit.lean` proves `audit_lovaszThetaC7_formula` (rfl) and `textbook_eq_project`
    return check_decl_axioms(
        ctx,
        ("ShannonC7.lovaszThetaC7", "E2EAudit.textbook_eq_project", "E2EAudit.audit_textbook_sandwich"),
    )


# ---------------------------------------------------------------------------
# F14 — Full Hygiene, #print axioms & Lexer/Runner BVA / Negative
# ---------------------------------------------------------------------------


def _t2_f14_01(ctx: SuiteContext):
    v_bad1 = scan_lean_hygiene("import ShannonC7.Main\nimport ShannonC7.Defs\n", mode="audit")
    v_bad2 = scan_lean_hygiene("import ShannonC7\n", mode="audit")
    v_good = scan_lean_hygiene("import ShannonC7.Main\nimport Mathlib.Combinatorics.SimpleGraph.CycleGraph\n", mode="audit")
    if not any(v.rule == "OPAQUE_BOX_VIOLATION" for v in v_bad1):
        return False, "HYGIENE_VIOLATION", "Audit mode failed to reject `import ShannonC7.Defs`", {}
    if not any(v.rule == "OPAQUE_BOX_VIOLATION" for v in v_bad2):
        return False, "HYGIENE_VIOLATION", "Audit mode failed to reject `import ShannonC7`", {}
    if v_good:
        return False, "HYGIENE_VIOLATION", f"False positive in clean audit fixture: {v_good}", {}
    return True, "OK", "Opaque-box audit mode rejected internal ShannonC7.* imports and accepted ShannonC7.Main", {}


def _t2_f14_02(ctx: SuiteContext):
    good_out = (
        "'A' does not depend on any axioms\n"
        "'B' depends on axioms: [Classical.choice,\n  Quot.sound, propext]\n"
    )
    ok_g, _, _ = verify_axiom_whitelist(parse_print_axioms(good_out), required_decls=("A", "B"))
    if not ok_g:
        return False, "MATH_MISMATCH", "Valid multiline #print axioms rejected", {}
    for bad_ax in ("sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler", "ShannonC7.fakeAx"):
        bad_out = f"'A' depends on axioms: [propext, {bad_ax}]\n"
        ok_b, c_b, _ = verify_axiom_whitelist(parse_print_axioms(bad_out), required_decls=("A",))
        if ok_b or c_b != "AXIOM_VIOLATION":
            return False, "MATH_MISMATCH", f"Disallowed axiom {bad_ax} not caught", {}
    ok_miss, c_miss, _ = verify_axiom_whitelist(parse_print_axioms(good_out), required_decls=("A", "B", "C"))
    if ok_miss or c_miss != "MISSING_AXIOM_REPORT":
        return False, "MATH_MISMATCH", "Missing theorem declaration not caught", {}
    return True, "OK", "#print axioms parser accepted valid multiline output and rejected all 4 cheat classes + missing decls", {}


def _t2_f14_03(ctx: SuiteContext):
    clean = (
        "-- sorry native_decide axiom\n"
        "/- /- sorry axiom -/ implemented_by -/\n"
        'def msg := "sorry native_decide unsafe"\n'
    )
    if scan_lean_hygiene(clean, mode="impl"):
        return False, "HYGIENE_VIOLATION", "False positive on comments / nested block comments / plain strings", {}
    live1 = "/- comment -/ sorry\n"
    live2 = 'def s := s!"val={sorry}"\n'
    v1 = scan_lean_hygiene(live1, mode="impl")
    v2 = scan_lean_hygiene(live2, mode="impl")
    if not (any(v.rule == "FORBIDDEN_SORRY" for v in v1) and any(v.rule == "FORBIDDEN_SORRY" for v in v2)):
        return False, "HYGIENE_VIOLATION", "Live sorry after block comment or inside s! interpolation missed", {}
    return True, "OK", "Nested comments/strings ignored while post-comment & interpolated s!\"{sorry}\" caught", {}


def _t2_f14_04(ctx: SuiteContext):
    clean = (
        "def no_sorry := 1\n"
        "def x' := 2\n"
        "def y'' := x'\n"
        "theorem ok_dec : 1 + 1 = 2 := by decide\n"
        "#print axioms ok_dec\n"
    )
    if scan_lean_hygiene(clean, mode="impl"):
        return False, "HYGIENE_VIOLATION", "False positive on no_sorry / x' / decide / #print axioms", {}
    bad_samples = (
        ("theorem t : True := by sorry\n", "FORBIDDEN_SORRY"),
        ("theorem t : True := by native_decide\n", "FORBIDDEN_NATIVE_DECIDE"),
        ("axiom bad : Prop\n", "FORBIDDEN_AXIOM"),
        ("set_option debug.skipKernelTC true\n", "FORBIDDEN_SKIP_KERNEL"),
        ("set_option _root_.debug.skipKernelTC true\n", "FORBIDDEN_SKIP_KERNEL"),
        ("def cheat := _root_.Lean.ofReduceBool\n", "FORBIDDEN_TRUST_AXIOM"),
        ("def cheat := _root_.Lean.«ofReduceBool»\n", "FORBIDDEN_TRUST_AXIOM"),
    )
    for src, expected_rule in bad_samples:
        viols = scan_lean_hygiene(src, mode="impl")
        if not any(v.rule == expected_rule for v in viols):
            return False, "HYGIENE_VIOLATION", f"Missed {expected_rule} in {src!r}", {}
    return True, "OK", "Identifier boundaries, primes, `decide`, `#print axioms` clean; live & _root_. cheats caught", {}


def _t2_f14_05(ctx: SuiteContext):
    # Empirically verified against Lean v4.32.2: `/-`, `/-/`, `/--/`, and `/-!/` are all unterminated comments,
    # whereas `/- -/`, `/---/`, `/-!-/` and `/- /- -/ -/` close cleanly.
    for src, label in (
        ("/- unclosed block comment\ndef x := 1\n", "/-"),
        ("/-/\ndef x := 1\n", "/-/"),
        ("/--/\ndef x := 1\n", "/--/"),
        ("/-!/\ndef x := 1\n", "/-!/"),
    ):
        viols = scan_lean_hygiene(src, mode="impl")
        if not any(v.rule == "UNCLOSED_BLOCK_COMMENT" for v in viols):
            return False, "HYGIENE_VIOLATION", f"Lean 4.32.2 unterminated comment `{label}` not flagged", {}
    for src, label in (
        ("/- -/\ndef x := 1\n", "/- -/"),
        ("/---/\ndef x := 1\n", "/---/"),
        ("/-!-/\ndef x := 1\n", "/-!-/"),
        ("/- /- -/ -/\ndef x := 1\n", "/- /- -/ -/"),
    ):
        viols = scan_lean_hygiene(src, mode="impl")
        if viols:
            return False, "HYGIENE_VIOLATION", f"Valid closed comment `{label}` falsely flagged: {viols}", {}
    return True, "OK", "Block/doc comment lexer matches Lean v4.32.2 (`/-`, `/-/`, `/--/`, `/-!/` unclosed; `/- -/`, `/---/`, `/-!-/` closed)", {}


def get_tier2_tests() -> list[TestCase]:
    return [
        # F01
        TestCase("T2-F01-01", "T2", "F01", "BVA: lean-toolchain exact single-line format rejects wrong versions", _t2_f01_01),
        TestCase("T2-F01-02", "T2", "F01", "Negative: lakefile.toml free of retired Azure URL & unpinned main/master", _t2_f01_02),
        TestCase("T2-F01-03", "T2", "F01", "BVA: valid UTF-8 & zero NUL bytes across all ShannonC7/**/*.lean", _t2_f01_03),
        TestCase("T2-F01-04", "T2", "F01", "Negative: wholesale `import Mathlib` rejected while leaf import accepted", _t2_f01_04),
        TestCase("T2-F01-05", "T2", "F01", "Corner: commented `/- import Mathlib -/` ignored & zero unclosed comments", _t2_f01_05),
        # F02
        TestCase("T2-F02-01", "T2", "F02", "BVA: d=0 strictly excluded from shannonSet & rejected by verifiers", _t2_f02_01),
        TestCase("T2-F02-02", "T2", "F02", "BVA: d=1 boundary alpha(C_7^1)=3 and textbook equivalence", _t2_f02_02),
        TestCase("T2-F02-03", "T2", "F02", "Corner: C_7 cyclic wrap-around 0~6, non-adj 0!~{2..5}, looplessness", _t2_f02_03),
        TestCase("T2-F02-04", "T2", "F02", "Negative: strong-power conflict (0,0,0)~(0,0,1) & wrap-around (0,0,6) caught", _t2_f02_04),
        TestCase("T2-F02-05", "T2", "F02", "Corner: distance-2 coordinate diff (0,0,0) vs (2,0,0) verified independent", _t2_f02_05),
        # F03
        TestCase("T2-F03-01", "T2", "F03", "BVA: 8-digit cubic boundary p(331766720/10^8) < 0 < p(331766721/10^8)", _t2_f03_01),
        TestCase("T2-F03-02", "T2", "F03", "BVA: 12-digit cubic boundary ...394/10^12 < theta < ...395/10^12", _t2_f03_02),
        TestCase("T2-F03-03", "T2", "F03", "BVA: 15-digit & 30-digit bisection catches float64 ...095 vs ...096 trap", _t2_f03_03),
        TestCase("T2-F03-04", "T2", "F03", "Negative: perturbed W_7 non-edge (+1e-6) and beta (+1e-6) fail PSD check", _t2_f03_04),
        TestCase("T2-F03-05", "T2", "F03", "Corner: Lovasz ceiling strictly beats fractional clique cover 7/2", _t2_f03_05),
        # F04
        TestCase("T2-F04-01", "T2", "F04", "BVA: derivative critical point p'(7/3)=0 & strict monotonicity past 7/3", _t2_f04_01),
        TestCase("T2-F04-02", "T2", "F04", "BVA: all 6 rational-root candidates +/-1,+/-7,+/-49 exact nonzero", _t2_f04_02),
        TestCase("T2-F04-03", "T2", "F04", "BVA: c7_lovasz_unattainable instantiated at d=1,2,3 in e2e_audit.lean", _t2_f04_03),
        TestCase("T2-F04-04", "T2", "F04", "Negative: Haemers rank<=3 blocked on C_7 (3-clique leaves vertex 6 zero)", _t2_f04_04),
        TestCase("T2-F04-05", "T2", "F04", "Corner: complement srg(27,16,10,8) has rank_Q(I-A_bar)=27 > 3=alpha", _t2_f04_05),
        # F05
        TestCase("T2-F05-01", "T2", "F05", "BVA: minimum odd cycle k=1 (C_3) tight equality theta(C_3)=1", _t2_f05_01),
        TestCase("T2-F05-02", "T2", "F05", "BVA: k=2 (C_5) tight equality Theta(C_5)=sqrt(5)", _t2_f05_02),
        TestCase("T2-F05-03", "T2", "F05", "BVA: decreasing complement cubic q(2109916264174/10^12) > 0 > q(...175)", _t2_f05_03),
        TestCase("T2-F05-04", "T2", "F05", "BVA: exact integer 17^(1/4) floor/ceiling & strict gap < theta(C_7^c)", _t2_f05_04),
        TestCase("T2-F05-05", "T2", "F05", "Negative: single cyclic-dist-2 mutation in C_7^c^4 17-word witness rejected", _t2_f05_05),
        # F06
        TestCase("T2-F06-01", "T2", "F06", "Negative BVA: Gao d=200 rounded-up ...909 rejected while ...908 passes", _t2_f06_01),
        TestCase("T2-F06-02", "T2", "F06", "Negative BVA: Polak-Schrijver & BPZ +1 ULP rejected while floors pass", _t2_f06_02),
        TestCase("T2-F06-03", "T2", "F06", "BVA: exact equality 3^3 == 1^3*27 accepted; den=0, d=0, num<0 rejected", _t2_f06_03),
        TestCase("T2-F06-04", "T2", "F06", "BVA: d=500 >7500-digit integer power safe under Python 3.12 limit", _t2_f06_04),
        TestCase("T2-F06-05", "T2", "F06", "Negative BVA: Trie7 rejects duplicate vertex & single conflict in C_7^3", _t2_f06_05),
        # F07
        TestCase("T2-F07-01", "T2", "F07", "Negative BVA: all C(7,4)=35 four-vertex subsets of C_7 fail independence", _t2_f07_01),
        TestCase("T2-F07-02", "T2", "F07", "BVA: all 39 extensions of 10-word C_7^2 witness fail independence", _t2_f07_02),
        TestCase("T2-F07-03", "T2", "F07", "Negative BVA: single coordinate mutation in C_7^3 33-set caught", _t2_f07_03),
        TestCase("T2-F07-04", "T2", "F07", "Negative BVA: C_7^5 343+1 conflict & C_7^3 duplicate vertex caught", _t2_f07_04),
        TestCase("T2-F07-05", "T2", "F07", "BVA: exact integer strict progression 3 < 10^(1/2) < 33^(1/3) < 108^(1/4) < 367^(1/5)", _t2_f07_05),
        # F08
        TestCase("T2-F08-01", "T2", "F08", "BVA: degenerate b=0 profile reduces to plain Cartesian product", _t2_f08_01),
        TestCase("T2-F08-02", "T2", "F08", "BVA: boundary b==a and d==c preserves invariants with zero underflow", _t2_f08_02),
        TestCase("T2-F08-03", "T2", "F08", "Negative BVA: invalid profiles (b>a, d>c) cleanly rejected", _t2_f08_03),
        TestCase("T2-F08-04", "T2", "F08", "BVA: exact integer homogeneous turnover peak at k=40 & Itty +64 gain", _t2_f08_04),
        TestCase("T2-F08-05", "T2", "F08", "Negative BVA: ValidTuple privacy leak & disjointness leak caught", _t2_f08_05),
        # F09
        TestCase("T2-F09-01", "T2", "F09", "Negative BVA: malformed tuple length (4-tuple in d=5) rejected", _t2_f09_01),
        TestCase("T2-F09-02", "T2", "F09", "Negative BVA: out-of-range ZMod 7 coordinates (-1 and 7) rejected", _t2_f09_02),
        TestCase("T2-F09-03", "T2", "F09", "BVA: single-word witness accepted & empty witness rejected for lower bound", _t2_f09_03),
        TestCase("T2-F09-04", "T2", "F09", "Project Main.lean exports positive c7_lower_num and c7_lower_den", _t2_f09_04),
        TestCase("T2-F09-05", "T2", "F09", "Negative: inflated RESULTS.md bound rejected by cross-checker", _t2_f09_05),
        # F10
        TestCase("T2-F10-01", "T2", "F10", "Negative BVA: vacuous c7_lower_den = 0 rejected cleanly (no ZeroDivisionError)", _t2_f10_01),
        TestCase("T2-F10-02", "T2", "F10", "BVA: -1 ULP below BPZ floor (...884) rejected while exact floor (...885) passes", _t2_f10_02),
        TestCase("T2-F10-03", "T2", "F10", "Negative BVA: cubic trap 33176672073945/10^13 & upper ceiling rejected", _t2_f10_03),
        TestCase("T2-F10-04", "T2", "F10", "BVA: reduced non-power-of-10 fraction accepted via cross-multiplication", _t2_f10_04),
        TestCase("T2-F10-05", "T2", "F10", "Project frontier gap width strictly satisfies 0 < upper - lower < 0.06", _t2_f10_05),
        # F11
        TestCase("T2-F11-01", "T2", "F11", "BVA: e2e_audit.lean explicitly proves ¬ (34 <= indepNum(C_7^3))", _t2_f11_01),
        TestCase("T2-F11-02", "T2", "F11", "BVA: odd/even slice double-counting floor boundaries (115, 392, 402)", _t2_f11_02),
        TestCase("T2-F11-03", "T2", "F11", "BVA: finite-power interval ordering 108<=112<=115<=121 & 367<=392<=401", _t2_f11_03),
        TestCase("T2-F11-04", "T2", "F11", "Negative: upper report claiming alpha(C_7^4) <= 107 rejected", _t2_f11_04),
        TestCase("T2-F11-05", "T2", "F11", "Negative: alpha_c7_pow3 using Lean.ofReduceBool rejected by axiom verifier", _t2_f11_05),
        # F12
        TestCase("T2-F12-01", "T2", "F12", "Negative BVA: C_5 SoS 2.0 & 2.2360679 rejected; 2.2360680 accepted", _t2_f12_01),
        TestCase("T2-F12-02", "T2", "F12", "Negative BVA: Sason Gilbert-32 Schrijver 4 & 4.4721359 rejected; 16/3 accepted", _t2_f12_02),
        TestCase("T2-F12-03", "T2", "F12", "Negative BVA: srg(27,10,1,5) 5.9 rejected; Haemers 7 (< 9) accepted", _t2_f12_03),
        TestCase("T2-F12-04", "T2", "F12", "Negative BVA: invalid bounds 3.25 on C_7 and 2.0 on C_7^c rejected", _t2_f12_04),
        TestCase("T2-F12-05", "T2", "F12", "Positive BVA: Lovasz theta ceilings pass all 5 obstruction graphs", _t2_f12_05),
        # F13
        TestCase("T2-F13-01", "T2", "F13", "Main.lean uses canonical SimpleGraph.cycleGraph 7 & strongPowPi cleanly", _t2_f13_01),
        TestCase("T2-F13-02", "T2", "F13", "Negative: false exact-solution claim in RESULTS.md triggers HONESTY_VIOLATION", _t2_f13_02),
        TestCase("T2-F13-03", "T2", "F13", "Negative: unresolved TODO/TBD/FIXME in RESULTS.md rejected", _t2_f13_03),
        TestCase("T2-F13-04", "T2", "F13", "Project RESULTS.md passes honesty, placeholder & downward-truncation audit", _t2_f13_04),
        TestCase("T2-F13-05", "T2", "F13", "Anti-tampering: audit_lovaszThetaC7_formula & textbook_eq_project verified", _t2_f13_05),
        # F14
        TestCase("T2-F14-01", "T2", "F14", "Negative: audit mode rejects internal ShannonC7.* imports & accepts Main", _t2_f14_01),
        TestCase("T2-F14-02", "T2", "F14", "Negative: #print axioms rejects sorryAx/ofReduceBool/trustCompiler/custom/missing", _t2_f14_02),
        TestCase("T2-F14-03", "T2", "F14", "BVA: nested comments & plain strings clean; post-comment & s!\"{sorry}\" caught", _t2_f14_03),
        TestCase("T2-F14-04", "T2", "F14", "BVA: no_sorry/x'/decide/#print axioms clean; live sorry/native_decide/skipKernelTC caught", _t2_f14_04),
        TestCase("T2-F14-05", "T2", "F14", "BVA: Lean v4.32.2 unclosed `/-`, `/-/`, `/--/`, `/-!/` flagged while `/- -/`, `/---/`, `/-!-/` close", _t2_f14_05),
    ]
