#!/usr/bin/env python3
"""Tier 1 — Category-Partition Isolated Feature Tests (70 tests: T1-F01-01 .. T1-F14-05).

5 isolated opaque-box tests per feature area across all 14 features (F01-F14).
Never skips or fake-passes missing project artifacts; emits crisp structured FAIL codes.
"""

from __future__ import annotations

import ast
from fractions import Fraction
import json
import re
from typing import Any

from common import SuiteContext, TestCase, check_decl_axioms, run_subprocess_safe
from cross_check import (
    BPZ_D200_EXACT_N,
    BPZ_LEAN_RECORD,
    FLOOR_LOWER,
    GAO_D200_EXACT_N,
    LOVASZ_LOWER_RAT,
    LOVASZ_UPPER_RAT,
    REQUIRED_AUDIT_AXIOM_DECLS,
    TANDON_RECORD,
    WITNESS_C5_POW2,
    WITNESS_C7_COMPL_POW4,
    WITNESS_C7_POW1,
    WITNESS_C7_POW2,
    WITNESS_C7_POW3,
    Profile,
    Trie7,
    build_c7_pow5_linear_343,
    build_polak_schrijver_clean_327,
    build_synthetic_c7_valid_tuple,
    c5_adj,
    c7_adj,
    c7_compl_adj,
    check_frontier_rational_bounds,
    check_nat_pow_bound,
    cubic_p,
    exact_rational_rank,
    profile_star,
    safe_int_preview,
    scan_lean_hygiene,
    split_tree_pow,
    verify_c5_obstruction,
    verify_c7_compl_psd,
    verify_c7_fourier_psd,
    verify_cubic_irreducibility_and_roots,
    verify_gilbert32_obstruction,
    verify_odd_cycle_lovasz_table,
    verify_profile_dp,
    verify_research_report,
    verify_results_md,
    verify_srg27_obstruction,
    verify_strong_power_independent_set,
    verify_valid_tuple,
    verify_witness_json,
)

# ---------------------------------------------------------------------------
# Helpers for static file presence & hygiene
# ---------------------------------------------------------------------------


def _check_lean_files_present_and_clean(
    ctx: SuiteContext, rel_paths: tuple[str, ...]
) -> tuple[bool, str, str, dict[str, Any]]:
    missing = []
    violations = []
    for rel in rel_paths:
        p = ctx.project_dir / rel
        if not p.is_file():
            missing.append(rel)
            continue
        raw = p.read_bytes()
        if b"\x00" in raw:
            return False, "HYGIENE_VIOLATION", f"NUL byte detected in {rel}", {"path": rel}
        try:
            src = raw.decode("utf-8")
        except UnicodeDecodeError as exc:
            return False, "HYGIENE_VIOLATION", f"Invalid UTF-8 in {rel}: {exc}", {"path": rel}
        viols = scan_lean_hygiene(src, path=rel, mode="impl")
        violations.extend(viols)
    if missing:
        return (
            False,
            "MISSING_FILE",
            f"Missing required Lean module(s): {', '.join(missing)}",
            {"missing": missing},
        )
    if violations:
        v0 = violations[0]
        return (
            False,
            "HYGIENE_VIOLATION",
            f"{len(violations)} hygiene violation(s) in {rel_paths}; first at {v0.path}:{v0.line} [{v0.rule}] `{v0.token}`",
            {"violations": [v.to_dict() for v in violations]},
        )
    return True, "OK", f"Verified {len(rel_paths)} module(s) present and hygiene-clean", {"files": list(rel_paths)}


# ---------------------------------------------------------------------------
# F01 — Toolchain & Build/Solver Environment
# ---------------------------------------------------------------------------


def _t1_f01_01(ctx: SuiteContext):
    p = ctx.project_dir / "lean-toolchain"
    if not p.is_file():
        return False, "MISSING_FILE", f"Missing {p}", {"path": str(p)}
    content = p.read_text(encoding="utf-8", errors="replace").strip()
    expected = "leanprover/lean4:v4.32.2"
    if content != expected:
        return False, "MATH_MISMATCH", f"lean-toolchain is {content!r}, expected {expected!r}", {"actual": content}
    return True, "OK", f"lean-toolchain pinned to {expected}", {"toolchain": content}


def _t1_f01_02(ctx: SuiteContext):
    p = ctx.project_dir / "lakefile.toml"
    if not p.is_file():
        return False, "MISSING_FILE", f"Missing {p}", {"path": str(p)}
    txt = p.read_text(encoding="utf-8", errors="replace")
    has_lib = "ShannonC7" in txt
    has_mathlib = "mathlib" in txt.lower()
    has_pin = "v4.32.2" in txt
    if not (has_lib and has_mathlib and has_pin):
        return (
            False,
            "REPORT_MISMATCH",
            f"lakefile.toml missing required declarations (ShannonC7={has_lib}, mathlib={has_mathlib}, v4.32.2={has_pin})",
            {"has_lib": has_lib, "has_mathlib": has_mathlib, "has_pin": has_pin},
        )
    return True, "OK", "lakefile.toml declares ShannonC7 and pins mathlib v4.32.2", {"path": str(p)}


def _t1_f01_03(ctx: SuiteContext):
    p = ctx.project_dir / "lake-manifest.json"
    if not p.is_file():
        return False, "MISSING_FILE", f"Missing {p}", {"path": str(p)}
    try:
        data = json.loads(p.read_text(encoding="utf-8"))
    except Exception as exc:
        return False, "MATH_MISMATCH", f"Invalid JSON in lake-manifest.json: {exc}", {"path": str(p)}
    pkgs = data.get("packages", []) if isinstance(data, dict) else []
    mathlib_pkgs = [pk for pk in pkgs if isinstance(pk, dict) and pk.get("name") == "mathlib"]
    if not mathlib_pkgs:
        return False, "REPORT_MISMATCH", "lake-manifest.json does not lock a `mathlib` package entry", {"packages": len(pkgs)}
    return True, "OK", f"lake-manifest.json valid JSON locking mathlib ({len(pkgs)} packages)", {"packages": len(pkgs)}


def _t1_f01_04(ctx: SuiteContext):
    script = ctx.project_dir / "scripts" / "verify_axioms.sh"
    if not script.is_file():
        return False, "MISSING_FILE", f"Missing {script}", {"path": str(script)}
    if script.stat().st_size == 0:
        return False, "REPORT_MISMATCH", "scripts/verify_axioms.sh is empty", {"path": str(script)}
    out = run_subprocess_safe(["bash", "-n", str(script)], timeout=15)
    if not out.ok:
        return False, "SUBPROCESS_FAILED", f"bash -n failed on verify_axioms.sh: {out.stderr.strip()}", {"rc": out.returncode}
    ok_m, code_m, msg_m, info_m = ctx.check_mathlib_cache()
    if not ok_m:
        return False, code_m, msg_m, info_m
    return True, "OK", "scripts/verify_axioms.sh syntax-valid and Mathlib .olean cache present", info_m


def _t1_f01_05(ctx: SuiteContext):
    ok, code, msg, info = ctx.scan_all_lean_files()
    if not ok and code in ("MISSING_DIR", "MISSING_FILE"):
        return False, code, msg, info
    enc_errs = info.get("encoding_errors", [])
    if enc_errs:
        return (
            False,
            "HYGIENE_VIOLATION",
            f"Encoding/NUL error prevented wholesale-import scan: {enc_errs[0]}",
            {"encoding_errors": enc_errs},
        )
    wholesale = [v for v in info.get("violations", []) if v.get("rule") == "WHOLESALE_MATHLIB_IMPORT"]
    if wholesale:
        return (
            False,
            "WHOLESALE_IMPORT",
            f"Found {len(wholesale)} wholesale `import Mathlib` statement(s); first at {wholesale[0]['path']}:{wholesale[0]['line']}",
            {"wholesale": wholesale},
        )
    return True, "OK", f"Zero wholesale `import Mathlib` across {info.get('files_scanned', 0)} .lean files", {"files_scanned": info.get("files_scanned", 0)}


# ---------------------------------------------------------------------------
# F02 — Core Shannon Capacity & Fekete Library
# ---------------------------------------------------------------------------


def _t1_f02_01(ctx: SuiteContext):
    return check_decl_axioms(ctx, ("ShannonC7.strongPowPi",))


def _t1_f02_02(ctx: SuiteContext):
    return check_decl_axioms(ctx, ("ShannonC7.c7_shannonCapacity_tendsto",))


def _t1_f02_03(ctx: SuiteContext):
    return check_decl_axioms(ctx, ("E2EAudit.textbook_eq_project", "ShannonC7.shannonCapacity"))


def _t1_f02_04(ctx: SuiteContext):
    # Verify C_7 graph axioms + strong-product symmetry & supermultiplicativity for d=1,2,3
    for u in range(7):
        if c7_adj(u, u):
            return False, "MATH_MISMATCH", f"C_7 has self-loop at {u}", {}
        deg = sum(1 for v in range(7) if c7_adj(u, v))
        if deg != 2:
            return False, "MATH_MISMATCH", f"C_7 degree({u}) = {deg} != 2", {}
        for v in range(7):
            if c7_adj(u, v) != c7_adj(v, u):
                return False, "MATH_MISMATCH", f"C_7 asymmetric at ({u},{v})", {}
    # Verify Cartesian concatenation of C_7^1 (3) and C_7^2 (10) gives valid 30-set in C_7^3 (<= 33)
    prod_30 = [a + b for a in WITNESS_C7_POW1 for b in WITNESS_C7_POW2]
    ok, code, info = verify_strong_power_independent_set(prod_30, c7_adj, 3, domain_size=7)
    if not ok or info["card"] != 30:
        return False, code, "Strong-product concatenation C_7^1 x C_7^2 -> C_7^3 failed", info
    return True, "OK", "C_7 is 2-regular/symmetric/loopless and strong-product concatenation (3*10=30 <= 33) verified", info


def _t1_f02_05(ctx: SuiteContext):
    return _check_lean_files_present_and_clean(
        ctx, ("ShannonC7/Defs.lean", "ShannonC7/Fekete.lean", "ShannonC7/CycleC7.lean")
    )


# ---------------------------------------------------------------------------
# F03 — Lovasz Upper-Bound Engine & Exact theta(C_7)
# ---------------------------------------------------------------------------


def _t1_f03_01(ctx: SuiteContext):
    return check_decl_axioms(ctx, ("ShannonC7.lovaszThetaC7",))


def _t1_f03_02(ctx: SuiteContext):
    return check_decl_axioms(ctx, ("ShannonC7.c7_upper_lovasz",))


def _t1_f03_03(ctx: SuiteContext):
    return check_decl_axioms(ctx, ("ShannonC7.c7_upper_rational",))


def _t1_f03_04(ctx: SuiteContext):
    return check_decl_axioms(ctx, ("ShannonC7.c5_shannonCapacity_eq_sqrt_five",))


def _t1_f03_05(ctx: SuiteContext):
    ok1, c1, i1 = verify_c7_fourier_psd()
    if not ok1:
        return False, c1, "Rank-4 Fourier dual PSD / primal SDP verification failed", i1
    if not (cubic_p(LOVASZ_LOWER_RAT) < 0 < cubic_p(LOVASZ_UPPER_RAT)):
        return False, "MATH_MISMATCH", "12-digit cubic enclosure failed", {}
    return True, "OK", "Rank-4 Fourier dual PSD (modes {1,2,5,6}), primal SDP X, and 12-digit cubic enclosure verified", i1


# ---------------------------------------------------------------------------
# F04 — Galois Unattainability & Haemers Obstruction
# ---------------------------------------------------------------------------


def _t1_f04_01(ctx: SuiteContext):
    return check_decl_axioms(ctx, ("ShannonC7.c7_lovasz_unattainable",))


def _t1_f04_02(ctx: SuiteContext):
    ok, code, info = verify_cubic_irreducibility_and_roots()
    if not ok:
        return False, code, "Cubic irreducibility verification failed", info
    return True, "OK", "p(t) = t^3 + 7t^2 - 49t + 49 verified irreducible over F_3 and Q (all 6 rational candidates nonzero)", info


def _t1_f04_03(ctx: SuiteContext):
    b1 = cubic_p(Fraction(-12)) < 0 < cubic_p(Fraction(-11))
    b2 = cubic_p(Fraction(1)) > 0 > cubic_p(Fraction(2))
    b3 = cubic_p(Fraction(3)) < 0 < cubic_p(Fraction(4))
    if not (b1 and b2 and b3):
        return False, "MATH_MISMATCH", "Disjoint 3-root separation brackets failed", {}
    return (
        True,
        "OK",
        "All 3 real roots strictly separated in (-12,-11), (1,2), (3,4) => |r2| < 2 < 3 < |r3| < 4 < 11 < |r1|",
        {"brackets": ["(-12,-11)", "(1,2)", "(3,4)"]},
    )


def _t1_f04_04(ctx: SuiteContext):
    # 4-clique cover fitting matrix for C_7: blocks {0,1}, {2,3}, {4,5}, {6}
    blocks = ((0, 1), (2, 3), (4, 5), (6,))
    M = [[0] * 7 for _ in range(7)]
    for blk in blocks:
        for u in blk:
            for v in blk:
                M[u][v] = 1
    # Verify fitting property on C_7: diag != 0, non-edges == 0
    for u in range(7):
        if M[u][u] == 0:
            return False, "MATH_MISMATCH", "Clique-cover matrix zero on diagonal", {}
        for v in range(7):
            if u != v and not c7_adj(u, v) and M[u][v] != 0:
                return False, "MATH_MISMATCH", f"Non-edge ({u},{v}) nonzero in C_7 fitting matrix", {}
    r_c7 = exact_rational_rank(M)
    if r_c7 != 4 or not (3 * 3 < 10):
        return False, "MATH_MISMATCH", f"Unexpected C_7 fitting rank {r_c7}", {}
    ok_srg, code_srg, info_srg = verify_srg27_obstruction()
    if not ok_srg:
        return False, code_srg, "srg(27,10,1,5) Haemers rank-7 verification failed", info_srg
    return True, "OK", "C_7 4-clique fitting rank=4 (>= ceil(sqrt(10))=4) and srg(27,10,1,5) rank_Q(I-A)=7 < 9 verified", info_srg


def _t1_f04_05(ctx: SuiteContext):
    return _check_lean_files_present_and_clean(
        ctx, ("ShannonC7/CubicBounds.lean", "ShannonC7/Haemers.lean")
    )


# ---------------------------------------------------------------------------
# F05 — Generalizations (Upper): C_7^c & Odd Cycles C_{2k+1}
# ---------------------------------------------------------------------------


def _t1_f05_01(ctx: SuiteContext):
    return check_decl_axioms(ctx, ("ShannonC7.c7_compl_sandwich",))


def _t1_f05_02(ctx: SuiteContext):
    return check_decl_axioms(ctx, ("ShannonC7.oddCycle_upper_lovasz",))


def _t1_f05_03(ctx: SuiteContext):
    # `e2e_audit.lean` explicitly instantiates oddCycle_upper_lovasz at k=1,2,3,4
    audit = ctx.run_lean_audit()
    if not audit.ok:
        return False, audit.code, audit.message, {"returncode": audit.returncode}
    return True, "OK", "oddCycle_upper_lovasz instantiated cleanly at k=1,2,3,4 (C_3,C_5,C_7,C_9) in e2e_audit.lean", {}


def _t1_f05_04(ctx: SuiteContext):
    ok, code, info = verify_c7_compl_psd()
    if not ok:
        return False, code, "Complement C_7^c cubic / Rank-2 PSD verification failed", info
    return True, "OK", "theta(C_7^c)=1+sec(pi/7)=7/theta(C_7), cubic q(u), and Rank-2 dual PSD verified", info


def _t1_f05_05(ctx: SuiteContext):
    ok, code, info = verify_odd_cycle_lovasz_table()
    if not ok:
        return False, code, "Odd-cycle Lovasz table verification failed", info
    return True, "OK", "Verified theta(C_{2k+1}) < (2k+1)/2 for k=1..7 & k=100 (C_3=1, C_5=sqrt(5), C_7~3.317667)", info


# ---------------------------------------------------------------------------
# F06 — Pure-Kernel Radix-7 Trie Verifier & Exact Decimal Bridge
# ---------------------------------------------------------------------------


def _t1_f06_01(ctx: SuiteContext):
    return _check_lean_files_present_and_clean(
        ctx, ("ShannonC7/TrieVerifier.lean", "ShannonC7/Decimal.lean")
    )


def _t1_f06_02(ctx: SuiteContext):
    return check_decl_axioms(
        ctx,
        (
            "ShannonC7.alpha_c7_pow3",
            "ShannonC7.c7_lower_num",
            "ShannonC7.c7_lower_den",
            "ShannonC7.c7_lower_frontier",
            "ShannonC7.c7_shannonCapacity_sandwich",
        ),
    )


def _t1_f06_03(ctx: SuiteContext):
    benchmarks = (
        ("C7^1", 3000000000000, 10**12, 1, 3),
        ("C7^2", 3162277660168, 10**12, 2, 10),
        ("C7^3", 3207534329995, 10**12, 3, 33),
        ("C7^4", 3223709795470, 10**12, 4, 108),
        ("C7^5_lin", 3214095849716, 10**12, 5, 343),
        ("C7^5_PS", 3257865966783, 10**12, 5, 367),
        ("C7^10_Itty", 3258020737293, 10**12, 10, 134753),
        ("C7^200_Gao", 3258789153908, 10**12, 200, GAO_D200_EXACT_N),
        ("C7^200_BPZ", 3258805369885, 10**12, 200, BPZ_D200_EXACT_N),
        ("C7c^4", 2030543184868, 10**12, 4, 17),
    )
    for label, num, den, d, N in benchmarks:
        ok, msg = check_nat_pow_bound(num, den, d, N)
        if not ok:
            return False, "MATH_MISMATCH", f"Exact power check failed on {label}: {msg}", {"label": label}
    return True, "OK", f"Exact integer power inequality num^d <= den^d * N verified across {len(benchmarks)} milestones", {"count": len(benchmarks)}


def _t1_f06_04(ctx: SuiteContext):
    t33, c33, i33 = Trie7.from_vertices(WITNESS_C7_POW3, 3)
    if t33 is None or t33.card() != 33 or not t33.is_indep():
        return False, c33, "Trie7 failed on 33-word C_7^3 witness", i33
    lin343 = build_c7_pow5_linear_343()
    t343, c343, i343 = Trie7.from_vertices(lin343, 5)
    if t343 is None or t343.card() != 343 or not t343.is_indep():
        return False, c343, "Trie7 failed on 343-word C_7^5 linear witness", i343
    # Verify disjointness on split halves of C_7^3 witness
    ta, _, _ = Trie7.from_vertices(WITNESS_C7_POW3[:16], 3)
    tb, _, _ = Trie7.from_vertices(WITNESS_C7_POW3[16:], 3)
    if ta is None or tb is None or not ta.disjoint(tb) or ta.disjoint(ta):
        return False, "MATH_MISMATCH", "Trie7 disjointness check failed", {}
    return True, "OK", "Reference Trie7 verified cardinality, independence & disjointness on C_7^3 (33) and C_7^5 (343)", {"c7_3": 33, "c7_5": 343}


def _t1_f06_05(ctx: SuiteContext):
    ok, code, info = ctx.get_main_bounds()
    if not ok:
        return False, code, info.get("reason", f"Could not extract Main.lean bounds ({code})"), info
    num, den = info["c7_lower_num"], info["c7_lower_den"]
    if num <= 0 or den <= 0:
        return (
            False,
            "BOUNDS_VIOLATION",
            f"Invalid c7_lower_num={safe_int_preview(num)}, c7_lower_den={safe_int_preview(den)}",
            info,
        )
    return (
        True,
        "OK",
        f"Extracted positive exact rational c7_lower ({safe_int_preview(num)}/{safe_int_preview(den)}, source={info['source']})",
        info,
    )


# ---------------------------------------------------------------------------
# F07 — Certified Small Powers (d=1..5) & C_7^c Lower Bound
# ---------------------------------------------------------------------------


def _t1_f07_01(ctx: SuiteContext):
    return check_decl_axioms(ctx, ("ShannonC7.alpha_c7_pow1",))


def _t1_f07_02(ctx: SuiteContext):
    return check_decl_axioms(ctx, ("ShannonC7.alpha_c7_pow2",))


def _t1_f07_03(ctx: SuiteContext):
    return check_decl_axioms(ctx, ("ShannonC7.alpha_c7_pow3",))


def _t1_f07_04(ctx: SuiteContext):
    ok, code, msg, info = check_decl_axioms(ctx, ("ShannonC7.c7_compl_sandwich",))
    if not ok:
        return False, code, msg, info
    ok_w, code_w, info_w = verify_strong_power_independent_set(
        WITNESS_C7_COMPL_POW4, c7_compl_adj, 4, domain_size=7
    )
    if not ok_w or info_w["card"] != 17:
        return False, code_w, "Independent 17-word C_7^c^4 witness check failed", info_w
    return True, "OK", "c7_compl_sandwich lower half 17^(1/4) <= Theta(C_7^c) & 17-word witness verified", info_w


def _t1_f07_05(ctx: SuiteContext):
    lin343 = build_c7_pow5_linear_343()
    ps327 = build_polak_schrijver_clean_327()
    checks = (
        ("C7^1", WITNESS_C7_POW1, c7_adj, 1, 7, 3),
        ("C7^2", WITNESS_C7_POW2, c7_adj, 2, 7, 10),
        ("C7^3", WITNESS_C7_POW3, c7_adj, 3, 7, 33),
        ("C7^5_lin", lin343, c7_adj, 5, 7, 343),
        ("C7^5_PS_seed", ps327, c7_adj, 5, 7, 327),
        ("C7c^4", WITNESS_C7_COMPL_POW4, c7_compl_adj, 4, 7, 17),
    )
    for label, verts, fn, d, dom, exp_n in checks:
        ok, code, info = verify_strong_power_independent_set(verts, fn, d, domain_size=dom)
        if not ok or info["card"] != exp_n:
            return False, code, f"Witness {label} failed (expected {exp_n}, got {info})", info
    return _check_lean_files_present_and_clean(ctx, ("ShannonC7/SmallPowers.lean",))


# ---------------------------------------------------------------------------
# F08 — Constructive ValidTuple.star & Heterogeneous/Layered Engine
# ---------------------------------------------------------------------------


def _t1_f08_01(ctx: SuiteContext):
    return _check_lean_files_present_and_clean(
        ctx, ("ShannonC7/ValidTuple.lean", "ShannonC7/HeteroLayered.lean")
    )


def _t1_f08_02(ctx: SuiteContext):
    base = Profile(367, 8, 367, 321)
    itty = profile_star(base, base)
    if itty.a != 134753:
        return False, "MATH_MISMATCH", f"Expected Itty a=134753, got {itty.a}", {"itty": itty.__dict__}
    return True, "OK", "Exact Profile.star: (367,8,367,321) * (367,8,367,321) yields a = 134753 (Itty d=10)", {"itty_a": itty.a}


def _t1_f08_03(ctx: SuiteContext):
    gao40 = split_tree_pow(Profile(367, 8, 367, 321), 40)
    c40 = 367**40
    ok = (
        gao40.a == GAO_D200_EXACT_N
        and gao40.c == c40
        and gao40.d == (c40 + 275**40) // 2
        and gao40.b == 2 * (c40 - 275**40) // 23
    )
    if not ok:
        return False, "MATH_MISMATCH", "Gao d=200 splitTree40 exact 103-digit cardinality/closed-form mismatch", {}
    return True, "OK", "Gao d=200 splitTree40 matches exact 103-digit M_40 and closed forms c_40, d_40, b_40", {"digits": len(str(gao40.a))}


def _t1_f08_04(ctx: SuiteContext):
    ok, code, info = verify_profile_dp()
    if not ok:
        return False, code, "BPZ v1 d=200 Profile.star DP verification failed", info
    return True, "OK", "BPZ v1 d=200 splitTree40 matches exact 103-digit M_40 and certifies 3258805369885/10^12", info


def _t1_f08_05(ctx: SuiteContext):
    ok, code, info = ctx.get_main_bounds()
    if not ok:
        return False, code, info.get("reason", f"Could not extract Main.lean bounds ({code})"), info
    num, den = info["c7_lower_num"], info["c7_lower_den"]
    if den <= 0:
        return False, "BOUNDS_VIOLATION", f"Non-positive c7_lower_den={safe_int_preview(den)}", info
    # Must strictly exceed 367^(1/5), 134753^(1/10), and exact Gao M_40^(1/200)
    if not (
        pow(num, 5) > pow(den, 5) * 367
        and pow(num, 10) > pow(den, 10) * 134753
        and pow(num, 200) > pow(den, 200) * GAO_D200_EXACT_N
    ):
        return False, "BOUNDS_VIOLATION", "Main.lean frontier bound does not strictly beat Polak-Schrijver, Itty, and exact Gao d=200", info
    return True, "OK", "Main.lean frontier bound strictly beats 367^(1/5), 134753^(1/10), and exact Gao M_40^(1/200)", info


# ---------------------------------------------------------------------------
# F09 — Dual Exact Verifier & Automated Lean Certificate Emitter
# ---------------------------------------------------------------------------


def _t1_f09_01(ctx: SuiteContext):
    d = ctx.project_dir / "search" / "lower"
    if not d.is_dir():
        return False, "MISSING_DIR", f"Missing directory {d}", {"path": str(d)}
    scripts = [p for p in d.rglob("*") if p.is_file() and p.suffix in (".py", ".cpp", ".cc", ".rs", ".sh")]
    if not scripts:
        return False, "MISSING_FILE", f"No verifier/codegen/search source files found under {d}", {"path": str(d)}
    return True, "OK", f"Found {len(scripts)} tooling/search file(s) under search/lower/", {"count": len(scripts)}


def _t1_f09_02(ctx: SuiteContext):
    d = ctx.project_dir / "search" / "lower"
    if not d.is_dir():
        return False, "MISSING_DIR", f"Missing directory {d}", {"path": str(d)}
    py_files = sorted(d.rglob("*.py"))
    if not py_files:
        return False, "MISSING_FILE", f"No Python verifier/codegen scripts found under {d}", {"path": str(d)}
    for p in py_files:
        try:
            ast.parse(p.read_text(encoding="utf-8"), filename=str(p))
        except SyntaxError as exc:
            return False, "SUBPROCESS_FAILED", f"SyntaxError in {p.name}: {exc}", {"path": str(p)}
    return True, "OK", f"All {len(py_files)} Python script(s) under search/lower/ passed ast.parse", {"files": [p.name for p in py_files]}


def _t1_f09_03(ctx: SuiteContext):
    d = ctx.project_dir / "search" / "lower"
    if not d.is_dir():
        return False, "MISSING_DIR", f"Missing directory {d}", {"path": str(d)}
    json_files = sorted(d.rglob("*.json"))
    checked = 0
    for jf in json_files:
        try:
            data = json.loads(jf.read_text(encoding="utf-8"))
        except Exception:
            continue
        if isinstance(data, dict) and "vertices" in data and "d" in data:
            ok, code, info = verify_witness_json(jf)
            if not ok:
                return False, code, f"Witness JSON {jf.name} failed verification ({code})", info
            checked += 1
    # Also verify Main.lean bounds are extractable and consistent
    ok_b, code_b, info_b = ctx.get_main_bounds()
    if not ok_b:
        return False, code_b, info_b.get("reason", f"Main.lean bounds unavailable ({code_b})"), info_b
    return True, "OK", f"Verified {checked} witness JSON artifact(s) under search/lower/ and Main.lean bounds", {"witness_jsons": checked}


def _t1_f09_04(ctx: SuiteContext):
    I_v, S_v, X_v, f0, f1 = build_synthetic_c7_valid_tuple()
    ok, code, info = verify_valid_tuple(c7_adj, I_v, S_v, X_v, f0, f1)
    if not ok or info.get("profile") != (3, 1, 2, 2):
        return False, code, f"Synthetic C_7 ValidTuple verification failed: {info}", info
    return True, "OK", "Independent ValidTuple conflict/privacy/disjointness verifier validated C_7 profile (3,1,2,2)", info


def _t1_f09_05(ctx: SuiteContext):
    return _check_lean_files_present_and_clean(ctx, ("ShannonC7/FrontierLower.lean",))


# ---------------------------------------------------------------------------
# F10 — Frontier Lower-Bound Computational Campaign & FrontierLower.lean
# ---------------------------------------------------------------------------


def _t1_f10_01(ctx: SuiteContext):
    return check_decl_axioms(ctx, ("E2EAudit.audit_c7_lower_den_pos", "ShannonC7.c7_lower_num", "ShannonC7.c7_lower_den"))


def _t1_f10_02(ctx: SuiteContext):
    return check_decl_axioms(ctx, ("ShannonC7.c7_lower_frontier",))


def _t1_f10_03(ctx: SuiteContext):
    return check_decl_axioms(ctx, ("E2EAudit.audit_c7_lower_floor", "E2EAudit.audit_c7_lower_lt_upper"))


def _t1_f10_04(ctx: SuiteContext):
    ok, code, info = ctx.get_main_bounds()
    if not ok:
        return False, code, info.get("reason", f"Could not extract Main.lean bounds ({code})"), info
    ok_r, code_r, info_r = check_frontier_rational_bounds(info["c7_lower_num"], info["c7_lower_den"])
    if not ok_r:
        return False, code_r, info_r.get("reason", "Frontier bound check failed"), info_r
    return (
        True,
        "OK",
        f"Frontier bound {info_r['decimal_20']} verified (beats_bpz_lean={info_r['beats_bpz_lean']}, beats_tandon={info_r['beats_tandon']})",
        info_r,
    )


def _t1_f10_05(ctx: SuiteContext):
    report_path = ctx.project_dir / "search" / "lower" / "LOWER_RESEARCH_REPORT.md"
    if not report_path.is_file():
        return False, "MISSING_FILE", f"Missing {report_path}", {"path": str(report_path)}
    ok_b, code_b, info_b = ctx.get_main_bounds()
    if not ok_b:
        return (
            False,
            code_b,
            info_b.get("reason", f"Cannot verify LOWER_RESEARCH_REPORT.md consistency without Main.lean bounds ({code_b})"),
            info_b,
        )
    ok, code, info = verify_research_report(
        report_path,
        kind="lower",
        lower_num=info_b["c7_lower_num"],
        lower_den=info_b["c7_lower_den"],
    )
    if not ok:
        return False, code, info.get("reason", f"LOWER_RESEARCH_REPORT.md failed ({code})"), info
    return True, "OK", "search/lower/LOWER_RESEARCH_REPORT.md present, substantive, and consistent with Main.lean", info


# ---------------------------------------------------------------------------
# F11 — Exact alpha(C_7^3) = 33 Lean Proof & alpha(C_7^4) <= 112 Audit
# ---------------------------------------------------------------------------


def _t1_f11_01(ctx: SuiteContext):
    # `e2e_audit.lean` proves both alpha_c7_pow3 = 33 AND audit_alpha_pow3_not_34
    audit = ctx.run_lean_audit()
    if not audit.ok:
        return False, audit.code, audit.message, {"returncode": audit.returncode}
    return check_decl_axioms(ctx, ("ShannonC7.alpha_c7_pow3",))


def _t1_f11_02(ctx: SuiteContext):
    ok, code, msg, info = check_decl_axioms(ctx, ("ShannonC7.alpha_c7_pow3",))
    if not ok:
        return False, code, msg, info
    return True, "OK", "alpha_c7_pow3 proved in pure Lean kernel (zero Lean.ofReduceBool / native_decide)", info


def _t1_f11_03(ctx: SuiteContext):
    return _check_lean_files_present_and_clean(
        ctx, ("ShannonC7/AlphaC7Cube.lean", "ShannonC7/FinitePowerUpper.lean")
    )


def _t1_f11_04(ctx: SuiteContext):
    # Exact slice double-counting & powers of theta(C_7)
    s4 = (33 * 7) // 2
    s5_cond = (112 * 7) // 2
    # Exact integer checks for floor(theta(C7)^5) = 401 and floor(theta(C7)^10) = 161557:
    # Since LOVASZ_LOWER_RAT < theta < LOVASZ_UPPER_RAT:
    p5_lo = LOVASZ_LOWER_RAT**5
    p5_hi = LOVASZ_UPPER_RAT**5
    p10_lo = LOVASZ_LOWER_RAT**10
    p10_hi = LOVASZ_UPPER_RAT**10
    ok = (
        s4 == 115
        and s5_cond == 392
        and int(p5_lo) == 401
        and int(p5_hi) == 401
        and int(p10_lo) == 161557
        and int(p10_hi) == 161557
        and s5_cond < 401
    )
    if not ok:
        return False, "MATH_MISMATCH", "Slice double-counting / theta power ceiling mismatch", {}
    return True, "OK", "Verified floor(33*7/2)=115, floor(112*7/2)=392 < 401=floor(theta^5), floor(theta^10)=161557", {}


def _t1_f11_05(ctx: SuiteContext):
    ok, code, info = verify_research_report(
        ctx.project_dir / "search" / "upper" / "UPPER_RESEARCH_REPORT.md",
        kind="upper",
    )
    if not ok:
        return False, code, info.get("reason", f"UPPER_RESEARCH_REPORT.md failed ({code})"), info
    return True, "OK", "search/upper/UPPER_RESEARCH_REPORT.md documents alpha(C_7^3)=33 & alpha(C_7^4) audit", info


# ---------------------------------------------------------------------------
# F12 — Obstruction-Gated Asymptotic Upper-Bound Research
# ---------------------------------------------------------------------------


def _t1_f12_01(ctx: SuiteContext):
    p = ctx.project_dir / "search" / "upper" / "obstruction_testbed.py"
    if not p.is_file():
        return False, "MISSING_FILE", f"Missing {p}", {"path": str(p)}
    try:
        ast.parse(p.read_text(encoding="utf-8"), filename=str(p))
    except SyntaxError as exc:
        return False, "SUBPROCESS_FAILED", f"SyntaxError in obstruction_testbed.py: {exc}", {"path": str(p)}
    return True, "OK", "search/upper/obstruction_testbed.py exists and passed ast.parse", {"path": str(p)}


def _t1_f12_02(ctx: SuiteContext):
    ok, code, info = verify_c5_obstruction()
    if not ok:
        return False, code, "C_5 obstruction verification failed", info
    return True, "OK", "C_5 obstruction verified: alpha=2, alpha(C_5^2)=5, Theta(C_5)=sqrt(5) > SoS=2", info


def _t1_f12_03(ctx: SuiteContext):
    ok, code, info = verify_gilbert32_obstruction()
    if not ok:
        return False, code, "Sason Gilbert-32 obstruction verification failed", info
    return True, "OK", "Sason Gilbert-32 verified: 15-regular, alpha=4, 20-set in G^2, theta'=4 < sqrt(20) < 16/3=theta", info


def _t1_f12_04(ctx: SuiteContext):
    ok, code, info = verify_srg27_obstruction()
    if not ok:
        return False, code, "srg(27,10,1,5) obstruction verification failed", info
    return True, "OK", "srg(27,10,1,5) verified: lambda=1, mu=5, alpha=6, exact rank_Q(I-A)=7 < 9=theta", info


def _t1_f12_05(ctx: SuiteContext):
    ok, code, info = verify_research_report(
        ctx.project_dir / "search" / "upper" / "UPPER_RESEARCH_REPORT.md",
        kind="upper",
    )
    if not ok:
        return False, code, info.get("reason", f"UPPER_RESEARCH_REPORT.md honesty/barrier check failed ({code})"), info
    return True, "OK", "UPPER_RESEARCH_REPORT.md honestly documents Bukh-Cox/Bi-Tang/Sason obstructions", info


# ---------------------------------------------------------------------------
# F13 — Canonical Main.lean, Open-Problem Props & RESULTS.md
# ---------------------------------------------------------------------------


def _t1_f13_01(ctx: SuiteContext):
    ok_h, code_h, msg_h, info_h = _check_lean_files_present_and_clean(ctx, ("ShannonC7/Main.lean",))
    if not ok_h:
        return False, code_h, msg_h, info_h
    audit = ctx.run_lean_audit()
    if not audit.ok:
        return False, audit.code, audit.message, {"returncode": audit.returncode}
    return True, "OK", "ShannonC7/Main.lean hygiene-clean and all 16 PROJECT.md § 4.4 exports verified", info_h


def _t1_f13_02(ctx: SuiteContext):
    return check_decl_axioms(ctx, ("ShannonC7.c7_shannonCapacity_sandwich", "E2EAudit.audit_textbook_sandwich"))


def _t1_f13_03(ctx: SuiteContext):
    return check_decl_axioms(ctx, ("ShannonC7.OpenQuestion_StrictGap",))


def _t1_f13_04(ctx: SuiteContext):
    return check_decl_axioms(ctx, ("ShannonC7.OpenQuestion_ExactValue",))


def _t1_f13_05(ctx: SuiteContext):
    results_path = ctx.project_dir / "RESULTS.md"
    if not results_path.is_file():
        return False, "MISSING_FILE", f"Missing {results_path}", {"path": str(results_path)}
    ok_b, code_b, info_b = ctx.get_main_bounds()
    if not ok_b:
        return (
            False,
            code_b,
            info_b.get("reason", f"Cannot verify RESULTS.md consistency without Main.lean bounds ({code_b})"),
            info_b,
        )
    ok, code, info = verify_results_md(
        results_path,
        lower_num=info_b["c7_lower_num"],
        lower_den=info_b["c7_lower_den"],
    )
    if not ok:
        return False, code, info.get("reason", f"RESULTS.md audit failed ({code})"), info
    return True, "OK", "RESULTS.md present, substantive, honest, and numerically consistent with Main.lean", info


# ---------------------------------------------------------------------------
# F14 — Final Integration: Build, Hygiene, TCB Whitelist & Reproducibility
# ---------------------------------------------------------------------------


def _t1_f14_01(ctx: SuiteContext):
    ok_a, code_a, msg_a, info_a = ctx.scan_audit_file()
    if not ok_a:
        return False, code_a, msg_a, info_a
    return ctx.scan_all_lean_files()


def _t1_f14_02(ctx: SuiteContext):
    return check_decl_axioms(ctx, REQUIRED_AUDIT_AXIOM_DECLS)


def _t1_f14_03(ctx: SuiteContext):
    return ctx.run_verify_axioms_script()


def _t1_f14_04(ctx: SuiteContext):
    bres = ctx.run_lean_build()
    if not bres.ok:
        return False, bres.code, bres.message, {"rc": bres.returncode}
    return True, "OK", bres.message, {"elapsed_s": round(bres.elapsed_s, 2), "max_rss_kb": bres.max_rss_kb}


def _t1_f14_05(ctx: SuiteContext):
    ok_b, code_b, info_b = ctx.get_main_bounds()
    if not ok_b:
        return False, code_b, info_b.get("reason", f"Main.lean bounds unavailable ({code_b})"), info_b
    lnum, lden = info_b["c7_lower_num"], info_b["c7_lower_den"]
    for label, fn in (
        ("RESULTS.md", lambda: verify_results_md(ctx.project_dir / "RESULTS.md", lnum, lden)),
        (
            "LOWER_RESEARCH_REPORT.md",
            lambda: verify_research_report(
                ctx.project_dir / "search" / "lower" / "LOWER_RESEARCH_REPORT.md", "lower", lnum, lden
            ),
        ),
        (
            "UPPER_RESEARCH_REPORT.md",
            lambda: verify_research_report(
                ctx.project_dir / "search" / "upper" / "UPPER_RESEARCH_REPORT.md", "upper", lnum, lden
            ),
        ),
    ):
        ok, code, info = fn()
        if not ok:
            return False, code, f"{label} cross-report consistency failed: {info.get('reason', code)}", info
    return True, "OK", "RESULTS.md, LOWER_RESEARCH_REPORT.md, and UPPER_RESEARCH_REPORT.md agree with Main.lean", info_b


def get_tier1_tests() -> list[TestCase]:
    return [
        # F01
        TestCase("T1-F01-01", "T1", "F01", "lean-toolchain pins exact leanprover/lean4:v4.32.2", _t1_f01_01),
        TestCase("T1-F01-02", "T1", "F01", "lakefile.toml declares ShannonC7 and pins mathlib v4.32.2", _t1_f01_02),
        TestCase("T1-F01-03", "T1", "F01", "lake-manifest.json is valid JSON locking mathlib", _t1_f01_03),
        TestCase("T1-F01-04", "T1", "F01", "scripts/verify_axioms.sh syntax-valid and Mathlib .olean cache present", _t1_f01_04),
        TestCase("T1-F01-05", "T1", "F01", "Zero wholesale `import Mathlib` statements across ShannonC7/", _t1_f01_05),
        # F02
        TestCase("T1-F02-01", "T1", "F02", "ShannonC7.strongPowPi matches independent strongPowTextbook", _t1_f02_01),
        TestCase("T1-F02-02", "T1", "F02", "ShannonC7.c7_shannonCapacity_tendsto exact Fekete type & axioms", _t1_f02_02),
        TestCase("T1-F02-03", "T1", "F02", "Opaque-box Fekete equivalence shannonCapacity = shannonCapacityTextbook", _t1_f02_03),
        TestCase("T1-F02-04", "T1", "F02", "Independent C_7 adjacency & strong-product supermultiplicativity", _t1_f02_04),
        TestCase("T1-F02-05", "T1", "F02", "Core M1 modules (Defs, Fekete, CycleC7) present & hygiene-clean", _t1_f02_05),
        # F03
        TestCase("T1-F03-01", "T1", "F03", "ShannonC7.lovaszThetaC7 exact closed-form formula & axioms", _t1_f03_01),
        TestCase("T1-F03-02", "T1", "F03", "ShannonC7.c7_upper_lovasz exact signature & axioms", _t1_f03_02),
        TestCase("T1-F03-03", "T1", "F03", "ShannonC7.c7_upper_rational (< 3317667207395/10^12) & axioms", _t1_f03_03),
        TestCase("T1-F03-04", "T1", "F03", "ShannonC7.c5_shannonCapacity_eq_sqrt_five exact signature & axioms", _t1_f03_04),
        TestCase("T1-F03-05", "T1", "F03", "Independent Rank-4 Fourier dual PSD, primal SDP & 12-digit cubic enclosure", _t1_f03_05),
        # F04
        TestCase("T1-F04-01", "T1", "F04", "ShannonC7.c7_lovasz_unattainable exact signature & axioms", _t1_f04_01),
        TestCase("T1-F04-02", "T1", "F04", "Independent F_3 and Q irreducibility of cubic p(t)=t^3+7t^2-49t+49", _t1_f04_02),
        TestCase("T1-F04-03", "T1", "F04", "Exact 3-root moduli separation |r2| < |r3| < |r1|", _t1_f04_03),
        TestCase("T1-F04-04", "T1", "F04", "Independent Haemers rank=4 on C_7 and exact rank_Q(I-A)=7 on srg(27,10,1,5)", _t1_f04_04),
        TestCase("T1-F04-05", "T1", "F04", "CubicBounds.lean and Haemers.lean present & hygiene-clean", _t1_f04_05),
        # F05
        TestCase("T1-F05-01", "T1", "F05", "ShannonC7.c7_compl_sandwich upper bound & axioms", _t1_f05_01),
        TestCase("T1-F05-02", "T1", "F05", "ShannonC7.oddCycle_upper_lovasz universal signature & axioms", _t1_f05_02),
        TestCase("T1-F05-03", "T1", "F05", "oddCycle_upper_lovasz instantiations at k=1,2,3,4 (C_3..C_9)", _t1_f05_03),
        TestCase("T1-F05-04", "T1", "F05", "Independent complement C_7^c cubic q(u), product=7 & Rank-2 PSD", _t1_f05_04),
        TestCase("T1-F05-05", "T1", "F05", "Independent odd-cycle Lovasz table k=1..7 & k=100", _t1_f05_05),
        # F06
        TestCase("T1-F06-01", "T1", "F06", "TrieVerifier.lean and Decimal.lean present & pure-kernel hygiene-clean", _t1_f06_01),
        TestCase("T1-F06-02", "T1", "F06", "Pure-kernel axioms (zero Lean.ofReduceBool) on lower/cube theorems", _t1_f06_02),
        TestCase("T1-F06-03", "T1", "F06", "Exact integer power bridge num^d <= den^d * N across 10 milestones", _t1_f06_03),
        TestCase("T1-F06-04", "T1", "F06", "Reference Radix-7 Trie7 checks C_7^3 (33) and C_7^5 (343) independence/disjointness", _t1_f06_04),
        TestCase("T1-F06-05", "T1", "F06", "Extracted c7_lower_num and c7_lower_den are positive exact naturals", _t1_f06_05),
        # F07
        TestCase("T1-F07-01", "T1", "F07", "ShannonC7.alpha_c7_pow1 (= 3) exact signature & axioms", _t1_f07_01),
        TestCase("T1-F07-02", "T1", "F07", "ShannonC7.alpha_c7_pow2 (= 10) exact signature & axioms", _t1_f07_02),
        TestCase("T1-F07-03", "T1", "F07", "ShannonC7.alpha_c7_pow3 (= 33) exact signature & axioms", _t1_f07_03),
        TestCase("T1-F07-04", "T1", "F07", "ShannonC7.c7_compl_sandwich lower bound 17^(1/4) & 17-word witness", _t1_f07_04),
        TestCase("T1-F07-05", "T1", "F07", "Independent witnesses (C_7^1..3, C_7^5 343/327, C_7^c^4 17) & SmallPowers.lean hygiene", _t1_f07_05),
        # F08
        TestCase("T1-F08-01", "T1", "F08", "ValidTuple.lean and HeteroLayered.lean present & hygiene-clean", _t1_f08_01),
        TestCase("T1-F08-02", "T1", "F08", "Exact Profile.star reproduces Itty d=10 cardinality 134753", _t1_f08_02),
        TestCase("T1-F08-03", "T1", "F08", "Exact splitTree40 reproduces Gao 103-digit M_40 & closed forms", _t1_f08_03),
        TestCase("T1-F08-04", "T1", "F08", "Exact splitTree40 reproduces BPZ v1 103-digit M_40 & 3.258805369885 floor", _t1_f08_04),
        TestCase("T1-F08-05", "T1", "F08", "Main.lean frontier bound strictly beats 367^(1/5), 134753^(1/10) & Gao", _t1_f08_05),
        # F09
        TestCase("T1-F09-01", "T1", "F09", "search/lower/ directory contains verifier & codegen tooling", _t1_f09_01),
        TestCase("T1-F09-02", "T1", "F09", "Python scripts under search/lower/ pass ast.parse syntax check", _t1_f09_02),
        TestCase("T1-F09-03", "T1", "F09", "Witness JSON artifacts under search/lower/ & Main.lean bounds verified", _t1_f09_03),
        TestCase("T1-F09-04", "T1", "F09", "Independent ValidTuple graph-level conflict/privacy/disjointness verifier", _t1_f09_04),
        TestCase("T1-F09-05", "T1", "F09", "Generated ShannonC7/FrontierLower.lean present & pure-kernel hygiene-clean", _t1_f09_05),
        # F10
        TestCase("T1-F10-01", "T1", "F10", "Pure-kernel proof 0 < c7_lower_den & clean constant axioms", _t1_f10_01),
        TestCase("T1-F10-02", "T1", "F10", "ShannonC7.c7_lower_frontier exact signature & axioms", _t1_f10_02),
        TestCase("T1-F10-03", "T1", "F10", "Pure-kernel GMP floor (>= 3258805369885/10^12) & ceiling (< 3317667207395/10^12)", _t1_f10_03),
        TestCase("T1-F10-04", "T1", "F10", "Exact Python rational & cubic classification of c7_lower_num/c7_lower_den", _t1_f10_04),
        TestCase("T1-F10-05", "T1", "F10", "search/lower/LOWER_RESEARCH_REPORT.md present & matches Main.lean", _t1_f10_05),
        # F11
        TestCase("T1-F11-01", "T1", "F11", "ShannonC7.alpha_c7_pow3 proves exact = 33 (and rules out 34)", _t1_f11_01),
        TestCase("T1-F11-02", "T1", "F11", "ShannonC7.alpha_c7_pow3 pure-kernel axioms (zero native_decide)", _t1_f11_02),
        TestCase("T1-F11-03", "T1", "F11", "AlphaC7Cube.lean and FinitePowerUpper.lean present & hygiene-clean", _t1_f11_03),
        TestCase("T1-F11-04", "T1", "F11", "Exact slice double-counting (115, 392 < 401) & theta^10 ceiling (161557)", _t1_f11_04),
        TestCase("T1-F11-05", "T1", "F11", "search/upper/UPPER_RESEARCH_REPORT.md documents cube proof & quad audit", _t1_f11_05),
        # F12
        TestCase("T1-F12-01", "T1", "F12", "search/upper/obstruction_testbed.py exists and passes ast.parse", _t1_f12_01),
        TestCase("T1-F12-02", "T1", "F12", "Independent C_5 obstruction graph invariants verified", _t1_f12_02),
        TestCase("T1-F12-03", "T1", "F12", "Independent Sason Gilbert-32 invariants, 20-set G^2 & Krawtchouk LP verified", _t1_f12_03),
        TestCase("T1-F12-04", "T1", "F12", "Independent srg(27,10,1,5) parameters & exact rank-7 fitting matrix verified", _t1_f12_04),
        TestCase("T1-F12-05", "T1", "F12", "UPPER_RESEARCH_REPORT.md honestly reports all upper-bound obstructions", _t1_f12_05),
        # F13
        TestCase("T1-F13-01", "T1", "F13", "ShannonC7/Main.lean hygiene-clean & exports all 16 PROJECT.md § 4.4 symbols", _t1_f13_01),
        TestCase("T1-F13-02", "T1", "F13", "c7_shannonCapacity_sandwich & audit_textbook_sandwich verified with clean axioms", _t1_f13_02),
        TestCase("T1-F13-03", "T1", "F13", "OpenQuestion_StrictGap exact Prop definition & clean axioms", _t1_f13_03),
        TestCase("T1-F13-04", "T1", "F13", "OpenQuestion_ExactValue exact Prop definition & clean axioms", _t1_f13_04),
        TestCase("T1-F13-05", "T1", "F13", "RESULTS.md present, substantive, honest & consistent with Main.lean", _t1_f13_05),
        # F14
        TestCase("T1-F14-01", "T1", "F14", "Global static hygiene scan across ShannonC7/**/*.lean & verify/e2e_audit.lean", _t1_f14_01),
        TestCase("T1-F14-02", "T1", "F14", "Exhaustive #print axioms whitelist across all 24 audited declarations", _t1_f14_02),
        TestCase("T1-F14-03", "T1", "F14", "scripts/verify_axioms.sh executes and exits 0", _t1_f14_03),
        TestCase("T1-F14-04", "T1", "F14", "LEAN_NUM_THREADS=2 lake build ShannonC7.Main exits 0 within 7.8 GiB RAM guardrail", _t1_f14_04),
        TestCase("T1-F14-05", "T1", "F14", "Cross-report numeric consistency across RESULTS.md & lower/upper reports", _t1_f14_05),
    ]
