#!/usr/bin/env python3
"""Isolated positive + negative/mutation `--self-test` harness (18 suites: ST-01 .. ST-18).

Executes strictly inside a private `mktemp -d` (`chmod 700`) sandbox with guaranteed
`try/finally` cleanup, proving every detector catches genuine cheats/bugs with zero false positives.
"""

from __future__ import annotations

from fractions import Fraction
import json
import os
from pathlib import Path
import re
import shutil
import sys
import tempfile
import time
from typing import Any

from common import (
    _LEAN_ERROR_LINE_RE,
    _LEAN_SORRY_WARN_RE,
    SuiteContext,
    TestCase,
    _safe_str_obj,
    _sanitize_details,
    execute_test,
    format_result_line,
    run_subprocess_safe,
)
from cross_check import (
    BPZ_D200_EXACT_N,
    FLOOR_LOWER,
    GAO_D200_EXACT_N,
    LOVASZ_CUBIC_TRAP,
    LOVASZ_UPPER_RAT,
    REQUIRED_AUDIT_AXIOM_DECLS,
    WITNESS_C7_COMPL_POW4,
    WITNESS_C7_POW2,
    WITNESS_C7_POW3,
    Profile,
    Trie7,
    _find_impossible_upper_claim,
    _find_inflated_lower_claims,
    _safe_ratio_preview,
    bisect_theta_c7,
    build_synthetic_c7_valid_tuple,
    c7_adj,
    c7_compl_adj,
    check_frontier_rational_bounds,
    check_nat_pow_bound,
    extract_main_bounds,
    format_fraction_down,
    parse_e2e_consts,
    parse_print_axioms,
    profile_star,
    safe_int_preview,
    scan_lean_hygiene,
    split_tree_pow,
    validate_upper_bound_claim,
    verify_axiom_whitelist,
    verify_research_report,
    verify_results_md,
    verify_strong_power_independent_set,
    verify_valid_tuple,
    verify_witness_json,
)


def _sandbox_dir(prefix: str) -> Path:
    d = Path(tempfile.mkdtemp(prefix=prefix))
    os.chmod(d, 0o700)
    return d


def _st_01(ctx: SuiteContext):
    tmp = _sandbox_dir("shannon_c7_st01_")
    try:
        f = tmp / "Clean.lean"
        f.write_text(
            "import Mathlib.Data.ZMod.Basic\n"
            "-- zero sorry native_decide axiom unsafe implemented_by extern\n"
            "/- outer /- nested sorry axiom -/ implemented_by extern -/\n"
            'def docStr : String := "sorry native_decide axiom unsafe"\n'
            'def rawStr : String := r#"sorry admit axiom"#\n'
            "def no_sorry_proof : Nat := 42\n"
            "theorem arithmetic_ok : 2 + 2 = 4 := by decide\n"
            "#print axioms arithmetic_ok\n",
            encoding="utf-8",
        )
        viols = scan_lean_hygiene(f.read_text(encoding="utf-8"), path=str(f), mode="impl")
        if viols:
            return False, "HYGIENE_VIOLATION", f"False positive in clean control: {viols[0]}", {"violations": [v.to_dict() for v in viols]}
        return True, "OK", "Positive hygiene control produced 0 false positives across comments, strings, decide & #print axioms", {}
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def _st_02(ctx: SuiteContext):
    tmp = _sandbox_dir("shannon_c7_st02_")
    try:
        f = tmp / "BadSorry.lean"
        f.write_text("theorem bad1 : True := by\n  sorry\ntheorem bad2 : True := by trivial; sorry\n", encoding="utf-8")
        viols = scan_lean_hygiene(f.read_text(encoding="utf-8"), path=str(f), mode="impl")
        hits = [v for v in viols if v.rule == "FORBIDDEN_SORRY"]
        if len(hits) != 2 or hits[0].line != 2 or hits[1].line != 3:
            return False, "MATH_MISMATCH", f"Expected 2 FORBIDDEN_SORRY hits at lines 2,3; got {hits}", {}
        return True, "OK", "Injected `sorry` detected at exact lines 2 and 3", {"lines": [h.line for h in hits]}
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def _st_03(ctx: SuiteContext):
    tmp = _sandbox_dir("shannon_c7_st03_")
    try:
        f = tmp / "BadAdmit.lean"
        f.write_text("def admits_bound := 1\ntheorem bad : True := by admit\n", encoding="utf-8")
        viols = scan_lean_hygiene(f.read_text(encoding="utf-8"), path=str(f), mode="impl")
        hits = [v for v in viols if v.rule == "FORBIDDEN_ADMIT"]
        if len(hits) != 1 or hits[0].line != 2:
            return False, "MATH_MISMATCH", f"Expected 1 FORBIDDEN_ADMIT at line 2; got {hits}", {}
        return True, "OK", "Injected `admit` caught at line 2 while `admits_bound` ignored", {}
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def _st_04(ctx: SuiteContext):
    tmp = _sandbox_dir("shannon_c7_st04_")
    try:
        f = tmp / "BadAxiom.lean"
        f.write_text("axiom fake : True\nprivate axiom fake2 : False\n#print axioms fake\n", encoding="utf-8")
        viols = scan_lean_hygiene(f.read_text(encoding="utf-8"), path=str(f), mode="impl")
        hits = [v for v in viols if v.rule == "FORBIDDEN_AXIOM"]
        if len(hits) != 2:
            return False, "MATH_MISMATCH", f"Expected 2 FORBIDDEN_AXIOM hits; got {hits}", {}
        return True, "OK", "Injected `axiom` and `private axiom` caught (2 hits) while `#print axioms` ignored", {}
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def _st_05(ctx: SuiteContext):
    tmp = _sandbox_dir("shannon_c7_st05_")
    try:
        fixtures = (
            ("unsafe.lean", "unsafe def cheat : Nat := 0\n", "FORBIDDEN_UNSAFE"),
            ("unsafecast.lean", "def c (x : Nat) : Int := unsafeCast x\n", "FORBIDDEN_UNSAFE"),
            ("lcproof.lean", "theorem p : False := lcProof\n", "FORBIDDEN_UNSAFE"),
            ("impl1.lean", "@[implemented_by foo]\ndef bar : Nat := 1\n", "FORBIDDEN_IMPLEMENTED_BY"),
            ("impl2.lean", "attribute [implemented_by foo] bar\n", "FORBIDDEN_IMPLEMENTED_BY"),
            ("extern1.lean", '@[extern "c_fn"]\nopaque extFn : Nat -> Nat\n', "FORBIDDEN_EXTERN"),
            ("extern2.lean", 'attribute [inline, extern "c_fn"] extFn\n', "FORBIDDEN_EXTERN"),
            ("skip.lean", "set_option debug.skipKernelTC true\n", "FORBIDDEN_SKIP_KERNEL"),
        )
        for fname, src, rule in fixtures:
            fp = tmp / fname
            fp.write_text(src, encoding="utf-8")
            viols = scan_lean_hygiene(fp.read_text(encoding="utf-8"), path=str(fp), mode="impl")
            if not any(v.rule == rule for v in viols):
                return False, "MATH_MISMATCH", f"Fixture {fname} failed to trigger {rule} (got {viols})", {}
        return True, "OK", f"All {len(fixtures)} TCB-bypass mutations (unsafe/unsafeCast/lcProof/implemented_by/extern/skipKernelTC) caught", {}
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def _st_06(ctx: SuiteContext):
    tmp = _sandbox_dir("shannon_c7_st06_")
    try:
        fixtures = (
            ("nd.lean", "theorem t : 1 = 1 := by native_decide\n", "FORBIDDEN_NATIVE_DECIDE"),
            ("orb.lean", "def x := Lean.ofReduceBool\n", "FORBIDDEN_TRUST_AXIOM"),
            ("tc.lean", "def y := Lean.trustCompiler\n", "FORBIDDEN_TRUST_AXIOM"),
            ("sax.lean", "def z := sorryAx\n", "FORBIDDEN_SORRY"),
            ("root_orb.lean", "def a := _root_.Lean.ofReduceBool\n", "FORBIDDEN_TRUST_AXIOM"),
            ("root_orn.lean", "def b := _root_.Lean.ofReduceNat\n", "FORBIDDEN_TRUST_AXIOM"),
            ("root_tc.lean", "def c := _root_.Lean.trustCompiler\n", "FORBIDDEN_TRUST_AXIOM"),
            ("root_fq.lean", "def d := _root_.Lean.«ofReduceBool»\n", "FORBIDDEN_TRUST_AXIOM"),
            ("root_skip.lean", "set_option _root_.debug.skipKernelTC true\n", "FORBIDDEN_SKIP_KERNEL"),
            ("nul.lean", "def n := 1\x00\n", "NUL_BYTE"),
        )
        for fname, src, rule in fixtures:
            fp = tmp / fname
            fp.write_text(src, encoding="utf-8")
            viols = scan_lean_hygiene(fp.read_text(encoding="utf-8"), path=str(fp), mode="impl")
            if not any(v.rule == rule for v in viols):
                return False, "MATH_MISMATCH", f"Fixture {fname} failed to trigger {rule} (got {viols})", {}
        return True, "OK", f"All {len(fixtures)} trust/bypass mutations (incl. _root_.Lean.ofReduceBool, French quotes, _root_.debug.skipKernelTC & NUL) caught", {}
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def _st_07(ctx: SuiteContext):
    req = ("ShannonC7.a", "ShannonC7.b")
    clean = (
        "'ShannonC7.a' does not depend on any axioms\n"
        "'ShannonC7.b' depends on axioms: [Classical.choice,\n  Quot.sound, propext]\n"
    )
    ok_c, _, _ = verify_axiom_whitelist(parse_print_axioms(clean), required_decls=req)
    if not ok_c:
        return False, "MATH_MISMATCH", "Clean #print axioms control failed", {}

    for bad_ax in ("Lean.ofReduceBool", "sorryAx", "Lean.trustCompiler", "ShannonC7.customAx"):
        mut = (
            "'ShannonC7.a' does not depend on any axioms\n"
            f"'ShannonC7.b' depends on axioms: [propext, {bad_ax}]\n"
        )
        ok_b, code_b, _ = verify_axiom_whitelist(parse_print_axioms(mut), required_decls=req)
        if ok_b or code_b != "AXIOM_VIOLATION":
            return False, "MATH_MISMATCH", f"Unauthorized axiom {bad_ax} not caught", {}

    # Duplicate declaration reports: a later clean line must NEVER mask an earlier violation
    dup_cases = (
        "'A' depends on axioms: [propext, sorryAx]\n'A' depends on axioms: [propext]\n",
        "'A' depends on axioms: [Lean.ofReduceBool]\n'A' does not depend on any axioms\n",
    )
    for raw_dup in dup_cases:
        ok_d, code_d, _ = verify_axiom_whitelist(parse_print_axioms(raw_dup), required_decls=("A",), raw_output=raw_dup)
        if ok_d or code_d != "AXIOM_VIOLATION":
            return False, "MATH_MISMATCH", f"Duplicate #print axioms masked violation: {raw_dup!r}", {}

    missing_out = "'ShannonC7.a' does not depend on any axioms\n"
    ok_m, code_m, _ = verify_axiom_whitelist(parse_print_axioms(missing_out), required_decls=req)
    if ok_m or code_m != "MISSING_AXIOM_REPORT":
        return False, "MATH_MISMATCH", "Missing required declaration in #print axioms not caught", {}

    # Lean v4.32.2 backticked & legacy Unknown constant / identifier (including primed names `foo'`)
    unk_cases = (
        ("'A' depends on axioms: [propext]\nerror: Unknown constant `B`\n", "B"),
        ("'A' depends on axioms: [propext]\nerror: Unknown identifier `B`\n", "B"),
        ("'A' depends on axioms: [propext]\nverify/e2e_audit.lean:450:15: error(lean.unknownIdentifier): Unknown constant `B`\n", "B"),
        ("'A' depends on axioms: [propext]\nerror: Unknown constant `foo'`\n", "foo'"),
        ("'A' depends on axioms: [propext]\nerror: unknown constant 'B'\n", "B"),
        ("'A' depends on axioms: [propext]\nerror: unknown identifier 'B'\n", "B"),
        ("'A' depends on axioms: [propext]\nerror: unknown constant 'Foo.bar', see docs\n", "Foo.bar"),
        ("'A' depends on axioms: [propext]\nerror: unknown constant 'Foo.bar'.\n", "Foo.bar"),
        ("'A' depends on axioms: [propext]\nerror: unknown constant 'Foo.bar'; check imports\n", "Foo.bar"),
        ("'A' depends on axioms: [propext]\n(error: unknown constant 'Foo.bar')\n", "Foo.bar"),
    )
    for raw_unk, exp_sym in unk_cases:
        ok_u, code_u, info_u = verify_axiom_whitelist(
            parse_print_axioms(raw_unk), required_decls=("A",), raw_output=raw_unk
        )
        if ok_u or code_u != "MISSING_AXIOM_REPORT" or exp_sym not in info_u.get("unknown_consts", []):
            return (
                False,
                "MATH_MISMATCH",
                f"Lean v4.32.2 unknown constant/identifier `{exp_sym}` not caught: {info_u}",
                {},
            )

    # Lean v4.32.2 tagged & end-pos-ranged error line regex checks
    for err_ln in (
        "verify/e2e_audit.lean:450:15: error(lean.unknownIdentifier): Unknown constant `B`\n",
        "verify/e2e_audit.lean:10:4-10:12: error(lean.synthInstance): failed to synthesize\n",
        "ShannonC7/Main.lean:12:0: error: type mismatch\n",
        "ShannonC7/Main.lean:12:0-12:8: error: unknown tactic\n",
    ):
        if not _LEAN_ERROR_LINE_RE.search(err_ln):
            return False, "MATH_MISMATCH", f"_LEAN_ERROR_LINE_RE missed Lean v4.32.2 error: {err_ln!r}", {}
    if _LEAN_ERROR_LINE_RE.search("'ShannonC7.a' depends on axioms: [propext]\nwarning: unused variable\n"):
        return False, "MATH_MISMATCH", "_LEAN_ERROR_LINE_RE false-matched non-error output", {}

    # Lean v4.32.2 backticked, pp.sorrySource, sorryAx & legacy sorry warning checks
    for warn_ln in (
        "verify/e2e_audit.lean:12:8: warning: declaration uses `sorry`\n",
        "verify/e2e_audit.lean:12:8: warning: declaration uses 'sorry'\n",
        "verify/e2e_audit.lean:12:8: warning: declaration uses `sorry `«_stdin:2:23»`\n",
        "verify/e2e_audit.lean:12:8: warning: declaration uses `sorryAx`\n",
    ):
        if not _LEAN_SORRY_WARN_RE.search(warn_ln):
            return False, "MATH_MISMATCH", f"_LEAN_SORRY_WARN_RE missed sorry warning: {warn_ln!r}", {}
    if _LEAN_SORRY_WARN_RE.search("verify/e2e_audit.lean:12:8: warning: unused variable `x`\n"):
        return False, "MATH_MISMATCH", "_LEAN_SORRY_WARN_RE false-matched unused variable warning", {}

    # Single-quoted primed declaration names in `#print axioms` (Lean v4.32.2 printAxiomsOf)
    primed_clean = "'foo'' does not depend on any axioms\n"
    ok_pc, _, _ = verify_axiom_whitelist(parse_print_axioms(primed_clean), required_decls=("foo'",))
    if not ok_pc:
        return False, "MATH_MISMATCH", "Clean single-quoted primed #print axioms 'foo'' failed", {}
    for raw_pb, req_decl in (
        ("'foo'' depends on axioms: [sorryAx]\n", "foo'"),
        ("'ShannonC7.foo''' depends on axioms: [propext, Lean.ofReduceBool]\n", "ShannonC7.foo''"),
        ("info: 'foo'' depends on axioms: [sorryAx]\n", "foo'"),
        ("note 'x' unrelated; 'foo'' depends on axioms: [sorryAx]\n", "foo'"),
        ("warning: 'x' is unused; 'qux'' depends on axioms: [Lean.ofReduceBool]\n", "qux'"),
    ):
        parsed_pb = parse_print_axioms(raw_pb)
        ok_pb, code_pb, _ = verify_axiom_whitelist(parsed_pb, required_decls=(req_decl,))
        if req_decl not in parsed_pb or ok_pb or code_pb != "AXIOM_VIOLATION":
            return False, "MATH_MISMATCH", f"Primed #print axioms violation missed for {req_decl!r}: {parsed_pb}", {}

    # Explicit `@sorryAx` warning under `set_option pp.explicit true`
    for exp_warn in (
        "verify/e2e_audit.lean:12:8: warning: declaration uses `@sorryAx`\n",
        "verify/e2e_audit.lean:12:8: warning: declaration uses `@sorryAx Prop False`\n",
        "verify/e2e_audit.lean:12:8: warning: declaration uses '@sorryAx'\n",
    ):
        if not _LEAN_SORRY_WARN_RE.search(exp_warn):
            return False, "MATH_MISMATCH", f"_LEAN_SORRY_WARN_RE missed explicit @sorryAx warning: {exp_warn!r}", {}
    if _LEAN_SORRY_WARN_RE.search("verify/e2e_audit.lean:12:8: warning: declaration uses `@foo`\n"):
        return False, "MATH_MISMATCH", "_LEAN_SORRY_WARN_RE false-matched `@foo`", {}

    # parse_e2e_consts >100k-digit line guard (zero ValueError)
    giant_consts = parse_e2e_consts(f"E2E_CONST giant={'9' * 100005}\nE2E_CONST ok_val=42\n")
    if giant_consts != {"ok_val": 42}:
        return False, "MATH_MISMATCH", f"parse_e2e_consts giant-digit guard failed: {giant_consts}", {}

    # R4-D7 & Section 3 O(N) ReDoS guards: repeated `:'` / `;'`, French-quoted `'«a:b;c»'` / `'«:'»'`,
    # `_extract_unknown_consts`, and `parse_e2e_consts`
    fq_bad = parse_print_axioms("'«a:b;c»' depends on axioms: [sorryAx]\n")
    ok_fqb, code_fqb, _ = verify_axiom_whitelist(fq_bad, required_decls=("«a:b;c»",))
    if "«a:b;c»" not in fq_bad or ok_fqb or code_fqb != "AXIOM_VIOLATION":
        return False, "MATH_MISMATCH", f"French-quoted colon/semicolon axiom parse failed: {fq_bad}", {}
    fq_ok = parse_print_axioms("'«a:b;c»' does not depend on any axioms\n")
    if not verify_axiom_whitelist(fq_ok, required_decls=("«a:b;c»",))[0]:
        return False, "MATH_MISMATCH", f"Clean French-quoted colon/semicolon axiom parse failed: {fq_ok}", {}
    t0_d7 = time.process_time()
    p_col = parse_print_axioms(":'" * 500 + " 'foo' depends on axioms: [sorryAx]\n")
    p_sem = parse_print_axioms(";'" * 500 + " 'bar' depends on axioms: [Lean.ofReduceBool]\n")
    parse_print_axioms(":'" * 1500)
    parse_print_axioms(";'" * 1500)
    parse_print_axioms("'«:'»" * 2000)
    verify_axiom_whitelist(
        fq_ok,
        required_decls=("«a:b;c»",),
        raw_output="unknown constant '" + "«unknown constant '»" * 1000,
    )
    parse_e2e_consts(" \n" * 3000)
    dt_d7 = time.process_time() - t0_d7
    if p_col != {"foo": {"sorryAx"}} or p_sem != {"bar": {"Lean.ofReduceBool"}}:
        return False, "MATH_MISMATCH", f"Post-ReDoS #print axioms parse mismatch: {p_col}, {p_sem}", {}
    if dt_d7 > 0.5:
        return False, "MATH_MISMATCH", f"R4-D7 O(N^2) ReDoS regression in Section 3 diagnostic parsers ({dt_d7:.2f}s CPU)", {}

    # R5-C2-D01 / R5-R2-D3 / R5-D5: dead ReDoS regexes deleted + O(N) parse_print_axioms ReDoS guards
    import cross_check as _cc
    if hasattr(_cc, "_AXIOM_RE") or hasattr(_cc, "_UNKNOWN_CONST_RE"):
        return False, "MATH_MISMATCH", "Dead quadratic _AXIOM_RE or _UNKNOWN_CONST_RE still present in cross_check", {}
    t0_r5_ax = time.process_time()
    p_sp = parse_print_axioms(" " * 8000 + "x")
    p_nl = parse_print_axioms("\n" * 4000 + "x")
    p_uncl = parse_print_axioms(" depends on axioms: [" * 2000)
    p_ind = parse_print_axioms(" " * 4000 + "'Foo.ok' depends on axioms: [propext]\n")
    dt_r5_ax = time.process_time() - t0_r5_ax
    if p_sp or p_nl or p_uncl or p_ind != {"Foo.ok": {"propext"}}:
        return False, "MATH_MISMATCH", f"R5 parse_print_axioms O(N) guard parse mismatch: {(p_sp, p_nl, p_uncl, p_ind)}", {}
    if dt_r5_ax > 0.5:
        return False, "MATH_MISMATCH", f"R5-C2-D01/R5-R2-D3/R5-D5 O(N^2) ReDoS regression in parse_print_axioms ({dt_r5_ax:.2f}s CPU)", {}

    return True, "OK", "#print axioms & Lean v4.32.2 diagnostics (Unknown constant/identifier, tagged errors, sorry warnings, French-quoted names & O(N) ReDoS guard) verified", {}


def _st_08(ctx: SuiteContext):
    # Clean controls
    for verts, adj, d in ((WITNESS_C7_POW2, c7_adj, 2), (WITNESS_C7_POW3, c7_adj, 3), (WITNESS_C7_COMPL_POW4, c7_compl_adj, 4)):
        ok, code, _ = verify_strong_power_independent_set(verts, adj, d, domain_size=7)
        if not ok:
            return False, code, "Clean witness control failed", {}
    # Mutate 1 vertex in C_7^2 (wrap-around 0~6), C_7^3, and C_7^c^4
    mut2 = list(WITNESS_C7_POW2)
    mut2[0] = (6, 5)  # duplicate or conflict; let's use wrap-around conflict (6, 6) adjacent to (6, 5)
    mut2[0] = (6, 6)
    ok2, c2, _ = verify_strong_power_independent_set(mut2, c7_adj, 2, domain_size=7)
    mut3 = list(WITNESS_C7_POW3)
    mut3[0] = (0, 1, 4)  # adjacent to (1,1,4)
    ok3, c3, _ = verify_strong_power_independent_set(mut3, c7_adj, 3, domain_size=7)
    t3, _, _ = Trie7.from_vertices(mut3, 3)
    mut4 = list(WITNESS_C7_COMPL_POW4)
    mut4[0] = (0, 0, 0, 2)
    ok4, c4, _ = verify_strong_power_independent_set(mut4, c7_compl_adj, 4, domain_size=7)
    if ok2 or c2 != "CONFLICT_EDGE" or ok3 or c3 != "CONFLICT_EDGE" or (t3 is not None and t3.is_indep()) or ok4 or c4 != "CONFLICT_EDGE":
        return False, "MATH_MISMATCH", f"Single-conflict mutations missed (c2={c2}, c3={c3}, c4={c4})", {}
    return True, "OK", "Single cyclic-conflict mutations (including 0~6 wrap-around, Trie7 & C_7^c^4) all caught", {}


def _st_09(ctx: SuiteContext):
    dup2 = list(WITNESS_C7_POW2) + [WITNESS_C7_POW2[3]]
    dup3 = list(WITNESS_C7_POW3) + [WITNESS_C7_POW3[0]]
    ok2, c2, _ = verify_strong_power_independent_set(dup2, c7_adj, 2, domain_size=7)
    ok3, c3, _ = verify_strong_power_independent_set(dup3, c7_adj, 3, domain_size=7)
    t3, ct3, _ = Trie7.from_vertices(dup3, 3)
    if ok2 or c2 != "DUPLICATE_VERTEX" or ok3 or c3 != "DUPLICATE_VERTEX" or t3 is not None or ct3 != "DUPLICATE_VERTEX":
        return False, "MATH_MISMATCH", "Duplicate-vertex mutation not caught across witness & Trie7 verifiers", {}
    return True, "OK", "Duplicate-vertex mutations in C_7^2, C_7^3, and Trie7 all caught (DUPLICATE_VERTEX)", {}


def _st_10(ctx: SuiteContext):
    # Rounded-up truncation + d=500 big-int + ValidTuple/Profile mutations
    assert_pairs = (
        (3258805369885, 10**12, 200, BPZ_D200_EXACT_N, True),
        (3258805369886, 10**12, 200, BPZ_D200_EXACT_N, False),
        (3258789153908, 10**12, 200, GAO_D200_EXACT_N, True),
        (3258789153909, 10**12, 200, GAO_D200_EXACT_N, False),
        (3257865966783, 10**12, 5, 367, True),
        (3257865966784, 10**12, 5, 367, False),
        (3, 1, 3, 27, True),
    )
    for num, den, d, N, exp in assert_pairs:
        ok, _ = check_nat_pow_bound(num, den, d, N)
        if ok != exp:
            return False, "MATH_MISMATCH", f"check_nat_pow_bound({num}/{den}, d={d}) expected {exp}, got {ok}", {}

    # d=500 > 7500 digits safety
    n500 = 3258827985920007
    d500 = 10**15
    N500 = (pow(n500, 500) + pow(d500, 500) - 1) // pow(d500, 500)
    ok_big_p, _ = check_nat_pow_bound(n500, d500, 500, N500)
    ok_big_f, _ = check_nat_pow_bound(n500, d500, 500, N500 - 1)
    if not (ok_big_p and not ok_big_f):
        return False, "MATH_MISMATCH", "d=500 big-int exact power check failed", {}

    # ValidTuple & Profile mutations (including toggle_S, identical f0==f1 & split_tree_pow(invalid, 1))
    I_v, S_v, X_v, f0, f1 = build_synthetic_c7_valid_tuple()
    ok_vt, _, _ = verify_valid_tuple(c7_adj, I_v, S_v, X_v, f0, f1)
    ok_priv, c_priv, _ = verify_valid_tuple(c7_adj, I_v, S_v, X_v, f0, {0: 1})
    ok_disj, c_disj, _ = verify_valid_tuple(c7_adj, I_v, S_v, [0, 2, 4], f0, f1)
    ok_eq, c_eq, _ = verify_valid_tuple(c7_adj, I_v, S_v, X_v, f0, f0)
    c7_2 = lambda u, v: u != v and all(u[k] == v[k] or c7_adj(u[k], v[k]) for k in range(2))
    ok_tog, c_tog, _ = verify_valid_tuple(c7_2, [(0, 0)], [(0, 0)], [(0, 6)], {(0, 0): (1, 1)}, {(0, 0): (6, 1)})
    ok_prof, _ = Profile(10, 11, 10, 5).validate()
    ok_bool_prof, _ = Profile(True, 0, 1, 0).validate()  # type: ignore[arg-type]
    split_invalid_raised = False
    try:
        split_tree_pow(Profile(5, 99, 5, 99), 1)
    except ValueError:
        split_invalid_raised = True
    if (
        not ok_vt
        or ok_priv
        or c_priv != "PRIVACY_VIOLATION"
        or ok_disj
        or c_disj != "DISJOINTNESS_VIOLATION"
        or ok_eq
        or c_eq != "MATH_MISMATCH"
        or ok_tog
        or c_tog != "MATH_MISMATCH"
        or ok_prof
        or ok_bool_prof
        or not split_invalid_raised
    ):
        return False, "MATH_MISMATCH", "ValidTuple / toggle_S / Profile / split_tree_pow mutation check failed", {}

    # Strict int (reject bool) & malformed non-int inputs (zero TypeError!)
    if check_nat_pow_bound(True, True, True, True)[0]:  # type: ignore[arg-type]
        return False, "MATH_MISMATCH", "check_nat_pow_bound accepted bool as int", {}
    if verify_strong_power_independent_set([(0,)], c7_adj, True, 7)[0]:  # type: ignore[arg-type]
        return False, "MATH_MISMATCH", "verify_strong_power_independent_set accepted bool d", {}
    if verify_strong_power_independent_set([(0, 0), (2, 2)], c7_adj, 2.0, 7)[0]:  # type: ignore[arg-type]
        return False, "MATH_MISMATCH", "verify_strong_power_independent_set accepted float d", {}
    if verify_strong_power_independent_set([(0, 0)], c7_adj, "2", 7)[0]:  # type: ignore[arg-type]
        return False, "MATH_MISMATCH", "verify_strong_power_independent_set accepted str d", {}
    if Trie7.from_vertices([(0,)], True)[0] is not None:  # type: ignore[arg-type]
        return False, "MATH_MISMATCH", "Trie7.from_vertices accepted bool d", {}
    if Trie7.from_vertices([5], 1)[0] is not None:  # type: ignore[list-item]
        return False, "MATH_MISMATCH", "Trie7.from_vertices accepted non-sequence vertex", {}

    tmp = _sandbox_dir("shannon_c7_st10_")
    try:
        for idx_j, payload in enumerate(
            (
                {"graph": "C7", "d": True, "vertices": [[0], [2], [4]], "num": True, "den": True},
                {"graph": "C7", "d": "1", "vertices": [[0]]},
                {"graph": "C7", "d": None, "vertices": [[0]]},
                {"graph": "C7", "d": 1, "vertices": [[0], [2], [4]], "num": 10**50, "den": 1},
            )
        ):
            jp = tmp / f"bad_{idx_j}.json"
            jp.write_text(json.dumps(payload), encoding="utf-8")
            ok_j, _, _ = verify_witness_json(jp)
            if ok_j:
                return False, "MATH_MISMATCH", f"Malformed/invalid witness JSON {payload} was not rejected", {}
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    # R2-N02: profile_star, split_tree_pow & Trie7.disjoint strict type checks (must raise TypeError)
    unit_prof = Profile(1, 0, 1, 0)
    for bad_p, bad_q in (
        (None, unit_prof),
        (unit_prof, None),
        ("bad", unit_prof),
        (unit_prof, (1, 0, 1, 0)),
    ):
        try:
            profile_star(bad_p, bad_q)  # type: ignore[arg-type]
            return False, "MATH_MISMATCH", f"profile_star({bad_p!r}, {bad_q!r}) did not raise TypeError", {}
        except TypeError:
            pass
    try:
        split_tree_pow(None, 1)  # type: ignore[arg-type]
        return False, "MATH_MISMATCH", "split_tree_pow(None, 1) did not raise TypeError", {}
    except TypeError:
        pass
    t_small, _, _ = Trie7.from_vertices([(0,)], 1)
    assert t_small is not None
    try:
        t_small.disjoint(None)  # type: ignore[arg-type]
        return False, "MATH_MISMATCH", "Trie7.disjoint(None) did not raise TypeError", {}
    except TypeError:
        pass

    # R2-N03: verify_valid_tuple malformed inputs -> clean (False, "MATH_MISMATCH"), zero TypeError/IndexError
    malformed_vt = (
        (None, [0, 2], [0], [2], {0: 0}, {0: 6}),
        (c7_adj, I_v, S_v, X_v, None, f1),
        (c7_adj, I_v, S_v, X_v, f0, None),
        (c7_adj, [2], [2], [], {2: 2}, [0, 2]),
        (c7_adj, None, [], [], {}, {}),
        (c7_adj, 123, [], [], {}, {}),
        (c7_adj, "024", [], [], {}, {}),
        (c7_adj, {0, 2}, [], [], {}, {}),
        (c7_adj, (x for x in [0, 2]), [], [], {}, {}),
        (c7_adj, [0], None, [], {}, {}),
        (c7_adj, [0], [], None, {}, {}),
        (c7_adj, [[0], [2]], [[0]], [[2]], {}, {}),
        (c7_adj, [{}], [], [], {}, {}),
        (lambda u, v: (u == [1] and v == 0) or (v == [1] and u == 0), [0], [0], [], {0: 0}, {0: [1]}),
    )
    for idx_m, args_m in enumerate(malformed_vt):
        ok_m, code_m, _ = verify_valid_tuple(*args_m)  # type: ignore[arg-type]
        if ok_m or code_m != "MATH_MISMATCH":
            return False, "MATH_MISMATCH", f"Malformed verify_valid_tuple case {idx_m} returned ({ok_m}, {code_m})", {}
    ok_het, code_het, _ = verify_valid_tuple(
        lambda u, v: u == 99 or v == 99, [0, "a"], [0], [], {0: 0}, {0: 99}
    )
    if ok_het or code_het != "PRIVACY_VIOLATION":
        return False, "MATH_MISMATCH", f"Heterogeneous verify_valid_tuple expected PRIVACY_VIOLATION, got ({ok_het}, {code_het})", {}

    # R2-N01: >100,000-digit integer guards across math/Profile/Trie7/witness/_sanitize_details (zero ValueError!)
    BIG = 1 << 1700000
    if not check_nat_pow_bound(1, 1, BIG, 1)[0]:
        return False, "MATH_MISMATCH", "check_nat_pow_bound(1, 1, BIG, 1) failed", {}
    for bad_pow_args in ((-BIG, 1, 1, 1), (1, -BIG, 1, 1), (1, 1, -BIG, 1), (1, 1, 1, -BIG)):
        if check_nat_pow_bound(*bad_pow_args)[0]:
            return False, "MATH_MISMATCH", "check_nat_pow_bound accepted negative giant int", {}
    if Profile(0, BIG, 0, 0).validate()[0] or Profile(-BIG, 0, 0, 0).validate()[0]:
        return False, "MATH_MISMATCH", "Profile.validate accepted invalid giant int", {}
    for fn_call in (
        lambda: split_tree_pow(unit_prof, -BIG),
        lambda: bisect_theta_c7(-BIG),
        lambda: format_fraction_down(Fraction(1, 2), 200000),
    ):
        try:
            fn_call()
            return False, "MATH_MISMATCH", "Expected ValueError on giant negative/precision arg", {}
        except ValueError as exc:
            if "Exceeds the limit" in str(exc):
                return False, "MATH_MISMATCH", f"Hit Python int-str limit instead of safe guard: {exc}", {}
    if Trie7.from_vertices([[BIG]], 1)[0] is not None or Trie7.from_vertices([], -BIG)[0] is not None:
        return False, "MATH_MISMATCH", "Trie7.from_vertices accepted giant invalid coord/dim", {}
    if (
        verify_strong_power_independent_set([[BIG]], c7_adj, 1, 7)[0]
        or verify_strong_power_independent_set([], c7_adj, -BIG, 7)[0]
    ):
        return False, "MATH_MISMATCH", "verify_strong_power_independent_set accepted giant invalid coord/dim", {}
    sanitized = _sanitize_details({"big": BIG, "neg_big": -BIG, BIG: [BIG]})
    json.dumps(sanitized)

    # R3-N01 & R3-N03: positive d=BIG formatting, nested big-int containers, and non-callable adj_fn
    if Trie7.from_vertices([[0]], BIG)[:2] != (None, "MATH_MISMATCH"):
        return False, "MATH_MISMATCH", "Trie7.from_vertices([[0]], BIG) did not return clean MATH_MISMATCH", {}
    if verify_strong_power_independent_set([[0]], c7_adj, BIG, 7)[:2] != (False, "MATH_MISMATCH"):
        return False, "MATH_MISMATCH", "verify_strong_power_independent_set([[0]], ..., BIG) failed", {}
    for bad_adj in (None, 42, "c7"):
        if verify_strong_power_independent_set([(0,), (2,)], bad_adj, 1, 7)[:2] != (False, "MATH_MISMATCH"):  # type: ignore[arg-type]
            return False, "MATH_MISMATCH", f"verify_strong_power_independent_set did not reject adj_fn={bad_adj!r}", {}
        if verify_strong_power_independent_set([], bad_adj, 1, 7)[:2] != (False, "MATH_MISMATCH"):  # type: ignore[arg-type]
            return False, "MATH_MISMATCH", f"verify_strong_power_independent_set([]) did not reject adj_fn={bad_adj!r}", {}
    for nested_big in ((BIG,), Fraction(BIG, 1), Profile(BIG, 0, 0, 0)):
        prev_s = safe_int_preview(nested_big)
        if not isinstance(prev_s, str) or not prev_s:
            return False, "MATH_MISMATCH", f"safe_int_preview failed on {type(nested_big).__name__}", {}
    ok_vt_big1, c_vt_big1, info_vt_big1 = verify_valid_tuple(
        lambda u, v: u == 99 or v == 99, [0, "a", BIG], [0], [], {0: 0}, {0: 99}
    )
    if ok_vt_big1 or c_vt_big1 != "PRIVACY_VIOLATION":
        return False, "MATH_MISMATCH", f"verify_valid_tuple([0, 'a', BIG]) returned ({ok_vt_big1}, {c_vt_big1})", {}
    json.dumps(_sanitize_details(info_vt_big1))
    if verify_valid_tuple(lambda u, v: False, [(BIG,)], [(BIG,)], [], {}, {})[:2] != (False, "MATH_MISMATCH"):
        return False, "MATH_MISMATCH", "verify_valid_tuple([(BIG,)]) did not return clean MATH_MISMATCH", {}
    nested_san = _sanitize_details(
        {
            (BIG, 1): "v",
            "f": Fraction(BIG, 1),
            "p": Profile(BIG, 0, 0, 0),
            Fraction(BIG, 3): "fk",
            Profile(BIG, 0, 0, 0): "pk",
            "s": {BIG, (BIG,), Fraction(BIG, 3)},
        }
    )
    json.dumps(nested_san)

    # R4-C2-N01: pathological __str__/__repr__/__eq__ in _safe_str_obj, safe_int_preview, _sanitize_details & execute_test
    class _BadStrTypeErr:
        def __str__(self) -> str:
            raise TypeError("broken __str__")
        def __repr__(self) -> str:
            raise TypeError("broken __repr__")

    class _BadStrExc(Exception):
        def __str__(self) -> str:
            raise TypeError("broken exc __str__")

    class _BadEqKey:
        def __hash__(self) -> int:
            return 7
        def __eq__(self, other: object) -> bool:
            raise RuntimeError("broken __eq__")
        def __str__(self) -> str:
            raise RuntimeError("broken key __str__")

    bad_obj = _BadStrTypeErr()
    if not isinstance(_safe_str_obj(bad_obj), str) or not isinstance(safe_int_preview(bad_obj), str):
        return False, "MATH_MISMATCH", "R4-C2-N01 _safe_str_obj / safe_int_preview failed on TypeError __str__", {}
    san_bad = _sanitize_details({_BadEqKey(): bad_obj, "s": {bad_obj, BIG}, "per_file": "drop"})
    if "per_file" in san_bad:
        return False, "MATH_MISMATCH", "R4-C2-N01 _sanitize_details failed to strip per_file", {}
    json.dumps(san_bad)

    def _raise_bad_exc(_ctx: SuiteContext):
        raise _BadStrExc()

    res_bad_exc = execute_test(TestCase("ST-BAD-EXC", "SELF_TEST", "CONTROL", "bad exc", _raise_bad_exc), ctx)
    if res_bad_exc.status != "FAIL" or res_bad_exc.code != "INTERNAL_EXCEPTION":
        return False, "MATH_MISMATCH", f"execute_test failed on _BadStrExc: {res_bad_exc}", {}
    json.dumps(res_bad_exc.to_dict())
    res_bad_det = execute_test(
        TestCase("ST-BAD-DET", "SELF_TEST", "CONTROL", "bad det", lambda _c: (True, "OK", "ok", {"x": bad_obj})),
        ctx,
    )
    if res_bad_det.status != "PASS":
        return False, "MATH_MISMATCH", f"execute_test failed sanitizing _BadStrTypeErr details: {res_bad_det}", {}
    json.dumps(res_bad_det.to_dict())

    # R5-C2-N02: pathological str subclasses overriding __eq__/__str__/__lt__ in _sanitize_details
    class _EvilStr(str):
        def __eq__(self, other: object) -> bool:
            raise RuntimeError("boom eq")
        def __hash__(self) -> int:
            return super().__hash__()

    class _EvilStrAll(str):
        def __eq__(self, other: object) -> bool:
            raise RuntimeError("boom eq")
        def __lt__(self, other: object) -> bool:
            raise RuntimeError("boom lt")
        def __str__(self) -> str:
            raise RuntimeError("boom str")
        def __hash__(self) -> int:
            return super().__hash__()

    class _EvilStrSelf(str):
        def __eq__(self, other: object) -> bool:
            raise RuntimeError("boom eq")
        def __str__(self) -> str:
            return self
        def __hash__(self) -> int:
            return super().__hash__()

    san_evil_str = _sanitize_details(
        {
            _EvilStr("per_file"): 1,
            _EvilStrAll("k"): _EvilStrAll("v"),
            _EvilStrSelf("s1"): _EvilStrSelf("s2"),
            "evil_set": {_EvilStrAll("a"), _EvilStrAll("b")},
        }
    )
    json.dumps(san_evil_str)

    # R5-C2-N03: _safe_ratio_preview exact max_int_digits boundary (10^200 -> preview; 10^200 - 1 -> decimal)
    prev_200 = _safe_ratio_preview(10**200, 1)
    prev_200_neg = _safe_ratio_preview(-(10**200), 1)
    prev_199 = _safe_ratio_preview(10**200 - 1, 1, digits=2)
    prev_199_neg = _safe_ratio_preview(-(10**200 - 1), 1, digits=2)
    prev_mul_ge = _safe_ratio_preview(7 * (10**200), 7)
    prev_mul_lt = _safe_ratio_preview(7 * (10**200) - 1, 7, digits=2)
    if (
        not prev_200.startswith("<rational ")
        or not prev_200_neg.startswith("-<rational ")
        or prev_199 != ("9" * 200 + ".00")
        or prev_199_neg != ("-" + "9" * 200 + ".00")
        or not prev_mul_ge.startswith("<rational ")
        or prev_mul_lt != ("9" * 200 + ".85")
    ):
        return False, "MATH_MISMATCH", f"R5-C2-N03 _safe_ratio_preview boundary mismatch: {(prev_200[:30], prev_199[:15], prev_mul_lt[-10:])}", {}

    # R6-R2-N1 / R6-C2-N01: EvilInt (bit_length/__lt__/__str__/__repr__/__int__), EvilFloat & EvilPathLike
    # in _sanitize_details + json.dumps + run_subprocess_safe (FileNotFoundError & TimeoutExpired)
    class _EvilInt(int):
        def bit_length(self) -> int:
            raise RuntimeError("boom bit_length")
        def __lt__(self, other: object) -> bool:
            raise RuntimeError("boom lt")
        def __str__(self) -> str:
            raise RuntimeError("boom str")
        def __repr__(self) -> str:
            raise RuntimeError("boom repr")
        def __int__(self) -> int:
            raise RuntimeError("boom int")

    class _EvilFloat(float):
        def __lt__(self, other: object) -> bool:
            raise RuntimeError("boom lt")
        def __str__(self) -> str:
            raise RuntimeError("boom str")
        def __repr__(self) -> str:
            raise RuntimeError("boom repr")
        def __float__(self) -> float:
            raise RuntimeError("boom float")

    class _EvilPathLike(os.PathLike):
        def __init__(self, target: str) -> None:
            self._target = target
        def __fspath__(self) -> str:
            return self._target
        def __str__(self) -> str:
            raise RuntimeError("boom path str")
        def __repr__(self) -> str:
            raise RuntimeError("boom path repr")

    ei_sm = _EvilInt(42)
    ei_big = _EvilInt(1 << 400000)
    ei_nbig = _EvilInt(-(1 << 400000))
    ef_v = _EvilFloat(3.25)
    epl_miss = _EvilPathLike("/nonexistent_shannon_c7_e2e_probe_xyz")
    epl_py = _EvilPathLike(sys.executable)

    san_sub = _sanitize_details(
        {
            "ei_sm": ei_sm,
            "ei_big": ei_big,
            "ei_nbig": ei_nbig,
            "ef": ef_v,
            "epl": epl_miss,
            "set_i": {_EvilInt(2), _EvilInt(1)},
            "set_f": {_EvilFloat(2.5), _EvilFloat(1.5)},
            ei_sm: "k_sm",
            ei_big: "k_big",
            ef_v: "k_flt",
        }
    )
    json.dumps(san_sub)
    if (
        type(san_sub.get("ei_sm")) is not int
        or san_sub["ei_sm"] != 42
        or san_sub.get("ei_big") != "<int bit_length=400001>"
        or san_sub.get("ei_nbig") != "-<int bit_length=400001>"
        or type(san_sub.get("ef")) is not float
        or san_sub["ef"] != 3.25
        or san_sub.get("set_i") != [1, 2]
        or san_sub.get("set_f") != [1.5, 2.5]
        or san_sub.get("42") != "k_sm"
        or san_sub.get("<int bit_length=400001>") != "k_big"
        or san_sub.get("3.25") != "k_flt"
    ):
        return False, "MATH_MISMATCH", f"R6-R2-N1/R6-C2-N01 _sanitize_details subclass coercion mismatch: {san_sub}", {}

    out_miss_pl = run_subprocess_safe([epl_miss])  # type: ignore[list-item]
    out_miss_es = run_subprocess_safe([_EvilStrAll("/nonexistent_shannon_c7_e2e_probe_xyz")])
    out_to_pl = run_subprocess_safe([epl_py, "-B", "-c", "import time; time.sleep(5)"], timeout=0.05)  # type: ignore[list-item,arg-type]
    if (
        out_miss_pl.ok
        or out_miss_pl.code != "MISSING_TOOL"
        or out_miss_pl.returncode != 127
        or type(out_miss_pl.stderr) is not str
        or out_miss_es.ok
        or out_miss_es.code != "MISSING_TOOL"
        or out_to_pl.ok
        or out_to_pl.code != "TIMEOUT"
        or not out_to_pl.timed_out
        or type(out_to_pl.stderr) is not str
    ):
        return False, "MATH_MISMATCH", f"R6-R2-N1/R6-C2-N01 run_subprocess_safe evil subclass guard failed: {(out_miss_pl.code, out_miss_es.code, out_to_pl.code)}", {}

    # Iter-8 R7-C2-N01: execute_test must coerce pathological code/message/passed into exact base str/bool
    def _evil_return_fn(_ctx: SuiteContext):
        return (
            1,
            _EvilStrAll("EVIL_CODE"),
            _EvilStrAll("EVIL_MSG"),
            {"k": _EvilStrAll("v")},
        )

    def _evil_empty_code_fn(_ctx: SuiteContext):
        return (0, _EvilStrAll(""), _EvilStrAll("boom"), {})

    res_ec1 = execute_test(TestCase("ST-X1", 0, "F15", "evil-ret-1", _evil_return_fn), ctx)
    res_ec2 = execute_test(TestCase("ST-X2", 0, "F15", "evil-ret-2", _evil_empty_code_fn), ctx)
    for r_ec in (res_ec1, res_ec2):
        if type(r_ec.code) is not str or type(r_ec.message) is not str:
            return False, "MATH_MISMATCH", f"R7-C2-N01 execute_test leaked non-str code/message: {(type(r_ec.code), type(r_ec.message))}", {}
        if r_ec.status not in ("PASS", "FAIL"):
            return False, "MATH_MISMATCH", f"R7-C2-N01 execute_test invalid status: {r_ec.status!r}", {}
        _ = format_result_line(r_ec, verbose=True)
        _ = json.dumps(r_ec.to_dict())
    if res_ec1.status != "PASS" or res_ec2.status != "FAIL" or res_ec2.code != "FAIL":
        return False, "MATH_MISMATCH", f"R7-C2-N01 execute_test coercion mismatch: {(res_ec1.status, res_ec2.status, res_ec2.code)}", {}

    return True, "OK", "Rounded-up decimals, d=500 & >100k-digit big-ints, Profile/Trie7/ValidTuple, _safe_ratio_preview & pathological __str__/str/int/float/PathLike subclass guards verified", {}


def _st_11(ctx: SuiteContext):
    good = ((3258805369885, 10**12), (3258827985920007, 10**15), (651761073977, 200000000000))
    BIG = 1 << 1700000
    bad = (
        (3258805369884, 10**12),       # -1 ULP below floor
        (3317667207395, 10**12),       # == upper ceiling
        (33176672073945, 10**13),      # cubic trap (< upper rat yet > theta(C7)!)
        (3258805369885, 0),            # den == 0
        (0, 10**12),                   # num == 0
        (10**300, 1),                  # giant numerator (no Decimal InvalidOperation!)
        (BIG, 1),                      # >100k-digit positive numerator (zero ValueError!)
        (-BIG, 1),                     # >100k-digit negative numerator (zero ValueError!)
        (1, -BIG),                     # >100k-digit negative denominator (zero ValueError!)
        (True, True),                  # bool-as-int rejected
    )
    for num, den in good:
        ok, code, _ = check_frontier_rational_bounds(num, den)
        if not ok:
            return False, code, f"Valid bound {num}/{den} wrongly rejected", {}
    for num, den in bad:
        ok, code, _ = check_frontier_rational_bounds(num, den)
        if ok or code != "BOUNDS_VIOLATION":
            return False, "MATH_MISMATCH", f"Invalid bound rejected check failed (ok={ok}, code={code})", {}

    # Exact arbitrary-precision format_fraction_down regression checks (no InvalidOperation, no 0E-12)
    if format_fraction_down(Fraction(0, 1), 12) != "0.000000000000":
        return False, "MATH_MISMATCH", "format_fraction_down(0, 12) emitted unexpected format", {}
    if format_fraction_down(Fraction(1, 10**100), 12) != "0.000000000000":
        return False, "MATH_MISMATCH", "format_fraction_down(1/10^100, 12) emitted scientific notation", {}
    if format_fraction_down(Fraction(-5, 3), 2) != "-1.67":
        return False, "MATH_MISMATCH", "format_fraction_down(-5/3, 2) floor failed", {}
    if format_fraction_down(Fraction(10**300, 1), 20) != ("1" + "0" * 300 + "." + "0" * 20):
        return False, "MATH_MISMATCH", "format_fraction_down(10^300, 20) failed", {}
    if check_nat_pow_bound(10**50, 1, 2, 1)[0]:
        return False, "MATH_MISMATCH", "check_nat_pow_bound(10^50, 1, 2, 1) failed to reject", {}

    # R4-C2-N01: fast exact zero-GCD 350k-bit coprime check_frontier_rational_bounds (was >2.5s -> <20ms)
    m350 = 1 << 350000
    t0_350 = time.process_time()
    ok_350_fl, _, _ = check_frontier_rational_bounds(3258805369885 * m350 + 1, 10**12 * m350)
    ok_350_lo, _, _ = check_frontier_rational_bounds(3317667207394095 * m350 + 1, 10**15 * m350)
    ok_350_hi, c_350_hi, _ = check_frontier_rational_bounds(3317667207394096 * m350 + 1, 10**15 * m350)
    dt_350 = time.process_time() - t0_350
    if not ok_350_fl or not ok_350_lo or ok_350_hi or c_350_hi != "BOUNDS_VIOLATION":
        return False, "MATH_MISMATCH", f"350k-bit exact bounds check mismatch: {(ok_350_fl, ok_350_lo, ok_350_hi, c_350_hi)}", {}
    if dt_350 > 0.5:
        return False, "MATH_MISMATCH", f"R4-C2-N01 350k-bit check_frontier_rational_bounds slow ({dt_350:.2f}s CPU)", {}

    return True, "OK", "Valid bounds accepted; <floor, >=upper, cubic trap, den=0, num=0, >100k-digit & 350k-bit zero-GCD bounds verified", {}


def _st_12(ctx: SuiteContext):
    must_fail = (
        ("C5", Fraction(2, 1)),
        ("C5", Fraction(22360679, 10**7)),
        ("SasonGilbert32", Fraction(4, 1)),
        ("SasonGilbert32", Fraction(44721359, 10**7)),
        ("SRG27", Fraction(59, 10)),
        ("C7", Fraction(325, 100)),
        ("C7_compl", Fraction(2, 1)),
    )
    must_pass = (
        ("C5", Fraction(22360680, 10**7)),
        ("SasonGilbert32", Fraction(16, 3)),
        ("SRG27", Fraction(7, 1)),
        ("C7", LOVASZ_UPPER_RAT),
        ("C7_compl", Fraction(2109916264175, 10**12)),
    )
    for g, b in must_fail:
        ok, _ = validate_upper_bound_claim(g, b)
        if ok:
            return False, "OBSTRUCTION_VIOLATION", f"Invalid bound {b} on {g} not rejected", {}
    for g, b in must_pass:
        ok, msg = validate_upper_bound_claim(g, b)
        if not ok:
            return False, "OBSTRUCTION_VIOLATION", f"Valid bound {b} on {g} wrongly rejected: {msg}", {}
    return True, "OK", "Obstruction validator caught all 7 invalid bounds and accepted all 5 valid baselines", {}


def _st_13(ctx: SuiteContext):
    v_ok = scan_lean_hygiene("import ShannonC7.Main\nimport Mathlib.Combinatorics.SimpleGraph.CycleGraph\n", mode="audit")
    v_defs = scan_lean_hygiene("import ShannonC7.Main\nimport ShannonC7.Defs\n", mode="audit")
    v_root = scan_lean_hygiene("import ShannonC7\n", mode="audit")
    v_nomain = scan_lean_hygiene("import Mathlib.Combinatorics.SimpleGraph.CycleGraph\n", mode="audit")
    v_whole = scan_lean_hygiene("import ShannonC7.Main\nimport Mathlib\n", mode="audit")
    if v_ok:
        return False, "HYGIENE_VIOLATION", f"Clean audit control failed: {v_ok}", {}
    if not any(v.rule == "OPAQUE_BOX_VIOLATION" for v in v_defs):
        return False, "MATH_MISMATCH", "import ShannonC7.Defs missed", {}
    if not any(v.rule == "OPAQUE_BOX_VIOLATION" for v in v_root):
        return False, "MATH_MISMATCH", "import ShannonC7 missed", {}
    if not any(v.rule == "MISSING_MAIN_IMPORT" for v in v_nomain):
        return False, "MATH_MISMATCH", "Missing ShannonC7.Main import missed", {}
    if not any(v.rule == "WHOLESALE_MATHLIB_IMPORT" for v in v_whole):
        return False, "MATH_MISMATCH", "Wholesale import Mathlib missed", {}
    return True, "OK", "Opaque-box & wholesale Mathlib import rules enforced cleanly", {}


def _st_14(ctx: SuiteContext):
    tmp = _sandbox_dir("shannon_c7_st14_")
    try:
        empty_proj = tmp / "empty_project"
        empty_proj.mkdir()
        json_out = tmp / "report.json"
        run_sh = ctx.verify_dir / "run_e2e.sh"
        out = run_subprocess_safe(
            [str(run_sh), "--all", "--project-dir", str(empty_proj), "--json-out", str(json_out)],
            cwd=ctx.verify_dir,
            timeout=60,
            extra_env={"SHANNON_C7_E2E_NESTED": "1"},
        )
        combined = out.stdout + "\n" + out.stderr
        if out.returncode != 1:
            return False, "SUBPROCESS_FAILED", f"Expected exit code 1 on empty project dir, got {out.returncode}", {}
        if "Traceback" in combined:
            return False, "INTERNAL_EXCEPTION", "Unhandled Python traceback found on empty project dir", {}
        if not json_out.is_file():
            return False, "MISSING_FILE", "Expected JSON report not written on empty project dir", {}
        rep = json.loads(json_out.read_text(encoding="utf-8"))
        summary = rep.get("summary", {})
        if summary.get("total") != 164 or summary.get("failed", 0) <= 0:
            return False, "REPORT_MISMATCH", f"Unexpected summary on empty project dir: {summary}", summary
        codes = {r.get("code") for r in rep.get("results", []) if r.get("status") == "FAIL"}
        if not (codes & {"MISSING_FILE", "MISSING_DIR", "MISSING_TOOL"}):
            return False, "REPORT_MISMATCH", f"Expected crisp MISSING_* codes, got {codes}", {}
        return True, "OK", f"Empty project dir exited 1 with 0 tracebacks and valid JSON (total=164, failed={summary['failed']})", summary
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def _st_15(ctx: SuiteContext):
    tmp = _sandbox_dir("shannon_c7_st15_")
    try:
        # Static Main.lean extraction resilient to char '"' & raw r#"\"# comment desync,
        # `(10 : ℕ) ^ 12` ascriptions, and multiline type signatures
        main_lean = tmp / "Main.lean"
        main_lean.write_text(
            "namespace ShannonC7\n"
            "def c : Char := '\"'\n"
            'def rawS : String := r#"\\"#\n'
            "def c7_lower_num\n  : ℕ := 3_258_805_369_885\n"
            "def c7_lower_den : ℕ := (10 : ℕ) ^ 12\n"
            "/-\n"
            "def c7_lower_num : ℕ := 9999999999999\n"
            "-/\n"
            "end ShannonC7\n",
            encoding="utf-8",
        )
        ok_b, code_b, info_b = extract_main_bounds(main_lean)
        if not ok_b or info_b["c7_lower_num"] != 3258805369885 or info_b["c7_lower_den"] != 10**12:
            return False, code_b, f"Static Main.lean extraction failed: {info_b}", {}

        # Secondary fallback to FrontierLower.lean when Main.lean only re-exports
        sub_dir = tmp / "reexport"
        sub_dir.mkdir()
        (sub_dir / "Main.lean").write_text("import ShannonC7.FrontierLower\n", encoding="utf-8")
        (sub_dir / "FrontierLower.lean").write_text(
            "def c7_lower_num : Nat := 3258805369885\ndef c7_lower_den : Nat := 10 ^ 12\n",
            encoding="utf-8",
        )
        ok_fl, code_fl, info_fl = extract_main_bounds(sub_dir / "Main.lean")
        if not ok_fl or info_fl["c7_lower_num"] != 3258805369885 or info_fl["c7_lower_den"] != 10**12:
            return False, code_fl, f"FrontierLower.lean static fallback failed: {info_fl}", {}

        # Lean v4.32.2 `public def` & declaration boundary words + right-assoc `2 ^ 3 ^ 2 = 512`
        pub_main = tmp / "PublicMain.lean"
        pub_main.write_text(
            "namespace ShannonC7\n"
            "public def c7_lower_num : ℕ := 3258805369885\n"
            "public def c7_lower_den : ℕ := 10 ^ 12\n"
            "local notation \"dummy\" => 0\n"
            "end ShannonC7\n",
            encoding="utf-8",
        )
        ok_pub, code_pub, info_pub = extract_main_bounds(pub_main)
        if not ok_pub or info_pub["c7_lower_num"] != 3258805369885 or info_pub["c7_lower_den"] != 10**12:
            return False, code_pub, f"Lean v4.32.2 public def extraction failed: {info_pub}", {}

        rpow_main = tmp / "RPowMain.lean"
        rpow_main.write_text(
            "def c7_lower_num : Nat := 2 ^ 3 ^ 2\n"
            "scoped def c7_lower_den : Nat := 10 ^ 2\n"
            "partial def helper : Nat := 0\n",
            encoding="utf-8",
        )
        ok_rp, code_rp, info_rp = extract_main_bounds(rpow_main)
        if not ok_rp or info_rp["c7_lower_num"] != 512 or info_rp["c7_lower_den"] != 100:
            return False, code_rp, f"Right-assoc pow / scoped / partial boundary extraction failed: {info_rp}", {}

        # Recursion-depth & >100k-digit DoS guards in _eval_nat_tokens (zero RecursionError / ValueError)
        for bad_name, bad_src in (
            ("deep_parens.lean", f"def c7_lower_num : Nat := {'(' * 2000}1{')' * 2000}\ndef c7_lower_den : Nat := 1\n"),
            ("deep_pow.lean", f"def c7_lower_num : Nat := {'1 ^ ' * 2000}1\ndef c7_lower_den : Nat := 1\n"),
            ("huge_lit.lean", f"def c7_lower_num : Nat := 1{'0' * 100005}\ndef c7_lower_den : Nat := 1\n"),
        ):
            fp_bad = tmp / bad_name
            fp_bad.write_text(bad_src, encoding="utf-8")
            ok_dos, code_dos, _ = extract_main_bounds(fp_bad)
            if ok_dos or code_dos != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"DoS guard `{bad_name}` returned ({ok_dos}, {code_dos})", {}

        # Consistent honest RESULTS.md (cleanly separated per Option A-Report) -> PASS
        good_md = tmp / "RESULTS_good.md"
        good_base = (
            "# Shannon Capacity of C_7 Formalization Results\n\n"
            "The exact value of Theta(C_7) remains an open problem (OpenQuestion_StrictGap).\n"
            "We have not proved that Theta(C_7) = 3.317667207394; it remains an open gap.\n"
            "Certified Lean 4 lower bound: 3.258805369885 (3258805369885 / 10^12).\n"
            "Our formalization verifies 3.258805369885 in the pure Lean 4 kernel.\n"
            "It remains below the external August 2026 BPZ record (3.258827985920007, which relies on native_decide).\n"
            "The unrefereed Aug 31, 2026 lower bound 3.258832620353 has not yet been formalized in Lean 4.\n"
            "Track L2 C++17 candidate lower bound (not yet formalized): 3.258835123456.\n\n"
            "| Reference | Method | d | Lower Bound |\n"
            "|---|---|---|---|\n"
            "| BPZ (2026) | External native_decide | 500 | 3.258827985920007 |\n"
            "| Unrefereed d=500 lower bound | C++17 search | 500 | 3.258832620353 |\n"
            "| This work | Pure Lean 4 kernel | 200 | 3.258805369885 |\n\n"
            "Lovasz upper bound: theta(C_7) < 3.317667207395.\n"
            "Exact small powers verified: alpha(C_7)=3, alpha(C_7^2)=10, alpha(C_7^3)=33.\n"
            "Pure-kernel TCB: strictly {propext, Classical.choice, Quot.sound}, zero sorry, zero native_decide.\n"
        )
        good_md.write_text(good_base, encoding="utf-8")
        ok_g, c_g, i_g = verify_results_md(good_md, info_b["c7_lower_num"], info_b["c7_lower_den"])
        if not ok_g:
            return False, c_g, f"Honest RESULTS.md with BPZ/Tandon table & negation wrongly rejected: {i_g}", {}

        # Honest positive RESULTS.md regressions (cleanly separated Lovasz truncations, external benchmarks, embedded-dot negations, Fekete lim)
        honest_extra_lines = (
            "Certified Lovasz upper bound: 3.31766720739.",
            "Certified Lovasz upper bound: 3.317667.",
            "Verified in Lean 4: Theta(C_7) <= lovaszThetaC7 (~3.317667).",
            "Our certified Lean 4 sandwich proves 3.258805369885 <= Theta(C_7) <= 3.317667.",
            "Our formalization proves Theta(C_7) <= lovaszThetaC7 ≈ 3.317667207.",
            "This work certifies 3.258805369885 <= Theta(C_7) <= 3.31766720739.",
            "| Certified Lean 4 sandwich | [3.258805369885, 3.317667] |",
            "Our lower-bound campaign targeted Tandon's unrefereed record of 3.258832620353 and BPZ's August 2026 external native_decide record of 3.258827985920007.",
            "We did not achieve 3.258832620353 in Lean 4; our formalization has not yet reached 3.258827985920007.",
            r"We have not proved that $\Theta(C_7) = 3.317667207394$ or solved the 70-year open problem exactly.",
            "We do not claim in Main.lean that we proved Theta(C_7) = 3.258805369885.",
            "We have not reached 3.317667207394 or proved that Theta(C_7) = 3.317667207394.",
            "Even with Lean 4.32.2, we have not solved the 70-year open problem exactly.",
            r"We proved that $\Theta(C_7) = \lim_{d\to\infty} \alpha(C_7^{\boxtimes d})^{1/d}$ via Fekete.",
        )
        for idx_he, ok_line in enumerate(honest_extra_lines):
            he_md = tmp / f"RESULTS_honest_{idx_he}.md"
            he_md.write_text(good_base + "\n" + ok_line + "\n", encoding="utf-8")
            ok_he, c_he, i_he = verify_results_md(he_md, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if not ok_he:
                return False, c_he, f"Honest RESULTS.md regression {idx_he} wrongly rejected ({ok_line!r}): {i_he}", {}

        # Inflated RESULTS.md mutations (all 22 MUST FAIL with REPORT_MISMATCH)
        inflated_lines = (
            "Our Lean 4 verified lower bound is 3.258832620353.",
            "Our Lean 4 verified lower bound beats Tandon at 3.258899999999!",
            "3258805369885 is the baseline, and our target-beating certified Lean 4 lower bound is 3.299999999999!",
            "Our Lean 4 certified lower bound is 3.315000000000.",
            "Our Lean 4 certified lower bound is 3258899999999 / 10^12.",
            "3.258899999999 is our Lean 4 verified lower bound.",
            "Our Lean 4 certified lower bound is:\n3.258899999999",
            "| Pure-kernel Lean 4 (no native_decide) | 500 | 3.258899999999 |",
            "Pure-kernel Lean 4 formalization (zero native_decide) certifies 3.258899999999.",
            "Our Lean 4 bound surpasses Tandon (unrefereed): 3.258899999999.",
            "Our Lean 4 bound achieves a new world record surpassing Tandon's record: 3.258899999999.",
            "Our Lean 4 certified lower bound is:\n**3.258899999999**",
            "Our Lean 4 certified lower bound is:\n`3.258899999999`",
            "Our Lean 4 certified lower bound is:\n- 3.258899999999",
            "Our Lean 4 certified lower bound is:\n$$\n\\frac{3258899999999}{10^{12}}\n$$",
            "Our Lean 4 verified lower bound is 3.26.",
            "Our Lean 4 verified lower bound is 3.299.",
            "Our Lean 4 verified lower bound is 3.317667207394.",
            "Our Lean 4 verified lower bound is 3.25883262035312345678.",
            "Our Lean 4 certified lower bound is 32589 / 10000.",
            "Our Lean 4 certified lower bound is 326 / 100.",
            r"Our Lean 4 verified lower bound is $\frac{3258899999999}{10^{12}}$.",
        )
        for idx_i, bad_line in enumerate(inflated_lines):
            inf_md = tmp / f"RESULTS_inflated_{idx_i}.md"
            inf_md.write_text(good_base + "\n" + bad_line + "\n", encoding="utf-8")
            ok_i, c_i, _ = verify_results_md(inf_md, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_i or c_i != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Inflated RESULTS.md case {idx_i} not caught: {bad_line!r}", {}

        # Dishonest exact-solution mutations in RESULTS.md -> FAIL HONESTY_VIOLATION
        dishonest_lines = (
            "We proved Theta(C_7) = 3.258805369885 exactly.",
            "We proved Θ(C₇) = 3.258805369885.",
            r"We proved that $\Theta(C_7) = 3.258805369885$.",
            r"The exact value of \Theta(C_{7}) is proven.",
            r"We proved $\Theta(C_7)$ = 3.258805369885.",
            "Although Theta(C_7) was not known previously, we proved Theta(C_7) = 3.258805369885.",
            "We have not finished L3 and we prove Theta(C_7) = 3.258805369885.",
        )
        for idx_h, bad_line in enumerate(dishonest_lines):
            bad_md = tmp / f"RESULTS_dishonest_{idx_h}.md"
            bad_md.write_text(good_base + "\n" + bad_line + "\n", encoding="utf-8")
            ok_h, c_h, _ = verify_results_md(bad_md, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_h or c_h != "HONESTY_VIOLATION":
                return False, "MATH_MISMATCH", f"False exact-solution claim {idx_h} not caught: {bad_line!r}", {}

        # LOWER_RESEARCH_REPORT.md: honest Lovasz truncation control passes; exact-solution claims FAIL HONESTY_VIOLATION
        low_base = (
            "# Lower Frontier Research Report\n\n"
            "Our formalization narrows the pure-kernel gap to Lovasz theta (~3.317667) from 3.258805369885.\n"
            "All pure-kernel certificates verified in Lean 4 without native_decide; exact value of Theta(C_7) remains open.\n"
        )
        low_good = tmp / "LOWER_good.md"
        low_good.write_text(low_base, encoding="utf-8")
        ok_lg, c_lg, i_lg = verify_research_report(
            low_good, kind="lower", lower_num=info_b["c7_lower_num"], lower_den=info_b["c7_lower_den"]
        )
        if not ok_lg:
            return False, c_lg, f"Honest LOWER_RESEARCH_REPORT.md wrongly rejected: {i_lg}", {}
        for idx_lh, bad_lh in enumerate(
            (
                "We proved Theta(C_7) = 3.258805369885! Exact solution proven in Lean.",
                "We solved the 70-year open problem exactly in our lower-bound search.",
            )
        ):
            low_bad = tmp / f"LOWER_dishonest_{idx_lh}.md"
            low_bad.write_text(low_base + "\n" + bad_lh + "\n", encoding="utf-8")
            ok_lb, c_lb, _ = verify_research_report(
                low_bad, kind="lower", lower_num=info_b["c7_lower_num"], lower_den=info_b["c7_lower_den"]
            )
            if ok_lb or c_lb != "HONESTY_VIOLATION":
                return False, "MATH_MISMATCH", f"LOWER exact-solution claim {idx_lh} not caught: {bad_lh!r}", {}

        # Upper research report: honest embedded-dot negations & giant upper bound pass; all 13 impossible bounds FAIL
        up_base = (
            "# Upper Research Report\n"
            "Exact alpha(C_7^3) = 33 certified; alpha(C_7^4) <= 115 via slice double-counting.\n"
            "Obstructions audited: Bukh-Cox, Bi-Tang, Sason Gilbert-32, srg(27,10,1,5).\n"
            "We ruled out alpha(C_7^4) <= 107 because a 108-vertex witness exists.\n"
        )
        for idx_uh, ok_u_line in enumerate(
            (
                "",
                "We ruled out (via SmallPowers.lean) alpha(C_7^4) <= 107.",
                "Because 3.317667207395 is tight, we ruled out 3.2588 and alpha(C_7^4) <= 107.",
                "We prove alpha(C_7^4) <= " + "9" * 100005 + ".",
            )
        ):
            up_good = tmp / f"UPPER_good_{idx_uh}.md"
            up_good.write_text(up_base + ("\n" + ok_u_line + "\n" if ok_u_line else ""), encoding="utf-8")
            ok_ug, c_ug, i_ug = verify_research_report(up_good, kind="upper")
            if not ok_ug:
                return False, c_ug, f"Honest UPPER_RESEARCH_REPORT.md case {idx_uh} wrongly rejected: {i_ug}", {}

        for idx_u, bad_u in enumerate(
            (
                "Later we claim α(C_7^4) <= 107.",
                "We claim alpha(C_7^4) <= 107.",
                r"We claim $\alpha(C_7^{\boxtimes 4}) \le 107$.",
                "We claim alpha(C_7^5) <= 360.",
                r"We prove $\alpha(C_7^4) \leq 107$.",
                r"We prove $\alpha(C_7^{\boxtimes 4}) \leq 107$.",
                r"We prove $\alpha(C_7^{\boxtimes 5}) \leq 360$.",
                "We prove alpha(C_7^4) < 108.",
                "We prove alpha(C_7^5) < 367.",
                "We prove α(C₇⁴) <= 107.",
                "We prove α(C₇⁵) <= 366.",
                "Although α(C_7^4) <= 112 was not proven previously, we prove α(C_7^4) <= 107.",
                "We ruled out alpha(C_7^4) <= 106, and we prove alpha(C_7^4) <= 107.",
            )
        ):
            up_bad = tmp / f"UPPER_bad_{idx_u}.md"
            up_bad.write_text(up_base + "\n" + bad_u + "\n", encoding="utf-8")
            ok_ub, c_ub, _ = verify_research_report(up_bad, kind="upper")
            if ok_ub or c_ub != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Impossible upper claim {idx_u} not caught: {bad_u!r}", {}

        # Strict UTF-8 & zero-NUL rejection across all 3 reports + R2-N01 gigantic-int safety
        bad_utf8 = tmp / "bad_utf8.md"
        bad_utf8.write_bytes(b"# Report\n\xff\xfe\n" + b"x" * 250)
        bad_nul = tmp / "bad_nul.md"
        bad_nul.write_bytes(good_base.encode("utf-8") + b"\x00")
        for fp_enc in (bad_utf8, bad_nul):
            if verify_results_md(fp_enc)[:2] != (False, "REPORT_MISMATCH"):
                return False, "MATH_MISMATCH", f"verify_results_md failed to reject {fp_enc.name}", {}
            if verify_research_report(fp_enc, "lower")[:2] != (False, "REPORT_MISMATCH"):
                return False, "MATH_MISMATCH", f"verify_research_report(lower) failed to reject {fp_enc.name}", {}
            if verify_research_report(fp_enc, "upper")[:2] != (False, "REPORT_MISMATCH"):
                return False, "MATH_MISMATCH", f"verify_research_report(upper) failed to reject {fp_enc.name}", {}

        # Iteration 4 report-analyzer regression locks (R3-D5..R3-D8, R3-N02, R2 Polish 1-3)
        # Compact 257-char base keeps 30+ full verify_results_md checks strictly < 100ms total.
        min_base = (
            "# Shannon Capacity of C_7 Results\n"
            "The exact value of Theta(C_7) remains an open gap.\n"
            "Certified Lean 4 lower bound: 3.258805369885; Lovasz upper bound < 3.317667207395.\n"
            "Small powers: alpha(C_7)=3, alpha(C_7^2)=10, alpha(C_7^3)=33; pure-kernel TCB {propext}.\n"
        )

        # R3-D5 + R3-N02: Honest cleanly-separated RESULTS.md controls (MUST PASS)
        r4_honest_results = (
            r"Trivial bound: $\alpha(C_7^4) \le 7^4 = 2401$.",  # R3-D5 (#10)
            "Our Metric | Lower Bound\n"
            "--- | ---\n"
            "Pure-kernel Lean 4 | 3.258805369885\n"
            "Tandon Benchmark | 3.258832620353",  # R3-D5 (GFM pipe table no leading |, separated rows)
            "| Feature | Metric | Certified Value |\n"
            "|---|---|---|\n"
            "| F3 | Lovasz upper bound | 3.317 |",  # R3-N02 (3-col table 3-digit Lovasz)
            "| Reference | d | Lower Bound | Notes |\n"
            "|---|---|---|---|\n"
            "| BPZ (Aug 2026) | 500 | 3.258827985920007 | Beats Gao (2025) |",
            "| Metric | Value | Notes |\n"
            "|---|---|---|\n"
            "| Certified Lean 4 lower bound | 3.258805369885 | Below Lovász upper bound 3.317667 |",
        )
        for idx_r4h, ok_ln in enumerate(r4_honest_results):
            fp_r4h = tmp / f"RESULTS_r4_honest_{idx_r4h}.md"
            fp_r4h.write_text(min_base + "\n" + ok_ln + "\n", encoding="utf-8")
            ok_rh, c_rh, i_rh = verify_results_md(fp_r4h, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if not ok_rh:
                return False, c_rh, f"Iter 4 honest RESULTS.md case {idx_r4h} wrongly rejected: {i_rh}", {}

        # R3-D6 + R3-D7 + R3-N02 + Polish 1: Inflated RESULTS.md mutations (MUST FAIL REPORT_MISMATCH)
        r4_inflated_results = (
            # R3-D6 (4 table analyzer bypasses + inflated GFM pipe table)
            "| Method | d | Certified Lower Bound | Notes |\n"
            "| --- | --- | --- | --- |\n"
            "| Lean 4 formalization | 500 | 3.258899999999 | Beats Tandon |",
            "| Campaign | Our Certified Lower Bound | Comparison |\n"
            "| --- | --- | --- |\n"
            "| Track L2 (d=500) | 3.258899999999 | Beats Tandon! |",
            "| Metric | Our Certified Lower Bound | Upper Bound |\n"
            "| --- | --- | --- |\n"
            "| Lovász comparison | 3.258899999999 | 3.317667 |",
            "| Ref | Result |\n"
            "| --- | --- |\n"
            "| vs Tandon | Our Lean 4 certified lower bound: 3.258899999999 |",
            "Our Metric | Our Certified Bound | Tandon Benchmark\n"
            "--- | --- | ---\n"
            "Pure-kernel Lean 4 | 3.258899999999 | 3.258832620353",
            # R3-D7 (upper-phrase boundary, negated native_decide, below Lovasz at, `<`)
            "Under the Lovász ceiling our Lean 4 bound is 3.258899999999.",
            "Beneath the Lovász upper bound we certified 3.258899999999.",
            "With gap to Lovász our bound is 3.258899999999.",
            "Our Lovász upper bound is 3.317667 and our bound is 3.258899999999.",
            "Our Lean 4 proof (no sorry, admit, or native_decide) certifies 3.258899999999.",
            "Our pure-kernel Lean 4 proof (does not use native_decide) certifies 3.258899999999.",
            "Our pure-kernel Lean 4 proof (never uses native_decide) certifies 3.258899999999.",
            "Our Lean 4 lower bound stays strictly below Lovász at 3.258899999999.",
            "Our Lean 4 proof establishes $3.258805369885 < 3.258899999999$ as our certified bound.",
            # R3-N02 (narrow NLP boundaries)
            "Our Lean 4 formalization proves Theta(C_7) >= 3.317667207394.",
            "Our certified Lean 4 lower bound reaches 3.317667207394.",
            "Our certified Lean 4 lower bound:\n$$\n\\Theta(C_7) \\ge 3.258899999999\n$$",
            "| Method | Notes | Lower Bound |\n|---|---|---|\n| Lean 4 certified | Beats Tandon | 3.258899999999 |",
            "Our Lean 4 certified lower bound is 3258899999999 / (10^12).",
            # R2 Polish 1 (key-value table row_is_lower symmetry)
            "| Metric | Value |\n|---|---|\n| Certified Lean 4 lower bound | 3.317667207394 |",
        )
        for idx_r4i, bad_ln in enumerate(r4_inflated_results):
            fp_r4i = tmp / f"RESULTS_r4_inf_{idx_r4i}.md"
            fp_r4i.write_text(min_base + "\n" + bad_ln + "\n", encoding="utf-8")
            ok_ri, c_ri, _ = verify_results_md(fp_r4i, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_ri or c_ri != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 4 inflated RESULTS.md case {idx_r4i} missed: {bad_ln!r}", {}

        # R3-D7: False exact-solution bypasses (parenthetical, nevertheless, `in Lean 4`) -> HONESTY_VIOLATION
        for idx_r4e, bad_ex in enumerate(
            (
                "We (unlike others who did not succeed) proved Theta(C_7) = 3.258805369885.",
                "We did not prove the upper bound, nevertheless we proved Theta(C_7) = 3.258805369885.",
                "We proved in Lean 4 that Theta(C_7) = 3.258805369885.",
            )
        ):
            fp_r4e = tmp / f"RESULTS_r4_exact_{idx_r4e}.md"
            fp_r4e.write_text(min_base + "\n" + bad_ex + "\n", encoding="utf-8")
            ok_re, c_re, _ = verify_results_md(fp_r4e, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_re or c_re != "HONESTY_VIOLATION":
                return False, "MATH_MISMATCH", f"Iter 4 exact-claim case {idx_r4e} missed: {bad_ex!r}", {}

        # R3-D5 (10 honest textbook compound-RHS & giant-frac upper bounds in UPPER_RESEARCH_REPORT.md -> PASS)
        r4_honest_upper = (
            r"By trivial vertex count, $\alpha(C_7^4) \le 7^4 = 2401$.",
            r"By trivial vertex count, $\alpha(C_7^5) \le 7^5 = 16807$.",
            r"By trivial vertex count, $\alpha(C_7^4) \le 2,401$.",
            r"By trivial vertex count, $\alpha(C_7^5) \le 16,807$.",
            r"By Lovász submultiplicativity, $\alpha(C_7^4) \le 3.317667^4 < 121.2$.",
            r"By Lovász submultiplicativity, $\alpha(C_7^5) \le 3.317667^5 < 402.1$.",
            r"By slice double-counting, $\alpha(C_7^4) \le 7/2 \cdot 33 = 115.5$.",
            r"By slice double-counting, $\alpha(C_7^5) \le 3.5 \times 115 = 402.5$.",
            r"Our LP relaxation yields $\alpha(C_7^4) < 108.5$.",
            "Our LP relaxation yields alpha(C_7^4) < 108." + ("0" * 100005) + "1.",
        )
        for idx_r4uh, ok_ul in enumerate(r4_honest_upper):
            fp_r4uh = tmp / f"UPPER_r4_honest_{idx_r4uh}.md"
            fp_r4uh.write_text(up_base + "\n" + ok_ul + "\n", encoding="utf-8")
            ok_ruh, c_ruh, i_ruh = verify_research_report(fp_r4uh, kind="upper")
            if not ok_ruh:
                return False, c_ruh, f"Iter 4 honest UPPER textbook bound {idx_r4uh} wrongly rejected ({ok_ul[:80]!r}): {i_ruh}", {}

        # R3-D5 decimal impossible + R3-D7 intro-comma `Although,` + R3-N02 `and proved` -> REPORT_MISMATCH
        for idx_r4ub, bad_ul in enumerate(
            (
                r"We prove $\alpha(C_7^4) \le 107.9$.",
                r"We prove $\alpha(C_7^4) < 108.0$.",
                "Although, as noted above, alpha(C_7^4) <= 112 was not proved, alpha(C_7^4) <= 107 holds.",
                "We ruled out alpha(C_7^4) <= 106, and proved alpha(C_7^4) <= 107.",
            )
        ):
            fp_r4ub = tmp / f"UPPER_r4_bad_{idx_r4ub}.md"
            fp_r4ub.write_text(up_base + "\n" + bad_ul + "\n", encoding="utf-8")
            ok_rub, c_rub, _ = verify_research_report(fp_r4ub, kind="upper")
            if ok_rub or c_rub != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 4 impossible UPPER claim {idx_r4ub} missed: {bad_ul!r}", {}

        # R3-D8 & R2 Polish 3: O(N) clause-splitting stress guards (was 7.16s / 1.8s quadratic -> < 90ms CPU linear)
        t0_d8 = time.process_time()
        _find_inflated_lower_claims(", we " * 5000, FLOOR_LOWER, "3.258805369885")
        _find_inflated_lower_claims("(" * 100 + ", we " * 3000 + ")" * 100, FLOOR_LOWER, "3.258805369885")
        dt_d8 = time.process_time() - t0_d8
        if dt_d8 >= 0.5:
            return False, "MATH_MISMATCH", f"R3-D8 O(N^2) regression in _find_inflated_lower_claims ({dt_d8:.3f}s CPU on 25KB)", {}

        t0_p3 = time.process_time()
        _find_impossible_upper_claim("alpha(C_7^4) <= 115; " * 500)
        _find_impossible_upper_claim("We ruled out alpha(C_7^4) <= 107; " * 500)
        dt_p3 = time.process_time() - t0_p3
        if dt_p3 >= 0.35:
            return False, "MATH_MISMATCH", f"R2 Polish 3 quadratic single-line regression ({dt_p3:.3f}s CPU)", {}

        # Iteration 5 report-analyzer regression locks (R4-D4..D6, R4-C2-D01..D05, R4-R1-N1, R4-C2-N02)
        # R4-D4 & R4-C2-D03: LaTeX thin-space thousands & additive/implicit-mul textbook UPPER bounds -> PASS
        r5_honest_upper = (
            r"Trivial count: $\alpha(C_7^4) \le 2\,401$.",
            r"Trivial count: $\alpha(C_7^5) \le 16\,807$.",
            r"Linear code decomposition: $\alpha(C_7^5) \le 343 + 58 = 401$.",
            r"Slice sum: $\alpha(C_7^4) \le 33 + 33 + 33 + 16 = 115$.",
            r"Slice product: $\alpha(C_7^4) \le 33 \ast 3.5$.",
            r"Slice double-counting: $\alpha(C_7^4) \le 7 \lfloor 33/2 \rfloor = 112$.",
            r"Partition bound: $\alpha(C_7^4) \le 3(38) = 114$.",
            r"Combinatorial bound: $\alpha(C_7^4) \le 7 \binom{6}{2} + 10 = 115$.",
        )
        for idx_r5uh, ok_u5 in enumerate(r5_honest_upper):
            fp_r5uh = tmp / f"UPPER_r5_honest_{idx_r5uh}.md"
            fp_r5uh.write_text(up_base + "\n" + ok_u5 + "\n", encoding="utf-8")
            ok_u5r, c_u5r, i_u5r = verify_research_report(fp_r5uh, kind="upper")
            if not ok_u5r:
                return False, c_u5r, f"Iter 5 honest UPPER case {idx_r5uh} wrongly rejected ({ok_u5!r}): {i_u5r}", {}

        # R4-D4 negative prose-paren & non-thousands thin-space guard + R4-D6 mid-subordinate comma -> FAIL REPORT_MISMATCH
        for idx_r5ub, bad_u5 in enumerate(
            (
                r"We prove $\alpha(C_7^4)\,\le\,107$.",
                r"We prove $\alpha(C_7^4) \le 107$ (new proof).",
                "Although we have, as noted above, not proved alpha(C_7^4) <= 112, alpha(C_7^4) <= 107 holds.",
            )
        ):
            fp_r5ub = tmp / f"UPPER_r5_bad_{idx_r5ub}.md"
            fp_r5ub.write_text(up_base + "\n" + bad_u5 + "\n", encoding="utf-8")
            ok_u5b, c_u5b, _ = verify_research_report(fp_r5ub, kind="upper")
            if ok_u5b or c_u5b != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 5 impossible UPPER case {idx_r5ub} missed: {bad_u5!r}", {}

        # R4-C2-D01, R4-C2-D02, R4-D5: Honest M4 Status table (LOWER_RESEARCH_REPORT.md) -> PASS
        fp_r5l = tmp / "LOWER_r5_status_table.md"
        fp_r5l.write_text(
            low_base
            + "\n| Track | $d$ | Lower Bound | Status |\n"
            "|---|---:|---|---|\n"
            "| Track L1 | 500 | 3.258835400000 | Unformalized C++17 candidate |\n"
            "| Track L2 | 1000 | 3.258838900000 | Not yet formalized in Lean 4 |\n"
            "| Track L3 | 500 | 3.258835000000 | Not yet formalized in our Lean 4 build |\n"
            "| Certified frontier | 200 | 3.258805369885 | Verified in pure Lean 4 kernel |\n",
            encoding="utf-8",
        )
        ok_r5l, c_r5l, i_r5l = verify_research_report(
            fp_r5l, kind="lower", lower_num=info_b["c7_lower_num"], lower_den=info_b["c7_lower_den"]
        )
        if not ok_r5l:
            return False, c_r5l, f"Iter 5 honest M4 Status table wrongly rejected: {i_r5l}", {}

        # R4-C2-D01, R4-C2-D02, R4-D5, R4-C2-D05, R4-R1-N1: Honest M6 tables & prose controls -> PASS
        r5_honest_results = (
            "| Method | Notes | Lower Bound |\n|---|---|---|\n"
            "| External d=500 | BPZ Aug 2026 (native_decide) | 3.258827985920007 |\n"
            "| C++17 search (d=500) | Tandon Aug 2026 (unrefereed) | 3.258832620353 |\n"
            "| Our pure-kernel Lean 4 | Below BPZ, beats floor | 3.258805369885 |",
            "| Campaign | d | Lower Bound | Status |\n| --- | --- | --- | --- |\n"
            "| Track L2 (d=500) | 500 | 3.258832620353 | Uncertified (not yet formalized in Lean) |",
            "| Feature | Metric | Value | Notes |\n|---|---|---|---|\n"
            "| F3 | Lovász upper bound | 3.317667 | Strictly above lower bound |",
            "Tandon reaches 3.258832620353.",
            "Tandon stands at 3.258832620353.",
            "BPZ proves 3.258827985920007 via native_decide.",
            r"Our formalization proves $\Theta(C_7) = \lim_{d\to\infty} \alpha(C_7^{\boxtimes d})^{1/d}$.",
            "Lovász upper bound is 3.317667.",
        )
        for idx_r5hr, ok_r5 in enumerate(r5_honest_results):
            fp_r5hr = tmp / f"RESULTS_r5_honest_{idx_r5hr}.md"
            fp_r5hr.write_text(min_base + "\n" + ok_r5 + "\n", encoding="utf-8")
            ok_5h, c_5h, i_5h = verify_results_md(fp_r5hr, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if not ok_5h:
                return False, c_5h, f"Iter 5 honest RESULTS.md case {idx_r5hr} wrongly rejected: {i_5h}", {}

        # R4-C2-D02, R4-D5, R4-D6, R4-C2-D05, R4-C2-N02 + proactive table/post-paren locks -> FAIL REPORT_MISMATCH
        r5_inflated_results = (
            "| Method | d | Certified Lower Bound | Details |\n| --- | --- | --- | --- |\n| Lean 4 formalization | 500 | 3.258899999999 | New record vs Tandon |",
            "| Method | Our Certified Bound | Notes |\n| --- | --- | --- |\n| Pure-kernel Lean 4 | 3.258899999999 | Below Lovász ceiling |",
            "| Method | Our Certified Bound | Notes |\n| --- | --- | --- |\n| Pure-kernel Lean 4 | 3.258899999999 | Tandon surpassed! |",
            "| Method | Certified Value | Notes |\n| --- | --- | --- |\n| Our pure-kernel Lean 4 | 3.258899999999 | Below Lovász upper bound |",
            "| Method | Our Lean 4 Bound | Gap |\n| --- | --- | --- |\n| Pure-kernel | 3.258899999999 | 0.058 below Lovász |",
            "| Ref | Result |\n| --- | --- |\n| Campaign | Our Lean 4 bound: 3.258899999999 (above Tandon) |",
            "| Ref | Result |\n| --- | --- |\n| Campaign | Our Lean 4 bound: 3.258899999999 (new record vs Tandon) |",
            "| Metric | Value |\n|---|---|\n| Our Lean 4 bound (below Lovász) | 3.258899999999 |",
            "Our pure-kernel Lean 4 lower bound is 3.258899999999 (below Lovász).",
            "Our pure-kernel Lean 4 lower bound is 3.258899999999 (above Tandon).",
            "Our pure-kernel Lean 4 lower bound is 3.258899999999 (new world record, ahead of Tandon).",
            "Our pure-kernel Lean 4 bound (which did not use native_decide, unlike BPZ) is 3.258899999999.",
            "Our pure-kernel Lean 4 bound (unlike Tandon's) equals 3.258899999999.",
            "Our pure-kernel Lean 4 bound (compared to BPZ) reaches 3.258899999999.",
            "Under the Lovász ceiling, Lean 4 proved 3.258899999999.",
            "Under the Lovász ceiling, the certified Lean 4 bound reached 3.258899999999.",
            "Beneath the Lovász ceiling, the verified Lean 4 bound is 3.258899999999.",
            "Our Lean 4 bound under the Lovász ceiling is 3.258899999999.",
            "Our certified Lean 4 lower bound stays strictly below Lovász: 3.258899999999.",
            "Our Lean 4 lower bound stays below Tandon at 3.258899999999.",
            "Our Lean 4 lower bound stays below Tandon, reaching 3.258899999999.",
            r"Our Lean 4 verified lower bound is $\frac{3258899999999}{(10^{12})}$.",
        )
        for idx_r5i, bad_r5i in enumerate(r5_inflated_results):
            fp_r5i = tmp / f"RESULTS_r5_inf_{idx_r5i}.md"
            fp_r5i.write_text(min_base + "\n" + bad_r5i + "\n", encoding="utf-8")
            ok_5i, c_5i, _ = verify_results_md(fp_r5i, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_5i or c_5i != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 5 inflated RESULTS.md case {idx_r5i} missed: {bad_r5i!r}", {}

        # R4-D6, R4-R1-N1, R4-C2-N02: False exact-solution prose bypasses -> FAIL HONESTY_VIOLATION
        for idx_r5e, bad_r5e in enumerate(
            (
                "We — unlike others who did not succeed — proved Theta(C_7) = 3.258805369885.",
                "We [unlike others who did not succeed] proved Theta(C_7) = 3.258805369885.",
                "Our formalization proves Theta(C_7) = 3.258805369885.",
                "We proved via Lean 4 that Theta(C_7) = 3.258805369885.",
                "We proved using Lean 4 that Theta(C_7) = 3.258805369885.",
            )
        ):
            fp_r5e = tmp / f"RESULTS_r5_exact_{idx_r5e}.md"
            fp_r5e.write_text(min_base + "\n" + bad_r5e + "\n", encoding="utf-8")
            ok_5e, c_5e, _ = verify_results_md(fp_r5e, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_5e or c_5e != "HONESTY_VIOLATION":
                return False, "MATH_MISMATCH", f"Iter 5 exact-claim case {idx_r5e} missed: {bad_r5e!r}", {}

        # R4-C2-D04: O(N) NBSP & horizontal-whitespace ReDoS guard in _CLAUSE_CUT_RE, _WS_RUN_RE & _UPPER_FINITE_BOUND_RE
        nbsp_fp = tmp / "RESULTS_r5_nbsp.md"
        nbsp_fp.write_text(
            min_base + "\nOur Lean 4 bound is 3.258899999999" + ("\xa0" * 500) + "x\n",
            encoding="utf-8",
        )
        t0_nb = time.process_time()
        ok_nb, c_nb, _ = verify_results_md(nbsp_fp, info_b["c7_lower_num"], info_b["c7_lower_den"])
        _find_impossible_upper_claim("alpha(C_7^4) <= 107" + (" " * 5000) + "x")
        _find_inflated_lower_claims("Our Lean 4 bound is 3.258899999999" + ("\xa0" * 1500) + "x", FLOOR_LOWER, "3.258805369885")
        dt_nb = time.process_time() - t0_nb
        if ok_nb or c_nb != "REPORT_MISMATCH":
            return False, "MATH_MISMATCH", f"R4-C2-D04 NBSP inflated claim missed ({ok_nb}, {c_nb})", {}
        if dt_nb > 0.5:
            return False, "MATH_MISMATCH", f"R4-C2-D04 O(N^2) whitespace ReDoS regression ({dt_nb:.2f}s CPU)", {}

        # Iteration 6 report-analyzer regression locks (R5-C2-D02..D05, R5-R2-N1, R5-D7..D9, R5-C2-N01)
        # R5-C2-D02 / R5-D7: Honest Unicode/LaTeX & algebraic-paren UPPER textbook bounds -> PASS
        r6_honest_upper = (
            "Slice product: α(C₇⁴) ≤ 7 ⋅ 16 = 112.",
            "Slice product: α(C₇⁴) ≤ 7 ∗ 16 = 112.",
            r"Slice product: $\alpha(C_7^4) \le 33 \dfrac{7}{2} = 115.5$.",
            r"Slice product: $\alpha(C_7^4) \le 33 \tfrac{7}{2} = 115.5$.",
            "By slice double-counting, α(C_7^4) ≤ 7 α(C_7^3) / 2 = 115.5.",
            "By slice double-counting, α(C_7^4) ≤ 3.5 α(C_7^3) = 115.5.",
            r"By slice double-counting, $\alpha(C_7^4) \le 7 \bigl\lfloor 33/2 \bigr\rfloor = 112$.",
            r"A partition bound yields $\alpha(C_7^4) \le 7 (k + 1)$ for $k = 16$.",
        )
        for idx_r6uh, ok_u6 in enumerate(r6_honest_upper):
            fp_r6uh = tmp / f"UPPER_r6_honest_{idx_r6uh}.md"
            fp_r6uh.write_text(up_base + "\n" + ok_u6 + "\n", encoding="utf-8")
            ok_u6r, c_u6r, i_u6r = verify_research_report(fp_r6uh, kind="upper")
            if not ok_u6r:
                return False, c_u6r, f"Iter 6 honest UPPER case {idx_r6uh} wrongly rejected ({ok_u6!r}): {i_u6r}", {}

        # R5-C2-D02 / R5-R2-N1 / R5-D7 / R5-D9: parenthetical/boxed/sized upper bypasses + subordinate-comma bypasses -> FAIL REPORT_MISMATCH
        r6_bad_upper = (
            "Our audit proves alpha(C_7^4) <= 107 (2026).",
            r"Our audit proves $\alpha(C_7^4) \le 107$ (2026 update).",
            r"Our solver proves $\alpha(C_7^4) \le 107$ (2026 preprint).",
            "We proved alpha(C_7^4) <= 100 (1st exact bound).",
            "We proved alpha(C_7^5) <= 360 (5th power).",
            "We proved alpha(C_7^4) <= 107 (100% verified).",
            r"We proved $\alpha(C_7^4) \le 107$ ($\alpha$ tightened).",
            r"We prove $\alpha(C_7^4) \le 107$ ($\vartheta$ improved).",
            "We proved alpha(C_7^4) <= 107(d=4).",
            r"We prove $\alpha(C_7^4) \le 107$(a).",
            r"We prove $\alpha(C_7^5) \le 366$(1).",
            "We proved alpha(C_7^5) <= 366 (3.25^5).",
            r"We prove $\alpha(C_7^4) \le \boxed{107}$.",
            r"We prove $\alpha(C_7^4) \le 107$ (\cite{foo}).",
            r"We proved $\alpha(C_7^4) \le 107\text{ (2026)}$.",
            r"We proved $\alpha(C_7^4) \le 107 \left(2026\right)$.",
            "Although our search remains, strictly speaking, unable to refute alpha(C_7^4) <= 112, alpha(C_7^4) <= 107 holds.",
            "Although we have, as carefully explained in Section 2 of our detailed technical report, not proved alpha(C_7^4) <= 112, alpha(C_7^4) <= 107 holds.",
        )
        for idx_r6ub, bad_u6 in enumerate(r6_bad_upper):
            fp_r6ub = tmp / f"UPPER_r6_bad_{idx_r6ub}.md"
            fp_r6ub.write_text(up_base + "\n" + bad_u6 + "\n", encoding="utf-8")
            ok_u6b, c_u6b, _ = verify_research_report(fp_r6ub, kind="upper")
            if ok_u6b or c_u6b != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 6 impossible UPPER case {idx_r6ub} missed: {bad_u6!r}", {}

        # R5-C2-D03 / R5-D8: Honest M4 unformalized rows & prose in LOWER_RESEARCH_REPORT.md -> PASS
        fp_r6l_tbl = tmp / "LOWER_r6_honest_m4.md"
        fp_r6l_tbl.write_text(
            low_base
            + "\n| Track | d | Lower Bound | Status |\n"
            "|---|---:|---|---|\n"
            "| Our Track L1 campaign | 500 | 3.258835400000 | Unformalized C++17 candidate |\n"
            "| Our Track L1 frontier search | 500 | 3.258835400000 | Unformalized C++17 candidate |\n"
            "| This work (C++17 search) | 500 | 3.258835400000 | Not yet formalized in Lean 4 |\n"
            "| Our campaign (Track L2) | 1000 | 3.258838900000 | Candidate (pending Lean formalization) |\n"
            "| This work (unformalized C++17) | 500 | 3.258835400000 | C++17 |\n"
            "| Our pure-kernel Lean 4 frontier | 200 | 3.258805369885 | Verified in pure Lean 4 kernel |\n\n"
            "| Description | Lower Bound |\n"
            "|---|---|\n"
            "| Our Rust frontier candidate (unformalized) | 3.258835400000 |\n\n"
            "Our Rust lower bound (not yet formalized in Lean 4) reached 3.258835400000.\n"
            "Our Track L1 result — unformalized C++17 candidate — reached 3.258835400000.\n"
            "Our Track L1 result [unformalized C++17 candidate] reached 3.258835400000.\n",
            encoding="utf-8",
        )
        ok_r6l, c_r6l, i_r6l = verify_research_report(
            fp_r6l_tbl, kind="lower", lower_num=info_b["c7_lower_num"], lower_den=info_b["c7_lower_den"]
        )
        if not ok_r6l:
            return False, c_r6l, f"Iter 6 honest M4 LOWER_RESEARCH_REPORT.md wrongly rejected: {i_r6l}", {}

        # R5-C2-N01: LOWER_RESEARCH_REPORT.md must also catch impossible finite-power upper bounds
        fp_r6l_imp = tmp / "LOWER_r6_imp_upper.md"
        fp_r6l_imp.write_text(low_base + "\nWe proved alpha(C_7^4) <= 107.\n", encoding="utf-8")
        ok_r6li, c_r6li, _ = verify_research_report(
            fp_r6l_imp, kind="lower", lower_num=info_b["c7_lower_num"], lower_den=info_b["c7_lower_den"]
        )
        if ok_r6li or c_r6li != "REPORT_MISMATCH":
            return False, "MATH_MISMATCH", "R5-C2-N01 LOWER_RESEARCH_REPORT.md missed impossible alpha(C_7^4) <= 107", {}

        # R5-C2-D03 / R5-C2-D05: Honest F2 isomorphism equalities & unformalized prose in RESULTS.md -> PASS
        for idx_r6hr, ok_r6h in enumerate(
            (
                r"We prove in Lean 4 that $\Theta(C_7) = \Theta(\text{SimpleGraph.cycleGraph } 7)$.",
                r"We prove in Lean 4 that $\Theta(C_7) = \Theta(\text{circulantGraph } \{1\})$.",
                "Our Rust lower bound (not yet formalized in Lean 4) reached 3.258835400000.",
            )
        ):
            fp_r6hr = tmp / f"RESULTS_r6_honest_{idx_r6hr}.md"
            fp_r6hr.write_text(min_base + "\n" + ok_r6h + "\n", encoding="utf-8")
            ok_6h, c_6h, i_6h = verify_results_md(fp_r6hr, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if not ok_6h:
                return False, c_6h, f"Iter 6 honest RESULTS.md case {idx_r6hr} wrongly rejected ({ok_r6h!r}): {i_6h}", {}

        # R5-C2-D03 / R5-D8 / R5-C2-D04 / R5-D9: Inflated RESULTS.md table & prose bypasses -> FAIL REPORT_MISMATCH
        r6_inflated_results = (
            "| Method | d | Lower Bound | Status |\n|---|---|---|---|\n| Our pure-kernel Lean 4 certified bound | 500 | 3.258899999999 | Unformalized |",
            "| Method | d | Certified Lower Bound | Notes |\n| --- | --- | --- | --- |\n| Lean 4 formalization | 500 | 3.258899999999 | Beats Tandon; prior record was BPZ |",
            "| Method | d | Certified Lower Bound | Notes |\n| --- | --- | --- | --- |\n| Lean 4 formalization | 500 | 3.258899999999 | Tops Tandon |",
            "| Method | d | Certified Lower Bound | Notes |\n| --- | --- | --- | --- |\n| Lean 4 formalization | 500 | 3.258899999999 | Breaks Tandon's record |",
            "| Method | d | Certified Lower Bound | Notes |\n| --- | --- | --- | --- |\n| Lean 4 formalization | 500 | 3.258899999999 | +0.000067 over Tandon |",
            "| Method | Certified Lower Bound (not native_decide) |\n| --- | --- |\n| Lean 4 | 3.258899999999 |",
            "| Method | Lovász Upper Bound |\n|---|---|\n| Our pure-kernel Lean 4 lower bound | 3.258899999999 |",
            "| Method | Lower Bound | Notes |\n|---|---|---|\n| Lean 4 certified | 3.258899999999 | BPZ & Tandon surpassed |",
            "Our certified Lean 4 bound achieved 3.258899999999 (unformalized).",
            "Our pure-kernel Lean 4 lower bound is 3.258899999999 (Tandon (Aug 2026) beaten).",
            "Our pure-kernel Lean 4 lower bound is 3.258899999999 (BPZ & Tandon beaten).",
            "Our pure-kernel Lean 4 lower bound is 3.258899999999 (Tandon's Aug 2026 record is beaten).",
            "Our pure-kernel Lean 4 lower bound is 3.258899999999 (prior record broken).",
            "Our pure-kernel Lean 4 lower bound replaces native_decide and reaches 3.258899999999.",
            "Our pure-kernel Lean 4 bound sets a new world record over Tandon at 3.258899999999.",
            "Our pure-kernel Lean 4 lower bound breaks Tandon's record at 3.258899999999.",
            "Our pure-kernel Lean 4 bound is higher than Tandon's 2026 record of 3.258899999999.",
            "Our pure-kernel Lean 4 lower bound is 3.258899999999 (+0.000067 over Tandon).",
            "Our pure-kernel Lean 4 lower bound is 3.258899999999 (not native_decide).",
            "Our pure-kernel Lean 4 lower bound, which is not a preprint, reaches 3.258899999999.",
            "Our pure-kernel Lean 4 lower bound stays strictly below Lovász, yielding 3.258899999999.",
            "Our pure-kernel Lean 4 lower bound stays strictly below Tandon, yielding 3.258899999999.",
            "Our pure-kernel Lean 4 lower bound falls short of Tandon and produces 3.258899999999.",
            "Our pure-kernel Lean 4 lower bound stands at 3.317667207394.",
            "We prove a lower bound for Theta(C_7) of 3.317667207394.",
        )
        for idx_r6i, bad_r6i in enumerate(r6_inflated_results):
            fp_r6i = tmp / f"RESULTS_r6_inf_{idx_r6i}.md"
            fp_r6i.write_text(min_base + "\n" + bad_r6i + "\n", encoding="utf-8")
            ok_6i, c_6i, _ = verify_results_md(fp_r6i, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_6i or c_6i != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 6 inflated RESULTS.md case {idx_r6i} missed: {bad_r6i!r}", {}

        # R5-D9 / R5-C2-D05: ASCII `-- ... --`, multi-modifier/kernel/verb & lowercase vartheta exact claims -> FAIL HONESTY_VIOLATION
        for idx_r6e, bad_r6e in enumerate(
            (
                "We -- unlike others who did not succeed -- proved Theta(C_7) = 3.258805369885.",
                "We proved formally in Lean 4 that Theta(C_7) = 3.258805369885.",
                "We proved in pure Lean 4 kernel that Theta(C_7) = 3.258805369885.",
                "We certified in Lean 4 that Theta(C_7) = 3.258805369885.",
                r"We prove in Lean 4 that $\Theta(C_7) = \vartheta(C_7)$.",
            )
        ):
            fp_r6e = tmp / f"RESULTS_r6_exact_{idx_r6e}.md"
            fp_r6e.write_text(min_base + "\n" + bad_r6e + "\n", encoding="utf-8")
            ok_6e, c_6e, _ = verify_results_md(fp_r6e, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_6e or c_6e != "HONESTY_VIOLATION":
                return False, "MATH_MISMATCH", f"Iter 6 exact-claim case {idx_r6e} missed: {bad_r6e!r}", {}

        # Iteration 7 report-analyzer regression locks (R6-C2-D01..D05, R6-D6, R6-R2-D4, R6-C2-N02..N03, R1 Obs)
        # R6-C2-D01: O(N) CPU lock on _find_inflated_lower_claims paren burst (< 0.25s combined)
        fp_r7_dos1 = tmp / "RESULTS_r7_dos_frac.md"
        fp_r7_dos2 = tmp / "RESULTS_r7_dos_dec.md"
        fp_r7_dos3 = tmp / "RESULTS_r7_dos_hello.md"
        fp_r7_dos1.write_text(min_base + "\nOur bound: " + "(325889/100000)" * 533 + "\n", encoding="utf-8")
        fp_r7_dos2.write_text(min_base + "\nOur bound: " + "(3.258899999999)" * 235 + "\n", encoding="utf-8")
        fp_r7_dos3.write_text(
            min_base + "\nOur bound: (" + ("hello " * 600) + ")" + "(325889/100000)" * 100 + "\n",
            encoding="utf-8",
        )
        t0_r7_dos = time.process_time()
        for dos_lbl, dos_fp in (("frac533", fp_r7_dos1), ("dec235", fp_r7_dos2), ("hello600", fp_r7_dos3)):
            ok_d, c_d, _ = verify_results_md(dos_fp, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_d or c_d != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"R6-C2-D01 inflated burst `{dos_lbl}` not caught: ({ok_d}, {c_d})", {}
        dt_r7_dos = time.process_time() - t0_r7_dos
        if dt_r7_dos >= 0.25:
            return False, "MATH_MISMATCH", f"R6-C2-D01 _find_inflated_lower_claims CPU regression ({dt_r7_dos:.3f}s >= 0.25s)", {}

        # R6-C2-D02 / R6-D6 #1-2 / R6-R2-D4 / R6-C2-D03 / R6-C2-D05 / R6-C2-N03:
        # Contradictory Lean-cert+unformalized, new brag verbs, explicit self-bound `(Tandon)`, & mixed brackets -> FAIL REPORT_MISMATCH
        r7_inflated_results = (
            "| Method | Lower Bound |\n|---|---|\n| Our pure-kernel Lean 4 | 3.258899999999 (unformalized) |",
            "| Track | d | Certified Lower Bound | Status |\n|---|---|---|---|\n| Our Track L1 | 500 | 3.258899999999 | Unformalized |",
            "| Track | d | Verified Lower Bound | Status |\n|---|---|---|---|\n| Our Track L1 | 500 | 3.258899999999 | Unformalized |",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Lean 4 certified | 3.258899999999 | Unformalized |",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Verified in Lean 4 | 3.258899999999 | Unformalized |",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Certified in Lean 4 | 3.258899999999 | Unformalized |",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Formalized in Lean 4 | 3.258899999999 | Unformalized |",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Proven in Lean 4 | 3.258899999999 | Unformalized |",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Lean 4 proof | 3.258899999999 | Unformalized |",
            "| Method | Lean 4 Certified Lower Bound | Status |\n|---|---|---|\n| Track L1 | 3.258899999999 | Unformalized |",
            "| Track | Lower Bound | Status |\n|---|---|---|\n| Track L1 | 3.258899999999 | Unformalized; our certified Lean 4 bound |",
            "Verified in Lean 4: 3.258899999999 (unformalized).",
            "The bound 3.258899999999 (unformalized) is certified by our pure-kernel Lean 4 formalization.",
            "The bound (unformalized) 3.258899999999 is certified by our pure-kernel Lean 4 formalization.",
            "Our certified Lean 4 bound is an unrefereed candidate at 3.258899999999.",
            "Our certified Lean 4 bound is an unformalized bound of 3.258899999999.",
            "Our pure-kernel Lean 4 lower bound is 3.258899999999, an unformalized candidate.",
            "Our Track L1 reached 3.258899999999, beating Tandon (unformalized).",
            "Our Track L1 (unformalized; our certified Lean 4 bound) reached 3.258899999999.",
            "Our pure-kernel Lean 4 lower bound moved past Tandon's record to 3.258899999999.",
            "Our pure-kernel Lean 4 lower bound pushed beyond Tandon's record to 3.258899999999.",
            "Our pure-kernel Lean 4 lower bound is beyond Tandon's record at 3.258899999999.",
            "Our pure-kernel Lean 4 lower bound outstrips Tandon's record at 3.258899999999.",
            "Our pure-kernel Lean 4 lower bound shatters Tandon's record at 3.258899999999.",
            "Our pure-kernel Lean 4 lower bound overtakes Tandon's record at 3.258899999999.",
            "Our pure-kernel Lean 4 lower bound is 3.258899999999 (Tandon's record overtaken).",
            "Our pure-kernel Lean 4 lower bound is 3.258899999999 (Tandon).",
            "Our certified Lean 4 lower bound equals 3.258899999999 (Tandon's record).",
            "Our pure-kernel Lean 4 lower bound is 3.258899999999 (Tandon [Aug 2026) beaten].",
        )
        for idx_r7i, bad_r7i in enumerate(r7_inflated_results):
            fp_r7i = tmp / f"RESULTS_r7_inf_{idx_r7i}.md"
            fp_r7i.write_text(min_base + "\n" + bad_r7i + "\n", encoding="utf-8")
            ok_7i, c_7i, _ = verify_results_md(fp_r7i, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_7i or c_7i != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 7 inflated RESULTS.md case {idx_r7i} missed: {bad_r7i!r}", {}

        # Cleanly separated M4/M6 controls (Option A-Report: separated external/unformalized sentences & rows -> PASS)
        r7_honest_lower_lines = (
            "Our campaign is hoping to push above Tandon's 3.258832620353.",
            "Our campaign is trying to push above Tandon's 3.258832620353.",
            "Our Track L1 campaign reached 3.258835400000, an unformalized C++17 candidate.",
            "Our Track L1 campaign (C++17 search) reached 3.258835400000, which is not yet formalized in Lean 4.",
            "It remains below the external Aug 10, 2026 native_decide benchmark of BPZ (3.258827985920007).",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| BPZ (Aug 2026) | 3.258827985920007 | External literature benchmark (native_decide) |",
        )
        for idx_r7h, ok_r7h in enumerate(r7_honest_lower_lines):
            fp_r7h = tmp / f"RESULTS_r7_honest_{idx_r7h}.md"
            fp_r7h.write_text(min_base + "\n" + ok_r7h + "\n", encoding="utf-8")
            ok_7h, c_7h, i_7h = verify_results_md(fp_r7h, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if not ok_7h:
                return False, c_7h, f"Iter 7 honest RESULTS.md case {idx_r7h} wrongly rejected ({ok_r7h!r}): {i_7h}", {}
        fp_r7_low_all = tmp / "LOWER_r7_honest_all.md"
        fp_r7_low_all.write_text(low_base + "\n" + "\n".join(r7_honest_lower_lines) + "\n", encoding="utf-8")
        ok_7la, c_7la, i_7la = verify_research_report(
            fp_r7_low_all, kind="lower", lower_num=info_b["c7_lower_num"], lower_den=info_b["c7_lower_den"]
        )
        if not ok_7la:
            return False, c_7la, f"Iter 7 honest LOWER_RESEARCH_REPORT.md controls wrongly rejected: {i_7la}", {}

        # R6-C2-D04 / R6-D6 #3 / R1 Obs: _scan_upper_rhs_impossible paren bypass locks -> FAIL REPORT_MISMATCH
        r7_bad_upper = (
            r"We proved $\alpha(C_7^4) \le 107$ ($\alpha(C_7^4) < 112$).",
            r"We proved $\alpha(C_7^4) \le 107$ ($\alpha(C_7^4)$).",
            "We proved alpha(C_7^4) <= 107 (-1).",
            "We proved alpha(C_7^5) <= 366 (-1).",
            "We proved alpha(C_7^4) <= 107 (-5).",
            "We proved alpha(C_7^4) <= 107 (+0).",
            r"We proved $\alpha(C_7^4) \le 107 \left(-1\right)$.",
            "We proved alpha(C_7^4) <= 107 (108 - 1).",
            "We proved alpha(C_7^5) <= 366 (367 - 1).",
            "We prove alpha(C_7^4) <= 107 (1 - 0.5).",
            "We prove alpha(C_7^4) <= 107(1 - 0.5).",
            r"We proved $\alpha(C_7^4) \le 107$ ($\frac{1}{1}$).",
            r"We proved $\alpha(C_7^4) \le 107(\frac{1}{1})$.",
            "We proved alpha(C_7^4) <= 107(10 - 9).",
            r"We proved $\alpha(C_7^4) \le 107(\sqrt{1})$.",
            r"We proved $\alpha(C_7^4) \le 107(\binom{1}{1})$.",
            r"We proved $\alpha(C_7^4) \le 107(2^{-1})$.",
            r"We proved $\alpha(C_7^4) \le 107$ ($\lfloor 107.9 \rfloor$).",
        )
        for idx_r7ub, bad_u7 in enumerate(r7_bad_upper):
            fp_r7ub = tmp / f"UPPER_r7_bad_{idx_r7ub}.md"
            fp_r7ub.write_text(up_base + "\n" + bad_u7 + "\n", encoding="utf-8")
            ok_7ub, c_7ub, _ = verify_research_report(fp_r7ub, kind="upper")
            if ok_7ub or c_7ub != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 7 impossible UPPER case {idx_r7ub} missed: {bad_u7!r}", {}

        # Prefix-negated & honest standard symbolic multiplication controls -> PASS (post-negation moved to Option A-Report reject suite)
        r7_honest_upper = (
            "It is impossible that alpha(C_7^4) <= 107 since 108 <= alpha(C_7^4).",
            "It cannot hold that alpha(C_7^5) <= 366.",
            r"Partition bound: $\alpha(C_7^4) \le 3(38) = 114$.",
            r"Partition bound: $\alpha(C_7^4) \le 7(16) = 112$.",
            "Slice bound: alpha(C_7^4) <= 33 (7/2) = 115.5.",
            r"Slice bound: $\alpha(C_7^4) \le 33 \left(\frac{7}{2}\right) = 115.5$.",
            r"Partition bound: $\alpha(C_7^4) \le 7(k+1)$ for $k = 16$.",
            r"Slice bound: $\alpha(C_7^4) \le 3.5(\alpha(C_7^3)) = 115.5$.",
            "Partition bound: alpha(C_7^4) <= 10(11) + 2 = 112.",
        )
        for idx_r7uh, ok_u7 in enumerate(r7_honest_upper):
            fp_r7uh = tmp / f"UPPER_r7_honest_{idx_r7uh}.md"
            fp_r7uh.write_text(up_base + "\n" + ok_u7 + "\n", encoding="utf-8")
            ok_7uh, c_7uh, i_7uh = verify_research_report(fp_r7uh, kind="upper")
            if not ok_7uh:
                return False, c_7uh, f"Iter 7 honest UPPER case {idx_r7uh} wrongly rejected ({ok_u7!r}): {i_7uh}", {}

        # R6-C2-N02: `show`/`demonstrate` & 3-modifier exact claims -> FAIL HONESTY_VIOLATION (+ honest F2 controls -> PASS)
        for idx_r7e, bad_r7e in enumerate(
            (
                "We show in Lean 4 that Theta(C_7) = 3.258805369885.",
                "We demonstrate in Lean 4 that Theta(C_7) = 3.258805369885.",
                "We proved formally here in Lean 4 that Theta(C_7) = 3.258805369885.",
            )
        ):
            fp_r7e = tmp / f"RESULTS_r7_exact_{idx_r7e}.md"
            fp_r7e.write_text(min_base + "\n" + bad_r7e + "\n", encoding="utf-8")
            ok_7e, c_7e, _ = verify_results_md(fp_r7e, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_7e or c_7e != "HONESTY_VIOLATION":
                return False, "MATH_MISMATCH", f"Iter 7 exact-claim case {idx_r7e} missed: {bad_r7e!r}", {}
        for idx_r7ec, ok_r7ec in enumerate(
            (
                r"We show in Lean 4 that $\Theta(C_7) = \lim_{d\to\infty} \alpha(C_7^d)^{1/d}$.",
                r"We demonstrate in Lean 4 that $\Theta(C_7) = \Theta(\mathrm{cycleGraph}\;7)$.",
            )
        ):
            fp_r7ec = tmp / f"RESULTS_r7_exact_ok_{idx_r7ec}.md"
            fp_r7ec.write_text(min_base + "\n" + ok_r7ec + "\n", encoding="utf-8")
            ok_7ec, c_7ec, i_7ec = verify_results_md(fp_r7ec, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if not ok_7ec:
                return False, c_7ec, f"Iter 7 honest F2 exact control {idx_r7ec} wrongly rejected: {i_7ec}", {}

        # --- Iteration 8 Report Analyzer Locks (R7-D7, R7-D8a/b, R7-C2-D01..D04, R7-C2-N02) ---
        # 1. R7-D7: Table-pipe `|` negation clamp across RESULTS & UPPER (exact claims + impossible upper)
        for idx_p, (r8_body, r8_exp_code, r8_kind) in enumerate(
            (
                ("| Status | Claim |\n|---|---|\n| Not open anymore | We proved Theta(C_7) = 3.258805369885 |\n", "HONESTY_VIOLATION", "results"),
                ("| Power | Status | Bound |\n|---|---|---|\n| C_7^4 | Not a conjecture (proven) | alpha(C_7^4) <= 107 |\n", "REPORT_MISMATCH", "results"),
                ("| Status | Claim |\n|---|---|\n| Not open anymore | We proved Theta(C_7) = 3.26 |\n", "HONESTY_VIOLATION", "upper"),
                ("| Power | Status | Bound |\n|---|---|---|\n| C_7^4 | Not a conjecture (proven) | alpha(C_7^4) <= 107 |\n", "REPORT_MISMATCH", "upper"),
            )
        ):
            fp_p = tmp / f"R8_pipe_{idx_p}.md"
            if r8_kind == "results":
                fp_p.write_text(min_base + "\n" + r8_body, encoding="utf-8")
                ok_p, c_p, _ = verify_results_md(fp_p, info_b["c7_lower_num"], info_b["c7_lower_den"])
            else:
                fp_p.write_text(up_base + "\n" + r8_body, encoding="utf-8")
                ok_p, c_p, _ = verify_research_report(fp_p, "upper")
            if ok_p or c_p != r8_exp_code:
                return False, "MATH_MISMATCH", f"R7-D7 table-pipe leak {idx_p} missed ({r8_exp_code}, got {(ok_p, c_p)})", {}

        # 2. R7-C2-D01 + R7-D8b + R7-C2-D04 (#8): _eval_simple_paren_arith sign/undefined/pure-const + \binom = 100 + for k = 1 + impossible to beat
        r8_bad_upper_lines = (
            "We proved alpha(C_7^4) <= 107((-1)^(-14)).",
            "We proved alpha(C_7^4) <= 107((-1)^13 + 2).",
            "We proved alpha(C_7^4) <= 107((-1)¹³ + 2).",
            "We proved alpha(C_7^4) <= 107((-1)^(-15) + 1).",
            "We proved alpha(C_7^4) <= 107((-2)^13).",
            "We proved alpha(C_7^4) <= 107((-2)¹³).",
            "We proved alpha(C_7^4) <= 107((-0.5)^(-13)).",
            "We proved alpha(C_7^4) <= 107((-0.99)^(-13)).",
            "We proved alpha(C_7^4) <= 107(1/0 + 2).",
            r"We proved $\alpha(C_7^4) \le 107(\frac{1}{0} + 2)$.",
            "We proved alpha(C_7^4) <= 107(0^(-1) + 2).",
            r"We proved $\alpha(C_7^4) \le 107(\sqrt{-4} + 2)$.",
            "We proved alpha(C_7^4) <= 107(0.5^(1/3)).",
            "We proved alpha(C_7^4) <= 107(0.5^(2/3)).",
            "We proved alpha(C_7^4) <= 107(0.1^(1/4)).",
            r"We proved $\alpha(C_7^4) \le 107(0.5^{\frac{1}{3}})$.",
            "We proved alpha(C_7^4) <= 107 (0.5^(1/3)) = x.",
            r"We proved $\alpha(C_7^4) \le 107(\binom{1000000}{0})$.",
            "We proved alpha(C_7^4) <= 107((1/2)^10000000).",
            "We proved alpha(C_7^4) <= 107(1^10000000 + 0).",
            r"We proved $\alpha(C_7^4) \le 107(\frac12)$.",
            r"We proved $\alpha(C_7^4) \le 107(\sqrt[3]{0.5})$.",
            "We proved alpha(C_7^4) <= 107((((((((((0.5+0.1)))))))))).",
            "We proved alpha(C_7^4) <= 107({{{{{{{{{0.5+0.1}}}}}}}}}).",
            "We proved alpha(C_7^4) <= 107(1/1,).",
            "We proved alpha(C_7^4) <= 107(1 - ).",
            r"We proved $\alpha(C_7^4) \le 107(\cos(0) - 0.5)$.",
            r"We proved $\alpha(C_7^4) \le 107(1/1 \pm 0)$.",
            "We proved alpha(C_7^4) <= 107 (k - 1) for k = 1.",
            r"We proved $\alpha(C_7^4) \le 107(\cos(0)+0)$.",
            r"We proved $\alpha(C_7^4) \le 107(\pi-\pi)$.",
            r"We have $\alpha(C_7^4) \le 10 \binom{5}{2} = 100$.",
            "We proved alpha(C_7^4) <= 107 is impossible to beat.",
        )
        for idx_u8, bad_u8 in enumerate(r8_bad_upper_lines):
            fp_u8 = tmp / f"UPPER_r8_bad_{idx_u8}.md"
            fp_u8.write_text(up_base + "\n" + bad_u8 + "\n", encoding="utf-8")
            ok_u8, c_u8, _ = verify_research_report(fp_u8, "upper")
            if ok_u8 or c_u8 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 8 upper-bound bypass {idx_u8} missed in UPPER: {bad_u8!r}", {}
            fp_r8u = tmp / f"RESULTS_r8_u_{idx_u8}.md"
            fp_r8u.write_text(min_base + "\n" + bad_u8 + "\n", encoding="utf-8")
            ok_r8u, c_r8u, _ = verify_results_md(fp_r8u, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_r8u or c_r8u != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 8 upper-bound bypass {idx_u8} missed in RESULTS: {bad_u8!r}", {}

        # 3. R7-C2-D02 + R7-D8a + R7-C2-D04 (#1..7): Contradictory table/prose/intervening-paren/equiv/brag lower-bound cheats
        r8_bad_lower_blocks = (
            "| Method | Lower Bound | Notes |\n|---|---|---|\n| Our pure-kernel Lean 4 | 3.258899999999 (unformalized) | BPZ used native_decide at d=500 |\n",
            "| Track | Certified Lower Bound | Notes |\n|---|---|---|\n| Our Track L1 | 3.258899999999 (unformalized) | BPZ used native_decide |\n",
            "| Method | Lower Bound | Reference |\n|---|---|---|\n| Our pure-kernel Lean 4 | 3.258899999999 (unformalized) | Tandon |\n",
            "| Method | Lower Bound | Notes |\n|---|---|---|\n| Our pure-kernel Lean 4 | 3.258899999999 (unformalized) | Prior baseline |\n",
            "| Method | Lower Bound |\n|---|---|\n| Our pure-kernel Lean 4 | 3.258899999999 (Tandon) |\n",
            "| Method | Lower Bound |\n|---|---|\n| Our pure-kernel Lean 4 | 3.258899999999 (BPZ) |\n",
            "| Method | Lower Bound |\n|---|---|\n| Our pure-kernel Lean 4 | 3.258899999999 (unformalized; Tandon) |\n",
            "| Method | Lean 4 Certified Lower Bound |\n|---|---|\n| Our Track L1 | 3.258899999999 (Tandon) |\n",
            "| Method | Lean 4 Certified Lower Bound | Reference |\n|---|---|---|\n| Our Track L1 | 3.258899999999 (unformalized) | Tandon |\n",
            "This work (pure-kernel Lean 4) achieved 3.258899999999 (unformalized).\n",
            "This work (Lean 4) achieved 3.258899999999, an unformalized candidate.\n",
            "This work (pure-kernel Lean 4) achieved 3.258899999999 (Tandon).\n",
            "Our Track L1 (verified in pure-kernel Lean 4) achieved 3.258899999999 (unformalized).\n",
            "Our Track L1 (pure-kernel Lean 4) reached 3.258899999999, an unformalized candidate.\n",
            "Our Track L1 reached 3.258899999999, an unformalized candidate, (verified in Lean 4).\n",
            "Our Track L1 (unformalized) (our pure-kernel Lean 4 proof) reached 3.258899999999.\n",
            "Our Track L1 (unformalized) (beating Tandon's record!) reached 3.258899999999.\n",
            "Our pure-kernel Lean 4 lower bound matches 3.258899999999 (Tandon).\n",
            "Our pure-kernel Lean 4 lower bound ties 3.258899999999 (Tandon).\n",
            "Our pure-kernel Lean 4 lower bound equals Tandon's 3.258899999999.\n",
            "Our pure-kernel Lean 4 lower bound matches Tandon's 3.258899999999.\n",
            "Our pure-kernel Lean 4 theorem gives 3.258899999999 (Tandon).\n",
            "The bound 3.258899999999 (Tandon) is our pure-kernel Lean 4 lower bound.\n",
            "Our pure-kernel Lean 4 lower bound leapfrogs Tandon's record to 3.258899999999.\n",
        )
        for idx_l8, bad_l8 in enumerate(r8_bad_lower_blocks):
            fp_l8 = tmp / f"RESULTS_r8_l_{idx_l8}.md"
            fp_l8.write_text(min_base + "\n" + bad_l8, encoding="utf-8")
            ok_l8, c_l8, _ = verify_results_md(fp_l8, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_l8 or c_l8 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 8 lower-bound bypass {idx_l8} missed: {bad_l8!r}", {}

        # 4. Cleanly separated honest M4/M5/M6 controls (MUST ALL PASS!)
        r8_honest_lower_blocks = (
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Our Track L1 | 3.258835400000 | Has not been formalized in Lean 4 |\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Our Track L1 | 3.258835400000 | Has not yet been formalized in Lean 4 |\n",
            "Our Track L1 campaign reached 3.258835400000 (has not been formalized in Lean 4).\n",
            "Our Track L1 campaign reached 3.258835400000 (has not yet been verified in Lean 4).\n",
            "Our Track L1 campaign reached 3.258835400000, which has not been verified in Lean 4.\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Our Track L1 | 3.258835400000 | Unformalized (awaiting pure-kernel Lean 4 verification) |\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Our Track L1 | 3.258835400000 | Pending a pure-kernel Lean 4 proof |\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Our Track L1 | 3.258835400000 | Not yet a Lean 4 proof |\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Our Track L1 | 3.258835400000 | Not formally verified in Lean 4 |\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Our Track L1 | 3.258835400000 | Not yet formalized as a pure-kernel Lean 4 proof |\n",
            "Our Track L1 campaign reached 3.258835400000, awaiting Lean 4 formalization.\n",
            "Our Track L1 campaign reached 3.258835400000, which is not yet a Lean 4 certified bound.\n",
            "Our Track L1 campaign has not been able to formalize 3.258835400000.\n",
            "Our Track L1 campaign (unformalized) improved from 3.258805369885 to 3.258835400000.\n",
        )
        for idx_hl8, ok_hl8 in enumerate(r8_honest_lower_blocks):
            fp_hl8 = tmp / f"RESULTS_r8_ok_{idx_hl8}.md"
            fp_hl8.write_text(min_base + "\n" + ok_hl8, encoding="utf-8")
            ok_r, c_r, i_r = verify_results_md(fp_hl8, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if not ok_r:
                return False, c_r, f"Iter 8 honest M4/M6 control {idx_hl8} wrongly rejected in RESULTS: {i_r}", {}
            fp_ll8 = tmp / f"LOWER_r8_ok_{idx_hl8}.md"
            fp_ll8.write_text(low_base + "\n" + ok_hl8, encoding="utf-8")
            ok_lr, c_lr, i_lr = verify_research_report(fp_ll8, "lower", info_b["c7_lower_num"], info_b["c7_lower_den"])
            if not ok_lr:
                return False, c_lr, f"Iter 8 honest M4/M6 control {idx_hl8} wrongly rejected in LOWER: {i_lr}", {}

        for idx_hu8, ok_hu8 in enumerate(
            (
                "Polak-Schrijver refuted alpha(C_7^4) <= 107.",
                "It is false that alpha(C_7^4) <= 107.",
            )
        ):
            fp_hu8 = tmp / f"UPPER_r8_ok_{idx_hu8}.md"
            fp_hu8.write_text(up_base + "\n" + ok_hu8 + "\n", encoding="utf-8")
            ok_hu, c_hu, i_hu = verify_research_report(fp_hu8, "upper")
            if not ok_hu:
                return False, c_hu, f"Iter 8 honest M5 prefix-negation control {idx_hu8} wrongly rejected: {i_hu}", {}

        # --- Iteration 9 Section 5 Locks (R8-C2-D01..D05, R8-D7..D9, R8-R2-N1, N02, N03, Auditor L73) ---
        # 5. R8-C2-D01: Option A 100% exact Fraction arithmetic only (11 bypasses + exact unit controls + code-object retirement)
        import cross_check as _cc_s5
        _s5_exact_unit_cases = (
            (r"\sqrt{4}", Fraction(2, 1)),
            (r"\sqrt{9}", Fraction(3, 1)),
            ("0.25^(1/2)", Fraction(1, 2)),
            ("0.25^(-1/2)", Fraction(2, 1)),
            ("(1/8)^(1/3)", Fraction(1, 2)),
            ("0.5^(1/3)", None),
            ("2^10", Fraction(1024, 1)),
            ("(-1)^(-16)", Fraction(1, 1)),
            ("(-1)^15", Fraction(-1, 1)),
            ("(-1)^{10^{12}+1}+2", Fraction(1, 1)),
            ("(-1)^{3^{27}}+2", Fraction(1, 1)),
            ("(-2)^{3^{27}}", None),
            ("(-2)^{10^{12}+1}", None),
            ("(-0.5)^{-(3^{27})}", None),
            ("1.0000000000385^13", None),
            (r"\sqrt{2}", None),
            (r"\sqrt{3}", None),
        )
        for u_expr, u_exp in _s5_exact_unit_cases:
            u_got = _cc_s5._eval_simple_paren_arith(u_expr)
            if u_got != u_exp:
                return False, "MATH_MISMATCH", f"R8-C2-D01 exact arithmetic mismatch on {u_expr!r}: got {u_got}, expected {u_exp}", {}

        def _collect_code_syms(co):
            syms = {co.co_name}
            syms.update(co.co_varnames)
            syms.update(co.co_freevars)
            syms.update(co.co_names)
            gnames = set(co.co_names)
            for c in co.co_consts:
                if hasattr(c, "co_code"):
                    cs, cg = _collect_code_syms(c)
                    syms.update(cs)
                    gnames.update(cg)
            return syms, gnames

        s5_code_syms, s5_co_names = _collect_code_syms(_cc_s5._eval_simple_paren_arith.__code__)
        for extra_fn in (_cc_s5._parse_exact_arith_num, _cc_s5._int_exact_root, _cc_s5._parse_bounded_fraction):
            ex_syms, ex_names = _collect_code_syms(extra_fn.__code__)
            s5_code_syms |= ex_syms
            s5_co_names |= ex_names
            if any(isinstance(c, float) for c in extra_fn.__code__.co_consts):
                return False, "MATH_MISMATCH", f"Float literal present in {extra_fn.__name__}", {}
        if any(isinstance(c, float) for c in _cc_s5._eval_simple_paren_arith.__code__.co_consts):
            return False, "MATH_MISMATCH", "Float literal present in _eval_simple_paren_arith", {}
        for retired_s5 in (
            "_sqrt_upper", "_CAP", "_clamp", "_pow_int", "log1p",
            "_HEADER_VALUE_COL_RE", "_COMPOUND_PROSE_CONT_WORDS",
            "_UPPER_POST_NEGATION_RE", "_PROSE_MATH_OP_MAP", "_INCIDENTAL_EXT_PREFIX_RE",
            "_is_isolated_unformalized_paren_aside", "_CLAUSE_TRANSITION_RE",
            "_UPPER_POST_NEG_ADV", "_MATH_VAR_FOLLOW_WORDS", "_MATH_VAR_I_FOLLOW_WORDS",
            "_ASIDE_LIVE_CERT_RE", "_has_stripped_unformalized_paren", "_has_live_paren_lean_cert",
            "_analyze_table_cell_status", "_POST_COMMA_UNFORMALIZED_RE", "_SUP_COMP_NEG_RE",
            "_EXT_EQUIV_VERB_BEFORE_RE", "_SELF_ASSIGN_BEFORE_RE",
        ):
            if retired_s5 in s5_code_syms or hasattr(_cc_s5, retired_s5):
                return False, "MATH_MISMATCH", f"Retired float/clamp/NLU Section 5 symbol still present: {retired_s5}", {}
        for banned_float_ref in ("log1p", "log", "exp", "float", "round"):
            if banned_float_ref in s5_co_names:
                return False, "MATH_MISMATCH", f"Forbidden float/transcendental call `{banned_float_ref}` in exact-Fraction arithmetic", {}

        # 6. R8-C2-D01, R8-C2-D02, R8-D8, R8-C2-D03, R8-D7, R8-R2-N1, R8-C2-N02 bad uppers (UPPER & RESULTS)
        r9_bad_upper_lines = (
            # R8-C2-D01 (11 exact-Fraction bypasses)
            "We proved alpha(C_7^4) <= 107((-2)^{10^{12}+1}).",
            "We proved alpha(C_7^4) <= 107((-2)^{3^{27}}).",
            "We proved alpha(C_7^4) <= 107((-2)^{999999^3}).",
            "We proved alpha(C_7^4) <= 107((-1)^{10^{12}+1} + 2).",
            "We proved alpha(C_7^4) <= 107((-1)^{3^{27}} + 2).",
            "We proved alpha(C_7^4) <= 107((-0.5)^{-(3^{27})}).",
            r"We proved $\alpha(C_7^4) \le 76.35(\sqrt{2})$.",
            r"We proved $\alpha(C_7^5) \le 211.8(\sqrt{3})$.",
            r"We proved $\alpha(C_7^4) \le 107(\sqrt{2} - 0.405)$.",
            r"We proved $\alpha(C_7^4) \le 107(10000(\sqrt{2} - 1.4143))$.",
            "We proved alpha(C_7^4) <= 107.99999994(1.0000000000385^13).",
            # R8-C2-D02 + R8-D8 + proactive red-team compound-RHS bypasses
            "We proved alpha(C_7^4) <= 107(1) + 0.",
            "We proved alpha(C_7^4) <= 107(2 - 2.5) + 0.",
            "We proved alpha(C_7^4) <= 107(1)/2.",
            "We proved alpha(C_7^4) <= 107(0.5)^2.",
            "We proved alpha(C_7^4) <= 107(0.5 + 0.5) * 1.",
            "We proved alpha(C_7^4) <= 107(1) * 1.",
            r"We proved $\alpha(C_7^4) \le 10 \binom{5}{2} = 50 + 50$.",
            "We proved alpha(C_7^4) <= 200 / 2 = 50 + 50.",
            r"We proved $\alpha(C_7^4) \le 10 \binom{5}{2} = \frac{200}{2}$.",
            "We proved alpha(C_7^4) <= 100 * 1 = (100).",
            "We proved alpha(C_7^4) <= 100 * 1 = 100 + 0.",
            "We proved alpha(C_7^4) <= 100 * 1 >= 0.",
            "We proved alpha(C_7^4) <= 100 * 1 and verified it.",
            "We proved alpha(C_7^4) <= 100 * 1 to close the gap.",
            "We proved alpha(C_7^4) <= 50 * 2 or smaller.",
            r"We proved $\alpha(C_7^4) \le 10 \binom{5}{2}$ and certified it.",
            r"We proved $\alpha(C_7^4) \le 10 \binom{5}{2}$ (exact).",
            "We proved alpha(C_7^4) <= 200 / 2 (proven).",
            "We proved alpha(C_7^4) <= 100 * 1 (2026).",
            "We proved alpha(C_7^4) <= 200 / 2 (d=4).",
            "We proved alpha(C_7^4) <= 100 * 1 [exact].",
            r"We proved $\alpha(C_7^4) \le 100 \cdot 1 \implies \text{done}$.",
            r"We proved $\alpha(C_7^4) \le 100 + 0 \approx 100$.",
            "We proved alpha(C_7^4) <= 107 * (0.5^(1/3)).",
            "We proved alpha(C_7^4) <= 107 * (1/0 + 2).",
            r"We proved $\alpha(C_7^4) \le 107 \cdot \frac12$.",
            r"We proved $\alpha(C_7^4) \le 107 \cdot \sqrt[3]{0.5}$.",
            r"We proved $\alpha(C_7^4) \le 107 \cdot \cos(0)$.",
            "We proved alpha(C_7^4) <= 107 * 1^10000000.",
            "We proved alpha(C_7^4) <= 115 <= 107.",
            "We proved alpha(C_7^4) <= 115 < 108.",
            "We proved alpha(C_7^4) <= 115 = 107.",
            "We proved alpha(C_7^4) <= 200 - 100 = 100.",
            "We proved alpha(C_7^4) <= 115 - 20 = 95.",
            "We proved alpha(C_7^4) <= 112 - 5.",
            "We proved alpha(C_7^4) <= 200(0.5).",
            r"We proved $\alpha(C_7^4) \le 200(\frac{1}{2})$.",
            "We proved alpha(C_7^4) <= 200 (0.5) = 100.",
            "We proved alpha(C_7^4) <= 115(1) - 10 = 105.",
            "We proved alpha(C_7^4) <= 107(2) - 107 = 107.",
            "We proved alpha(C_7^4) <= 107 - a tight bound.",
            "We proved alpha(C_7^4) <= 107 (k + 0) for k = 2/3.",
            "We proved alpha(C_7^4) <= 107 (2 * k) for k = 1/2.",
            r"We proved $\alpha(C_7^4) \le 107 (2 * k)$ for $k = \frac{1}{2}$.",
            "We proved alpha(C_7^4) <= 107 (1 / k^(1/3)) for k = 2.",
            "We proved alpha(C_7^4) <= 100" + " + 0" * 26 + " = 100.",
            # R8-C2-D03, R8-D7, R8-R2-N1, R8-C2-N02
            "(This is not open anymore. We proved alpha(C_7^4) <= 107)",
            "[Not a guess. alpha(C_7^4) <= 107]",
            "(Not refuted; (see Thm 1: alpha(C_7^4) <= 107))",
            "(not valid; see (1; 2) alpha(C_7^4) <= 107)",
            "Not a conjecture (see Section 2. We proved alpha(C_7^4) <= 107).",
            "Not a conjecture (note! We proved alpha(C_7^4) <= 107).",
            "Not a conjecture (and we proved alpha(C_7^4) <= 107).",
            "Not a conjecture (note: alpha(C_7^4) <= 107).",
            "Not a conjecture (see Thm 1: alpha(C_7^4) <= 107).",
            "We proved alpha(C_7^4) <= 107 is impossible to refute.",
            "We proved alpha(C_7^4) <= 107 is impossible to disprove.",
            "We proved alpha(C_7^4) <= 107 is impossible to violate.",
            "We proved alpha(C_7^4) <= 107 is impossible to overturn.",
            "Bogus claim: alpha(C_7^4) <= 107 contradicts known 108-vertex lower bound.",
            "{ Not open | alpha(C_7^4) <= 107 }",
        )
        for idx_u9, bad_u9 in enumerate(r9_bad_upper_lines):
            fp_u9 = tmp / f"UPPER_r9_bad_{idx_u9}.md"
            fp_u9.write_text(up_base + "\n" + bad_u9 + "\n", encoding="utf-8")
            ok_u9, c_u9, _ = verify_research_report(fp_u9, "upper")
            if ok_u9 or c_u9 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 9 upper-bound bypass {idx_u9} missed in UPPER: {bad_u9!r}", {}
            fp_r9u = tmp / f"RESULTS_r9_u_{idx_u9}.md"
            fp_r9u.write_text(min_base + "\n" + bad_u9 + "\n", encoding="utf-8")
            ok_r9u, c_r9u, _ = verify_results_md(fp_r9u, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_r9u or c_r9u != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 9 upper-bound bypass {idx_u9} missed in RESULTS: {bad_u9!r}", {}

        # 7. R8-C2-D03, R8-D7, R8-R2-N1 false exact-solution paren leaks (HONESTY_VIOLATION in RESULTS)
        r9_bad_exact_lines = (
            "(We did not solve it before. We proved Theta(C_7) = 3.258805369885)",
            "(Not open; (see Thm 1: We proved Theta(C_7) = 3.258805369885))",
            "(not proven; see (1; 2) we proved Theta(C_7) = 3.3)",
            "Not open (see Section 2. We proved Theta(C_7) = 3.258805369885).",
            "Not open (note; (We proved Theta(C_7) = 3.258805369885)).",
            "Not open (and we proved Theta(C_7) = 3.258805369885).",
        )
        for idx_e9, bad_e9 in enumerate(r9_bad_exact_lines):
            fp_e9 = tmp / f"RESULTS_r9_e_{idx_e9}.md"
            fp_e9.write_text(min_base + "\n" + bad_e9 + "\n", encoding="utf-8")
            ok_e9, c_e9, _ = verify_results_md(fp_e9, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_e9 or c_e9 != "HONESTY_VIOLATION":
                return False, "MATH_MISMATCH", f"Iter 9 paren exact-claim leak {idx_e9} missed: {bad_e9!r} -> {(ok_e9, c_e9)}", {}

        # 8. R8-C2-D04, R8-C2-D05, R8-D9, R8-C2-N03 lower-bound inflation bypasses (RESULTS & LOWER)
        r9_bad_lower_blocks = (
            "Our Track L1 (verified in Lean 4, beating Tandon) reached 3.258899999999 (unformalized).\n",
            "Our Track L1 (certified in Lean 4 unlike BPZ) reached 3.258899999999 (unformalized).\n",
            "Our Track L1 (proven in Lean 4 vs BPZ) reached 3.258899999999 (unformalized).\n",
            "Our Track L1 (unformalized) (verified in Lean 4, beating Tandon) reached 3.258899999999.\n",
            "Our Track L1 (Tandon; verified in Lean 4) reached 3.258899999999 (unformalized).\n",
            "Our Track L1 reached 3.258899999999 (unformalized) (beating Tandon).\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Our Track L1 | 3.258899999999 (unformalized) | Verified in Lean 4, beating Tandon |\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Our Track L1 | 3.258899999999 (unformalized) | Certified in Lean 4 unlike BPZ |\n",
            "| Method | Lower Bound | Reference | Status |\n|---|---|---|---|\n| This work | 3.258899999999 (unformalized) | Tandon | Verified in Lean 4 |\n",
            "| Method | Lower Bound | Baseline | Status |\n|---|---|---|---|\n| Our Track L1 | 3.258899999999 (unformalized) | BPZ | Verified in Lean 4 |\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Our Track L1 | 3.258899999999 (unformalized) | Beats Tandon |\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Our Track L1 | 3.258899999999 | Unformalized, beating Tandon |\n",
            "We formalized Tandon's 3.258899999999 in pure-kernel Lean 4.\n",
            "We verified Tandon's 3.258899999999 in pure-kernel Lean 4.\n",
            "We certified Tandon's 3.258899999999 in pure-kernel Lean 4.\n",
            "We proved Tandon's 3.258899999999 in pure-kernel Lean 4.\n",
            "Our pure-kernel Lean 4 bound is equal to Tandon's 3.258899999999.\n",
            "Our pure-kernel Lean 4 proof reaches Tandon's 3.258899999999.\n",
            "Our pure-kernel Lean 4 proof achieves Tandon's 3.258899999999.\n",
            "Our pure-kernel Lean 4 proof reproduces Tandon's 3.258899999999.\n",
            "Our pure-kernel Lean 4 certificate gives 3.258899999999 (Tandon).\n",
            "We certify the bound 3.258899999999 (Tandon) in pure-kernel Lean 4.\n",
            "Our pure-kernel Lean 4 bound of 3.258899999999 (Tandon) is certified.\n",
            "Our pure-kernel Lean 4 proof proves the value 3.258899999999 (Tandon).\n",
            "Our pure-kernel Lean 4 bound: 3.258899999999 (Tandon).\n",
            "Our pure-kernel Lean 4 proof: 3.258899999999 (Tandon).\n",
            "Our pure-kernel Lean 4 result of 3.258899999999 (Tandon).\n",
            "Our pure-kernel Lean 4 campaign yielded 3.258899999999 (Tandon).\n",
            "| Method | Bound | Notes |\n|---|---|---|\n| Our pure-kernel Lean 4 | 3.258899999999 (Tandon) | d=500 |\n",
            "| Method | Lower Bound | Reference |\n|---|---|---|\n| Our Track L1 | 3.258899999999 (unformalized) | Tandon; verified in Lean 4 |\n",
            "Our pure-kernel Lean 4 formalization achieved 3.258805369885 (3.258899999999).\n",
            "Our pure-kernel Lean 4 formalization achieved 3.258805369885 (previously unformalized; now certified at 3.258899999999).\n",
            "Our pure-kernel Lean 4 formalization achieved 3.258805369885 (previously unformalized, now certified at 3.258899999999).\n",
            "Our pure-kernel Lean 4 formalization achieved 3.258805369885 (our unformalized pure-kernel proof reached 3.258835400000).\n",
            "Our pure-kernel Lean 4 formalization achieved 3.258805369885 (an unformalized search reached 3.258835400000, verified in Lean 4).\n",
            "Our pure-kernel Lean 4 formalization achieved 3.258805369885 (an unformalized search reached 3.258835400000, beating Tandon).\n",
        )
        for idx_l9, bad_l9 in enumerate(r9_bad_lower_blocks):
            fp_l9 = tmp / f"RESULTS_r9_l_{idx_l9}.md"
            fp_l9.write_text(min_base + "\n" + bad_l9, encoding="utf-8")
            ok_l9, c_l9, _ = verify_results_md(fp_l9, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_l9 or c_l9 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 9 lower-bound bypass {idx_l9} missed in RESULTS: {bad_l9!r}", {}
            fp_ll9 = tmp / f"LOWER_r9_l_{idx_l9}.md"
            fp_ll9.write_text(low_base + "\n" + bad_l9, encoding="utf-8")
            ok_ll9, c_ll9, _ = verify_research_report(fp_ll9, "lower", info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_ll9 or c_ll9 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 9 lower-bound bypass {idx_l9} missed in LOWER: {bad_l9!r}", {}

        # 9. Iteration 9 cleanly separated honest M4/M5/M6 controls (MUST ALL PASS!)
        r9_honest_lower_blocks = (
            "Our Track L1 campaign reached 3.258835400000 (not yet a pure-kernel Lean 4 bound).\n",
            "Our Track L1 campaign reached 3.258835400000 (pending a pure-kernel Lean 4 proof).\n",
            "Our Track L1 campaign reached 3.258835400000 (d=500) (unformalized).\n",
            "We did not formalize Tandon's 3.258832620353 in pure-kernel Lean 4.\n",
            "Our formalization has not reached Tandon's 3.258832620353.\n",
            "| Reference | d | Lower Bound | Notes |\n|---|---|---|---|\n| BPZ (Aug 2026) | 500 | 3.258827985920007 | Beats Gao (2025) |\n",
            "Note: (not yet proven that Theta(C_7) = 3.3).\n",
        )
        for idx_hl9, ok_hl9 in enumerate(r9_honest_lower_blocks):
            fp_hl9 = tmp / f"RESULTS_r9_ok_{idx_hl9}.md"
            fp_hl9.write_text(min_base + "\n" + ok_hl9, encoding="utf-8")
            ok_r9, c_r9, i_r9 = verify_results_md(fp_hl9, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if not ok_r9:
                return False, c_r9, f"Iter 9 honest control {idx_hl9} wrongly rejected in RESULTS: {i_r9}", {}
            fp_ll9ok = tmp / f"LOWER_r9_ok_{idx_hl9}.md"
            fp_ll9ok.write_text(low_base + "\n" + ok_hl9, encoding="utf-8")
            ok_lr9, c_lr9, i_lr9 = verify_research_report(fp_ll9ok, "lower", info_b["c7_lower_num"], info_b["c7_lower_den"])
            if not ok_lr9:
                return False, c_lr9, f"Iter 9 honest control {idx_hl9} wrongly rejected in LOWER: {i_lr9}", {}

        r9_honest_upper_lines = (
            r"Partition bound: $\alpha(C_7^4) \le 56(\sqrt{4}) = 112$.",
            r"We have $\alpha(C_7^4) \le 4(29) = 116$.",
            r"We have $\alpha(C_7^4) \le 10(11) + 2 = 112$.",
            r"We have $\alpha(C_7^4) \le 7\binom{6}{2} + 10 = 115$.",
            r"We have $\alpha(C_7^4) \le 7\alpha(C_7^3)/2$.",
            r"We have $\alpha(C_7^4) \le 33\dfrac{7}{2} = 115.5$.",
            r"We have $\alpha(C_7^4) \le 8(m+2)$ for $m = 13$.",
            r"We have $\alpha(C_7^5) \le 11(34) = 374$.",
            r"We have $\alpha(C_7^4) \le 115$ - via slice double-counting.",
            r"We have $\alpha(C_7^4) \le 115 < \lfloor \vartheta(C_7)^4 \rfloor = 121$.",
            r"We have $\alpha(C_7^4) \le 115(1)$.",
            r"We have $\alpha(C_7^4) \le 115(2026)$.",
            r"We have $\alpha(C_7^4) \le 115$ (115 - 108 = 7).",
            "It is not true that the event { x | alpha(C_7^4) <= 107 } holds.",
            "We ruled out (via SmallPowers.lean) alpha(C_7^4) <= 107.",
        )
        for idx_hu9, ok_hu9 in enumerate(r9_honest_upper_lines):
            fp_hu9 = tmp / f"UPPER_r9_ok_{idx_hu9}.md"
            fp_hu9.write_text(up_base + "\n" + ok_hu9 + "\n", encoding="utf-8")
            ok_hu9_r, c_hu9_r, i_hu9_r = verify_research_report(fp_hu9, "upper")
            if not ok_hu9_r:
                return False, c_hu9_r, f"Iter 9 honest upper control {idx_hu9} wrongly rejected: {i_hu9_r}", {}

        # 10. Iteration 10 Section 5 Locks (R9-C2-D01 .. R9-C2-D05)
        for u10_expr, u10_exp in (
            ("0." + "0" * 105 + "1", None),
            ("0.5" + "0" * 120, Fraction(1, 2)),
            ("107 + 10^{101} * 0." + "0" * 105 + "1", None),
            ("107 + 10^{101} * 1e-106", None),
            ("107 + 1e-5", Fraction(10700001, 100000)),
            ("107 + 1e2", Fraction(207, 1)),
            (r"100 \choose 1", Fraction(100, 1)),
        ):
            u10_got = _cc_s5._eval_simple_paren_arith(u10_expr)
            if u10_got != u10_exp:
                return False, "MATH_MISMATCH", f"R9-C2-D01 exact arith mismatch on {u10_expr!r}: got {u10_got}, expected {u10_exp}", {}

        r10_bad_upper_lines = (
            # R9-C2-D01 + 3 red-teamed siblings
            "We proved alpha(C_7^4) <= 107 + 10^{101} * 0." + "0" * 105 + "1.",
            r"We proved $\alpha(C_7^5) \le 366 + 10^{101} \cdot 0." + "0" * 105 + r"1$.",
            "We proved alpha(C_7^4) <= 107 + 10^{101} * 1e-106.",
            "We proved alpha(C_7^4) <= 107 + 1e-5.",
            "We proved alpha(C_7^4) <= 107(1e-106).",
            "We proved alpha(C_7^4) <= 0(1000000).",
            "We proved alpha(C_7^4) <= 0.000001(1000000).",
            "We proved alpha(C_7^4) <= 10 * k = 100." + "0" * 105 + "1.",
            # R9-C2-D02
            "We proved alpha(C_7^4) <= 200 / 2 over all graphs.",
            r"We proved $\alpha(C_7^4) \le 10 \binom{5}{2}$ over $C_7^4$.",
            "We proved alpha(C_7^4) <= 115 - 20 minus 5.",
            "We proved alpha(C_7^4) <= 100 * 1 divided by 2.",
            "We proved alpha(C_7^4) <= 100 * 1 plus 0.",
            "We proved alpha(C_7^4) <= 100 * 1 times 1.",
            "We proved alpha(C_7^4) <= 100 * 1 choose 1.",
            "We proved alpha(C_7^4) <= 107(1) + 0 mod 1000.",
            "We proved alpha(C_7^4) <= 100 * 1 — a tight bound.",
            "We proved alpha(C_7^4) <= 200 / 2: a new record.",
            r"We proved $\alpha(C_7^4) \le 10 \binom{5}{2}$ - a tight bound.",
            "We proved alpha(C_7^4) <= 100 * 1 a tight bound.",
            "We proved alpha(C_7^4) <= 200 / 2 I verified.",
            "We proved alpha(C_7^4) <= 10 * 10 + 2 [1].",
            "We proved alpha(C_7^4) <= 108 * 1 (1,000) * 0.0001.",
            "We proved alpha(C_7^4) <= 107(10)(0.1).",
            "We proved alpha(C_7^4) <= 200(0.6)(0.5).",
            "We proved alpha(C_7^4) <= 200(0.6)².",
            "We proved alpha(C_7^4) <= 107(10)⁰.",
            r"We proved $\alpha(C_7^4) \le 107(2.0)\frac{1}{2}$.",
            r"We proved $\alpha(C_7^4) \le 107(10)\binom{1}{2}$.",
            r"We proved $\alpha(C_7^4) \le 107(10)\lfloor 0.5 \rfloor$.",
            r"We proved $\alpha(C_7^4) \le 107(10)\sqrt{0.01}$.",
            "We proved alpha(C_7^4) <= 108 - +1.",
            "We proved alpha(C_7^4) <= 115 - -(-10).",
            r"We proved $\alpha(C_7^4) \le 200 \left(\frac{1}{2}\right)$.",
            r"We proved $\alpha(C_7^4) \le 200 (\frac{1}{2})$.",
            # R9-C2-D03
            "(Not open (a (b (c (d (e (f. We proved alpha(C_7^4) <= 107)))))))",
            "(Not refuted (a (b (c (d (e (f; alpha(C_7^4) <= 107)))))))",
            "Not open (Theorem 1: We proved alpha(C_7^4) <= 107).",
            "Not open (Claim: alpha(C_7^4) <= 107).",
            "Status | Claim\n---|---\nNot refuted {x | We proved alpha(C_7^4) <= 107}",
            "We proved alpha(C_7^4) <= 107 is impossible to prove false.",
            "We proved alpha(C_7^4) <= 107 is impossible to prove wrong.",
            "We proved alpha(C_7^4) <= 107 is impossible to establish otherwise.",
        )
        for idx_u10, bad_u10 in enumerate(r10_bad_upper_lines):
            fp_u10 = tmp / f"UPPER_r10_{idx_u10}.md"
            fp_u10.write_text(up_base + "\n" + bad_u10 + "\n", encoding="utf-8")
            ok_u10, c_u10, _ = verify_research_report(fp_u10, "upper")
            if ok_u10 or c_u10 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 10 upper bypass {idx_u10} missed in UPPER: {bad_u10!r}", {}
            fp_ru10 = tmp / f"RESULTS_r10_u_{idx_u10}.md"
            fp_ru10.write_text(min_base + "\n" + bad_u10 + "\n", encoding="utf-8")
            ok_ru10, c_ru10, _ = verify_results_md(fp_ru10, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_ru10 or c_ru10 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 10 upper bypass {idx_u10} missed in RESULTS: {bad_u10!r}", {}

        r10_bad_exact_lines = (
            "(Not open (a (b (c (d (e (f. We proved Theta(C_7) = 3.258805369885)))))))",
            "Status | Claim\n---|---\nNot open {x | We proved Theta(C_7) = 3.258805369885}",
        )
        for idx_e10, bad_e10 in enumerate(r10_bad_exact_lines):
            fp_e10 = tmp / f"RESULTS_r10_e_{idx_e10}.md"
            fp_e10.write_text(min_base + "\n" + bad_e10 + "\n", encoding="utf-8")
            ok_e10, c_e10, _ = verify_results_md(fp_e10, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_e10 or c_e10 != "HONESTY_VIOLATION":
                return False, "MATH_MISMATCH", f"Iter 10 exact-claim bypass {idx_e10} missed: {bad_e10!r} -> {(ok_e10, c_e10)}", {}

        r10_honest_upper_lines = (
            "We proved alpha(C_7^4) <= 108 + 0." + "0" * 105 + ".",
            "We proved alpha(C_7^4) <= 10 * 11 + 2 [1].",
            r"We proved $\alpha(C_7^4) \le 7 \binom{6}{2} + 10$ [3].",
            r"We proved $\alpha(C_7^4) \le 56(\sqrt{4}) = 112$: exact.",
            r"We proved $\alpha(C_7^4) \le 56 \left(\sqrt{4}\right)$.",
            "We proved alpha(C_7^4) <= 10(2)(6).",
            "We proved alpha(C_7^4) <= 10 * 11 + 2 over all graphs.",
            "We proved alpha(C_7^4) <= 10 * 11 + 2 — see Table 1.",
            'We proved "alpha(C_7^4) <= 10 * 11 + 2" in Section 3.',
            "We proved alpha(C_7^4) <= 10 * 11 + 2 (1, 2).",
            "We proved alpha(C_7^4) <= 115 - a where a <= 7.",
            "It is not true that the set { (x, y) | alpha(C_7^4) <= 107 } is nonempty.",
            r"It is not true that $\{ x \in C_{7}^4 | \alpha(C_7^4) \le 107 \}$ is nonempty.",
            r"It is not true that $\{ x \in C_7^{\boxtimes 4} | \alpha(C_7^4) \le 107 \}$ is nonempty.",
        )
        for idx_hu10, ok_hu10 in enumerate(r10_honest_upper_lines):
            fp_hu10 = tmp / f"UPPER_r10_ok_{idx_hu10}.md"
            fp_hu10.write_text(up_base + "\n" + ok_hu10 + "\n", encoding="utf-8")
            ok_hu10_r, c_hu10_r, i_hu10_r = verify_research_report(fp_hu10, "upper")
            if not ok_hu10_r:
                return False, c_hu10_r, f"Iter 10 honest upper control {idx_hu10} wrongly rejected: {i_hu10_r}", {}

        r10_bad_lower_blocks = (
            "| Method | Bounds | Status |\n|---|---|---|\n| Our pure-kernel Lean 4 | 3.258899999999 (Tandon) | Verified in Lean 4 |\n",
            "| Method | Capacity | Status |\n|---|---|---|\n| Our pure-kernel Lean 4 | 3.258899999999 (Tandon) | Verified in Lean 4 |\n",
            "| Our pure-kernel Lean 4 | 3.258899999999 (Tandon) | Verified in Lean 4 |\n",
            "Our Track L1 (verified in Lean 4) reached 3.258899999999 (unformalized) in August 2026.\n",
            "Our Track L1 (verified in Lean 4) reached 3.258899999999 (unformalized) using prior work.\n",
            "Our Track L1 (verified in Lean 4) reached 3.258899999999 (unformalized) building on BPZ.\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Our Track L1 | 3.258899999999 (unformalized) | Verified in Lean 4 (August 2026) |\n",
            "Our Track L1 reached 3.258899999999 (d=500) (unformalized) (beating Tandon).\n",
            "| Method | Bound | Status |\n|---|---|---|\n| Track L1 | 3.258899999999 (Tandon) | Verified in Lean 4, beating BPZ |\n",
            "We confirmed Tandon's 3.258899999999 in pure-kernel Lean 4.\n",
            "We validated Tandon's 3.258899999999 in pure-kernel Lean 4.\n",
            "Our pure-kernel Lean 4 proof is identical to Tandon's 3.258899999999.\n",
        )
        for idx_l10, bad_l10 in enumerate(r10_bad_lower_blocks):
            fp_l10 = tmp / f"RESULTS_r10_l_{idx_l10}.md"
            fp_l10.write_text(min_base + "\n" + bad_l10, encoding="utf-8")
            ok_l10, c_l10, _ = verify_results_md(fp_l10, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_l10 or c_l10 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 10 lower-bound bypass {idx_l10} missed in RESULTS: {bad_l10!r}", {}
            fp_ll10 = tmp / f"LOWER_r10_l_{idx_l10}.md"
            fp_ll10.write_text(low_base + "\n" + bad_l10, encoding="utf-8")
            ok_ll10, c_ll10, _ = verify_research_report(fp_ll10, "lower", info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_ll10 or c_ll10 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 10 lower-bound bypass {idx_l10} missed in LOWER: {bad_l10!r}", {}

        r10_honest_lower_blocks = (
            "| Method | Lower Bound | Status | Notes |\n|---|---|---|---|\n| Track L1 C++17 search | 3.258835400000 | Unformalized | Not yet in our Lean 4 formalization |\n",
            "| Method | Lower Bound | Status | Notes |\n|---|---|---|---|\n| Track L1 | 3.258835400000 | Unformalized | Pending certification in our pure-kernel Lean 4 suite |\n",
            "| Method | Lower Bound | Status | Notes |\n|---|---|---|---|\n| Track L1 | 3.258835400000 | Unformalized | Separate from our Lean 4 formalization |\n",
            "Our Track L1 campaign reached 3.258835400000 (not yet verified by our pure-kernel Lean 4 proof).\n",
            "Our Track L1 campaign reached 3.258835400000 (d=500) (C++17) (unformalized).\n",
            "We are not certifying Tandon's 3.258832620353 in pure-kernel Lean 4.\n",
        )
        for idx_hl10, ok_hl10 in enumerate(r10_honest_lower_blocks):
            fp_hl10 = tmp / f"RESULTS_r10_ok_{idx_hl10}.md"
            fp_hl10.write_text(min_base + "\n" + ok_hl10, encoding="utf-8")
            ok_r10, c_r10, i_r10 = verify_results_md(fp_hl10, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if not ok_r10:
                return False, c_r10, f"Iter 10 honest control {idx_hl10} wrongly rejected in RESULTS: {i_r10}", {}
            fp_ll10ok = tmp / f"LOWER_r10_ok_{idx_hl10}.md"
            fp_ll10ok.write_text(low_base + "\n" + ok_hl10, encoding="utf-8")
            ok_lr10, c_lr10, i_lr10 = verify_research_report(fp_ll10ok, "lower", info_b["c7_lower_num"], info_b["c7_lower_den"])
            if not ok_lr10:
                return False, c_lr10, f"Iter 10 honest control {idx_hl10} wrongly rejected in LOWER: {i_lr10}", {}

        # 11. Iteration 11 Option A-Report Locks (SCOPE.md:48-61 + R10-C2-D01..D04 + Fail-Closed Conversions + Live Zero-FP)
        # 11a. Authorized Option A-Report Fail-Closed Conversions (former post-negation, prose-math, colon-in-paren -> FAIL REPORT_MISMATCH)
        opt_a_rep_bad_upper = (
            # Group B1 (10 former post-negation controls + 1 colon-in-paren)
            "Our audit confirms alpha(C_7^4) <= 107 is impossible since 108 <= alpha(C_7^4).",
            "Note that alpha(C_7^4) <= 107 cannot hold because 108 <= alpha(C_7^4).",
            "Thus alpha(C_7^5) <= 366 cannot hold.",
            "The earlier conjecture alpha(C_7^4) <= 107 was refuted by Polak-Schrijver.",
            "The bound alpha(C_7^4) <= 107 has been ruled out.",
            "The earlier conjecture alpha(C_7^4) <= 107 was independently refuted by Polak-Schrijver.",
            "The claim alpha(C_7^4) <= 107 has long been ruled out.",
            "The bound alpha(C_7^4) <= 107 is provably false.",
            "The claim alpha(C_7^4) <= 107 has independently been ruled out.",
            "The conjecture alpha(C_7^4) <= 107 is impossible to prove.",
            "We ruled out several bounds (namely: alpha(C_7^4) <= 107).",
            # Group B2 (2 former English prose-math controls)
            "We proved alpha(C_7^4) <= 100 * 1 plus 20 = 120.",
            "We proved alpha(C_7^4) <= 100 * 1 choose 2.",
            # R10-C2-D01 (scientific notation + >82-char paren fail-closed)
            "We proved alpha(C_7^4) <= 1e2.",
            "We proved alpha(C_7^4) <= 1.07e2.",
            "We proved alpha(C_7^4) <= 107e0.",
            "We proved alpha(C_7^4) <= 1e-5.",
            "We proved alpha(C_7^5) <= 3.66e2.",
            "We proved alpha(C_7^4) <= 1.07e2 + 0.",
            "We proved alpha(C_7^4) <= 1.07E2.",
            "We proved alpha(C_7^4) <= 108(0." + "9" * 105 + ").",
            "We proved alpha(C_7^4) <= 200(" + "0+" * 42 + "0.5).",
            # R10-C2-D02 (signed paren, alphanumeric citations, TeX {n \choose k}, Unicode/long unary signs)
            "We proved alpha(C_7^4) <= 200(+0.5).",
            "We proved alpha(C_7^4) <= 200(-0.5).",
            "We proved alpha(C_7^4) <= 200(+0.5) + 0.",
            "We proved alpha(C_7^4) <= 200(-1) + 200.",
            "We proved alpha(C_7^4) <= 200 (+0.5) + 0.",
            "We proved alpha(C_7^4) <= 200 (-1) + 200.",
            "We proved alpha(C_7^4) <= 100 * 1 [1a].",
            "We proved alpha(C_7^4) <= 100 * 1 [2026a].",
            "We proved alpha(C_7^4) <= 100 * 1 [B].",
            "We proved alpha(C_7^4) <= 100 * 1 [a].",
            r"We proved $\alpha(C_7^4) \le 200 {2 \choose 3}$.",
            "We proved alpha(C_7^4) <= 115 -−(-10).",
            "We proved alpha(C_7^4) <= 115 −−(-10).",
            "We proved alpha(C_7^4) <= 115 - - - - - 10.",
            "We proved alpha(C_7^4) <= 115 - + + + + 10.",
            # R10-C2-D03 (clause/paren/post-negation leaks)
            "Not refuted, however, (alpha(C_7^4) <= 107).",
            "(Not refuted (a, however, (alpha(C_7^4) <= 107)))",
            "Not open (Table 1: alpha(C_7^4) <= 107).",
            "Not open (Appendix A: alpha(C_7^4) <= 107).",
            "Not open (Corollary 2.1 (main): We proved alpha(C_7^4) <= 107).",
            "We proved alpha(C_7^4) <= 107 is impossible to prove it false.",
            "We proved alpha(C_7^4) <= 107 is impossible to prove the contrary.",
        )
        for idx_u11, bad_u11 in enumerate(opt_a_rep_bad_upper):
            fp_u11 = tmp / f"UPPER_r11_{idx_u11}.md"
            fp_u11.write_text(up_base + "\n" + bad_u11 + "\n", encoding="utf-8")
            ok_u11, c_u11, _ = verify_research_report(fp_u11, "upper")
            if ok_u11 or c_u11 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 11 upper reject {idx_u11} missed in UPPER: {bad_u11!r}", {}
            fp_ru11 = tmp / f"RESULTS_r11_u_{idx_u11}.md"
            fp_ru11.write_text(min_base + "\n" + bad_u11 + "\n", encoding="utf-8")
            ok_ru11, c_ru11, _ = verify_results_md(fp_ru11, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_ru11 or c_ru11 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 11 upper reject {idx_u11} missed in RESULTS: {bad_u11!r}", {}

        # 11b. R10-C2-D01/D02/D03 honest upper controls (MUST ALL PASS!)
        r11_honest_upper = (
            "We proved alpha(C_7^4) <= 1.15e2.",
            "We proved alpha(C_7^5) <= 4.01e2.",
            "We proved alpha(C_7^4) <= 1e3.",
            "We proved alpha(C_7^4) <= 112 (+4).",
            "We proved alpha(C_7^4) <= 112 (-3).",
            r"We proved $\alpha(C_7^4) \le 8 {6 \choose 2}$.",
            r"We proved $\alpha(C_7^4) \le 7 {6 \choose 2} + 10$.",
            r"We proved $\alpha(C_7^4) \le 100 + 2 {5 \choose 2}$.",
            "We proved alpha(C_7^4) <= 60(1) (2).",
            r"We proved $\alpha(C_7^4) \le 60(1) \left(2\right)$.",
            r"It is not true that $\{ x \in [n] | \alpha(C_7^4) \le 107 \}$ is nonempty.",
        )
        for idx_hu11, ok_hu11 in enumerate(r11_honest_upper):
            fp_hu11 = tmp / f"UPPER_r11_ok_{idx_hu11}.md"
            fp_hu11.write_text(up_base + "\n" + ok_hu11 + "\n", encoding="utf-8")
            ok_hu11_r, c_hu11_r, i_hu11_r = verify_research_report(fp_hu11, "upper")
            if not ok_hu11_r:
                return False, c_hu11_r, f"Iter 11 honest upper control {idx_hu11} wrongly rejected: {i_hu11_r}", {}

        # 11c. Option A-Report Group B3 Fail-Closed Separation Conversions (24 former mixed controls) + R10-C2-D04 bypasses -> FAIL REPORT_MISMATCH
        opt_a_rep_bad_lower = (
            # Group B3 (24 former mixed-sentence / mixed-row / unnegated-Lean-cert controls)
            "Unlike the August 2026 BPZ Lean 4 record (3.258827985920007, which relies on native_decide), our formalization verifies 3.258805369885 in the pure Lean 4 kernel.\n",
            "Our pure-kernel bound `3.258805369885` remains below Tandon's `3.258832620353`.\n",
            "Our pure-kernel bound $3.258805369885$ remains below Tandon's $3.258832620353$.\n",
            "Our pure-kernel bound 3.258805369885 is slightly below BPZ (d=500) 3.258827985920007.\n",
            "Our pure-kernel bound 3.258805369885 is below Tandon (Aug 31, 2026) 3.258832620353.\n",
            "Our Lean 4 verified lower bound is 3.258805369885 (below the unrefereed C++17 search lower bound of 3.258832620353).\n",
            "| This work (pure Lean 4) | 200 | 3.258805369885 | 3.258827985920007 (BPZ) |\n",
            "Our Metric | Our Certified Bound | Tandon Benchmark\n--- | --- | ---\nPure-kernel Lean 4 | 3.258805369885 | 3.258832620353\n",
            "Our Lean 4 formalization beats Gao (3.258789153908) at 3.258805369885, trailing Tandon's 3.258832620353.\n",
            "Our pure-kernel Lean 4 lower bound failed to rise above Tandon's 3.258832620353.\n",
            "Our pure-kernel Lean 4 lower bound is unable to climb above Tandon's 3.258832620353.\n",
            "Our pure-kernel Lean 4 lower bound cannot move ahead of Tandon's 3.258832620353.\n",
            "Our certified Lean 4 bound has not yet formalized 3.258835400000.\n",
            "Our pure-kernel Lean 4 lower bound remains below 3.258832620353 (Tandon).\n",
            "Our pure-kernel Lean 4 lower bound compares against 3.258832620353 (Tandon).\n",
            "The lower bound is 3.258827985920007 (BPZ), verified in Lean 4.\n",
            "| Method | Certified Lower Bound | Status |\n|---|---|---|\n| BPZ (Aug 2026) | 3.258827985920007 | Verified in Lean 4 (native_decide) |\n",
            "| Method | Lower Bound | Comparison |\n|---|---|---|\n| Our pure-kernel Lean 4 | 3.258805369885 | Below 3.258832620353 (Tandon) |\n",
            "| Method | Lower Bound | Notes |\n|---|---|---|\n| Our pure-kernel Lean 4 | 3.258805369885 | Below 3.258832620353 (Tandon) |\n",
            "BPZ (verified in Lean 4 via native_decide) achieved 3.258827985920007.\n",
            "| Method | Lower Bound | Notes |\n|---|---|---|\n| Our pure-kernel Lean 4 | 3.258805369885 | Unformalized C++17 candidate reached 3.258835400000 |\n",
            "| Method | Lower Bound | Notes |\n|---|---|---|\n| Our pure-kernel Lean 4 | 3.258805369885 | Separate unformalized search reached 3.258835400000 (not yet formalized in Lean 4) |\n",
            "Our pure-kernel Lean 4 formalization achieved 3.258805369885 (separately, an unformalized C++17 search reached 3.258835400000).\n",
            "| Reference | Lower Bound | Status |\n|---|---|---|\n| BPZ | 3.258827985920007 | Verified in Lean 4 |\n",
            "Our pure-kernel Lean 4 formalization achieved 3.258805369885 (our separate unformalized C++17 search reached 3.258835400000).\n",
            "| Reference | Lower Bound | Status |\n|---|---|---|\n| BPZ | 3.258827985920007 | Verified in Lean 4 with native_decide, beating Gao |\n",
            # R10-C2-D04 (all 5 bypass classes)
            "| Method | Lower Bound | Status | Notes |\n|---|---|---|---|\n| Track L1 | 3.258899999999 | Unformalized | Verified in our pure-kernel Lean 4 proof |\n",
            "| Method | Lower Bound (Details) |\n|---|---|\n| Our pure-kernel Lean 4 | 3.258899999999 (unformalized) |\n",
            "| Method | Lower Bound (vs. Tandon) |\n|---|---|\n| Our pure-kernel Lean 4 | 3.258899999999 (unformalized) |\n",
            "Our Track L1 (verified in Lean 4) reached 3.258899999999 (unformalized) building on the work of BPZ.\n",
            "Our Track L1 (verified in Lean 4) reached 3.258899999999 (unformalized) generalizing BPZ.\n",
            "We formally verified Tandon's August 2026 bound 3.258899999999 in pure-kernel Lean 4.\n",
            "Our pure-kernel Lean 4 proof recovers Tandon's 3.258899999999.\n",
            "Our pure-kernel Lean 4 formalization achieved 3.258805369885 (previously unformalized, verified to 3.258899999999).\n",
            "Our Track L1 reached 3.258899999999 (d=500) (N=100) (v2) (unformalized) (beating Tandon).\n",
        )
        for idx_l11, bad_l11 in enumerate(opt_a_rep_bad_lower):
            fp_l11 = tmp / f"RESULTS_r11_l_{idx_l11}.md"
            fp_l11.write_text(min_base + "\n" + bad_l11, encoding="utf-8")
            ok_l11, c_l11, _ = verify_results_md(fp_l11, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_l11 or c_l11 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 11 Option A-Report lower reject {idx_l11} missed in RESULTS: {bad_l11!r}", {}
            fp_ll11 = tmp / f"LOWER_r11_l_{idx_l11}.md"
            fp_ll11.write_text(low_base + "\n" + bad_l11, encoding="utf-8")
            ok_ll11, c_ll11, _ = verify_research_report(fp_ll11, "lower", info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_ll11 or c_ll11 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 11 Option A-Report lower reject {idx_l11} missed in LOWER: {bad_l11!r}", {}

        # 11d. Clean separated Option A-Report M4/M6 positive controls (MUST ALL PASS!)
        r11_honest_lower = (
            "Our pure-kernel Lean 4 formalization achieved 3.258805369885. It remains below Tandon's external benchmark (3.258832620353).\n",
            "Our Track L1 campaign reached 3.258835400000 (not yet verified by our main pure-kernel Lean 4 proof).\n",
            "Our Track L1 campaign reached 3.258835400000 (outside our Lean 4 formalization).\n",
            "| Method | Lower Bound | Notes |\n|---|---|---|\n| Track L1 (unformalized) | 3.258835400000 | Outside our Lean 4 formalization |\n",
            "Our Track L1 campaign reached 3.258835400000 (d=500) (N=100) (v2) (C++17) (unformalized).\n",
        )
        for idx_hl11, ok_hl11 in enumerate(r11_honest_lower):
            fp_hl11 = tmp / f"RESULTS_r11_ok_{idx_hl11}.md"
            fp_hl11.write_text(min_base + "\n" + ok_hl11, encoding="utf-8")
            ok_r11, c_r11, i_r11 = verify_results_md(fp_hl11, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if not ok_r11:
                return False, c_r11, f"Iter 11 clean lower control {idx_hl11} wrongly rejected in RESULTS: {i_r11}", {}
            fp_ll11ok = tmp / f"LOWER_r11_ok_{idx_hl11}.md"
            fp_ll11ok.write_text(low_base + "\n" + ok_hl11, encoding="utf-8")
            ok_lr11, c_lr11, i_lr11 = verify_research_report(fp_ll11ok, "lower", info_b["c7_lower_num"], info_b["c7_lower_den"])
            if not ok_lr11:
                return False, c_lr11, f"Iter 11 clean lower control {idx_hl11} wrongly rejected in LOWER: {i_lr11}", {}

        # 11e. Live Research Reports Zero-FP Lock (LOWER_RESEARCH_REPORT.md & UPPER_RESEARCH_REPORT.md)
        live_low_rep = ctx.project_dir / "search" / "lower" / "LOWER_RESEARCH_REPORT.md"
        if live_low_rep.is_file():
            ok_ll_act, c_ll_act, i_ll_act = verify_research_report(live_low_rep, "lower", 3258822357711717, 10**15)
            if not ok_ll_act:
                return False, c_ll_act, f"Live LOWER_RESEARCH_REPORT.md false-positived against actual bound: {i_ll_act}", {}
            ok_ll_bpz, c_ll_bpz, _ = verify_research_report(live_low_rep, "lower", 3258805369885, 10**12)
            if ok_ll_bpz or c_ll_bpz != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Live LOWER_RESEARCH_REPORT.md failed to reject against BPZ v1 floor: {(ok_ll_bpz, c_ll_bpz)}", {}
        live_up_rep = ctx.project_dir / "search" / "upper" / "UPPER_RESEARCH_REPORT.md"
        if live_up_rep.is_file():
            ok_lu, c_lu, i_lu = verify_research_report(live_up_rep, "upper")
            if not ok_lu:
                return False, c_lu, f"Live UPPER_RESEARCH_REPORT.md false-positived: {i_lu}", {}

        # 12. Iteration 12 Section 5 Option A-Report Locks (R11-R2-D2/D3, R11-C2-D01..D04 + promoted legacy BPZ Lean 4 rejections + proactive siblings)
        r12_bad_upper = (
            # R11-R2-D2 / R11-C2-D01: scientific mantissa validation
            "We proved alpha(C_7^4) <= -1e5.",
            "We proved alpha(C_7^4) <= -0e5.",
            "We proved alpha(C_7^4) <= −1e5.",
            "We proved alpha(C_7^4) <= -1e6.",
            "We proved alpha(C_7^4) <= -0.5e6.",
            "We proved alpha(C_7^4) <= 0-1e6.",
            "We proved alpha(C_7^4) <= 100-1e2.",
            "We proved alpha(C_7^4) <= 100-100e0.",
            "We proved alpha(C_7^4) <= 1000-999e0.",
            "We proved alpha(C_7^4) <= 107+000e0.",
            "We proved alpha(C_7^4) <= 10+10+10+1e0.",
            "We proved alpha(C_7^4) <= 0e6.",
            "We proved alpha(C_7^5) <= -1e6.",
            # R11-C2-D01: fail-closed iv is None on pure-constant spaced parens
            "We proved alpha(C_7^4) <= 108 (0." + "9" * 105 + ").",
            r"We proved $\alpha(C_7^4) \le 200 (1 / \sqrt{5})$.",
            r"We proved $\alpha(C_7^4) \le 108 (1 / \sqrt{2})$.",
            r"We proved $\alpha(C_7^5) \le 400 (1 / \sqrt{2})$.",
            "We proved alpha(C_7^4) <= 200 (1e-106).",
            r"We proved $\alpha(C_7^4) \le 200 (1 / 2^{512})$.",
            r"We proved $\alpha(C_7^4) \le 108 (2^{-1/2})$.",
            "We proved alpha(C_7^4) <= 108 (1/10000000).",
            # R11-C2-D01: unary +, leading .5, \displaystyle/\textstyle
            "We proved alpha(C_7^4) <= +107.",
            "We proved alpha(C_7^5) <= +366.",
            "We proved alpha(C_7^4) <= .5.",
            "We proved alpha(C_7^4) <= +.5.",
            "We proved alpha(C_7^4) <= -.5.",
            r"We proved $\alpha(C_7^4) \le \displaystyle 107$.",
            r"We proved $\alpha(C_7^4) \le \textstyle 107$.",
            r"We proved $\alpha(C_7^4) \le \frac{\displaystyle 200}{2}$.",
            # R11-C2-D01: interrupted/unclosed parens, display math, for k =, 4th-power
            "We proved alpha(C_7^4) <= (107\n).",
            r"We proved $\alpha(C_7^4) \le \frac{200}{2" + "\n}$.",
            "We proved alpha(C_7^4) <= 100 + (7 by lemma).",
            "We proved alpha(C_7^4) <= (100 note).",
            "We proved alpha(C_7^4) <= {107 note}.",
            "We proved alpha(C_7^4) <= 200 (0.5\n).",
            "$$\n\\alpha(C_7^4) \\le 108\n- 1\n$$.",
            "$$ \\alpha(C_7^4) \\le 108\n- 1 $$",
            "We proved alpha(C_7^4) <= 200(k) for k = 1/2.",
            "We proved alpha(C_7^4) <= 200 (k) for k = 1/2.",
            "We proved alpha(C_7^4) <= 200 (2 k) for k = 1/4.",
            "We proved alpha(C_7^4) <= 200 (-k) for k = 1/2.",
            "We proved alpha(C_7^4) <= 200 a for a = 1/2.",
            "We proved alpha(C_7^4) <= 100 a 4th-power bound.",
            "We proved alpha(C_7^4) <= 100 - a 4-tuple bound.",
            # R11-C2-D02: scoped without/no/open, coordinate and, double negation, paren leakage
            "Without sorry we proved alpha(C_7^4) <= 107.",
            "Without native_decide we proved alpha(C_7^4) <= 107.",
            "Without custom axioms we proved alpha(C_7^4) <= 107.",
            "With no sorry we proved alpha(C_7^4) <= 107.",
            "With no custom axioms we proved alpha(C_7^4) <= 107.",
            "With no doubt we proved alpha(C_7^4) <= 107.",
            "There is no flaw in our proof that alpha(C_7^4) <= 107.",
            "In Theorem no. 3 we proved alpha(C_7^4) <= 107.",
            "Solving the 70-year open problem we proved alpha(C_7^4) <= 107.",
            "Without assuming anything extra we proved alpha(C_7^4) <= 107.",
            "We did not use sorry and alpha(C_7^4) <= 107.",
            "We did not fail to prove alpha(C_7^4) <= 107.",
            "We are not unable to prove alpha(C_7^4) <= 107.",
            "It is not yet refuted that alpha(C_7^4) <= 107.",
            "It has not been refuted that alpha(C_7^4) <= 107.",
            "It is not falsified that alpha(C_7^4) <= 107.",
            "Not ruled out that alpha(C_7^4) <= 107.",
            "Not contradicted that alpha(C_7^4) <= 107.",
            "It isn't impossible that alpha(C_7^4) <= 107.",
            "Not open (we formally proved alpha(C_7^4) <= 107).",
            "Not open (alpha(C_7^4) <= 107).",
        )
        for idx_u12, bad_u12 in enumerate(r12_bad_upper):
            fp_u12 = tmp / f"UPPER_r12_bad_{idx_u12}.md"
            fp_u12.write_text(up_base + "\n" + bad_u12 + "\n", encoding="utf-8")
            ok_u12, c_u12, _ = verify_research_report(fp_u12, kind="upper")
            if ok_u12 or c_u12 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 12 upper lock {idx_u12} missed in UPPER: {bad_u12!r}", {}
            fp_ru12 = tmp / f"RESULTS_r12_u_{idx_u12}.md"
            fp_ru12.write_text(min_base + "\n" + bad_u12 + "\n", encoding="utf-8")
            ok_ru12, c_ru12, _ = verify_results_md(fp_ru12, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_ru12 or c_ru12 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 12 upper lock {idx_u12} missed in RESULTS: {bad_u12!r}", {}

        r12_bad_exact = (
            "Without sorry we proved Theta(C_7) = 3.2588.",
            "Without native_decide we proved Theta(C_7) = 3.2588.",
            "With no custom axioms we proved Theta(C_7) = 3.2588.",
            "Without sorry we solved the 70-year open problem exactly.",
            "Without assuming anything extra we proved Theta(C_7) = 3.2588.",
            "We did not use native_decide and proved Theta(C_7) = 3.2588.",
            "We did not fail and solved the 70-year open problem exactly.",
            "We did not fail to prove Theta(C_7) = 3.2588.",
            "Not open (we proved Theta(C_7) = 3.2588).",
            "It is unproven (we certified Theta(C_7) = 3.2588).",
        )
        for idx_e12, bad_e12 in enumerate(r12_bad_exact):
            fp_e12 = tmp / f"RESULTS_r12_ex_{idx_e12}.md"
            fp_e12.write_text(min_base + "\n" + bad_e12 + "\n", encoding="utf-8")
            ok_e12, c_e12, _ = verify_results_md(fp_e12, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_e12 or c_e12 != "HONESTY_VIOLATION":
                return False, "MATH_MISMATCH", f"Iter 12 exact-claim lock {idx_e12} missed: {bad_e12!r}", {}

        r12_bad_lower = (
            # Promoted legacy BPZ Lean 4 lines (strictly stronger fail-closed Option A-Report separation)
            "| Reference | Method | d | Lower Bound |\n|---|---|---|---|\n| BPZ (2026) | Lean 4.32.2 (native_decide) | 500 | 3.258827985920007 |\n",
            "Our lower-bound campaign targeted Tandon's unrefereed record of 3.258832620353 and BPZ's August 2026 Lean 4 record of 3.258827985920007.\n",
            "| Method | Notes | Lower Bound |\n|---|---|---|\n| Lean 4 (d=500) | BPZ Aug 2026 (native_decide) | 3.258827985920007 |\n",
            # R11-R2-D3 / R11-C2-D03: _LEAN_CERT_NEG_RE loophole & _SELF_LEAN_CERT_RE + standalone cells
            "An unformalized pure-kernel Lean 4 bound is 3.258899999999.\n",
            "Our Track L1 reached 3.258899999999 (unformalized certified in Lean 4).\n",
            "Beyond native_decide our pure-kernel Lean 4 bound is 3.258899999999.\n",
            "Tandon's previously unformalized pure-kernel Lean 4 certified bound 3.258899999999.\n",
            "With native_decide our pure-kernel Lean 4 formalization achieved 3.258899999999.\n",
            "We achieved 3.258899999999 in Lean 4 (building on BPZ).\n",
            "Verified 3.258899999999 in Lean 4 (building on BPZ).\n",
            "Verified with Lean 4: 3.258899999999 (building on BPZ).\n",
            "Lean 4 certifies 3.258899999999 (building on BPZ).\n",
            "The Lean 4 kernel accepts 3.258899999999 (extending BPZ).\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Track L1 (BPZ method) | 3.258899999999 | Lean 4 |\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Track L1 (C++ search) | 3.258899999999 | Formally verified |\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Building on BPZ | 3.258899999999 | Certified |\n",
            "This paper verified 3.258899999999 (building on BPZ).\n",
            "This work formally verified 3.258899999999 (building on BPZ).\n",
            "Our codebase formally verifies 3.258899999999 (building on BPZ).\n",
            "Machine-checked in Lean 4: 3.258899999999 (building on BPZ).\n",
            # Paragraph line-wrapping, blockquote wrapping & `:` before display math
            "Our pure-kernel Lean 4 formalization certified the\nTandon lower bound 3.258899999999.\n",
            "> Our pure-kernel Lean 4 formalization certified the\n> Tandon lower bound 3.258899999999.\n",
            "Our pure-kernel Lean 4 formalization certified:\n$$\n\\Theta_{\\text{Tandon}}(C_7) \\ge 3.258899999999\n$$\n",
            # 3.31 boundary & c_up without r_ext
            "Our pure-kernel Lean 4 lower bound is 3.31, closing the gap.\n",
            "| Method | Lovász Upper Bound |\n|---|---|\n| Our Track L1 | 3.258899999999 |\n",
            # Unbounded decimal / scientific / >25-digit fraction candidates
            "Our pure-kernel Lean 4 certified lower bound is 3.25889" + "0" * 60 + ".\n",
            "Our pure-kernel Lean 4 formalization achieved 3.258899999999e0.\n",
            "Our pure-kernel Lean 4 formalization achieved 3258899999999e-12.\n",
            "Our pure-kernel Lean 4 formalization achieved 3.258899999999e0000000.\n",
            "Our pure-kernel Lean 4 certified lower bound is 32588999999990000000000000 / 10^25.\n",
            "Our pure-kernel Lean 4 certified lower bound is 3258899999999 / 10^0000012.\n",
            "Our pure-kernel Lean 4 certified lower bound is " + "3258899999999" + "0" * 100 + " / 10^112.\n",
            # R11-C2-D04: abbreviation-dot splitting (initials, e.g., i.e., months, EOL abbrev)
            "Our pure-kernel Lean 4 formalization verified R. Tandon's bound 3.258899999999.\n",
            "Our pure-kernel Lean 4 formalization verified P. Buys, S. Polak, and J. Zuiddam's bound 3.258899999999.\n",
            "Our pure-kernel Lean 4 formalization verified J.-P. Serre's bound 3.258899999999.\n",
            "Our pure-kernel Lean 4 formalization certified e.g. Tandon's bound 3.258899999999.\n",
            "Our pure-kernel Lean 4 formalization certified i.e. Tandon's bound 3.258899999999.\n",
            "Our pure-kernel Lean 4 formalization certified Aug. 2026 Tandon bound 3.258899999999.\n",
            "Our pure-kernel Lean 4 formalization certified Jul. 2026 BPZ bound 3.258899999999.\n",
            "Our pure-kernel Lean 4 formalization verified R.\nTandon's bound 3.258899999999.\n",
            "Our pure-kernel Lean 4 formalization verified Aug.\n2026 Tandon bound 3.258899999999.\n",
        )
        for idx_l12, bad_l12 in enumerate(r12_bad_lower):
            fp_l12 = tmp / f"RESULTS_r12_l_{idx_l12}.md"
            fp_l12.write_text(min_base + "\n" + bad_l12, encoding="utf-8")
            ok_l12, c_l12, _ = verify_results_md(fp_l12, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_l12 or c_l12 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 12 lower lock {idx_l12} missed in RESULTS: {bad_l12!r}", {}
            fp_ll12 = tmp / f"LOWER_r12_l_{idx_l12}.md"
            fp_ll12.write_text(low_base + "\n" + bad_l12, encoding="utf-8")
            ok_ll12, c_ll12, _ = verify_research_report(fp_ll12, "lower", info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_ll12 or c_ll12 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 12 lower lock {idx_l12} missed in LOWER: {bad_l12!r}", {}

        # 12b. Wave r12 honest positive controls (MUST ALL PASS!)
        r12_honest_upper = (
            "Trivial bound: alpha(C_7^4) <= 1e6.",
            "Trivial bound: alpha(C_7^4) <= +1e6.",
            "Trivial bound: alpha(C_7^4) <= 1.2e7.",
            "Trivial bound: alpha(C_7^4) <= 1e50.",
            "We proved alpha(C_7^4) <= +115.",
            "We proved alpha(C_7^4) <= 120 (see lemma 1).",
            "We proved alpha(C_7^4) <= 115 (+2).",
            "We proved alpha(C_7^4) <= 115 (-1).",
            "We proved alpha(C_7^4) <= (20)*6*(1).",
            "We proved alpha(C_7^4) <= (10)*12*(1).",
            "We proved alpha(C_7^4) <= 100 a for a = 2.",
            "We proved alpha(C_7^4) <= 100 a where a >= 2.",
            "We did not prove e.g. alpha(C_7^4) <= 107.",
            "No valid proof shows alpha(C_7^4) <= 107.",
            "There is no known proof that alpha(C_7^4) <= 107.",
            "Without proving alpha(C_7^4) <= 107, we study relaxations.",
            "It remains an open problem whether alpha(C_7^4) <= 107.",
            "We do not claim i.e. we proved Theta(C_7) = 3.2588.",
            "No known proof establishes Theta(C_7) = 3.2588.",
        )
        for idx_hu12, ok_hu12 in enumerate(r12_honest_upper):
            fp_hu12 = tmp / f"UPPER_r12_ok_{idx_hu12}.md"
            fp_hu12.write_text(up_base + "\n" + ok_hu12 + "\n", encoding="utf-8")
            ok_hu, c_hu, i_hu = verify_research_report(fp_hu12, kind="upper")
            if not ok_hu:
                return False, c_hu, f"Iter 12 honest upper control {idx_hu12} wrongly rejected in UPPER: {i_hu}", {}
            fp_hru12 = tmp / f"RESULTS_r12_uok_{idx_hu12}.md"
            fp_hru12.write_text(min_base + "\n" + ok_hu12 + "\n", encoding="utf-8")
            ok_hru, c_hru, i_hru = verify_results_md(fp_hru12, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if not ok_hru:
                return False, c_hru, f"Iter 12 honest upper control {idx_hu12} wrongly rejected in RESULTS: {i_hru}", {}

        r12_honest_lower = (
            "Our pure-kernel Lean 4 formalization has not reached Tandon's 3.258899999999.\n",
            "We did not verify our C++17 candidate 3.258899999999 in pure-kernel Lean 4.\n",
            "We did not formalize Tandon's Aug 2026 preprint 3.258899999999 in pure-kernel Lean 4.\n",
            "Our formalization covers Track A. Tandon's benchmark stands at 3.258832620353.\n",
            "Our script verified 3.258899999999 in Python (unformalized).\n",
        )
        for idx_hl12, ok_hl12 in enumerate(r12_honest_lower):
            fp_hl12 = tmp / f"RESULTS_r12_lok_{idx_hl12}.md"
            fp_hl12.write_text(min_base + "\n" + ok_hl12, encoding="utf-8")
            ok_rl12, c_rl12, i_rl12 = verify_results_md(fp_hl12, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if not ok_rl12:
                return False, c_rl12, f"Iter 12 honest lower control {idx_hl12} wrongly rejected in RESULTS: {i_rl12}", {}
            fp_hll12 = tmp / f"LOWER_r12_lok_{idx_hl12}.md"
            fp_hll12.write_text(low_base + "\n" + ok_hl12, encoding="utf-8")
            ok_ll12ok, c_ll12ok, i_ll12ok = verify_research_report(fp_hll12, "lower", info_b["c7_lower_num"], info_b["c7_lower_den"])
            if not ok_ll12ok:
                return False, c_ll12ok, f"Iter 12 honest lower control {idx_hl12} wrongly rejected in LOWER: {i_ll12ok}", {}

        # 12c. Iteration 13 Section 5 Option A-Report Locks (R12-C2-D01..D04, R12-R2-D3, Auditor r12 notes)
        # (a) R12-C2-D01: finite-time (< 0.5s CPU, SIGALRM-guarded) infinite-loop & O(N^2) regression locks
        import signal as _sig_r13
        import threading as _thr_r13
        _use_alrm = hasattr(_sig_r13, "SIGALRM") and _thr_r13.current_thread() is _thr_r13.main_thread()
        _prev_alrm_h = None
        if _use_alrm:
            def _r13_timeout_handler(_signum, _frame):
                raise TimeoutError("R12-C2-D01 _collapse_display_math_tagged infinite-loop regression (>5s)")
            _prev_alrm_h = _sig_r13.signal(_sig_r13.SIGALRM, _r13_timeout_handler)
            _sig_r13.alarm(5)
        try:
            t0_d01 = time.process_time()
            _r13_hang_payloads = (
                "$$\n```",
                "\\[\n```",
                "$$\n~~~",
                "Note $$ x\n```bash\necho ok\n```",
                "Note \\[ x\n```bash\necho ok\n```",
                "\\[\n" * 1000 + "```",
                "$$\n" * 1000 + "```",
            )
            for hp in _r13_hang_payloads:
                _cc_s5._collapse_display_math_tagged(hp.split("\n"))
            for idx_hp, hp in enumerate(_r13_hang_payloads[:5]):
                fp_hp_u = tmp / f"UPPER_r13_hp_{idx_hp}.md"
                fp_hp_u.write_text(up_base + "\n" + hp + "\n", encoding="utf-8")
                verify_research_report(fp_hp_u, kind="upper")
                fp_hp_l = tmp / f"LOWER_r13_hp_{idx_hp}.md"
                fp_hp_l.write_text(low_base + "\n" + hp + "\n", encoding="utf-8")
                verify_research_report(fp_hp_l, "lower", info_b["c7_lower_num"], info_b["c7_lower_den"])
                fp_hp_r = tmp / f"RESULTS_r13_hp_{idx_hp}.md"
                fp_hp_r.write_text(min_base + "\n" + hp + "\n", encoding="utf-8")
                verify_results_md(fp_hp_r, info_b["c7_lower_num"], info_b["c7_lower_den"])
            dt_d01 = time.process_time() - t0_d01
        finally:
            if _use_alrm:
                _sig_r13.alarm(0)
                _sig_r13.signal(_sig_r13.SIGALRM, _prev_alrm_h)
        if dt_d01 >= 0.5:
            return False, "MATH_MISMATCH", f"R12-C2-D01 unclosed-math-before-fence O(N) regression ({dt_d01:.3f}s >= 0.5s CPU)", {}

        # (b) R12-C2-D01 (multi-line display math), R12-C2-D02 (exact-Fraction upper scanner), R12-C2-D03 + Auditor r12 `relied on`
        r13_bad_upper = (
            # R12-C2-D01 multi-line blockquote, odd multi-block, chained closing & post-fence display math
            "> $$\n> \\alpha(C_7^4) \\le 108\n> - 1\n> $$",
            "> > $$\n> > \\alpha(C_7^4) \\le 108\n> > - 1\n> > $$",
            "$$ x = 1 $$ $$ \\alpha(C_7^4) \\le 108\n- 1 $$",
            "\\[ x = 1 \\] \\[ \\alpha(C_7^4) \\le 108\n- 1 \\]",
            "$$ x = 1\n$$ $$ \\alpha(C_7^4) \\le 108\n- 1 $$",
            "Note $$ unclosed\n```bash\necho ok\n```\n$$\n\\alpha(C_7^4) \\le 108\n- 1\n$$",
            # R12-C2-D02 year/year-range false meta-paren before has_after_op & non-year arith
            "We proved alpha(C_7^4) <= 115(2000)/4000.",
            "We proved alpha(C_7^4) <= 115 (2000) / 4000.",
            "We proved alpha(C_7^4) <= 115(2000) - 229900.",
            "We proved alpha(C_7^4) <= 115 (2026) * 0.",
            "We proved alpha(C_7^4) <= 115 (2026)^0 - 10.",
            "We proved alpha(C_7^4) <= 115 (2026) / 2026 - 10.",
            "We proved alpha(C_7^4) <= 115(2000/4000).",
            "We proved alpha(C_7^4) <= 115 (2000/4000).",
            "We proved alpha(C_7^4) <= 115(2000 - 2000).",
            "We proved alpha(C_7^4) <= 115(1999 - 2000).",
            "We proved alpha(C_7^4) <= 115 (2024 - 2023) / 2.",
            # R12-C2-D02 _UNARY_MINUS_CONT_PAT leading `.` & single-letter variable
            "We proved alpha(C_7^4) <= 108 (1) - .5.",
            "We proved alpha(C_7^4) <= 108 [1] - .5.",
            "We proved alpha(C_7^4) <= 108 (1) - .999999.",
            "We proved alpha(C_7^4) <= 108 (1) - k for k = 1.",
            # R12-C2-D02 single-letter inner before has_after_op & parenthesized `for k = (1/2)`
            "We proved alpha(C_7^4) <= 200(k) / 2 for k = 1.",
            "We proved alpha(C_7^4) <= 200(k) + 0 for k = 1/2.",
            "We proved alpha(C_7^4) <= 200 (k) = 100.",
            "We proved alpha(C_7^4) <= 200 (a) <= 107.",
            "We proved alpha(C_7^4) <= 115 (k) < 108.",
            "We proved alpha(C_7^4) <= 200 k for k = (1/2).",
            # R12-C2-D02 chained impossible bound after meta-paren or bracket note
            "We proved alpha(C_7^4) <= 107 (2026) <= 115.",
            "We proved alpha(C_7^4) <= 115 (Polak 2019) <= 107.",
            "We proved alpha(C_7^4) <= 115 (Polak 2019) [1] <= 107.",
            "We proved alpha(C_7^4) <= 115 (by slice bound) = 107.",
            "We proved alpha(C_7^4) <= 115 (2026) = 107.",
            "We proved alpha(C_7^4) <= 115 (1, 2) <= 107.",
            "We proved alpha(C_7^4) <= 115 [note] <= 107.",
            # R12-C2-D03 scoped no/without/open, _TCB_NEG_AND_RE (+ Auditor r12 `relied on`), unanchored paren, double-neg bridge
            "With no formal axioms alpha(C_7^4) <= 107.",
            "With no lean warnings alpha(C_7^4) <= 107.",
            "With no known gaps Theorem 1 proves alpha(C_7^4) <= 107.",
            "With no upper limit on runtime alpha(C_7^4) <= 107.",
            "Without assuming any conjectures Theorem 1 proves alpha(C_7^4) <= 107.",
            "Without assuming sorry it is proved that alpha(C_7^4) <= 107.",
            "Without assuming any axioms alpha(C_7^4) <= 107.",
            "It is still open and Theorem 1 proves alpha(C_7^4) <= 107.",
            "We never had a sorry and alpha(C_7^4) <= 107.",
            "We did not use the native_decide tactic and alpha(C_7^4) <= 107.",
            "We did not use Lean.ofReduceBool and alpha(C_7^4) <= 107.",
            "We did not invoke native_decide and alpha(C_7^4) <= 107.",
            "Our proof does not use any sorry or admit or native_decide or external unsafe axioms and alpha(C_7^4) <= 107.",
            "We haven't relied on native_decide and alpha(C_7^4) <= 107.",
            "It is unproven (in Lean 4 we proved alpha(C_7^4) <= 107).",
            "It is unproven (note that we proved alpha(C_7^4) <= 107).",
            "It is unproven (Theorem 1 proved alpha(C_7^4) <= 107).",
            "We did not stop (in Lean 4 we proved alpha(C_7^4) <= 107).",
            "It is not even remotely impossible that alpha(C_7^4) <= 107.",
        )
        for idx_u13, bad_u13 in enumerate(r13_bad_upper):
            fp_u13 = tmp / f"UPPER_r13_bad_{idx_u13}.md"
            fp_u13.write_text(up_base + "\n" + bad_u13 + "\n", encoding="utf-8")
            ok_u13, c_u13, _ = verify_research_report(fp_u13, kind="upper")
            if ok_u13 or c_u13 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 13 upper lock {idx_u13} missed in UPPER: {bad_u13!r}", {}
            fp_ru13 = tmp / f"RESULTS_r13_u_{idx_u13}.md"
            fp_ru13.write_text(min_base + "\n" + bad_u13 + "\n", encoding="utf-8")
            ok_ru13, c_ru13, _ = verify_results_md(fp_ru13, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_ru13 or c_ru13 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 13 upper lock {idx_u13} missed in RESULTS: {bad_u13!r}", {}

        # (c) R12-C2-D03 false exact-solution claims -> HONESTY_VIOLATION
        r13_bad_exact = (
            "With no formal gaps it is proved that Theta(C_7) = 3.2588.",
            "Without assuming native_decide Theorem 1 proves Theta(C_7) = 3.2588.",
            "It is still open and Theorem 1 proves Theta(C_7) = 3.2588.",
            "It is unproven (in Lean 4 we proved Theta(C_7) = 3.2588).",
            "It is unproven (here we proved Theta(C_7) = 3.2588).",
            "It is unproven (proved Theta(C_7) = 3.2588).",
        )
        for idx_e13, bad_e13 in enumerate(r13_bad_exact):
            fp_e13 = tmp / f"RESULTS_r13_ex_{idx_e13}.md"
            fp_e13.write_text(min_base + "\n" + bad_e13 + "\n", encoding="utf-8")
            ok_e13, c_e13, _ = verify_results_md(fp_e13, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_e13 or c_e13 != "HONESTY_VIOLATION":
                return False, "MATH_MISMATCH", f"Iter 13 exact-claim lock {idx_e13} missed: {bad_e13!r}", {}

        # (d) R12-R2-D3 & R12-C2-D04 lower-bound separation locks -> REPORT_MISMATCH in RESULTS & LOWER
        r13_bad_lower = (
            # R12-R2-D3 / R12-C2-D04 double-negation in _LEAN_CERT_NEG_RE
            "No longer pending Lean 4 formalization: Tandon bound 3.258899999999.\n",
            "No longer awaiting Lean 4 certification: Tandon bound 3.258899999999.\n",
            "Not outside our Lean 4 formalization: Tandon bound 3.258899999999.\n",
            "Never outside Lean 4: Tandon bound 3.258899999999.\n",
            "Not excluded from our Lean 4 formalization: Tandon bound 3.258899999999.\n",
            "Not separate from our Lean 4 formalization: Tandon bound 3.258899999999.\n",
            "No longer without pure-kernel Lean 4: Tandon bound 3.258899999999.\n",
            "No longer lacking pure-kernel Lean 4: Tandon bound 3.258899999999.\n",
            "No longer missing Lean 4 proof: Tandon bound 3.258899999999.\n",
            "Not just candidate for Lean 4: Tandon bound 3.258899999999.\n",
            "No longer a target for Lean 4: Tandon bound 3.258899999999.\n",
            "It isn't outside our Lean 4 proof: Tandon bound 3.258899999999.\n",
            "Tandon's 3.258899999999 is no longer outside pure-kernel Lean 4.\n",
            "Tandon's 3.258899999999 is not at all without pure-kernel Lean 4.\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Track L1 (BPZ) | 3.258899999999 | No longer pending Lean 4 |\n",
            # R12-C2-D04 mid-sentence display-math without `:` (incl. blank line) & blockquote blank line
            "Our pure-kernel Lean 4 formalization proved that\n$$\n\\Theta_{\\text{Tandon}}(C_7) \\ge 3.258899999999.\n$$\n",
            "Our pure-kernel Lean 4 formalization proved that\n\n$$\n\\Theta_{\\text{Tandon}}(C_7) \\ge 3.258899999999.\n$$\n",
            "Our pure-kernel Lean 4 formalization proved that\n\\[\n\\Theta_{\\text{Tandon}}(C_7) \\ge 3.258899999999.\n\\]\n",
            "> Our pure-kernel Lean 4 formalization certified:\n>\n> $$\n> \\Theta_{\\text{Tandon}}(C_7) \\ge 3.258899999999\n> $$\n",
            "Our pure-kernel Lean 4 formalization certified\n> Tandon's bound 3.258899999999.\n",
            # R12-C2-D04 table c_lean/c_up & annotated status cells
            "| Method | Lower Bound | Lean 4 Certified |\n|---|---|---|\n| Track L1 (C++ search) | 3.258899999999 | Yes |\n",
            "| Method | Lower Bound | Pure-Kernel Verified |\n|---|---|---|\n| Track L1 (C++ search) | 3.258899999999 | ✓ |\n",
            "| Method | Lean 4 Upper Bound |\n|---|---|\n| Tandon preprint | 3.258899999999 |\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Tandon (d=500) | 3.258899999999 | Certified (d=500) |\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Building on BPZ | 3.258899999999 | Verified (d=500) |\n",
            # R12-C2-D04 present-tense formally <verb> & kernel/machine/mechanically verified
            "Track L1 formally certifies Tandon's bound 3.258899999999.\n",
            "Theorem 1 formally proves Tandon's bound 3.258899999999.\n",
            "Track L1 formally verifies 3.258899999999 (building on BPZ).\n",
            "Tandon's 3.258899999999 is kernel-verified.\n",
            "Tandon's 3.258899999999 is machine-verified.\n",
            "Tandon's 3.258899999999 is mechanically verified.\n",
            # R12-C2-D04 standard candidate number formats
            "Our pure-kernel Lean 4 formalization achieved 03.258899999999.\n",
            "Our pure-kernel Lean 4 formalization certified 3,258,899,999,999 / 1,000,000,000,000.\n",
            r"Our pure-kernel Lean 4 formalization certified $\frac{3{,}258{,}899{,}999{,}999}{10^{12}}$." + "\n",
            "Our pure-kernel Lean 4 formalization certified (3258899999999) / 10^12.\n",
            "Our pure-kernel Lean 4 formalization certified 3258899999999 / 1e12.\n",
            "Our pure-kernel Lean 4 formalization certified 3258899999999 / 10¹².\n",
        )
        for idx_l13, bad_l13 in enumerate(r13_bad_lower):
            fp_l13 = tmp / f"RESULTS_r13_l_{idx_l13}.md"
            fp_l13.write_text(min_base + "\n" + bad_l13, encoding="utf-8")
            ok_l13, c_l13, _ = verify_results_md(fp_l13, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_l13 or c_l13 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 13 lower lock {idx_l13} missed in RESULTS: {bad_l13!r}", {}
            fp_ll13 = tmp / f"LOWER_r13_l_{idx_l13}.md"
            fp_ll13.write_text(low_base + "\n" + bad_l13, encoding="utf-8")
            ok_ll13, c_ll13, _ = verify_research_report(fp_ll13, "lower", info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_ll13 or c_ll13 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 13 lower lock {idx_l13} missed in LOWER: {bad_l13!r}", {}

        # (e) Wave r13 honest positive controls (R12-C2-D02/D03/D04 clean controls + Auditor r12 `haven't yet`)
        for idx_hu13, ok_hu13 in enumerate((
            "We proved alpha(C_7^4) <= 115 (2025-2026).",
            "We proved alpha(C_7^4) <= 115 (Polak 2019) <= 121.",
            "We proved alpha(C_7^4) <= 33 (7/2) = 115.5.",
            "We proved alpha(C_7^4) <= 115 [1] - a tight bound.",
            "We haven't yet proved alpha(C_7^4) <= 107.",
            "No exact value of Theta(C_7) is proven.",
        )):
            fp_hu13 = tmp / f"UPPER_r13_ok_{idx_hu13}.md"
            fp_hu13.write_text(up_base + "\n" + ok_hu13 + "\n", encoding="utf-8")
            ok_hu13_r, c_hu13_r, i_hu13_r = verify_research_report(fp_hu13, kind="upper")
            if not ok_hu13_r:
                return False, c_hu13_r, f"Iter 13 honest upper control {idx_hu13} wrongly rejected: {i_hu13_r}", {}

        for idx_hl13, ok_hl13 in enumerate((
            "We did not formally verify Tandon's 3.258899999999 in pure-kernel Lean 4.\n",
            "We did not formally certify Tandon's 3.258899999999 in Lean 4.\n",
            "| Method | Lower Bound | Lean 4 Certified |\n|---|---|---|\n| Track L1 (C++ search) | 3.258899999999 | No |\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Track L1 (C++ search) | 3.258899999999 | Verified (in Python) |\n",
            "We haven't yet certified our Rust candidate 3.2589 in pure-kernel Lean 4.\n",
            "No exact value of Theta(C_7) is proven.\n",
        )):
            fp_hl13 = tmp / f"RESULTS_r13_lok_{idx_hl13}.md"
            fp_hl13.write_text(min_base + "\n" + ok_hl13, encoding="utf-8")
            ok_rl13, c_rl13, i_rl13 = verify_results_md(fp_hl13, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if not ok_rl13:
                return False, c_rl13, f"Iter 13 honest lower control {idx_hl13} wrongly rejected in RESULTS: {i_rl13}", {}
            fp_hll13 = tmp / f"LOWER_r13_lok_{idx_hl13}.md"
            fp_hll13.write_text(low_base + "\n" + ok_hl13, encoding="utf-8")
            ok_ll13ok, c_ll13ok, i_ll13ok = verify_research_report(fp_hll13, "lower", info_b["c7_lower_num"], info_b["c7_lower_den"])
            if not ok_ll13ok:
                return False, c_ll13ok, f"Iter 13 honest lower control {idx_hl13} wrongly rejected in LOWER: {i_ll13ok}", {}

        # 12d. Iteration 14 Section 5 Option A-Report Locks (R13-C2-D01..D03 + Auditor r13 107 [2a] - .1)
        # (a) R13-C2-D01, Auditor r13 & R13-C2-D03 impossible upper-bound locks -> REPORT_MISMATCH in BOTH UPPER & RESULTS
        r14_bad_upper = (
            # R13-C2-D01: `for`/`where`/`with`/paren-`for` compound RHS (no truncation!)
            "We proved alpha(C_7^4) <= 200 k for k = 1 - 1/2.",
            "We proved alpha(C_7^4) <= 200 k for k = 2 * (1/4).",
            "We proved alpha(C_7^4) <= 200 k for k = 2^(-1).",
            "We proved alpha(C_7^4) <= 200 k, for k = 1/2.",
            "We proved alpha(C_7^4) <= 200 k where k = 1/2.",
            "We proved alpha(C_7^4) <= 200 k, where k = 1/2.",
            "We proved alpha(C_7^4) <= 108 - k, for k = 1.",
            "We proved alpha(C_7^4) <= 108 - k where k = 1.",
            "We proved alpha(C_7^4) <= 200 k with k = 1/2.",
            "We proved alpha(C_7^4) <= 200 k (for k = 1/2).",
            "We proved alpha(C_7^4) <= 200 k for k = 1/2 (2026).",
            r"We proved $\alpha(C_7^4) \le 200 k$ for $k = 1/\sqrt{2}$.",
            # R13-C2-D01: mixed-delimiter chained & non-chained bounds
            "We proved alpha(C_7^4) <= 115 (C_7^4 [Polak 2019]) <= 107.",
            "We proved alpha(C_7^4) <= 115 (a [Polak 2019]) <= 107.",
            r"We proved $\alpha(C_7^4) \le 115$ ($\alpha$ [Polak 2019]) $\le 107$.",
            "We proved alpha(C_7^4) <= 115 ({a Polak}) <= 107.",
            "We proved alpha(C_7^4) <= 115 [a (Polak)] <= 107.",
            "We proved alpha(C_7^4) <= 115 (a [note]) = 107.",
            "We proved alpha(C_7^4) <= 115 (x + [note]) <= 107.",
            r"We proved $\alpha(C_7^4) \le 115$ (a [\cite{polak}]) $\le 107$.",
            "We proved alpha(C_7^4) <= 107 (a [Polak 2019]).",
            "We proved alpha(C_7^4) <= 107 ({a Polak}).",
            "We proved alpha(C_7^4) <= 107 [a (Polak)].",
            "We proved alpha(C_7^4) <= 115 {a Polak} <= 107.",
            # R13-C2-D01: `/` year-range fractions, signed factor after parenthesized LHS/before rel, spaced juxtaposed `(`, Auditor r13 `[2a] - .1`
            "We proved alpha(C_7^4) <= 108 (1900/2100).",
            "We proved alpha(C_7^4) <= 115 (1900/2026).",
            "We proved alpha(C_7^4) <= 108 (2025/2026).",
            "We proved alpha(C_7^5) <= 367 (2025/2026).",
            "We proved alpha(C_7^4) <= (115) (-1).",
            "We proved alpha(C_7^4) <= (108 + 7) (-1).",
            "We proved alpha(C_7^4) <= 115 (-1) <= 115.",
            "We proved alpha(C_7^4) <= 200 (+0.5) <= 115.",
            "We proved alpha(C_7^4) <= 115 (2) (1/3).",
            "We proved alpha(C_7^4) <= 115 (2026) (0).",
            "We proved alpha(C_7^4) <= 115(2026) (0).",
            "We proved alpha(C_7^4) <= 115(2000) (1/4000).",
            "We proved alpha(C_7^4) <= 115 (k) (1/2) for k = 1.",
            "We proved alpha(C_7^4) <= 108 (1) (1/2).",
            "We proved alpha(C_7^4) <= 115 (2025/2026) (1/2).",
            "We proved alpha(C_7^4) <= 115 (2026) (2) (0).",
            "We proved alpha(C_7^4) <= 115 (2) (k) for k = 1/3.",
            "We proved alpha(C_7^4) <= 107 [2a] - .1.",
            "We proved alpha(C_7^4) <= 107 [1a] - .1.",
            # R13-C2-D03: double-negated `open whether/if`/`whether`, attributive TCB nouns, `_TCB_NEG_AND_RE`, `_PAREN_FRESH_CLAIM_RE`
            "It is not open whether alpha(C_7^4) <= 107.",
            "It is no longer open whether alpha(C_7^4) <= 107.",
            "It is not an open problem whether alpha(C_7^4) <= 107.",
            "It is not open if alpha(C_7^4) <= 107.",
            "It is no longer an open question whether alpha(C_7^4) <= 107.",
            "It does not remain open whether alpha(C_7^4) <= 107.",
            "It is not unproven whether alpha(C_7^4) <= 107.",
            "It is no longer an open matter at all whether alpha(C_7^4) <= 107.",
            "Without any unproven assumptions alpha(C_7^4) <= 107.",
            "Without unproven conjectures alpha(C_7^4) <= 107.",
            "Using zero unproven axioms alpha(C_7^4) <= 107.",
            "With no external unproven axioms alpha(C_7^4) <= 107.",
            "With zero failing checks alpha(C_7^4) <= 107.",
            "Free of unproven axioms alpha(C_7^4) <= 107.",
            "We did not use sorryAx and alpha(C_7^4) <= 107.",
            "We cannot use native_decide and alpha(C_7^4) <= 107.",
            "We did not leave any sorry and alpha(C_7^4) <= 107.",
            "We did not assume any conjectures and alpha(C_7^4) <= 107.",
            "We did not use unverified axioms and alpha(C_7^4) <= 107.",
            "Our proof never uses sorry and alpha(C_7^4) <= 107.",
            "It is unproven (proves alpha(C_7^4) <= 107).",
            "It is unproven (certifies alpha(C_7^4) <= 107).",
            "It is unproven (establishes alpha(C_7^4) <= 107).",
            "It is unproven (formally proved in Lean 4 that alpha(C_7^4) <= 107).",
        )
        for idx_u14, bad_u14 in enumerate(r14_bad_upper):
            fp_u14 = tmp / f"UPPER_r14_bad_{idx_u14}.md"
            fp_u14.write_text(up_base + "\n" + bad_u14 + "\n", encoding="utf-8")
            ok_u14, c_u14, _ = verify_research_report(fp_u14, kind="upper")
            if ok_u14 or c_u14 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 14 upper lock {idx_u14} missed in UPPER: {bad_u14!r}", {}
            fp_ru14 = tmp / f"RESULTS_r14_u_{idx_u14}.md"
            fp_ru14.write_text(min_base + "\n" + bad_u14 + "\n", encoding="utf-8")
            ok_ru14, c_ru14, _ = verify_results_md(fp_ru14, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_ru14 or c_ru14 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 14 upper lock {idx_u14} missed in RESULTS: {bad_u14!r}", {}

        # (b) R13-C2-D03 false exact-solution locks -> HONESTY_VIOLATION in RESULTS
        r14_bad_exact = (
            "It is unproven (proves Theta(C_7) = 3.2588).",
            "It is unproven (certifies Theta(C_7) = 3.2588).",
            "It is unproven (verifies Theta(C_7) = 3.2588).",
            "It is unproven (formally proved in Lean 4 that Theta(C_7) = 3.2588).",
            "It is not open whether we proved Theta(C_7) = 3.2588.",
            "It does not remain open whether we proved Theta(C_7) = 3.2588.",
            "Without any unproven axioms we proved Theta(C_7) = 3.2588.",
        )
        for idx_e14, bad_e14 in enumerate(r14_bad_exact):
            fp_e14 = tmp / f"RESULTS_r14_ex_{idx_e14}.md"
            fp_e14.write_text(min_base + "\n" + bad_e14 + "\n", encoding="utf-8")
            ok_e14, c_e14, _ = verify_results_md(fp_e14, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_e14 or c_e14 != "HONESTY_VIOLATION":
                return False, "MATH_MISMATCH", f"Iter 14 exact-claim lock {idx_e14} missed: {bad_e14!r}", {}

        # (c) R13-C2-D02 lower-bound separation locks -> REPORT_MISMATCH in BOTH RESULTS & LOWER
        r14_bad_lower = (
            # Post-display-math continuation (multi-line, single-line, \[\], blank-line, comma, blockquote, mid-sentence, two-block, em-dash, paren)
            "$$\n\\Theta_{\\text{Tandon}}(C_7) \\ge 3.258899999999\n$$\nis formally certified in pure-kernel Lean 4.\n",
            "$$ \\Theta_{\\text{Tandon}}(C_7) \\ge 3.258899999999 $$\nis formally certified in pure-kernel Lean 4.\n",
            "\\[\n\\Theta_{\\text{Tandon}}(C_7) \\ge 3.258899999999\n\\]\nis formally certified in pure-kernel Lean 4.\n",
            "$$\n\\Theta_{\\text{Tandon}}(C_7) \\ge 3.258899999999\n$$\n\nis formally certified in pure-kernel Lean 4.\n",
            "$$\n\\Theta_{\\text{Tandon}}(C_7) \\ge 3.258899999999,\n$$\ncertifying in pure-kernel Lean 4.\n",
            "> $$\n> \\Theta_{\\text{Tandon}}(C_7) \\ge 3.258899999999\n> $$\n> is formally certified in pure-kernel Lean 4.\n",
            "Tandon's bound\n$$\n3.258899999999\n$$\nis formally certified in pure-kernel Lean 4.\n",
            "Our pure-kernel Lean 4 formalization proved\n$$\n\\alpha(C_7^3) = 33\n$$\nand\n$$\n\\Theta_{\\text{Tandon}}(C_7) \\ge 3.258899999999\n$$\n",
            "$$\n\\Theta_{\\text{Tandon}}(C_7) \\ge 3.258899999999\n$$\n— certified in pure-kernel Lean 4.\n",
            "$$\n\\Theta_{\\text{Tandon}}(C_7) \\ge 3.258899999999\n$$\n(certified in pure-kernel Lean 4).\n",
            # Symbolic candidate formats: 10^(12), 10**(12), decimal/÷ fractions, LaTeX \times 10^k, Unicode × 10⁻¹
            "Our pure-kernel Lean 4 formalization certified 3258899999999 / 10^(12).\n",
            "Our pure-kernel Lean 4 formalization certified 3258899999999 / 10**(12).\n",
            r"Our pure-kernel Lean 4 formalization certified $\frac{3258899999999}{10^(12)}$." + "\n",
            "Our pure-kernel Lean 4 formalization certified 32.58899999999 / 10.\n",
            "Our pure-kernel Lean 4 formalization certified 32.58899999999 ÷ 10.\n",
            r"Our pure-kernel Lean 4 formalization certified $\frac{32.58899999999}{10}$." + "\n",
            "Our pure-kernel Lean 4 formalization certified 325.8899999999 / 100.\n",
            "Our pure-kernel Lean 4 formalization certified 32.58899999999 / 10^1.\n",
            r"Our pure-kernel Lean 4 formalization certified $\frac{325.8899999999}{10^2}$." + "\n",
            "Our pure-kernel Lean 4 formalization certified 32.58899999999 / 10.0.\n",
            "Our pure-kernel Lean 4 formalization certified 0.3258899999999 / 0.1.\n",
            r"Our pure-kernel Lean 4 formalization certified $32.58899999999 \times 10^{-1}$." + "\n",
            r"Our pure-kernel Lean 4 formalization certified $0.3258899999999 \times 10^1$." + "\n",
            "Our pure-kernel Lean 4 formalization certified 32.58899999999 × 10⁻¹.\n",
            # General backward-walk double-negation & TCB-noun `no`/`without` in `_LEAN_CERT_NEG_RE`
            "Tandon's 3.258899999999 is not really outside pure-kernel Lean 4.\n",
            "Tandon's 3.258899999999 is not even outside pure-kernel Lean 4.\n",
            "Tandon's 3.258899999999 is not technically outside pure-kernel Lean 4.\n",
            "Tandon's 3.258899999999 is not still pending Lean 4 formalization.\n",
            "Tandon's 3.258899999999 is not currently pending Lean 4 certification.\n",
            "Tandon's 3.258899999999 is not actually excluded from our Lean 4 formalization.\n",
            "Tandon's 3.258899999999 is no longer merely pending Lean 4 certification.\n",
            "Tandon's 3.258899999999 is no longer just a candidate for Lean 4.\n",
            "Tandon's 3.258899999999 isn't even without pure-kernel Lean 4.\n",
            "With no Lean 4 sorry, Tandon's bound 3.258899999999 is certified.\n",
            "With no pure-kernel axioms, Tandon's bound 3.258899999999 is proved.\n",
            "Without pure-kernel Lean 4 sorry, Tandon's bound 3.258899999999 is certified.\n",
            # Affirmative & annotated-status table cells
            "| Method | Lower Bound | Lean 4 Certified |\n|---|---|---|\n| Track L1 (C++ search) | 3.258899999999 | Done |\n",
            "| Method | Lower Bound | Lean 4 Certified |\n|---|---|---|\n| Track L1 (C++ search) | 3.258899999999 | Complete |\n",
            "| Method | Lower Bound | Lean 4 Certified |\n|---|---|---|\n| Track L1 (C++ search) | 3.258899999999 | Completed |\n",
            "| Method | Lower Bound | Lean 4 Certified |\n|---|---|---|\n| Track L1 (C++ search) | 3.258899999999 | Confirmed |\n",
            "| Method | Lower Bound | Lean 4 Certified |\n|---|---|---|\n| Track L1 (C++ search) | 3.258899999999 | Yes, d=500 |\n",
            "| Method | Lower Bound | Lean 4 Certified |\n|---|---|---|\n| Track L1 (C++ search) | 3.258899999999 | Yes — d=500 |\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Tandon (d=500) | 3.258899999999 | Certified, d=500 |\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Tandon (d=500) | 3.258899999999 | Certified — d=500 |\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Tandon (d=500) | 3.258899999999 | Certified [d=500] |\n",
        )
        for idx_l14, bad_l14 in enumerate(r14_bad_lower):
            fp_l14 = tmp / f"RESULTS_r14_l_{idx_l14}.md"
            fp_l14.write_text(min_base + "\n" + bad_l14, encoding="utf-8")
            ok_l14, c_l14, _ = verify_results_md(fp_l14, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_l14 or c_l14 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 14 lower lock {idx_l14} missed in RESULTS: {bad_l14!r}", {}
            fp_ll14 = tmp / f"LOWER_r14_l_{idx_l14}.md"
            fp_ll14.write_text(low_base + "\n" + bad_l14, encoding="utf-8")
            ok_ll14, c_ll14, _ = verify_research_report(fp_ll14, "lower", info_b["c7_lower_num"], info_b["c7_lower_den"])
            if ok_ll14 or c_ll14 != "REPORT_MISMATCH":
                return False, "MATH_MISMATCH", f"Iter 14 lower lock {idx_l14} missed in LOWER: {bad_l14!r}", {}

        # (d) Wave r14 honest positive controls (R13-C2-D01 valid-bound FP fixes + clean prose/table/negation controls)
        for idx_hu14, ok_hu14 in enumerate((
            "We proved alpha(C_7^4) <= 50 k for k = 2^2.",
            "We proved alpha(C_7^4) <= 60 k for k = 1 + 1.",
            "We proved alpha(C_7^4) <= 50 k for k = 2 * 2.",
            "We proved alpha(C_7^4) <= 50 k for k = 3/2 * 2.",
            "We proved alpha(C_7^4) <= 50 k for k = 2 + m.",
            "We proved alpha(C_7^4) <= 115 (2026) (see Table 1).",
            "We proved alpha(C_7^4) <= 115 (2026) (Polak 2019).",
            "We proved alpha(C_7^4) <= 112 (-3) (2026).",
            "We proved alpha(C_7^4) <= 115 (1 [Polak 2019]).",
            "We proved alpha(C_7^4) <= 115 [2a] - .1.",
            "We proved alpha(C_7^4) <= 107 [k] + 100.",
            "It is unproven (e.g. alpha(C_7^4) <= 107).",
            "It is unproven whether alpha(C_7^4) <= 107.",
            "It is not clear whether alpha(C_7^4) <= 107.",
            "The unproven conjecture alpha(C_7^4) <= 107 is still open.",
            "We did not assume alpha(C_7^4) <= 107 and instead proved 115.",
        )):
            fp_hu14 = tmp / f"UPPER_r14_ok_{idx_hu14}.md"
            fp_hu14.write_text(up_base + "\n" + ok_hu14 + "\n", encoding="utf-8")
            ok_hu14_r, c_hu14_r, i_hu14_r = verify_research_report(fp_hu14, kind="upper")
            if not ok_hu14_r:
                return False, c_hu14_r, f"Iter 14 honest upper control {idx_hu14} wrongly rejected: {i_hu14_r}", {}

        for idx_hl14, ok_hl14 in enumerate((
            "Tandon's 3.258899999999 was computed with no Lean 4 verification.\n",
            "Tandon's 3.258899999999 has no Lean 4 proof.\n",
            "| Method | Lower Bound | Lean 4 Certified |\n|---|---|---|\n| Track L1 (C++ search) | 3.258899999999 | No (C++ only) |\n",
            "| Method | Lower Bound | Lean 4 Certified |\n|---|---|---|\n| Track L1 (C++ search) | 3.258899999999 | Yes, Python only |\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Track L1 (C++ search) | 3.258899999999 | Verified, C++17 |\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Tandon (d=500) | 3.258899999999 | Verified — Python |\n",
            "| Method | Lower Bound | Status |\n|---|---|---|\n| Tandon (d=500) | 3.258899999999 | Certified, not in Lean 4 |\n",
        )):
            fp_hl14 = tmp / f"RESULTS_r14_lok_{idx_hl14}.md"
            fp_hl14.write_text(min_base + "\n" + ok_hl14, encoding="utf-8")
            ok_rl14, c_rl14, i_rl14 = verify_results_md(fp_hl14, info_b["c7_lower_num"], info_b["c7_lower_den"])
            if not ok_rl14:
                return False, c_rl14, f"Iter 14 honest lower control {idx_hl14} wrongly rejected in RESULTS: {i_rl14}", {}
            fp_hll14 = tmp / f"LOWER_r14_lok_{idx_hl14}.md"
            fp_hll14.write_text(low_base + "\n" + ok_hl14, encoding="utf-8")
            ok_ll14ok, c_ll14ok, i_ll14ok = verify_research_report(fp_hll14, "lower", info_b["c7_lower_num"], info_b["c7_lower_den"])
            if not ok_ll14ok:
                return False, c_ll14ok, f"Iter 14 honest lower control {idx_hl14} wrongly rejected in LOWER: {i_ll14ok}", {}

        # (e) Dedicated Iteration 14 Section 5 O(N) CPU guard (< 0.15s — kept separate from #13's 0.25s block!)
        t0_r14_on = time.process_time()
        _find_impossible_upper_claim("alpha(C_7^4) <= 115 (" + "a [b] " * 500 + ") <= 115.")
        _find_impossible_upper_claim("alpha(C_7^4) <= 115 k for k = 1" + " + 0" * 500 + ".")
        _find_impossible_upper_claim("alpha(C_7^4) <= 50 k for k = 2" + " + 0" * 500 + ".")
        _find_impossible_upper_claim("alpha(C_7^4) <= 115" + " (2)" * 500 + ".")
        _find_impossible_upper_claim("alpha(C_7^4) <= " + "115 (a [Polak]) <= " * 200 + "115.")
        _find_inflated_lower_claims("$$\n1\n$$\nand\n" * 400 + "done.\n", FLOOR_LOWER, "3.258805369885")
        _find_inflated_lower_claims("$$\n3.0\n$$\nand\n" * 200 + "end.", FLOOR_LOWER, "3.258805369885")
        _cc_s5._extract_lower_candidates(r"32.5889 \times 10^{-1} " * 400)
        _cc_s5._extract_lower_candidates(r"32.5889" + "0" * 10000 + r" \times 10^{-1}")
        dt_r14_on = time.process_time() - t0_r14_on
        if dt_r14_on >= 0.15:
            return False, "MATH_MISMATCH", f"Iter 14 Section 5 O(N) CPU regression ({dt_r14_on:.3f}s >= 0.15s)", {}

        # 13. Section 5 O(N) CPU guard (< 0.25s total)
        t0_s5_on = time.process_time()
        _cc_s5._eval_simple_paren_arith("100" + " + 0" * 2000)
        _cc_s5._split_line_table_cells("{ x | y " * 2000 + "}")
        _cc_s5._split_line_table_cells("{ (x, y) | z } " * 1000)
        _find_impossible_upper_claim("(not open; see (1; 2) alpha(C_7^4) <= 115) " * 800)
        _find_impossible_upper_claim("alpha(C_7^4) <= " + "115 (note) <= " * 400 + "115.")
        deep_p = "(" * 4000 + "a. alpha(C_7^4) <= 107" + ")" * 4000
        if _find_impossible_upper_claim(deep_p) is None:
            return False, "MATH_MISMATCH", "deep_nested_paren_same_clause missed impossible bound", {}
        opens_200 = "(a " * 200 + "b. alpha(C_7^4) <= 107" + ")" * 200
        if _find_impossible_upper_claim(opens_200) is None:
            return False, "MATH_MISMATCH", "same_clause_200_opens missed impossible bound", {}
        _cc_s5._collapse_display_math_tagged(["$$ x"] * 2000)
        _cc_s5._collapse_display_math_tagged([r"\[ x"] * 2000)
        _cc_s5._collapse_display_math_tagged(["$$"] * 1000 + ["```"])
        _cc_s5._collapse_display_math_tagged([r"\["] * 1000 + ["```"])
        _find_inflated_lower_claims("R.\n" * 2000 + "Tandon 3.258832620353\n", FLOOR_LOWER, "3.258805369885")
        _cc_s5._extract_lower_candidates("3.25889" + "0" * 20000 + "1")
        _cc_s5._extract_lower_candidates("325889" + "0" * 10000 + " / 1" + "0" * 10005)
        _cc_s5._extract_lower_candidates("1" + ",000" * 1000 + " / x")
        dt_s5_on = time.process_time() - t0_s5_on
        if dt_s5_on >= 0.25:
            return False, "MATH_MISMATCH", f"Iter 13 Section 5 O(N) CPU regression ({dt_s5_on:.3f}s >= 0.25s)", {}

        BIG = 1 << 1700000
        if verify_results_md(good_md, BIG, 1)[:2] != (False, "REPORT_MISMATCH"):
            return False, "MATH_MISMATCH", "verify_results_md giant lower_num guard failed", {}
        if verify_research_report(low_good, "lower", BIG, 1)[:2] != (False, "REPORT_MISMATCH"):
            return False, "MATH_MISMATCH", "verify_research_report(lower) giant lower_num guard failed", {}

        return True, "OK", "Main.lean/public def/DoS guards + Option A-Report fail-closed exact-Fraction RESULTS/LOWER/UPPER honesty, separation, live-report zero-FP & O(N) checks verified", {}
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def _st_16(ctx: SuiteContext):
    run_sh = ctx.verify_dir / "run_e2e.sh"
    bad_invocations = (
        ["--invalid-flag"],
        ["--tier", "9"],
        ["--tier", ""],
        ["--tier", ","],
        [],
        ["--self-test", "--all"],
        ["--all", "--tier", "1"],
        ["--all", "--tier", "9"],
        ["--tier", "1", "--filter", "NOMATCH_XYZ_999"],
    )
    for argv in bad_invocations:
        out = run_subprocess_safe([str(run_sh)] + argv, cwd=ctx.verify_dir, timeout=20)
        if out.returncode != 2:
            return False, "SUBPROCESS_FAILED", f"CLI {argv} expected exit 2, got {out.returncode}", {"stderr": out.stderr}

    out_list = run_subprocess_safe([str(run_sh), "--list"], cwd=ctx.verify_dir, timeout=20)
    if out_list.returncode != 0:
        return False, "SUBPROCESS_FAILED", f"--list failed (rc={out_list.returncode})", {}
    lines = out_list.stdout.splitlines()
    t1 = sum(1 for ln in lines if ln.startswith("T1-"))
    t2 = sum(1 for ln in lines if ln.startswith("T2-"))
    t3 = sum(1 for ln in lines if ln.startswith("T3-"))
    t4 = sum(1 for ln in lines if ln.startswith("T4-"))
    st = sum(1 for ln in lines if ln.startswith("ST-"))
    if (t1, t2, t3, t4, st) != (70, 70, 16, 8, 18):
        return False, "REPORT_MISMATCH", f"--list counts mismatch: got {(t1,t2,t3,t4,st)}, expected (70,70,16,8,18)", {}
    return True, "OK", "CLI exit codes (2 on bad/conflicting/empty flags, 0 on --list) & exact counts (164 + 18) verified", {}


def _st_17(ctx: SuiteContext):
    # 1. Core pure-math lexer & unambiguous pure-Init interpolator (`s!`, `f!`, `println!`) + Option A meta rejections
    cases = (
        ("unclosed_comment", "/- unclosed\ndef x := 1\n", "UNCLOSED_BLOCK_COMMENT"),
        ("lean_slash_dash_slash", "/-/\ndef x := 1\n", "UNCLOSED_BLOCK_COMMENT"),
        ("lean_doc_unclosed", "/--/\ndef x := 1\n", "UNCLOSED_BLOCK_COMMENT"),
        ("lean_moddoc_unclosed", "/-!/\ndef x := 1\n", "UNCLOSED_BLOCK_COMMENT"),
        ("interp_sorry", 'def msg := s!"prefix {sorry} suffix"\n', "FORBIDDEN_SORRY"),
        ("interp_double_brace_s", 'def x := s!"{{ fst := 0, snd := (by sorry : Nat) : Nat × Nat }.1}"\n', "FORBIDDEN_SORRY"),
        ("interp_double_brace_f", 'def x := f!"{{ fst := 0, snd := (by sorry : Nat) }.1}"\n', "FORBIDDEN_SORRY"),
        ("interp_double_brace_m", 'def x := m!"{{ fst := 0, snd := (by native_decide : Bool) }.1}"\n', "FORBIDDEN_META_API"),
        ("interp_v_bang", 'def x := v!"1.0.{sorry}"\n', "FORBIDDEN_META_API"),
        ("interp_custom_macro", 'macro "custom!" s:interpolatedStr(term) : term => `(s!$s)\ndef x := custom!"{sorry}"\n', "FORBIDDEN_META_SYNTAX"),
        ("interp_r_bang_macro", 'macro "r!" s:interpolatedStr(term) : term => `(s!$s)\ndef x := r!"{sorry}"\n', "FORBIDDEN_META_SYNTAX"),
        ("interp_unclosed_eof", 'def x := s!"hello { 1\n', "UNCLOSED_STRING"),
        ("interp_custom_unclosed", 'def x := custom!"unclosed { 1\n', "UNCLOSED_STRING"),
        ("raw0_backslash_desync", 'def s := r"\\"\ntheorem cheat : False := sorry\n-- "\n', "FORBIDDEN_SORRY"),
        ("char_quote_before_sorry", "def c := '\\''\ntheorem t : True := by sorry\n", "FORBIDDEN_SORRY"),
        ("spaced_s_interp", 'def x : String := s! "{(by sorry : Nat)}"\n', "FORBIDDEN_SORRY"),
        ("comment_s_interp", 'def x : String := s! /- c -/ "{sorry}"\n', "FORBIDDEN_SORRY"),
        ("line_comment_s_interp", 'def x : String := s! -- c\n"{sorry}"\n', "FORBIDDEN_SORRY"),
        ("spaced_f_interp", 'def x := f! "{sorry}"\n', "FORBIDDEN_SORRY"),
        ("println_interp", 'def x : IO Unit := println! "{(by sorry : Nat)}"\n', "FORBIDDEN_SORRY"),
        ("println_nospace_interp", 'def x : IO Unit := println!"{(by sorry : Nat)}"\n', "FORBIDDEN_SORRY"),
        ("nested_spaced_interp", 'def x := s!"outer {s! "inner {(by sorry : Nat)}"}"\n', "FORBIDDEN_SORRY"),
        ("escaped_bs_live_brace", 'def x := s!"\\\\{(by sorry : Nat)}"\n', "FORBIDDEN_SORRY"),
        ("prefix_bang_sorry", 'def bad : Bool := !sorry\n', "FORBIDDEN_SORRY"),
        ("prefix_qmark_sorry", 'def bad := ?sorry\n', "FORBIDDEN_SORRY"),
        # Explorer 1 Unicode-postfix, name-literal, qualified & plain-bang `sorry` bypasses
        ("unicode_sorry_compl", "def bad := sorryᶜ\n", "FORBIDDEN_SORRY"),
        ("unicode_sorry_inv", "def bad := sorry⁻¹\n", "FORBIDDEN_SORRY"),
        ("unicode_sorry_lambda", "def bad := sorryλx => x\n", "FORBIDDEN_SORRY"),
        ("name_lit_s_bang_desync", 'def a := f `s! "{"\ntheorem cheat : False := sorry\ndef b := "}"\n', "FORBIDDEN_SORRY"),
        ("qual_s_bang_desync", 'def a := Foo.s! "{"\ntheorem cheat : False := sorry\ndef b := "}"\n', "FORBIDDEN_SORRY"),
        ("myplain_bang_desync", 'def myplain! (s : String) := s\ndef a := myplain!"{"\ntheorem cheat : False := sorry\ndef b := "}"\n', "FORBIDDEN_SORRY"),
        # Option A fail-closed rejections: FORBIDDEN_META_API
        ("spaced_m_interp", 'def x := m! "{(by native_decide : Bool)}"\n', "FORBIDDEN_META_API"),
        ("x1_zero_import_m_bang_shadow", 'def m! (s : String) : String := s\ndef x := m!"{"\ntheorem cheat : False := sorry\ndef y := "}"\n', "FORBIDDEN_META_API"),
        ("x2_zero_import_v_bang_shadow", 'def v! (s : String) : String := s\ndef x := v!"{"\ntheorem cheat : False := sorry\ndef y := "}"\n', "FORBIDDEN_META_API"),
        ("x3_trace_array_shadow", 'def trace : Array (String → String) := #[id]\ndef x := trace[0] "{"\ntheorem cheat : False := sorry\ndef y := "}"\n', "FORBIDDEN_META_API"),
        ("trace_bracket_interp", 'def x := trace[debug] "{sorry}"\n', "FORBIDDEN_META_API"),
        ("macro_trace_bracket_interp", 'def x := Macro.trace[debug] "{sorry}"\n', "FORBIDDEN_META_API"),
        ("trace_bracket_qmark", 'def bad := trace[foo?] "{(by sorry : Nat)}"\n', "FORBIDDEN_META_API"),
        ("r4_low_trace_18_segments", 'def bad := trace[a0.a1.a2.a3.a4.a5.a6.a7.a8.a9.a10.a11.a12.a13.a14.a15.a16.a17] "{(by sorry : Nat)}"\n', "FORBIDDEN_META_API"),
        ("trace_goal_bracket_interp", 'def x := trace_goal[debug] "{sorry}"\n', "FORBIDDEN_META_API"),
        ("aesop_trace_interp", 'def x := aesop_trace[opt] "{sorry}"\n', "FORBIDDEN_META_API"),
        ("aesop_trace_bang_interp", 'def x := aesop_trace![opt] "{sorry}"\n', "FORBIDDEN_META_API"),
        ("reportIssue_interp", 'def x := reportIssue! "{sorry}"\n', "FORBIDDEN_META_API"),
        ("reportDbgIssue_interp", 'def x := reportDbgIssue! "{sorry}"\n', "FORBIDDEN_META_API"),
        ("reportEMatchIssue_interp", 'def x := reportEMatchIssue! "{sorry}"\n', "FORBIDDEN_META_API"),
        ("throwError_interp", 'def x := throwError "{(by sorry : Nat)}"\n', "FORBIDDEN_META_API"),
        ("throwErrorAt_ident", 'def x := throwErrorAt tk "{sorry}"\n', "FORBIDDEN_META_API"),
        ("throwErrorAt_paren", 'def x := throwErrorAt (← getRef) "{sorry}"\n', "FORBIDDEN_META_API"),
        ("throwErrorAt_dotIdent", 'def bad := throwErrorAt .missing "{(by sorry : Nat)}"\n', "FORBIDDEN_META_API"),
        ("throwErrorAt_at_tk", 'def bad (tk : Syntax) := throwErrorAt @tk "{(by sorry : Nat)}"\n', "FORBIDDEN_META_API"),
        ("throwErrorAt_array_idx_bang", 'def bad (tk : Syntax) := throwErrorAt #[tk][0]! "{(by sorry : Nat)}"\n', "FORBIDDEN_META_API"),
        ("throwErrorAt_cdot", 'def f := (throwErrorAt · "{(by sorry : Nat)}")\n', "FORBIDDEN_META_API"),
        ("throwNamedError_interp", 'def x := throwNamedError lean.unknownIdentifier "{sorry}"\n', "FORBIDDEN_META_API"),
        ("throwNamedErrorAt_interp", 'def x := throwNamedErrorAt tk lean.unknownIdentifier "{sorry}"\n', "FORBIDDEN_META_API"),
        ("logNamedError_interp", 'def x := logNamedError lean.unknownIdentifier "{sorry}"\n', "FORBIDDEN_META_API"),
        ("logNamedErrorAt_interp", 'def x := logNamedErrorAt tk lean.unknownIdentifier "{sorry}"\n', "FORBIDDEN_META_API"),
        ("logNamedWarning_interp", 'def x := logNamedWarning lean.unknownIdentifier "{sorry}"\n', "FORBIDDEN_META_API"),
        ("logNamedWarningAt_interp", 'def x := logNamedWarningAt tk lean.unknownIdentifier "{sorry}"\n', "FORBIDDEN_META_API"),
        ("logNamedInfo_interp", 'def x := logNamedInfo lean.unknownIdentifier "{sorry}"\n', "FORBIDDEN_META_API"),
        ("modifyEnv_bare", 'def bad := modifyEnv id\n', "FORBIDDEN_META_API"),
        ("modifyEnv_french_quoted", 'def bad := Lean.«modifyEnv» id\n', "FORBIDDEN_META_API"),
        ("setEnv_bare", 'def bad := setEnv env\n', "FORBIDDEN_META_API"),
        ("addDecl_bare", 'def bad := addDecl d\n', "FORBIDDEN_META_API"),
        ("addAndCompile_bare", 'def bad := addAndCompile d\n', "FORBIDDEN_META_API"),
        # Option A fail-closed rejections: FORBIDDEN_DBG_TRACE
        ("dbg_trace_term_interp", 'def x := dbg_trace "{(by sorry : Nat)}"; 0\n', "FORBIDDEN_DBG_TRACE"),
        ("dbg_trace_term_desync", 'def x := dbg_trace "{ "/-" }"; 0\ntheorem cheat : False := sorry\n-- -/\n', "FORBIDDEN_DBG_TRACE"),
        ("dbg_trace_tactic_desync", 'example : True := by\n  dbg_trace "{"\n  trivial\ntheorem cheat : False := sorry\ndef b := "}"\n', "FORBIDDEN_SORRY"),
        ("idbg_forbidden", 'def x := idbg 1\n', "FORBIDDEN_DBG_TRACE"),
        # Option A fail-closed rejections: FORBIDDEN_META_SYNTAX
        ("local_syntax_interp", 'syntax "myinterp " interpolatedStr(term) : term\ndef a := myinterp "{sorry}"\n', "FORBIDDEN_META_SYNTAX"),
        ("local_syntax_noWs_contiguous_interp", 'syntax "my!" noWs interpolatedStr(term) : term\ndef a := my!"{(by sorry : Nat)}"\n', "FORBIDDEN_META_SYNTAX"),
        ("r5_low1_syntax_paren_noWs_interp", 'syntax (name := foo) "bar" (noWs) interpolatedStr(term) : term\ndef a := bar"{(by sorry : Nat)}"\n', "FORBIDDEN_META_SYNTAX"),
        ("r5_low1_syntax_guillemet_interpolatedStr", 'syntax "myg" «interpolatedStr»(term) : term\ndef a := myg "{(by sorry : Nat)}"\n', "FORBIDDEN_META_SYNTAX"),
        ("french_quoted_interpolatedStr_only", 'def f := Lean.Parser.«interpolatedStr»\n', "FORBIDDEN_META_SYNTAX"),
        ("binder_predicate_forbidden", 'binder_predicate x "foo" s:interpolatedStr(term) => True\n', "FORBIDDEN_META_SYNTAX"),
        ("term_parser_attr_forbidden", '@[term_parser] def evilParser := 0\n', "FORBIDDEN_META_SYNTAX"),
        ("tactic_parser_attr_forbidden", '@[tactic_parser] def evilParser := 0\n', "FORBIDDEN_META_SYNTAX"),
        ("run_cmd_forbidden", 'run_cmd pure ()\n', "FORBIDDEN_META_SYNTAX"),
        ("run_elab_forbidden", 'run_elab pure ()\n', "FORBIDDEN_META_SYNTAX"),
        ("run_meta_forbidden", 'run_meta pure ()\n', "FORBIDDEN_META_SYNTAX"),
        ("initialize_forbidden", 'initialize myRef : IO.Ref Nat ← IO.mkRef 0\n', "FORBIDDEN_META_SYNTAX"),
        ("notation3_forbidden", 'notation3 "foo" x => x\n', "FORBIDDEN_META_SYNTAX"),
        ("prelude_unreserve_s_bang", 'prelude\nimport Init.Prelude\ndef s! (s : String) := s\ndef a := s!"{"\ntheorem cheat := sorryAx False false\ndef b := "}"\n', "FORBIDDEN_META_SYNTAX"),
        ("notation_shadow_s_bang", 'local notation:max "s!" x:max => x\ndef a := s!"{"\ntheorem cheat : False := sorry\ndef b := "}"\n', "FORBIDDEN_META_SYNTAX"),
        ("prefix_shadow_s_bang_hex", 'prefix:max "\\x73!" => id\ndef a := s!"{"\ntheorem cheat : False := sorry\ndef b := "}"\n', "FORBIDDEN_META_SYNTAX"),
        ("prefix_shadow_s_bang_unicode", 'prefix:max "\\u0073!" => id\n', "FORBIDDEN_META_SYNTAX"),
        ("prefix_shadow_s_bang_raw", 'prefix:max r#"s!"# => id\n', "FORBIDDEN_META_SYNTAX"),
        ("prefix_shadow_s_bang_gap", 'prefix:max "s\\\n  !" => id\n', "FORBIDDEN_META_SYNTAX"),
        ("notation_unicode_shadow_s_bang", 'notation unicode("s!", "alt") x => x\n', "FORBIDDEN_META_SYNTAX"),
        ("notation_shadow_f_bang", 'local notation:max "f!" x:max => x\n', "FORBIDDEN_META_SYNTAX"),
        ("notation_shadow_println_bang", 'local notation:max "println!" x:max => x\n', "FORBIDDEN_META_SYNTAX"),
        ("local_plain_macro_desync", 'macro "myplain!" s:term : term => `($s)\ndef a := myplain!"{"\ntheorem cheat : False := sorry\ndef b := "}"\n', "FORBIDDEN_SORRY"),
        ("scoped_syntax_panic_override", 'namespace Hidden\nscoped syntax "panic!" interpolatedStr(term) : term\nend Hidden\ndef a : Unit := panic!"{"\ntheorem cheat : False := sorry\naxiom fake : False\ndef b : String := "}"\n', "FORBIDDEN_SORRY"),
        ("scoped_syntax_plain_fn", 'namespace Hidden\nscoped syntax "myplain" interpolatedStr(term) : term\nend Hidden\ndef myplain (s : String) : String := s\ndef a : String := myplain "{"\ntheorem cheat : False := sorry\ndef b : String := "}"\n', "FORBIDDEN_SORRY"),
        ("local_syntax_noWs_spaced_desync", 'syntax "my!" noWs interpolatedStr(term) : term\ndef a := my! "{"\ntheorem cheat : False := sorry\ndef b := "}"\n', "FORBIDDEN_SORRY"),
        ("r5_low1_syntax_paren_noWs_spaced_desync", 'syntax (name := foo) "bar" (noWs) interpolatedStr(term) : term\ndef a := bar "{"\ntheorem cheat : False := sorry\ndef b := "}"\n', "FORBIDDEN_SORRY"),
    )
    for name, src, exp_rule in cases:
        viols = scan_lean_hygiene(src, mode="impl")
        if not any(v.rule == exp_rule for v in viols):
            return False, "HYGIENE_VIOLATION", f"Adversarial lexer case `{name}` missed {exp_rule} (got {viols})", {}

    # 2. Pure-math & plain-string full-file desync attacks (must catch SORRY, AXIOM, NATIVE_DECIDE with zero spurious UNCLOSED_STRING)
    desync_fixtures = (
        (
            "s_double_brace",
            'def s : String := s!"{{ fst := "/-", snd := "" : String × String }.2}"\n'
            "theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- -/\n",
        ),
        (
            "spaced_s",
            'def x : String := s! "{ "/-" }"\n'
            "theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- -/\n",
        ),
        (
            "println",
            'def x : IO Unit := println! "{ "/-" }"\n'
            "theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- -/\n",
        ),
        (
            "panic_plain_desync",
            'def a : Unit := panic!"{"\n'
            "theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n"
            'def b : String := "}"\n',
        ),
        (
            "assert_plain_desync",
            'def a : Unit := assert!"{"\n'
            "theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n"
            'def b : String := "}"\n',
        ),
        (
            "eval_bang_plain_desync",
            '#eval!"{"\n'
            "theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n"
            'def b : String := "}"\n',
        ),
        (
            "qualified_throwError_desync",
            'def a := Lean.throwError "{"\n'
            "theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n"
            'def b : String := "}"\n',
        ),
        (
            "char_literal_lf_desync",
            "def a : Char × Char := ('\n','\"')\n"
            "theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n"
            "def b : Char := '\"'\n",
        ),
        (
            "char_literal_cr_desync",
            "def a : Char × Char := ('\r','\"')\n"
            "theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n"
            "def b : Char := '\"'\n",
        ),
        (
            "spaced_trace_bracket_desync",
            'def a : Nat := 0\ndef trace (_ : List Nat) (s : String) : String := s\n'
            'def x : String := trace [a] "{"\n'
            "theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n"
            'def y : String := "}"\n',
        ),
        (
            "spaced_macro_trace_desync",
            'def x : String := Macro.trace [a] "{"\n'
            "theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n"
            'def y : String := "}"\n',
        ),
        (
            "spaced_aesop_trace_desync",
            'def x : String := aesop_trace! [a] "{"\n'
            "theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n"
            'def y : String := "}"\n',
        ),
        # R10-D1 + \/ comment splitters (full-file desync locks, zero UNCLOSED_BLOCK_COMMENT/UNCLOSED_STRING)
        (
            "r10_d1_subtype_slashslash_dash",
            'def decoy := { x : Int //-x = 0 }\n'
            "theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- -/\n",
        ),
        (
            "r10_d1_subtype_slashslash_dashdash",
            'def decoy := { x : Nat //-- comment\n  x = 0 }\n'
            "theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- -/\n",
        ),
        (
            "r11_or_backslash_slash_dash",
            'def decoy := True \\/-False\n'
            "theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- -/\n",
        ),
        (
            "r11_or_backslash_slash_dashdash",
            'def decoy := True \\/-- comment\n False\n'
            "theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- -/\n",
        ),
        # R10-D2 + Σ' unconditional Init quote-suffix operators + 2-char '' (zero UNCLOSED_STRING)
        (
            "r10_d2_pprod_times_quote",
            'def d := True ×\'"\' "\n'
            'theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- "\n',
        ),
        (
            "r10_d2_psum_oplus_quote",
            'def d := True ⊕\'"\' "\n'
            'theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- "\n',
        ),
        (
            "r10_d2_getelem_rbrack_quote",
            'def d := [0][0]\'"\' "\n'
            'theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- "\n',
        ),
        (
            "r10_d2_psigma_sigma_quote",
            'def d := Σ\'"\' "\n'
            'theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- "\n',
        ),
        (
            "r10_d2_set_image_double_quote",
            'def d := id \'\'"\' "\n'
            'theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- "\n',
        ),
        # Scientific number literal desyncs (decimalNumberFn vs fieldIdxFn) & Wave r12 quote/Dioph desyncs
        (
            "r11_sci_num_raw_desync",
            'def d := 1e0r"\\"\n'
            'theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- "\n',
        ),
        (
            "r12_d1_pprod_qq_dquote",
            'def d := True ×\'\'"\'\n'
            'theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- "\n',
        ),
        (
            "r12_d1_psum_qq_dquote",
            'def d := True ⊕\'\'"\'\n'
            'theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- "\n',
        ),
        (
            "r12_d1_getelem_qq_dquote",
            'def d := [0][0]\'\'"\'\n'
            'theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- "\n',
        ),
        (
            "r12_d1_pprod_qq_guillemet",
            'def d := True ×\'\'«\'\n'
            'theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- »\n',
        ),
        (
            "r12_d1_pprod_qqq_str",
            'def d := True ×\'\'\'"\' "\n'
            'theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- "\n',
        ),
        (
            "r12_d1_pprod_qqqq_dquote",
            'def d := True ×\'\'\'\'"\'\n'
            'theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- "\n',
        ),
        (
            "r12_dioph_1e0_raw_desync",
            'def d := D.1e0r"\\"\n'
            'theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- "\n',
        ),
    )
    for dname, dsrc in desync_fixtures:
        drules = {v.rule for v in scan_lean_hygiene(dsrc, mode="impl")}
        if not {"FORBIDDEN_SORRY", "FORBIDDEN_AXIOM", "FORBIDDEN_NATIVE_DECIDE"}.issubset(drules):
            return False, "HYGIENE_VIOLATION", f"Full-file desync `{dname}` missed violations: {drules}", {}
        if "UNCLOSED_STRING" in drules or "UNCLOSED_BLOCK_COMMENT" in drules:
            return False, "HYGIENE_VIOLATION", f"Full-file desync `{dname}` emitted spurious unclosed error: {drules}", {}

    # Literal '\n' inside Char literal advances line counter accurately
    lf_line_viols = [
        v for v in scan_lean_hygiene("def nl : Char := '\n'\ntheorem bad : False := sorry\n", mode="impl")
        if v.rule == "FORBIDDEN_SORRY"
    ]
    if len(lf_line_viols) != 1 or lf_line_viols[0].line != 3:
        return False, "HYGIENE_VIOLATION", f"Literal-newline char literal miscomputed line number: {lf_line_viols}", {}

    # CLI --hygiene must reject invalid UTF-8 / NUL bytes with exit code 1
    tmp = _sandbox_dir("shannon_c7_st17_")
    try:
        bad_bytes = tmp / "bad_utf8_nul.lean"
        bad_bytes.write_bytes(b"def x := 1\n\xff\xfe\x00\n")
        out_h = run_subprocess_safe(
            ["python3", "-B", str(ctx.verify_dir / "cross_check.py"), "--hygiene", str(bad_bytes)],
            cwd=ctx.verify_dir,
            timeout=20,
        )
        if out_h.returncode != 1:
            return False, "HYGIENE_VIOLATION", f"--hygiene accepted invalid UTF-8/NUL bytes (rc={out_h.returncode})", {}
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    # 3. Pure-math positive-compatibility clean controls (MUST return [])
    clean_cases = (
        ("primes", "def x' := 1\ndef y'' := x' + 1\n"),
        ("empty_block_comment", "/- -/\ndef a := 1\n"),
        ("empty_doc_comment", "/---/\ndef a := 1\n"),
        ("empty_moddoc_comment", "/-!-/\ndef a := 1\n"),
        ("nested_block", "/- /- -/ -/\ndef b := 2\n"),
        ("interp_clean", 'def msg := s!"E2E_CONST c7_lower_num={ShannonC7.c7_lower_num}"\n'),
        ("interp_escaped_brace", 'def msg := s!"\\{ sorry }"\n'),
        ("interp_triple_bs_brace", 'def msg := s!"\\\\\\{sorry}"\n'),
        ("panic_brace_clean", 'def f : String := panic!"unexpected { in json"\n'),
        ("panic_spaced_brace_clean", 'def f : String := panic! "unexpected { in json"\n'),
        ("panic_sorry_literal_clean", 'def f : String := panic!"{sorry}"\n'),
        ("assert_brace_clean", 'def f : Nat := assert!"{"; debug_assert!"{"; 0\n'),
        ("eval_bang_brace_clean", '#eval!"unexpected { in json"\n'),
        ("log_plain_clean", 'def x := logError "{"; logInfo "{"; logWarning "{"; IO.println "{"\n'),
        ("spaced_bang_not_interp", 'def x := s ! "{sorry}"\ndef y := foo ! "{sorry}"\ndef z := ! "{sorry}"\ndef w := get! "{"\n'),
        ("println_raw_clean", 'def x := println! r"{"\n'),
        ("custom_plain_brace_clean", 'def x := myplain!"unexpected { in json"\n'),
        ("spaced_s_clean", 'def x : String := s! "ok {42}"\n'),
        ("println_clean", 'def x : IO Unit := println! "ok {42}"\n'),
        ("char_literal_lf_cr_clean", "def nl : Char := '\n'\ndef cr : Char := '\r'\ndef ok : Nat := 1\n"),
        ("spaced_trace_bracket_clean", 'def a : Nat := 0\ndef trace (_ : List Nat) (s : String) : String := s\ndef x : String := trace [a] "unexpected {"\n'),
        ("isIdRest_qmark_bang_clean", "def sorry? : Nat := 1\ndef axiom? : Nat := 2\ndef admit? : Nat := 3\ndef unsafe! : Nat := 4\n"),
        ("unicode_ascii_mixed_ident_clean", "def x₁sorry : Nat := 1\n"),
        ("r5_d1_cdot_plain_clean", 'def f := foo · "unexpected {"\n'),
        # Option A pure-math positive controls
        ("opt_a_infixl_strongProd_clean", 'infixl:70 " ⊠ " => strongProd\n'),
        ("opt_a_postfix_factorial_clean", 'postfix:max "!" => Nat.factorial\n'),
        (
            "opt_a_ordinary_notations_clean",
            'infix:65 " ⊕ " => myAdd\ninfixr:80 " ⊗ " => myMul\nprefix:75 "¬¬" => myNeg\n'
            'postfix:max "†" => myAdj\nnotation "⟦" x "⟧" => eval x\nlocal notation "★" => (0 : Nat)\n',
        ),
        ("opt_a_matrix_trace_clean", "def tr (A B : Matrix) := Matrix.trace A + M.trace + trace B\n"),
        (
            "opt_a_french_quoted_meta_clean",
            'def «by» (x : Nat) := x\ndef «s!» (s : String) := s\ndef «f!» (s : String) := s\n'
            'def «println!» (s : String) := s\ndef «dbg_trace» (s : String) := s\ndef «idbg» := 0\n'
            'def «syntax» := 0\ndef «macro» := 0\ndef «macro_rules» := 0\ndef «elab» := 0\ndef «elab_rules» := 0\n'
            'def «m!» (s : String) := s\ndef «v!» (s : String) := s\ndef «trace» := 0\n'
            'def «throwError» (s : String) := s\ndef «throwErrorAt» := 0\ndef «logNamedError» := 0\n'
            'def ok1 := «s!» "{ sorry }"\ndef ok2 := «dbg_trace» "{ sorry }"\ndef ok3 := «throwError» "{ sorry }"\n',
        ),
        (
            "opt_a_name_lit_and_qual_s_bang_clean",
            'def ok1 := f `s! "{ sorry }"\ndef ok2 := f ``s! "{ sorry }"\n'
            'def ok3 := Foo.s! "{ sorry }"\ndef ok4 := f .s! "{ sorry }"\n'
            'def ok5 := (x).s! "{ sorry }"\ndef ok6 := a[0].s! "{ sorry }"\n'
            'def ok7 := "hi".s! "{ sorry }"\ndef ok8 := Foo.r"ok"\n',
        ),
        (
            "opt_a_myplain_and_println_paren_clean",
            'def myplain! (s : String) := s\ndef ok1 := myplain!"{ sorry }"\n'
            'def ok2 := println! ("{ sorry }")\ndef ok3 := println! r"{"\n',
        ),
        (
            "opt_a_doc_line_comment_and_raw_hashes_clean",
            '/-- -- -/\n-/\ndef r1 := r##"a""##\ndef r2 := r##"a"#""##\n'
            "def ids := x' + hB'card + x₁ + xᵥ + xₖ + compute_degree! + find?\n",
        ),
        (
            "opt_a_prefix_param_clean",
            'def foo (prefix : String) := if prefix == "s!" then 1 else 0\n'
            'def bar (\n  prefix : String\n) := if\n  prefix == "s!" then 1 else 0\n',
        ),
        # Wave r9 + R10-NEW-1/2/3 pure-math clean controls
        (
            "r9_r2_n1_prefix_ne_and_rhs_clean",
            'def isNotS (prefix : String) : Bool :=\n  prefix != "s!"\n'
            'notation:max "MYFMT" x => s!"{x}"\nnotation:max "MYTAG" => "s!"\n',
        ),
        (
            "r9_d1_range_bitvec_raw_interp_clean",
            'def ok1 := *...r"\\"\ndef ok2 := 0#r"\\"\n'
            'def ok3 := *...s!"{ let _ := "/-"; "" }"\n',
        ),
        (
            "r9_d3_doc_non_ascii_ws_clean",
            '/-- \u00a0 -- -/\ndef ok1 : Nat := 0\n/-! \u00a0 -- -/\ndef ok2 : Nat := 1\n',
        ),
        (
            "r9_r1_d2_non_attr_meta_clean",
            'def tactic : Nat := 1\ndef «tactic» : Nat := 2\ndef formatter : Nat := 3\n'
            '@[deprecated tactic] def f := 0\n@[inherit_doc tactic] def g := 0\n'
            '@[simp [tactic]] def h := 0\ndef lst := @ [tactic]\ndef lst2 := Foo.attribute [tactic]\n',
        ),
        # Wave r11 pure-math clean controls (notation atoms, balanced braces, // & <- & \/, Init quote ops & char literals, sci nums, Mathlib →r, non-attr init)
        (
            "r11_safe_notation_atoms_and_balanced_braces_clean",
            'notation:max "for" x => x\nnotation:max "bar" x => x\nnotation:max "a0r" x => x\n'
            'notation:max "a!r" x => x\nnotation:max "foo_s!" x => x\nnotation:max "a.s!" x => x\n'
            'notation:max "a.r" x => x\npostfix:max "⁻¹" => Inv.inv\n'
            'notation "{" x " | " p "}" => Set.mk x p\nnotation "{" "{" x "}" "}" => x\n',
        ),
        (
            "r11_slashslash_leftarrow_or_clean",
            'def negZero := { x : Int //-x = 0 }\ndef subC := { x : Nat //-- comment\n  x = 0 }\n'
            'def subBlock := { x : Nat ///- block -/\n  x = 0 }\ndef lc := <--- comment\n'
            'def orC := True \\/-- comment\n False\n'
            'def okS : String := s!"{ Id.run do let x <--pure 0; pure x }"\n',
        ),
        (
            "r11_init_quote_ops_and_char_literals_clean",
            'def ok1 := True ×\'"\' "\ndef ok2 := [0][0]\'"\' "\ndef ok3 := id \'\'"\' "\n'
            'def ok4 := f \'\'\'"\'\ndef ok5 := 0 # \'a\'\ndef ok6 : Char := \'"\'\n'
            "def ok7 := ('\"', c='\"', '\\n', '\\'', 'a')\n",
        ),
        (
            "r11_sci_num_fieldidx_reliso_and_non_attr_init_clean",
            'def f1 := x.1.2\ndef f2 := x.1.e0\ndef f3 := 1..2\ndef f4 := 3.258805369885\n'
            'def f5 := α →r β\ndef f6 := s < r"foo"\ndef f7 := α → r"foo"\n'
            'def init : Nat := 0\ndef «init» : Nat := 1\n'
            '@[deprecated init] def g1 := init\n@[simp [init]] def g2 := init\n',
        ),
        # Wave r12 pure-math clean controls (R11-D1 Init ×''"', scoped[MyNs], c='"', by norm_num/positivity, D.1.2, G ≃g H, balanced ()/[]/{} notation, pure-math attrs)
        (
            "r12_pure_math_controls_clean",
            'instance : Coe Char Prop := ⟨fun _ => True⟩\n'
            'def q1 := True ×\'\'"\'\ndef q2 := True ⊕\'\'"\'\ndef q3 := [0][0]\'\'"\'\n'
            'def q4 := True ×\'\'\'"\' "\ndef q5 := True ×\'\'\'\'"\'\n'
            "def q6 := ('\"', c='\"')\n"
            'scoped[MyNs] infixl:70 " ⊠ " => strongProd\n'
            'theorem t_nn : (1 : Nat) + 1 = 2 := by norm_num\n'
            'theorem t_pos (x : Nat) : 0 ≤ x := by positivity\n'
            'def f_idx := x.1.2 + x.1.e0 + D.1.2 + D.1.e0 + D.foo\n'
            'def f_dstr := (D.1.r"a\\"b", D.s!"{")\n'
            'def f_ops := (G ≃g H, a < rest, a < r1.2, a[0]_foo, 0#a, 0#s!"ok")\n'
            'notation "(" "[" "{" x "}" "]" ")" => x\n'
            '@[simp, ext] theorem t_simp : True := trivial\n'
            '@[local simp, scoped gcongr] theorem t_gc : True := trivial\n'
            '@[grind .] theorem t_gr : True := trivial\n'
            'attribute [-simp] t_simp\n',
        ),
        # Wave r13 pure-math clean controls (#v[1, 2], #v[], x=Quot.sound, 0#a, 0#8, 0#s!"ok", spaced ~m, x=Q/QL/Q0/Q1.2, a<r1e+0, a<r1.2.3)
        (
            "r13_pure_math_controls_clean",
            'def v1 : Vector Nat 2 := #v[1, 2]\ndef v0 : Vector Nat 0 := #v[]\n'
            'def eq_q := x=Quot.sound\ndef bv_ok := (0#a, 0#8, 0#s!"ok", 0#s! "ok", 0#v[1, 2])\n'
            'def sp_ok := (m ~m n, x = Q, x=Q, x=QL, x=Q0, x=Q1.2, a < r1e+0, a < r1.2.3)\n',
        ),
        # Wave r14 pure-math clean controls (R13-R2-D1 x.1_sorry companion FP fix, x.1 / x |>.1 / |>.s! / |>.r#", *...s! / *...r", inductive | prefix & fun notation => "s!")
        (
            "r14_pure_math_controls_clean",
            'infixl:70 "_sorry" => fun (_ : Nat) (_ : Nat) => (0 : Nat)\n'
            'def p0 : Nat × Nat := (0, 0)\n'
            'def p1 : Nat := p0.1_sorry 0\n'
            'def p2 : Nat := p0.1 + (0, 0).1 + (p0 |>.1) + (p0 |>.2)\n'
            'def p3 := *...s!"{ let _ := "/-"; "" }"\n'
            'def p4 := *...r"\\"\n'
            'def p5 := p0 |>.s! "{ \\\\"\n'
            'def p6 := p0 |>.r#"\\" "\n'
            'inductive U where\n  | prefix\n  | notation (x : Nat) : U\n  | bar\n'
            'def f_not := fun notation => "s!"\n'
            'def f_let := let prefix : String := "s!"; prefix\n',
        ),
    )
    for name, src in clean_cases:
        viols = scan_lean_hygiene(src, mode="impl")
        if viols:
            return False, "HYGIENE_VIOLATION", f"Clean lexer edge case `{name}` false-positived: {viols[0]}", {}

    # Live repo positive-compatibility check: 0 Option A FPs on real `e2e_audit.lean` & all `ShannonC7/**/*.lean`
    import cross_check as _cc
    audit_path = ctx.verify_dir / "e2e_audit.lean"
    audit_src_live, audit_enc_viols = _cc.read_lean_source_strict(audit_path, display_path="verify/e2e_audit.lean")
    if audit_src_live is None or audit_enc_viols:
        return False, "HYGIENE_VIOLATION", f"Live read of verify/e2e_audit.lean failed: {audit_enc_viols}", {}
    audit_viols_live = scan_lean_hygiene(audit_src_live, path="verify/e2e_audit.lean", mode="audit")
    if audit_viols_live:
        return False, "HYGIENE_VIOLATION", f"Live Option A scan of verify/e2e_audit.lean false-positived: {audit_viols_live[:2]}", {}
    shannon_dir = ctx.project_dir / "ShannonC7"
    if shannon_dir.is_dir():
        _opt_a_rules = {"FORBIDDEN_DBG_TRACE", "FORBIDDEN_META_SYNTAX", "FORBIDDEN_META_API", "UNCLOSED_BLOCK_COMMENT", "UNCLOSED_STRING"}
        for lf in sorted(shannon_dir.rglob("*.lean")):
            lsrc, _ = _cc.read_lean_source_strict(lf, display_path=str(lf.relative_to(ctx.project_dir)))
            if lsrc is not None:
                lviols = [v for v in scan_lean_hygiene(lsrc, path=str(lf), mode="impl") if v.rule in _opt_a_rules]
                if lviols:
                    return False, "HYGIENE_VIOLATION", f"Option A FP on real pure-math file {lf.name}: {lviols[0]}", {}

    # 4. Option A fail-closed rejection suite (former Option-B metaprogramming controls + ALL Wave r8 bypasses)
    option_a_reject_cases = (
        # Former Option-B clean controls converted under authorized Option A policy (SCOPE.md:43-44)
        ("opt_a_qualified_throwError_rejected", "impl", 'def x := Lean.throwError "unexpected {"\n', {"FORBIDDEN_META_API"}),
        ("opt_a_throwError_rejected", "impl", 'def x := throwError "ok {42}"\n', {"FORBIDDEN_META_API"}),
        ("opt_a_throwErrorAt_paren_foo_rejected", "impl", 'def ok := throwErrorAt tk (foo "{")\n', {"FORBIDDEN_META_API"}),
        ("opt_a_throwErrorAt_pipe_rejected", "impl", 'import Lean\nopen Lean\ndef ok (tk : Syntax) : CoreM Unit :=\n  throwErrorAt tk <| "{ sorry }"\n', {"FORBIDDEN_META_API"}),
        ("opt_a_dbg_trace_tactic_rejected", "impl", 'example : True := by\n  dbg_trace "{"\n  trivial\n', {"FORBIDDEN_DBG_TRACE"}),
        ("opt_a_dbg_trace_term_rejected", "impl", 'def x := dbg_trace "{ "/-" }"; 0\n', {"FORBIDDEN_DBG_TRACE"}),
        ("opt_a_dbg_trace_by_skip_rejected", "impl", 'theorem ok0 : True := by\n  skip\n  dbg_trace "{ sorry }"\n  trivial\n', {"FORBIDDEN_DBG_TRACE"}),
        ("opt_a_scoped_syntax_rejected", "impl", 'namespace Hidden\nscoped syntax "panic!" interpolatedStr(term) : term\nend Hidden\ndef a : Unit := panic!"unexpected {"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("opt_a_scoped_macro_rejected", "impl", 'namespace A\nscoped macro "m" s:interpolatedStr(term) : term => `(0)\nend A\ndef x := m "{"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("opt_a_r8_d3a_global_syntax_rejected", "impl", 'def throwErrorAt (a b c : String) : String := a\nsyntax "myinterp" interpolatedStr(term) : term\ndef ok : Nat := dbg_trace "{ 0 }"; 0\n', {"FORBIDDEN_DBG_TRACE", "FORBIDDEN_META_SYNTAX", "FORBIDDEN_META_API"}),
        ("opt_a_r8_d4_open_in_semi_rejected", "impl", 'theorem ok0 : True := by\n  skip\n  dbg_trace "{"\n  trivial\nnamespace Foo\nscoped syntax "myinterp" interpolatedStr(term) : term\nend Foo\nopen Foo in\ndef ok1 : String := myinterp "{ 0 }"\n', {"FORBIDDEN_DBG_TRACE", "FORBIDDEN_META_SYNTAX"}),
        # Preserved unclosed & extern locks
        ("r4_d2_unclosed_block_impl", "impl", 'def a : Nat := dbg_trace "{ 1 }"\ndef b : Nat := 2\n/- unclosed comment\n', {"FORBIDDEN_DBG_TRACE", "UNCLOSED_BLOCK_COMMENT"}),
        ("r4_d2_unclosed_str_impl", "impl", 'def a : Nat := dbg_trace "{ 1 }"\ndef b : Nat := 2\ndef c := "unclosed\n', {"FORBIDDEN_DBG_TRACE", "UNCLOSED_STRING"}),
        ("r4_d2_unclosed_ident_impl", "impl", 'def a : Nat := dbg_trace "{ 1 }"\ndef b : Nat := 2\ndef «unclosed := 3\n', {"FORBIDDEN_DBG_TRACE", "UNCLOSED_IDENT"}),
        ("r4_d2_unclosed_sinterp_impl", "impl", 'def a : Nat := dbg_trace "{ 1 }"\ndef b : Nat := 2\ndef c : String := s!"unclosed\n', {"FORBIDDEN_DBG_TRACE", "UNCLOSED_STRING"}),
        ("r4_d2_unclosed_raw_impl", "impl", 'def a : Nat := dbg_trace "{ 1 }"\ndef b : Nat := 2\ndef c : String := r#"unclosed\n', {"FORBIDDEN_DBG_TRACE", "UNCLOSED_STRING"}),
        ("r4_d2_foo_bang_unclosed_impl", "impl", 'def a := foo!"{ 1 }"\ndef b : Nat := 2\n/- unclosed comment\n', {"UNCLOSED_BLOCK_COMMENT"}),
        ("r4_d2_unclosed_block_audit", "audit", 'import ShannonC7.Main\ndef a : Nat := dbg_trace "{ 1 }"\ndef b : Nat := 2\n/- unclosed block comment\n', {"FORBIDDEN_DBG_TRACE", "UNCLOSED_BLOCK_COMMENT"}),
        ("r5_zd5_rres_ctx_attr_extern", "impl", 'def y : Nat := 0\n@[\nextern] def f : Nat := 0\n', {"FORBIDDEN_EXTERN"}),
        ("r7_two_unknown_bang_macro_upgrade", "impl", 'macro "bar!" s:interpolatedStr(term) : term => `(s!$s)\ndef a := foo!"{"\ndef bad := bar!"{ (by sorry : Nat) }"\n', {"FORBIDDEN_META_SYNTAX"}),
        # Wave r8 Section 2 bypasses (R8-R1-D1..D6, R8-R2-D1..D3, R8-D1..D5)
        ("r8_r1_d1_have_if_dbg_trace", "impl", 'theorem t : True := by\n  have _ : if True then dbg_trace "{ "/-" }"; True else True := trivial\n  trivial\ntheorem cheat : False := sorry\n-- -/\n', {"FORBIDDEN_DBG_TRACE"}),
        ("r8_r1_d1_match_if_dbg_trace", "impl", 'theorem t : True := by\n  match if True then dbg_trace "{ "/-" }"; 0 else 0 with\n  | _ => trivial\ntheorem cheat : False := sorry\n-- -/\n', {"FORBIDDEN_DBG_TRACE"}),
        ("r8_r1_d1_suffices_if_dbg_trace", "impl", 'theorem t : True := by\n  suffices if True then dbg_trace "{ "/-" }"; True else True from trivial\n  trivial\ntheorem cheat : False := sorry\n-- -/\n', {"FORBIDDEN_DBG_TRACE"}),
        ("r8_r1_d1_let_if_dbg_trace", "impl", 'theorem t : True := by\n  let x : if True then dbg_trace "{ "/-" }"; Nat else Nat := 0\n  trivial\ntheorem cheat : False := sorry\n-- -/\n', {"FORBIDDEN_DBG_TRACE"}),
        ("r8_r1_d1_specialize_if_dbg_trace", "impl", 'theorem t (h : Nat → True) : True := by\n  specialize h <| if True then dbg_trace "{ "/-" }"; 0 else 0\n  exact h\ntheorem cheat : False := sorry\n-- -/\n', {"FORBIDDEN_DBG_TRACE"}),
        ("r8_r1_d1_lambda_dbg_trace", "impl", 'def f := λ _ => dbg_trace "{ "/-" }"; 0\ntheorem cheat : False := sorry\n-- -/\n', {"FORBIDDEN_DBG_TRACE"}),
        ("r8_r2_d1_multiline_exact_plus_dbg_trace", "impl", 'theorem t : Nat := by\n  exact 0 +\n    dbg_trace "{ "/-" }"; 0\ntheorem cheat : False := sorry\n-- -/\n', {"FORBIDDEN_DBG_TRACE"}),
        ("r8_r2_d1_multiline_let_dbg_trace", "impl", 'theorem t : True := by\n  exact let _ := 0;\n    dbg_trace "{ "/-" }"; trivial\ntheorem cheat : False := sorry\n-- -/\n', {"FORBIDDEN_DBG_TRACE"}),
        ("r8_r2_d1_multiline_fun_dbg_trace", "impl", 'def f : Nat → Nat := by\n  exact fun _ =>\n    dbg_trace "{ "/-" }"; 0\ntheorem cheat : False := sorry\n-- -/\n', {"FORBIDDEN_DBG_TRACE"}),
        ("r8_d1_guillemet_by_dbg_trace", "impl", 'def «by» (x : Nat) := x\ndef bad := «by» (dbg_trace "{ "/-" }"; 0)\ntheorem cheat : False := sorry\n-- -/\n', {"FORBIDDEN_DBG_TRACE"}),
        ("r8_r1_d2_cases_dbg_trace", "impl", 'theorem t (b : Bool) : True := by\n  cases b <;> dbg_trace "{"\n  all_goals trivial\n', {"FORBIDDEN_DBG_TRACE"}),
        ("r8_r1_d2_macro_foo_bang", "impl", 'macro "foo!" s:str : term => `($s)\ndef x := foo!"{"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r8_r1_d2_shadowed_throwErrorAt", "impl", 'def throwErrorAt (a b : String) := a\ndef x := throwErrorAt "a" "{"\n', {"FORBIDDEN_META_API"}),
        ("r8_r1_d3_elab_interp", "impl", 'elab "myE" s:interpolatedStr(term) : term => pure default\ndef bad := myE "{ sorry }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r8_r1_d3_elab_rules", "impl", 'elab_rules | `(myE $s) => pure default\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r8_r1_d3_symbol_macro_star", "impl", 'macro "★" s:interpolatedStr(term) : term => `(s!$s)\ndef bad := ★ "{ sorry }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r8_r1_d3_symbol_macro_arrow", "impl", 'macro "~>" s:interpolatedStr(term) : term => `(s!$s)\ndef bad := ~> "{ sorry }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r8_r1_d3_param_macro_num", "impl", 'macro "myM" _x:num s:interpolatedStr(term) : term => `(s!$s)\ndef bad := myM 0 "{ sorry }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r8_r1_d4_syntax_max_in_throwErrorAt", "impl", 'import Lean\nopen Lean\nlocal syntax:max "myref" "in" ident : term\ndef bad : CoreM Unit := throwErrorAt myref in foo "{ (by sorry : Nat) }"\n', {"FORBIDDEN_META_SYNTAX", "FORBIDDEN_META_API"}),
        ("r8_d4_syntax_max_where_throwNamedErrorAt", "impl", 'import Lean\nopen Lean\nlocal syntax:max "myref" "where" ident : term\ndef bad : CoreM Unit := throwNamedErrorAt myref where foo lean.foo "{ (by sorry : Nat) }"\n', {"FORBIDDEN_META_SYNTAX", "FORBIDDEN_META_API"}),
        ("r8_r1_d5_open_in_variable_in_macro", "impl", 'namespace A\nscoped macro "myS" s:interpolatedStr(term) : term => `(s!$s)\nend A\nopen A in\nvariable (x : Nat) in\ndef bad := myS "{ sorry }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r8_d5_universe_in_macro", "impl", 'namespace A\nscoped macro "myS" s:interpolatedStr(term) : term => `(s!$s)\nend A\nopen A in\nuniverse u in\ndef bad := myS "{ sorry }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r8_r1_d6_nested_dbg_trace_unclosed", "impl", 'def bad := dbg_trace "{ "/-" ++ (dbg_trace "{ 0 }"; "") }"\ntheorem cheat : False := sorry\n-- -/\n', {"FORBIDDEN_DBG_TRACE"}),
        ("r8_r2_d2_raw_quote_shift_dbg_trace", "impl", 'theorem t : True := by\n  dbg_trace "{"\n  trivial\ndef a := r" } \\" -- " /-\ndef b := dbg_trace "{ (by sorry : Nat) }"; 0\n-- -/\n', {"FORBIDDEN_DBG_TRACE"}),
        ("r8_d2_have_semi_dbg_trace", "impl", 'theorem t : True := by\n  have h : True := trivial; dbg_trace "{"\n  trivial\ndef z := " } "\n', {"FORBIDDEN_DBG_TRACE"}),
        # Wave r9 + R10-NEW-1/2/3 Section 2 bypass locks
        ("r9_d1_sameline_def_notation_s", "impl", 'def dummy : Nat := 0 notation:max (priority := high + 1) "s!" x => (x : String)\ndef a := s!"{ \\\\"\ntheorem cheat : False := sorry\n-- " }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r9_d1_sameline_section_prefix_s", "impl", 'section S prefix:max "s!" => fun (_ : String) => ()\ndef a := s! "{ ) /-"\ntheorem cheat : False := sorry\n-- -/ }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r9_d1_with_weak_ns_infixl_s", "impl", 'with_weak_namespace Foo infixl:65 "s!" => fun (_ : Nat) (s : String) => s\ndef x := 0 s!"{"\ntheorem cheat : False := sorry\ndef z := " } "\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r9_d1_sameline_open_infixl_println", "impl", 'open Nat infixl:65 "println!" => fun (_ : Nat) (s : String) => s\ndef x := 0 println!"{"\ntheorem cheat : False := sorry\ndef z := " } "\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r9_d1_sameline_ns_notation_f", "impl", 'namespace A notation:65 a "f!" b:66 => (b : String)\ndef x := 0 f!"{"\ntheorem cheat : False := sorry\ndef z := " } "\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r9_d1_name_lemma_notation_s", "impl", 'notation:max (name := lemma) (priority := high + 1) "s!" x => (x : String)\ndef a := s!"{ \\\\"\ntheorem cheat : False := sorry\n-- " }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r9_d1_lhs_var_lemma_notation_s", "impl", 'notation:65 lemma "s!" b:66 => (b : String)\ndef x := 0 s!"{"\ntheorem cheat : False := sorry\ndef z := " } "\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r9_d1_sameline_unicode_alt_f", "impl", 'def dummy : Nat := 0 notation:max unicode("★", "f!") x => (x : String)\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r9_d1_qual_fun_and_french_fun_notation", "impl", 'def x := Foo.fun notation:max "s!" x => x\nnamespace «fun» notation:max "f!" x => x\n', {"FORBIDDEN_META_SYNTAX"}),
        # R10-NEW-1: custom notation lexer-desync atoms
        ("r10_new1_custom_desync_atoms", "impl", 'prefix:max "*--" => id\nprefix:max "*-" => id\nprefix:max "*/" => id\nprefix:max "*\\"" => id\nprefix:max "*r" => id\nprefix:max "*r#" => id\nprefix:max "*s!" => id\nprefix:max "*s" => id\nprefix:max "*." => id\nprefix:max "*`" => id\nprefix:max "*«" => id\n', {"FORBIDDEN_META_SYNTAX"}),
        # R9-R1-D2 & R10-NEW-2: @[tactic], @[«tactic»], @[«macro»], attribute [tactic], mkElabAttribute & simproc/cpass hooks
        ("r9_r1_d2_attr_tactic", "impl", '@[tactic Lean.Parser.Tactic.skip]\ndef evil := 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r9_r1_d2_local_scoped_attr_tactic", "impl", '@[local tactic Lean.Parser.Tactic.skip]\ndef e1 := 0\n@[scoped tactic Lean.Parser.Tactic.skip]\ndef e2 := 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r9_r1_d2_attribute_and_comma_tactic", "impl", 'attribute [tactic Lean.Parser.Tactic.skip] evil\n@[simp [foo], local tactic Lean.Parser.Tactic.skip]\ndef e3 := 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r10_new2_french_quoted_attr_tactic_macro", "impl", '@[«tactic» Lean.Parser.Tactic.skip]\ndef e1 := 0\n@[«macro» Lean.Parser.Tactic.skip]\ndef e2 := 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r9_r1_d2_builtin_elabs_and_inductive_elab", "impl", '@[builtin_tactic foo] def a := 0\n@[builtin_term_elab bar] def b := 0\n@[builtin_macro baz] def c := 0\n@[inductive_elab qux] def d := 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r9_r1_d2_grind_try_tactic", "impl", '@[grind_tactic foo] def a := 0\n@[try_tactic bar] def b := 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r9_r1_d2_simproc_cbv_cpass", "impl", '@[sym_simproc foo] def a := 0\n@[sym_dsimproc bar] def b := 0\nsimproc myS (_) := pure .continue\ndsimproc myDS (_) := pure .continue\ncbv_simproc myCS (_) := pure .continue\n@[cpass] def p := 0\n', {"FORBIDDEN_META_SYNTAX"}),
        # R9-D1 & R10-NEW-3: *... / ... / <... / 0# / # / /. / Term.proj / Term.dotIdent / `r"..."
        ("r9_d1_range_rio_s_interp", "impl", 'def bad := *...s!"{ (by sorry : Nat) } { let _ : 1 = 1 := (by native_decide); (0 : Nat) }"\n', {"FORBIDDEN_SORRY", "FORBIDDEN_NATIVE_DECIDE"}),
        ("r9_d1_range_dots_f_println", "impl", 'def bad1 := ""...f!"{ (by sorry : Nat) }"\ndef bad2 := ""<...println!"{ (by admit : Nat) }"\n', {"FORBIDDEN_SORRY", "FORBIDDEN_ADMIT"}),
        ("r9_d1_range_raw_backslash", "impl", 'def decoy := *...r"\\"\ntheorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- "\n', {"FORBIDDEN_SORRY", "FORBIDDEN_AXIOM", "FORBIDDEN_NATIVE_DECIDE"}),
        ("r9_d1_bitvec_hash_interp_and_raw", "impl", 'def bad1 := 0#s!"{ (by sorry : Nat) }"\ndef decoy := 0#r"\\"\naxiom fake : False\n-- "\n', {"FORBIDDEN_SORRY", "FORBIDDEN_AXIOM"}),
        ("r9_d1_prefix_hash_s_interp", "impl", 'prefix:max "#" => fun (x : String) => x\ndef bad : String := #s!"{ (by sorry : Nat) }"\n', {"FORBIDDEN_SORRY"}),
        ("r10_new3_rat_slash_dot_interp_and_raw", "impl", 'def bad1 := 0/.s!"{ (by sorry : Nat) }"\ndef decoy := 0/.r"\\"\naxiom fake : False\n-- "\n', {"FORBIDDEN_SORRY", "FORBIDDEN_AXIOM"}),
        ("r10_new3_term_proj_and_dotident_inversions", "impl", 'def a := "hi".r"a\\"b"\ntheorem c1 : False := sorry\n-- "\ndef b := ⟨0⟩.r"a\\"b"\naxiom f1 : False\n-- "\ndef c := 0x0.r"a\\"b"\ndef d := (.s!"{")\ntheorem c2 : False := by admit\ndef z := " } "\n', {"FORBIDDEN_SORRY", "FORBIDDEN_AXIOM", "FORBIDDEN_ADMIT"}),
        ("r10_new3_backtick_r_raw_inversion", "impl", 'def a := f `r"a\\"b"\ntheorem cheat : False := sorry\n-- "\n', {"FORBIDDEN_SORRY"}),
        # R9-D3: strict ASCII Char.isWhitespace inside /-- and /-! doc comments
        ("r9_d3_doc_nbsp_bypass", "impl", '/-- \u00a0 -- -/\ntheorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- -/\n', {"FORBIDDEN_SORRY", "FORBIDDEN_AXIOM", "FORBIDDEN_NATIVE_DECIDE"}),
        ("r9_d3_moddoc_emspace_bypass", "impl", '/-! \u2003 -- -/\ntheorem cheat : False := sorry\n-- -/\n', {"FORBIDDEN_SORRY"}),
        # R9-D4: by_elab, run_tac, init_quot, register_simp_attr, addDeclCore, addDeclWithoutChecking, mkSorry, admitGoal, evalConst
        ("r9_d4_by_elab_run_tac_register", "impl", 'theorem c1 : False := by_elab pure default\ntheorem c2 : False := by\n  run_tac pure ()\ninit_quot\nregister_simp_attr my_s\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r9_d4_kernel_and_eval_meta_apis", "impl", 'def b1 := Lean.«addDeclCore» env\ndef b2 := addDeclWithoutChecking env\ndef b3 := mkSorry t\ndef b4 := mkLabeledSorry t\ndef b5 := admitGoal g\ndef b6 := evalConst n\n', {"FORBIDDEN_META_API"}),
        # R10-D1 inline `<--` & R11 scientific number literals
        ("r10_d1_leftarrow_dash", "impl", 'theorem c1 : False := by rw [<--(by sorry : True = False)]; trivial\ntheorem c2 : False := Id.run do let x <--(by admit : Id False); pure x\n', {"FORBIDDEN_SORRY", "FORBIDDEN_ADMIT"}),
        ("r11_sci_num_literals", "impl", 'def a := 1e0sorry\ndef b := 1E0admit\ndef c := 1.0e0sorry\ndef d := 1.e0sorry\ndef e := 0..1e0sorry\ndef f := 1e0s!"{ (by native_decide : Bool) }"\n', {"FORBIDDEN_SORRY", "FORBIDDEN_ADMIT", "FORBIDDEN_NATIVE_DECIDE"}),
    )
    for mname, mmode, msrc, mexp in option_a_reject_cases:
        mrules = {v.rule for v in scan_lean_hygiene(msrc, mode=mmode)}
        if not mexp.issubset(mrules):
            return False, "HYGIENE_VIOLATION", f"Option A reject case `{mname}` missed {mexp - mrules} (got {mrules})", {}

    # 4b. Individual anti-masking Wave r11 Section 2 locks (each case tested separately — zero bundled masking!)
    r11_individual_meta_syntax = (
        # R10-R1-D1 / R10-D3 + Explorer 1 boundary notation atoms
        tuple(
            (f"atom_{idx_a}", f'prefix:max (priority := high + 1) "{atom}" => fun (x : String) => x\n')
            for idx_a, atom in enumerate((
                "!s!", "?s!", "₀s!", "!f!", "!println!", "!s", "!f",
                "*0_s!", "*0xas!", "*0b0_s!", "*0s!", "*0_s",
                "!r", "?r", "₀r", "!r#", "!r##", "*0_r", "*0xar", "*0o7_r", "*0r",
                "a !s!", "a !r", "*a", "a b", "*0x", "*0", "*<", "*\\\\", "*×", "*#", "*]", "@[", "*⁻¹",
            ))
        )
        + (
            ("atom_unicode_bang_s", 'notation:max unicode("★", "!s!") x => x\n'),
            ("atom_infixl_bang_rhash", 'infixl:90 "!r#" => fun (_ : Nat) (x : String) => x\n'),
            # R10-R1-D2 / R10-D4 multi-char & unbalanced brace notation atoms
            ("brace_postfix_star_r", 'postfix:max "*}" => fun (_ : Nat) => "x"\n'),
            ("brace_prefix_a_r", 'prefix:max "a}" => fun (x : String) => x\n'),
            ("brace_infixl_a_r", 'infixl:90 "a}" => fun (_ : Nat) (x : String) => x\n'),
            ("brace_prefix_a_l", 'prefix:max "a{" => fun (x : String) => x\n'),
            ("brace_prefix_star_l", 'prefix:max "*{" => fun (x : String) => x\n'),
            ("brace_notation_a_l", 'notation:max "a{" x => (x : String)\n'),
            ("brace_unbal_prefix_l", 'prefix:max "{" => fun (x : Nat) => x\n'),
            ("brace_unbal_notation_r", 'notation:max "}" => (0 : Nat)\n'),
            ("brace_reversed_r_l", 'notation:max "}" x "{" => x\n'),
            ("brace_unicode_l", 'notation:max unicode("{", "⟨") x "⟩" => x\n'),
            ("brace_unicode_alt_l", 'notation:max unicode("★", "{") x => x\n'),
            ("brace_eof_unclosed", 'prefix:max "{" => id'),
            ("brace_chained_unbal", 'notation:max "{" x notation:max "}" y => y\n'),
            # Scoped comment splitters (D--, D/-, </-)
            ("scoped_D_dashdash", 'def x := f D-- comment\n'),
            ("scoped_D_slashdash", 'def x := f D/- comment -/\n'),
            ("scoped_lt_slashdash", 'def x := </- comment -/\n'),
            # Dual-scope quote-suffix operators before delimiter char literal (Explorer 1 Hunk 6)
            ("dual_scope_hash_dquote", 'def d := 0#\'"\' "\n'),
            ("dual_scope_inv_dquote", 'def d := id ⁻¹\'"\' "\n'),
            ("dual_scope_comp_dquote", 'def d := id ∘\'"\' "\n'),
            ("dual_scope_hash_rbrace", "def d := 0#'}'\n"),
            ("dual_scope_hash_lbrace", "def d := 0#'{'\n"),
            ("dual_scope_hash_guillemet", "def d := 0#'«'\n"),
            # Mathlib ambiguous ...r" operators
            ("mathlib_reliso_to_r", 'def d := f →r"a\\"b"\n'),
            ("mathlib_reliso_emb_r", 'def d := f ↪r"a\\"b"\n'),
            ("mathlib_reliso_equiv_r", 'def d := f ≃r"a\\"b"\n'),
            ("mathlib_rotate_tilde_r", 'def d := f ~r"a\\"b"\n'),
            ("mathlib_matroid_le_r", 'def d := f ≤r"a\\"b"\n'),
            ("mathlib_matroid_lt_r", 'def d := f <r"a\\"b"\n'),
            # R10-D5 + R10-R1-N1 + Explorer 1 Lean v4.32.2 hooks
            ("hook_attr_init", '@[init]\ndef e : IO Unit := pure ()\n'),
            ("hook_attr_init_fn", '@[init mkEvil]\nopaque e : Nat\n'),
            ("hook_attribute_init", 'attribute [init] evilInit\n'),
            ("hook_french_attr_init", '@[«init»]\ndef e : IO Unit := pure ()\n'),
            ("hook_builtin_init", '@[builtin_init]\ndef e : IO Unit := pure ()\n'),
            ("hook_builtin_incremental", '@[builtin_incremental]\ndef e := 0\n'),
            ("hook_combinator_formatter", '@[combinator_formatter foo]\ndef e := pure ()\n'),
            ("hook_combinator_parenthesizer", '@[combinator_parenthesizer foo]\ndef e := pure ()\n'),
            ("hook_run_io", 'def e := run_io pure ()\n'),
            ("hook_register_try_tactic", 'register_try?_tactic myT\n'),
            ("hook_declare_simp_like", 'declare_simp_like_tactic myS\n'),
            ("hook_tactic_extension", 'tactic_extension myE\n'),
            ("hook_register_tactic_tag", 'register_tactic_tag myTag\n'),
            ("hook_deprecated_syntax", 'deprecated_syntax foo\n'),
            ("hook_code_action_provider", '@[code_action_provider] def e := 0\n'),
            ("hook_widget_module", '@[widget_module] def e := 0\n'),
            ("hook_missing_docs_handler", '@[missing_docs_handler] def e := 0\n'),
            ("hook_unused_vars_ignore_fn", '@[unused_variables_ignore_fn] def e := 0\n'),
            ("hook_test_runner", '@[test_runner] def e := 0\n'),
            ("hook_library_suggestions", '@[library_suggestions] def e := 0\n'),
            ("hook_tactic_alt", '@[tactic_alt] def e := 0\n'),
        )
    )
    for r11_lbl, r11_src in r11_individual_meta_syntax:
        if not any(v.rule == "FORBIDDEN_META_SYNTAX" for v in scan_lean_hygiene(r11_src, mode="impl")):
            return False, "HYGIENE_VIOLATION", f"Wave r11 individual lock `{r11_lbl}` missed FORBIDDEN_META_SYNTAX", {}
    for eval_lbl, eval_src in (
        ("evalExpr", "def bad := evalExpr Nat ty e\n"),
        ("evalExprCore", "def bad := evalExprCore Nat ty e\n"),
        ("evalExpr_prime", "def bad := evalExpr' Nat ty e\n"),
    ):
        if not any(v.rule == "FORBIDDEN_META_API" for v in scan_lean_hygiene(eval_src, mode="impl")):
            return False, "HYGIENE_VIOLATION", f"Wave r11 individual API lock `{eval_lbl}` missed FORBIDDEN_META_API", {}

    # 4c. Individual anti-masking Wave r12 Section 2 locks (ALL Wave r11 Section 2 defects + closed whitelist + proactive Trie.matchPrefix splits)
    r12_individual_exact = (
        # R11-D1: `''` fast-path vs _INIT_QUOTE_SUFFIX_OP_PREV & _SCOPED_QUOTE_SUFFIX_OP_PREV
        ("r11_d1_pprod_qq_rbrace_interp", 'def bad : String := s!"{ True ×\'\'}\' + (by sorry : Nat) }"\n', {"FORBIDDEN_SORRY"}),
        ("r11_d1_bitvec_qq_dquote", 'open BitVec\ndef d := 0#\'\'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d1_preimage_qq_dquote", 'def d := id ⁻¹\'\'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d1_dcomp_qq_dquote", 'def d := id ∘\'\'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
        # R11-R1-D1: 4-char escaped `'\"'` after scoped quote-suffix ops
        ("r11_r1_d1_bitvec_esc_dq", 'open BitVec\ndef d := 0#\'\\"\' "\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_r1_d1_preimage_esc_dq", 'def d := id ⁻¹\'\\"\' "\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_r1_d1_dcomp_esc_dq", 'def d := f ∘\'\\"\' "\n', {"FORBIDDEN_META_SYNTAX"}),
        # R11-R2-D1: ANY _CHAR_LITERAL_RE immediately after scoped quote-suffix ops
        ("r11_r2_d1_bitvec_p_qq", 'open scoped BitVec\ndef d := (0#\'p\'\',\'"\')\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_r2_d1_preimage_s_qq", 'def d := (id ⁻¹\'s\'\',\'"\')\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_r2_d1_preimage_space_dq", 'def d := id ⁻¹\' \'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_r2_d1_preimage_nl_dq", 'def d := id ⁻¹\'\n\'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_r2_d1_preimage_a_sbang", 'def d := id ⁻¹\'a\'s! "{"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_r2_d1_dcomp_space_dq", 'def d := f ∘\' \'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
        # R11-R1-D2 / R11-D5b: FirstOrder / ModelTheory `='`
        ("r11_r1_d2_firstorder_eq_q", 'import Mathlib.ModelTheory.Syntax\nopen scoped FirstOrder\ndef d := t =\'"\' "\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_r1_d2_firstorder_nospace", 'open scoped FirstOrder\ndef d := t=\'"\' "\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d5b_firstorder_eq_qq", 'open scoped FirstOrder\ndef d := t =\'\'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_r1_d2_firstorder_eq_escdq", 'open scoped FirstOrder\ndef d := t =\'\\"\' "\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_r1_d2_firstorder_eq_p", 'open scoped FirstOrder\ndef d := (t =\'p\'\',\'"\')\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_r1_d2_firstorder_eq_space", 'open scoped FirstOrder\ndef d := t =\' \'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
        # R11-R1-D3 / R11-D5a: Dioph `D.` scientific-literal glue & `D//-` / `D///-` / `<//-` / `<///-`
        ("r11_r1_d3_dioph_1e0axiom", 'def d := D.1e0axiom fake : False\n', {"FORBIDDEN_AXIOM"}),
        ("r11_r1_d3_dioph_1dot0e0axiom", 'def d := D.1.0e0axiom fake : False\n', {"FORBIDDEN_AXIOM"}),
        ("r11_r1_d3_dioph_1dote0axiom", 'def d := D.1.e0axiom fake : False\n', {"FORBIDDEN_AXIOM"}),
        ("r11_r1_d3_dioph_1e0unsafe", 'def d := D.1e0unsafe def e : Nat := 0\n', {"FORBIDDEN_UNSAFE"}),
        ("r11_r1_d3_dioph_1e0init", 'def d := D.1e0initialize IO.println "x"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_r1_d3_dioph_1e0prefix", 'def d := D.1e0prefix:max "!s!" => id\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_r1_d3_dioph_1e0sorry", 'def d := D.1e0sorry\n', {"FORBIDDEN_SORRY"}),
        ("r11_r1_d3_dioph_1e0sbang", 'def d := D.1e0s!"{ (by sorry : Nat) }"\n', {"FORBIDDEN_SORRY"}),
        ("r11_d5a_dioph_slashslash_dash", 'def d (x : Nat) := x D//- "\n-/ 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d5a_dioph_slashslash_dashdash", 'def d (x : Nat) := x D//-- comment\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d5a_dioph_slash3_dash", 'def d (x : Nat) := x D///- "\n-/ 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d5a_jsx_lt_slashslash_dash", 'def d := <//- "\n-/ div/>\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d5a_jsx_lt_slash3_dash", 'def d := <///- "\n-/ div/>\n', {"FORBIDDEN_META_SYNTAX"}),
        # R11-D2: `prev_is_binder` bypass via unbalanced `(`/`)` or `"fun"`/`"λ"`/`"let"` + cross-nesting + multi-char
        ("r11_d2_unbal_lparen", 'notation:max "foo" "(" => (0 : Nat)\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d2_postfix_lparen", 'postfix:max "(" => fun (x : Nat) => x\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d2_unbal_rparen", 'notation:max "foo" ")" => (0 : Nat)\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d2_multi_lparen", 'notation:max "*(" => (0 : Nat)\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d2_atom_fun", 'notation:max "foo" "fun" => (0 : Nat)\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d2_atom_lambda", 'notation:max "foo" "λ" => (0 : Nat)\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d2_atom_let", 'notation:max "foo" "let" => (0 : Nat)\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d2_cross_nested_delims", 'notation:max "foo" "[" x "(" y "]" z ")" => x\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d2_unicode_lparen", 'notation:max unicode("(", "⟨") x "⟩" => x\n', {"FORBIDDEN_META_SYNTAX"}),
        # R11-D3 + closed positive pure-math attribute whitelist (_ALLOWED_PURE_MATH_ATTRS)
        ("r11_d3_unbal_rbracket", 'notation:max "foo" "]" => (0 : Nat)\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d3_unbal_lbracket", 'notation:max "foo" "[" => (0 : Nat)\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d3_multi_rbracket", 'notation:max "*]" => (0 : Nat)\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d3_attr_norm_num", '@[norm_num foo] def e := 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d3_attribute_norm_num", 'attribute [norm_num foo] e\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d3_attr_positivity", '@[positivity foo] def e := 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d3_attribute_positivity", 'attribute [positivity foo] e\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d3_tactic_code_action", '@[tactic_code_action] def e := 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_whitelist_aesop", '@[aesop safe] def e := 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_whitelist_to_additive", '@[to_additive] def e := 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_whitelist_simps", '@[simps] structure S where a : Nat\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_whitelist_custom", '@[my_custom_attr] def e := 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_whitelist_dotted", '@[simp.evil] def e := 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_whitelist_french_dotted", '@[«simp».evil] def e := 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_whitelist_french_local", '@[«local» simp] def e := 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_whitelist_erase_then_init", 'attribute [-simp, init] e\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_whitelist_erase_then_extern", 'attribute [-simp, extern c "evil"] e\n', {"FORBIDDEN_EXTERN"}),
        # R11-D4: contiguous syntax quotations `( / `[ / `{ , commentBody/versoCommentBody, ProofWidgets/Jsx & Qq
        ("r11_d4_quot_commentBody", 'def d := `(Lean.Parser.Command.commentBody| " -/)\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d4_quot_versoCommentBody", 'def d := `(Lean.Parser.Command.versoCommentBody| " -/)\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d4_generic_syntax_quot", 'def d := ``(0)\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d4_bracket_quot", 'def d := `[Cli|\n]\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d4_brace_quot", 'def d := `{0}\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d4_import_proofwidgets_html", 'import ProofWidgets.Data.Html\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d4_import_proofwidgets_transitive", 'import Mathlib.Tactic.Widget.Conv\nopen scoped ProofWidgets.Jsx\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d4_import_qq", 'import Qq\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d4_qq_by_elabq", 'def d : Nat := by_elabq pure 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r11_d4_qq_run_tacq", 'def d : Nat := by run_tacq pure ()\n', {"FORBIDDEN_META_SYNTAX"}),
        # Proactive Trie.matchPrefix non-ident-start splitting (#-commands & symbol+ident operators)
        ("r12_trie_hash_evalr", '#evalr"\\"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_trie_hash_checkr", '#checkr"\\"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_trie_hash_evalbangr", '#eval!r"\\"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_trie_hash_evalsbang", '#evals!"{ (by sorry : Nat) }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_trie_hash_evalsorry", '#evalsorry\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_trie_hash_eval1e0axiom", '#eval1e0axiom\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_trie_bitvec_evalr", 'def x := 0#evalr"\\"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_trie_hash_check_qq", '#check\'\'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_trie_hash_check_prime_r", '#check\'r"\\"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_trie_hom_g_sorry", 'def x := G →gsorry\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_trie_hom_g_r", 'def x := G →gr"\\"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_trie_hom_g_sbang", 'def x := G →gs!"{ (by sorry : Nat) }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_trie_iso_g_sorry", 'def x := G ≃gsorry\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_trie_hom_g_dec_axiom", 'def x := G →g1.0e0axiom\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_trie_hom_g_dote0_axiom", 'def x := G →g1.e0axiom\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_trie_mod_r", 'def x := a [MODr"\\"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_trie_les_r", 'def x := a ≤sr"\\"\n', {"FORBIDDEN_META_SYNTAX"}),
    )
    for r12_lbl, r12_src, r12_exp in r12_individual_exact:
        r12_got = {v.rule for v in scan_lean_hygiene(r12_src, mode="impl")}
        if not r12_exp.issubset(r12_got):
            return False, "HYGIENE_VIOLATION", f"Wave r12 individual lock `{r12_lbl}` missed {r12_exp - r12_got} (got {r12_got})", {}

    # 4d. Individual anti-masking Wave r13 Section 2 locks (R12-R1-D1..D3, R12-R2-D1..D2, R12-D1..D3, R13-PROACTIVE-1)
    r13_individual_exact = (
        # R12-R1-D1 / R12-R2-D2a / R12-D1: core `#`-commands after `0#` + permanent `after_term` backstop + `#v[sorry]`
        ("r12_r1_d1_with_exporting_axiom", 'def d := 0#with_exportingaxiom fake : False\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r1_d1_with_exporting_unsafe", 'def d := 0#with_exportingunsafe def evil : Nat := 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r1_d1_with_exporting_init", 'def d := 0#with_exportinginitialize IO.println "pwned"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r1_d1_with_exporting_syntax", 'def d := 0#with_exportingsyntax:max "!hide!" : term\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r1_d1_with_exporting_prefix", 'def d := 0#with_exportingprefix:max (priority := high + 1) "s!" => fun (x : String) => x\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r1_d1_discr_tree_key_raw", 'def d := 0#discr_tree_keyr"\\"\ntheorem cheat : False := sorry\n-- "\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r1_d1_discr_tree_simp_raw", 'def d := 0#discr_tree_simp_keyr"\\"\ntheorem cheat : False := sorry\n-- "\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r1_d1_discr_tree_D_1e0axiom", 'def d := 0#discr_tree_keyD.1e0axiom fake : False\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r2_d2a_discr_tree_sorry", 'def d := 0#discr_tree_keysorry\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r2_d2a_discr_tree_simp_sbang", 'def d := 0#discr_tree_simp_keys!"{ (by sorry : Nat) }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d1_version_axiom", 'def d : Nat := 0#versionaxiom fake : False\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d1_version_unsafe", 'def d : Nat := 0#versionunsafe def h : Nat := 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d1_version_attr_init", 'def d : Nat := 0#versionattribute [init] evil\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d1_version_notation_s", 'def d : Nat := 0#versionnotation:max "s!" x => (x : String)\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d1_show_deprecated_axiom", 'def d : Nat := 0#show_deprecated_modulesaxiom fake : False\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d1_dump_async_axiom", 'def d : Nat := 0#dump_async_env_stateaxiom fake : False\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d1_adaptation_note_axiom", 'def d : Nat := 0#adaptation_noteaxiom fake : False\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d1_hash_vec_sorry", 'def v := #v[sorry]\n', {"FORBIDDEN_SORRY"}),
        ("r12_d1_future_cmd_axiom_backstop", 'def d : Nat := 0#future_cmdaxiom fake : False\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d1_future_cmd_raw_backstop", 'def d : Nat := 0#future_cmdr"\\"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d1_future_cmd_sbang_backstop", 'def d : Nat := 0#future_cmds!"{ (by sorry : Nat) }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d1_future_cmd_attr_backstop", 'def d : Nat := 0#future_cmdattribute [init] evil\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d1_future_cmd_import_backstop", 'def d : Nat := 0#future_cmdimport Qq\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d1_future_cmd_char_backstop", 'def d : Nat := 0#future_cmd\'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d1_future_cmd_lognamed_backstop", 'def d : Nat := 0#future_cmdlogNamedError "x"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d1_future_cmd_dioph_backstop", 'def d : Nat := 0#future_cmdD.1e0axiom\n', {"FORBIDDEN_META_SYNTAX"}),
        # R12-R1-D2 / R12-R2-D2b / R12-D3a: Core Lean `Std` `~m`
        ("r12_r1_d2_tildem_sorry", 'def d := m ~msorry\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r1_d2_tildem_raw", 'def d := m ~mr"\\"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r1_d2_tildem_char_dq", 'def d := m ~m\'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r1_d2_tildem_1e0axiom", 'def d := m ~m1.0e0axiom fake : False\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r1_d2_tildem_1e0dq", 'def d := m ~m1.0e0\'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d3a_tildem_1axiom", 'def d := m ~m1axiom fake : False\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r1_d2_tildem_sbang", 'def d := m ~ms!"{ (by sorry : Nat) }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r1_d2_tildem_spaced_sbang", 'def d := m ~ms! "{ (by sorry : Nat) }"\n', {"FORBIDDEN_META_SYNTAX"}),
        # R12-R1-D3 / R12-R2-D2b / R12-D3b: Global Mathlib `∫⋯∫⁻_`
        ("r12_r1_d3_marginal_raw", 'def d := ∫⋯∫⁻_r"\\"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r1_d3_marginal_sorry", 'def d := ∫⋯∫⁻_sorry\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r1_d3_marginal_sbang", 'def d := ∫⋯∫⁻_s!"{ (by sorry : Nat) }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r1_d3_marginal_spaced_sbang", 'def d := ∫⋯∫⁻_s! "{ (by sorry : Nat) }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r1_d3_marginal_char_dq", 'def d := ∫⋯∫⁻_\'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r1_d3_marginal_1e0dq", 'def d := ∫⋯∫⁻_1.0e0\'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
        # R12-R2-D1: `source[p] == "'"` in `_ambiguous_glued_ident_reason` decimal/scientific lookahead
        ("r12_r2_d1_hom_g_dec_dq", 'def d := G →g1.0e0\'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r2_d1_hom_g_dote0_dq", 'def d := G →g1.e0\'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r2_d1_hom_g_dec_guillemet", 'def d := G →g1.0e0\'«\'\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r2_d1_hom_g_dec_rbrace", 'def d := s!"{ G →g1.0e0\'}\' + (by sorry : Nat) }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r2_d1_hom_g_dec_char_sorry", 'def d := G →g1.0e0\'a\'sorry\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r2_d1_hom_g_dec_char_sbang", 'def d := G →g1.0e0\'a\'s!"{ (by sorry : Nat) }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_r2_d1_iso_g_dec_dq", 'def d := G ≃g1.0e0\'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
        # R12-D2: spaced s!/f!/println!, glued `attribute`/`import`, glued Dioph `D.`/`D--`/`D/-`/`D//-`
        ("r12_d2_spaced_sbang_hom", 'def d := G →gs! "{ (by sorry : Nat) }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d2_spaced_sbang_iso", 'def d := G ≃gs! "{ (by sorry : Nat) }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d2_spaced_fbang_hom", 'def d := G →gf! "{ (by sorry : Nat) }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d2_spaced_println_hom", 'def d := G →gprintln! "{ (by sorry : Nat) }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d2_spaced_1sbang_hom", 'def d := G →g1s! "{ (by sorry : Nat) }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d2_glued_attribute_init", 'def d := G →g1attribute [init] evil\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d2_glued_attribute_extern", 'def d := G →g1attribute [extern c "evil"] f\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d2_glued_bin_attribute_init", 'def d := G →g0b1attribute [init] evil\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d2_glued_import", 'def d := G →g1import Qq\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d2_glued_dioph_dot", 'def d := G →gD.1e0axiom fake : False\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d2_glued_dioph_dashdash", 'def d := G →gD-- (by sorry : Nat)\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d2_glued_dioph_slashdash", 'def d := G →gD/- "\\" "\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d2_glued_dioph_slashslash_dash", 'def d := G →gD//- "\n-/ 0\n', {"FORBIDDEN_META_SYNTAX"}),
        # R12-D3c: transitive `Qq` & `=Q` / `=QL`
        ("r12_d3c_open_qq", 'open Qq\ndef d := 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d3c_eq_Q_raw", 'def d := (r"\\" : String) =Qr"\\"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d3c_eq_Q_sorry", 'def d := (0 : Nat) =Qsorry\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d3c_eq_Q_sbang", 'def d := ("" : String) =Qs!"{ (by sorry : Nat) }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d3c_eq_Q_spaced_sbang", 'def d := ("" : String) =Qs! "{ (by sorry : Nat) }"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d3c_eq_QL_raw", 'def d := 0 =QLr"\\"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d3c_eq_QL_sorry", 'def d := 0 =QLsorry\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d3c_eq_Q_1axiom", 'def d := 0 =Q1axiom fake : False\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r12_d3c_eq_Q_1e0dq", 'def d := 0 =Q1.0e0\'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
        # R13-PROACTIVE-1: chained radix/decimal numerals & signed-scientific lookahead siblings
        ("r13_pro1_bin_chain_raw", 'def d := G →g0b12r"\\"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r13_pro1_bin_chain_sorry", 'def d := G →g0b12sorry\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r13_pro1_bin_chain_axiom", 'def d := G →g0b12axiom fake : False\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r13_pro1_bin_chain_dq", 'def d := G →g0b12\'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r13_pro1_bin_chain_dec_axiom", 'def d := G →g0b12.0e0axiom fake : False\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r13_pro1_oct_chain_raw", 'def d := G →g0o78r"\\"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r13_pro1_oct_chain_sorry", 'def d := G →g0o78sorry\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r13_pro1_sci_nodot_dq", 'def d := G →g1e0\'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r13_pro1_sci_plus_dq", 'def d := G →g1.0e+0\'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r13_pro1_dec_dq", 'def d := G →g1.2\'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r13_pro1_signed_exp_field_raw", 'def decoy := G →g1e+0.0e0r"\\" /- "\ntheorem cheat : False := sorry\n-- -/\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r13_pro1_dec_signed_exp_field_raw", 'def decoy := G →g1.0e+0.0e0r"\\" /- "\ntheorem cheat : False := sorry\n-- -/\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r13_pro1_signed_exp_neg_dq", 'def d := G →g1e-0\'"\'\n', {"FORBIDDEN_META_SYNTAX"}),
    )
    for r13_lbl, r13_src, r13_exp in r13_individual_exact:
        r13_got = {v.rule for v in scan_lean_hygiene(r13_src, mode="impl")}
        if not r13_exp.issubset(r13_got):
            return False, "HYGIENE_VIOLATION", f"Wave r13 individual lock `{r13_lbl}` missed {r13_exp - r13_got} (got {r13_got})", {}
    if not any(v.rule == "FORBIDDEN_META_SYNTAX" for v in scan_lean_hygiene("import ShannonC7.Main\ndef d := G →g1import ShannonC7.Defs\n", mode="audit")):
        return False, "HYGIENE_VIOLATION", "Wave r13 audit-mode glued import lock missed FORBIDDEN_META_SYNTAX", {}

    # 4e. Individual anti-masking Wave r14 Section 2 locks (R13-D1, R13-D2/R13-R2-D1, R14-PROACTIVE-1..4)
    _r14_tail_str = 'theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- "\n'
    _r14_tail_raw_hash = 'theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- "#\n'
    _r14_tail_interp = 'theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- " }"\n'
    _r14_tail_blk = 'theorem cheat : False := sorry\naxiom fake : False\ntheorem nd : 1 = 1 := by native_decide\n-- -/ }"\n'
    r14_individual_exact = (
        # R13-D1: `/.` (scoped Rat), 4-dot `....` (`...` + `.`), 2-dot `/..` / `→..` / `≃..`, `→.` / `≃.` before `s!`/`f!`/`println!`
        ("r13_d1_slash_dot_s", 'def Nat.«s!» (_ : String) : Nat := 0\ndef d : Nat := 1/.s! "{ \\\\"\n' + _r14_tail_interp, {"FORBIDDEN_META_SYNTAX"}),
        ("r13_d1_slash_dot_f", 'def Nat.«f!» (_ : String) : Nat := 0\ndef d : Nat := 1/.f! "{ \\\\"\n' + _r14_tail_interp, {"FORBIDDEN_META_SYNTAX"}),
        ("r13_d1_slash_dot_println", 'def Nat.«println!» (_ : String) : Nat := 0\ndef d : Nat := 1/.println! "{ \\\\"\n' + _r14_tail_interp, {"FORBIDDEN_META_SYNTAX"}),
        ("r13_d1_slash_dot_comment_s", 'def Nat.«s!» (_ : String) : Nat := 0\ndef d : Nat := 1/.s! /- c -/ "{ \\\\"\n' + _r14_tail_interp, {"FORBIDDEN_META_SYNTAX"}),
        ("r13_d1_slash_dot_nl_s", 'def Nat.«s!» (_ : String) : Nat := 0\ndef d : Nat := 1/.s!\n  "{ \\\\"\n' + _r14_tail_interp, {"FORBIDDEN_META_SYNTAX"}),
        ("r13_d1_4dots_s", 'def Nat.«s!» (_ : String) : Nat := 0\ndef d : Std.Rco Nat := 1....s! "{ \\\\"\n' + _r14_tail_interp, {"FORBIDDEN_META_SYNTAX"}),
        ("r13_d1_4dots_f", 'def Nat.«f!» (_ : String) : Nat := 0\ndef d : Std.Rco Nat := 1....f! "{ \\\\"\n' + _r14_tail_interp, {"FORBIDDEN_META_SYNTAX"}),
        ("r13_d1_4dots_println", 'def Nat.«println!» (_ : String) : Nat := 0\ndef d : Std.Rco Nat := 1....println! "{ \\\\"\n' + _r14_tail_interp, {"FORBIDDEN_META_SYNTAX"}),
        ("r13_d1_star_4dots_s", 'def Nat.«s!» (_ : String) : Nat := 0\ndef d : Std.Rio Nat := *....s! "{ \\\\"\n' + _r14_tail_interp, {"FORBIDDEN_META_SYNTAX"}),
        ("r13_d1_lt_4dots_s", 'def Nat.«s!» (_ : String) : Nat := 0\ndef d : Std.Roo Nat := 1<....s! "{ \\\\"\n' + _r14_tail_interp, {"FORBIDDEN_META_SYNTAX"}),
        ("r13_d1_slash_2dots_s", 'open scoped Rat\ndef Int.«s!» (_ : String) : Int := 0\ndef d : Rat := 1/..s! "{ \\\\"\n' + _r14_tail_interp, {"FORBIDDEN_META_SYNTAX"}),
        ("r13_d1_equiv_dot_s", 'local infixl:65 " ≃ " => Nat.add\ndef Nat.«s!» (_ : String) : Nat := 0\ndef d : Nat := 1≃.s! "{ \\\\"\n' + _r14_tail_interp, {"FORBIDDEN_META_SYNTAX"}),
        ("r13_d1_arrow_dot_s", 'local infixr:65 " → " => Nat.add\ndef Nat.«s!» (_ : String) : Nat := 0\ndef d : Nat := 1→.s! "{ \\\\"\n' + _r14_tail_interp, {"FORBIDDEN_META_SYNTAX"}),
        ("r13_d1_pfun_2dots_s", 'import Mathlib.Data.PFun\ndef Nat.«s!» (_ : String) : Type := Nat\ndef d : Type := Nat →..s! "{ \\\\"\n' + _r14_tail_interp, {"FORBIDDEN_META_SYNTAX"}),
        ("r13_d1_pequiv_2dots_s", 'import Mathlib.Data.PEquiv\ndef Nat.«s!» (_ : String) : Type := Nat\ndef d : Type := Nat ≃..s! "{ \\\\"\n' + _r14_tail_interp, {"FORBIDDEN_META_SYNTAX"}),
        # R14-PROACTIVE-1: raw-string `r"`/`r#"` & `|>..` multi-dot siblings
        ("r14_pro1_slash_dot_raw_hash", 'infixl:75 " # " => fun (_ : Nat) (_ : String) => (0 : Nat)\ndef Nat.r : Nat := 0\ndef d : Nat := 1/.r#"\\" "\n' + _r14_tail_raw_hash, {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro1_slash_dot_raw", 'def d : Nat := 1/.r"a\\"b"\n' + _r14_tail_str, {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro1_4dots_raw_hash", 'def d : Nat := 1....r#"\\" "\n' + _r14_tail_raw_hash, {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro1_star_4dots_raw_hash", 'def d : Nat := *....r#"\\" "\n' + _r14_tail_raw_hash, {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro1_lt_4dots_raw_hash", 'def d : Nat := 1<....r#"\\" "\n' + _r14_tail_raw_hash, {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro1_slash_2dots_raw_hash", 'def d : Nat := 1/..r#"\\" "\n' + _r14_tail_raw_hash, {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro1_arrow_dot_raw_hash", 'def d : Nat := 1→.r#"\\" "\n' + _r14_tail_raw_hash, {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro1_equiv_dot_raw_hash", 'def d : Nat := 1≃.r#"\\" "\n' + _r14_tail_raw_hash, {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro1_pipe_2dots_raw_hash", 'def d : Nat := x |>..r#"\\" "\n' + _r14_tail_raw_hash, {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro1_pipe_2dots_s", 'def d : Nat := x |>..s! "{ \\\\"\n' + _r14_tail_interp, {"FORBIDDEN_META_SYNTAX"}),
        # R13-R2-D1 / R13-D2 + R14-PROACTIVE-2: dual-scope `D.` underscore & scientific/separator siblings
        ("r13_r2_d1_dioph_1_r", 'infixl:70 "_r" => fun (_ : Nat) (_ : String) => (0 : Nat)\ndef d : Nat := D.1_r"a\\"b"\n' + _r14_tail_str, {"FORBIDDEN_META_SYNTAX"}),
        ("r13_r2_d1_dioph_1_0r", 'infixl:70 "_0r" => fun (_ : Nat) (_ : String) => (0 : Nat)\ndef d : Nat := D.1_0r"a\\"b"\n' + _r14_tail_str, {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro2_dioph_1e0r", 'infixl:70 "e0r" => fun (_ : Nat) (_ : String) => (0 : Nat)\ndef d : Nat := D.1e0r"\\" "\n' + _r14_tail_str, {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro2_dioph_1e0s", 'infixl:70 "e0s!" => fun (_ : Nat) (_ : String) => (0 : Nat)\ndef d : Nat := D.1e0s!"{ \\\\"\n' + _r14_tail_interp, {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro2_dioph_1_2_r", 'infixl:70 "_r" => fun (_ : Nat) (_ : String) => (0 : Nat)\ndef d : Nat := D.1.2_r"\\" "\n' + _r14_tail_str, {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro2_dioph_1_2e0r", 'infixl:70 "e0r" => fun (_ : Nat) (_ : String) => (0 : Nat)\ndef d : Nat := D.1.2e0r"\\" "\n' + _r14_tail_str, {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro2_dioph_1_dot_e0s", 'def Nat.«e0s!» (_ : Nat) (_ : String) : Nat := 0\ndef D : Nat × Nat := (0, 0)\ndef d : Nat := D.1.e0s! "{ \\\\"\n' + _r14_tail_interp, {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro2_dioph_1_dot_e0r_hash", 'def d : Nat := D.1.e0r#"\\" "\n' + _r14_tail_raw_hash, {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro2_dioph_1eplus0r", 'def d : Nat := D.1e+0r"\\" "\n' + _r14_tail_str, {"FORBIDDEN_META_SYNTAX"}),
        # R14-PROACTIVE-3: `prev_is_binder` removal (`| fun`, `| let`, `1/.fun`, `1/.let`, `1....fun`, `1/..fun` before mixfix/notation)
        ("r14_pro3_ctor_fun_prefix", 'inductive T where\n  | fun\nprefix:max (priority := high + 1) "!s!" => id\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro3_ctor_let_prefix", 'inductive T where\n  | let\nprefix:max (priority := high + 1) "!s!" => id\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro3_ctor_fun_notation", 'inductive T where\n  | fun\nnotation:max "!s!" x => x\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro3_ctor_fun_infixl", 'inductive T where\n  | fun\ninfixl:90 "!r#" => fun (_ : Nat) (x : String) => x\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro3_ctor_let_postfix", 'inductive T where\n  | let\npostfix:max "*}" => fun (_ : Nat) => "x"\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro3_slashdot_fun_prefix", 'def d : Nat := 1/.fun\nprefix:max "!s!" => id\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro3_slashdot_let_prefix", 'def d : Nat := 1/.let\nprefix:max "!s!" => id\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro3_4dots_fun_prefix", 'def d : Std.Rco Nat := 1....fun\nprefix:max "!s!" => id\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro3_slash2dots_fun_prefix", 'def d : Rat := 1/..fun\nprefix:max "!s!" => id\n', {"FORBIDDEN_META_SYNTAX"}),
        # R14-PROACTIVE-4: dotted scope-keyword attribute heads (`@[local.evil]`, `@[scoped.evil]`, `attribute [local.evil]`, `attribute [scoped.evil]`)
        ("r14_pro4_attr_local_dotted", '@[local.evil] def e := 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro4_attr_scoped_dotted", '@[scoped.evil] def e := 0\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro4_attribute_local_dotted", 'attribute [local.evil] x\n', {"FORBIDDEN_META_SYNTAX"}),
        ("r14_pro4_attribute_scoped_dotted", 'attribute [scoped.evil] x\n', {"FORBIDDEN_META_SYNTAX"}),
    )
    for r14_lbl, r14_src, r14_exp in r14_individual_exact:
        r14_got = {v.rule for v in scan_lean_hygiene(r14_src, mode="impl")}
        if not r14_exp.issubset(r14_got):
            return False, "HYGIENE_VIOLATION", f"Wave r14 individual lock `{r14_lbl}` missed {r14_exp - r14_got} (got {r14_got})", {}

    # R13-D2 / R13-R2-D1: `fieldIdxFn` strict ASCII `'0'..'9'` ONLY (must catch SORRY+AXIOM+NATIVE_DECIDE with ZERO spurious UNCLOSED_*)
    r14_fieldidx_desync = (
        ("r13_d2_proj_1_r_ab", 'infixl:70 "_r" => fun (_ : Nat) (_ : String) => (0 : Nat)\ndef x : Nat × Nat := (0, 0)\ndef d : Nat := x.1_r"a\\"b"\n' + _r14_tail_str),
        ("r13_d2_proj_1_r_esc", 'infixl:65 " _r " => fun (a : Nat) (_ : String) => a\ndef d (x : Nat × Nat) : Nat := x.1_r"\\" "\n' + _r14_tail_str),
        ("r13_d2_proj_1_0r", 'infixl:70 "_0r" => fun (_ : Nat) (_ : String) => (0 : Nat)\ndef x : Nat × Nat := (0, 0)\ndef d : Nat := x.1_0r"a\\"b"\n' + _r14_tail_str),
        ("r13_d2_proj_1_1r", 'infixl:65 " _1r " => fun (a : Nat) (_ : String) => a\ndef d (x : Nat × Nat) : Nat := x.1_1r"\\" "\n' + _r14_tail_str),
        ("r13_d2_proj_nested_1_2_r", 'infixl:65 " _r " => fun (a : Nat) (_ : String) => a\ndef d (x : (Nat × Nat) × Nat) : Nat := x.1.2_r"\\" "\n' + _r14_tail_str),
        ("r13_d2_proj_tuple_1_r", 'infixl:70 "_r" => fun (_ : Nat) (_ : String) => (0 : Nat)\ndef d : Nat := (0, 0).1_r"a\\"b"\n' + _r14_tail_str),
        ("r13_d2_proj_french_1_r", 'infixl:70 "_r" => fun (_ : Nat) (_ : String) => (0 : Nat)\ndef «a» : Nat × Nat := (0, 0)\ndef d : Nat := «a».1_r"a\\"b"\n' + _r14_tail_str),
        ("r13_d2_proj_num_1_0_1_r", 'infixl:70 "_r" => fun (_ : Nat) (_ : String) => (0 : Nat)\ndef d : Nat := 1.0.1_r"a\\"b"\n' + _r14_tail_str),
        ("r13_d2_pipeproj_1_r", 'infixl:65 " _r " => fun (a : Nat) (_ : String) => a\ndef d (x : Nat × Nat) : Nat := x |>.1_r"\\" "\n' + _r14_tail_str),
        ("r13_d2_proj_1_s_blk", 'infixl:70 "_s!" => fun (_ : Nat) (_ : String) => (0 : Nat)\ndef x : Nat × Nat := (0, 0)\ndef d : Nat := x.1_s!"{ /-"\n' + _r14_tail_blk),
        ("r13_d2_proj_1_0s_blk", 'infixl:70 "_0s!" => fun (_ : Nat) (_ : String) => (0 : Nat)\ndef x : Nat × Nat := (0, 0)\ndef d : Nat := x.1_0s!"{ /-"\n' + _r14_tail_blk),
        ("r13_d2_proj_1_f_interp", 'infixl:65 " _f! " => fun (a : Nat) (_ : String) => a\ndef d (x : Nat × Nat) : Nat := x.1_f!"{ \\\\"\n' + _r14_tail_interp),
        ("r13_d2_proj_1_println_interp", 'infixl:65 " _println! " => fun (a : Nat) (_ : String) => a\ndef d (x : Nat × Nat) : Nat := x.1_println!"{ \\\\"\n' + _r14_tail_interp),
        ("r13_d2_proj_1_1s_interp", 'infixl:65 " _1s! " => fun (a : Nat) (_ : String) => a\ndef d (x : Nat × Nat) : Nat := x.1_1s!"{ \\\\"\n' + _r14_tail_interp),
    )
    for fi_lbl, fi_src in r14_fieldidx_desync:
        fi_got = {v.rule for v in scan_lean_hygiene(fi_src, mode="impl")}
        if not {"FORBIDDEN_SORRY", "FORBIDDEN_AXIOM", "FORBIDDEN_NATIVE_DECIDE"}.issubset(fi_got):
            return False, "HYGIENE_VIOLATION", f"Wave r14 fieldIdx lock `{fi_lbl}` missed violations: {fi_got}", {}
        if "UNCLOSED_STRING" in fi_got or "UNCLOSED_BLOCK_COMMENT" in fi_got:
            return False, "HYGIENE_VIOLATION", f"Wave r14 fieldIdx lock `{fi_lbl}` emitted spurious unclosed error: {fi_got}", {}

    # Wave r14 audit-mode locks (R13-D1, R14-PROACTIVE-1 & R13-D2 hiding `import ShannonC7.Defs`)
    if not any(v.rule == "FORBIDDEN_META_SYNTAX" for v in scan_lean_hygiene('import ShannonC7.Main\ndef Nat.«s!» (_ : String) : Nat := 0\ndef d : Nat := 1/.s! "{ \\\\"\nimport ShannonC7.Defs\n' + _r14_tail_interp, mode="audit")):
        return False, "HYGIENE_VIOLATION", "Wave r14 audit-mode R13-D1 `1/.s!` lock missed FORBIDDEN_META_SYNTAX", {}
    if not any(v.rule == "FORBIDDEN_META_SYNTAX" for v in scan_lean_hygiene('import ShannonC7.Main\ndef d : Nat := 1/.r#"\\" "\nimport ShannonC7.Defs\n' + _r14_tail_raw_hash, mode="audit")):
        return False, "HYGIENE_VIOLATION", "Wave r14 audit-mode R14-PROACTIVE-1 `1/.r#\"` lock missed FORBIDDEN_META_SYNTAX", {}
    r14_aud_d2 = {v.rule for v in scan_lean_hygiene('import ShannonC7.Main\ninfixl:65 " _r " => fun (a : Nat) (_ : String) => a\ndef d (x : Nat × Nat) : Nat := x.1_r"\\" "\nimport ShannonC7.Defs\n' + _r14_tail_str, mode="audit")}
    if not {"OPAQUE_BOX_VIOLATION", "FORBIDDEN_SORRY"}.issubset(r14_aud_d2):
        return False, "HYGIENE_VIOLATION", f"Wave r14 audit-mode R13-D2 `x.1_r` lock missed OPAQUE_BOX_VIOLATION/FORBIDDEN_SORRY: {r14_aud_d2}", {}

    # 5. Expanded module-level AND nested code-object symbol-retirement lock (Iter 6..12 deleted symbols MUST be absent)
    import cross_check as _cc
    retired_module_syms = (
        "_AXIOM_RE", "_UNKNOWN_CONST_RE", "_ATTR_ONLY_META_SYNTAX",
        "_SigTables", "_compute_back_ctx_tag", "_JumpEntry", "_bounded_interp_kw_lookback",
        "_ProbeCache", "_LexResult", "_run_single_interp_probe", "_lex_lean4_core",
        "_lex_lean4_with_meta", "_res2_swallowed_clean_interp", "_track_local_interp_atom",
        "_skip_prev_atomic_term", "_skip_prev_dotted_ident", "_peel_term_max_prefixes",
        "_plain_string_has_unescaped_brace", "_find_interp_body_next_cached",
        "_classify_quote_trigger", "_is_inside_attr_brackets",
        "_PROBE_SCOPE_KW", "_TERM_EXPECTING_PREV_KW", "_KNOWN_ZERO_ARG_TACTICS",
        "_FALLBACK_STOP_KW", "_OPEN_IN_PREFIX_MOD_KW", "_LEAN_DUAL_MODE_KW_INTERPOLATORS",
        "_LEAN_1ARG_TERM_INTERPOLATORS", "_LEAN_1ARG_IDENT_INTERPOLATORS", "_LEAN_2ARG_INTERPOLATORS",
        "_is_in_by_tactic_head_for_last", "_update_scope_state_id",
        "_activate_ns", "_deactivate_ns", "_expand_open_targets",
        "_sqrt_upper", "_CAP", "_clamp", "_pow_int",
        "_HEADER_VALUE_COL_RE", "_COMPOUND_PROSE_CONT_WORDS",
        "_UPPER_POST_NEGATION_RE", "_PROSE_MATH_OP_MAP", "_INCIDENTAL_EXT_PREFIX_RE",
        "_is_isolated_unformalized_paren_aside", "_CLAUSE_TRANSITION_RE",
        "_has_stripped_unformalized_paren", "_analyze_table_cell_status",
    )
    for rsym in retired_module_syms:
        if hasattr(_cc, rsym):
            return False, "HYGIENE_VIOLATION", f"Retired Iter-6..12 symbol still present in cross_check: {rsym}", {}

    def _collect_co_names(co):
        out = {co.co_name}
        out.update(co.co_varnames)
        out.update(co.co_freevars)
        out.update(co.co_names)
        for c in co.co_consts:
            if hasattr(c, "co_code"):
                out.update(_collect_co_names(c))
        return out

    lex_co_names = (
        _collect_co_names(_cc._lex_lean4_single_pass.__code__)
        | _collect_co_names(_cc._lex_lean4.__code__)
        | _collect_co_names(_cc._scan_tokens_and_imports.__code__)
    )
    for rlocal in (
        "_is_in_by_tactic_head_for_last", "_update_scope_state_id",
        "_activate_ns", "_deactivate_ns", "_expand_open_targets",
        "by_stack", "open_in_frames", "active_arg_interp",
        "has_quote_or_guillemet", "in_term_expr", "scope_state_id",
        "notation_brace_bal", "notation_brace_min",
    ):
        if rlocal in lex_co_names:
            return False, "HYGIENE_VIOLATION", f"Retired nested Section 2 state `{rlocal}` still present in lexer code", {}

    # 6. Strict < 0.15s O(N) CPU stress locks (prior locks + ALL 8 Wave r8 quadratic DoS + 4 new single-pass workloads)
    # R4-D8 & R5-D6 pure-math nested `s!` + Option A `dbg_trace`
    s_d8_pure = 's!"{ ' * 150 + ' sorry ' + ' }"' * 150
    s_d8_dbg = 'dbg_trace "{ s!"{' * 150 + ' sorry ' + '}" }"' * 150
    s_r5_d6_enclosing = 's!"{ let _ := "/-"; ' * 150 + ' sorry ' + ' }"' * 150
    s_r5_d6_dbg = 's!"{ dbg_trace "{ "/-" }"; ' * 150 + ' sorry ' + ' }"' * 150
    t0_d8 = time.process_time()
    v_d8_pure = scan_lean_hygiene(s_d8_pure, mode="impl")
    v_d8_dbg = scan_lean_hygiene(s_d8_dbg, mode="impl")
    v_r5_pure = scan_lean_hygiene(s_r5_d6_enclosing, mode="impl")
    v_r5_dbg = scan_lean_hygiene(s_r5_d6_dbg, mode="impl")
    dt_d8 = time.process_time() - t0_d8
    if not any(v.rule == "FORBIDDEN_SORRY" for v in v_d8_pure):
        return False, "HYGIENE_VIOLATION", "Nested s! x 150 missed FORBIDDEN_SORRY", {}
    if not any(v.rule == "FORBIDDEN_DBG_TRACE" for v in v_d8_dbg):
        return False, "HYGIENE_VIOLATION", "R4-D8 nested dbg_trace/s! missed FORBIDDEN_DBG_TRACE", {}
    if not any(v.rule == "FORBIDDEN_SORRY" for v in v_r5_pure):
        return False, "HYGIENE_VIOLATION", "R5-D6 pure nested s! missed FORBIDDEN_SORRY", {}
    if not any(v.rule == "FORBIDDEN_DBG_TRACE" for v in v_r5_dbg):
        return False, "HYGIENE_VIOLATION", "R5-D6 dbg_trace nested s! missed FORBIDDEN_DBG_TRACE", {}
    if dt_d8 >= 0.15:
        return False, "HYGIENE_VIOLATION", f"R4-D8/R5-D6 O(N) CPU regression ({dt_d8:.3f}s >= 0.15s)", {}

    # Pure-math O(N) chains (MUST be CLEAN [] and < 0.15s each)
    pure_stress = (
        ("chained_idx_2000", "def x := a" + "[0]" * 2000 + "\n"),
        ("chained_dot_2000", 'def d := s!"{ 1 }"\ndef x := a' + ".a" * 2000 + "\n"),
        ("chained_dot_pct_2000", 'def p := 1 % 2\ndef d := s!"{ 1 }"\ndef x := a' + ".a" * 2000 + "\n"),
        ("no_index_2000", 'def d := s!"{ 1 }"\ndef x := ' + "no_index " * 2000 + "tk\n"),
        ("at_prefix_2000", 'def d := s!"{ 1 }"\ndef x := ' + "@ " * 2000 + "tk\n"),
        ("r7_d6_open_in_2000", "open A in " * 2000 + "def x := " + "1 + " * 2000 + "0\n"),
        ("r7_d6_nested_open_in_2000", "def x := " + "(open A in " * 2000 + "1 + " * 2000 + "0" + ")" * 2000 + "\n"),
        ("RawHash_5000", "def s := r" + "#" * 5000 + '"' + '"' * 200 + "#" * 4999 + '"' + "#" * 5000 + "\n"),
        ("NestedInterp_500", 'def s := ' + 's!"{' * 500 + '0' + '}"' * 500 + "\n"),
        ("Notation_5000_noarrow", 'notation ' + '"x" ' * 5000 + "\n"),
        ("R10_notation_parens_2000", 'notation:max ' + '(name := lemma) ' * 2000 + '"★" => 0\n'),
        ("R10_star_dots_raw_2000", 'def x := ' + '*...r"\\" + ' * 2000 + '0\n'),
        ("R10_doc_nbsp_2000", '/-- \u00a0 -- -/\n' * 2000 + 'def ok : Nat := 0\n'),
        ("R11_slashslash_and_quotes_2000", 'def x := { a : Int // -a = 0 }\n' * 1000 + "def y := id '' s\n" * 1000),
        ("R11_notation_braces_2000", 'notation "{" x " | " p "}" => Set.mk x p\n' * 500),
        ("R11_sci_num_chain_1000", 'def x := ' + '1.5e+2 + ' * 1000 + '0\n'),
        ("R11_huge_notation_atoms_r_1000", 'notation ' + '"bar" ' * 1000 + '=> 0\n'),
        ("R12_init_quote_double_800", 'def x := ' + 'True ×\'\'"\' + ' * 800 + '0\n'),
        ("R12_attr_whitelist_2000", '@[' + 'simp, ' * 2000 + 'ext] def e := 0\n'),
        ("R13_hash_vec_2000", "def v := " + "#v[1, 2] ++ " * 1000 + "#v[]\n"),
        ("R14_fieldidx_proj_2000", "def x := p" + ".1" * 2000 + "\n"),
    )
    for sname, ssrc in pure_stress:
        t0_s = time.process_time()
        v_s = scan_lean_hygiene(ssrc, mode="impl")
        dt_s = time.process_time() - t0_s
        if v_s:
            return False, "HYGIENE_VIOLATION", f"Pure-math stress payload `{sname}` false-positived: {v_s[:1]}", {}
        if dt_s >= 0.15:
            return False, "HYGIENE_VIOLATION", f"O(N) CPU regression on `{sname}` ({dt_s:.3f}s >= 0.15s)", {}

    # Extern_5000 (MUST emit FORBIDDEN_EXTERN and run in < 0.15s)
    t0_ext = time.process_time()
    v_ext5k = scan_lean_hygiene("@[" + "simp, " * 5000 + "extern] opaque f : Nat\n", mode="impl")
    dt_ext = time.process_time() - t0_ext
    if not any(v.rule == "FORBIDDEN_EXTERN" for v in v_ext5k) or dt_ext >= 0.15:
        return False, "HYGIENE_VIOLATION", f"Extern_5000 failed (viols={len(v_ext5k)}, dt={dt_ext:.3f}s)", {}

    # ALL 8 Wave r8 Theta(N^2) DoS workloads + R6-D3 / R7-D6 / R7-torture (MUST reject under Option A and run < 0.15s each!)
    dos_reject_stress = (
        ("r6_d3_alt_80", "import Lean\nopen Lean\ndef f : CoreM Unit :=\n" + "".join(f'  let _ := dbg_trace "{{ 0 }}"; {"throwErrorAt (" if j % 2 == 0 else "id ("}\n' for j in range(80)) + "  Syntax.missing" + "".join(') ""' if j % 2 == 0 else ")" for j in reversed(range(80))) + "\n", "FORBIDDEN_DBG_TRACE"),
        ("r7_torture_unclosed_paren_400", 'dbg_trace "{ "; let _ := "("; ' * 400 + ' }"' * 400, "FORBIDDEN_DBG_TRACE"),
        ("r7_torture_deep_section_1000", "section\n" * 1000 + 'def d := dbg_trace "{ 1 }"; 0\n' + "end\n" * 1000, "FORBIDDEN_DBG_TRACE"),
        ("r7_r2_d3_valid_foo_1600", 'macro "foo!" s:str : term => `($s)\ndef xs : List String := [' + ",".join(['foo!"{"'] * 1600) + ']\ndef tail := "' + "} " * 1600 + '"\n', "FORBIDDEN_META_SYNTAX"),
        ("r7_r2_d3_unclosed_dbg_1600", 'dbg_trace "{ "' * 1600 + '" ' + "} " * 1600 + "a" * 8000 + "\n", "FORBIDDEN_DBG_TRACE"),
        ("r7_d6_scoped_syntax_2000", 'namespace A\n' + 'scoped syntax "f" interpolatedStr\n' * 2000 + 'end A\nopen A\ndef x := ' + 'f "" ' * 1200 + 'f "{ 1 }"\n', "FORBIDDEN_META_SYNTAX"),
        ("r7_d6_deep_ns_open_2000", 'def d := dbg_trace "{ 1 }"; 0\nnamespace ' + ".".join(["A"] * 2000) + "\n" + "open B\n" * 2000, "FORBIDDEN_DBG_TRACE"),
        # Wave r8 exact 8 Theta(N^2) DoS workloads (previously 426ms..12.44s -> now < 0.08s!)
        ("r8_r2_d4a_section_foo_800", 'macro "m" s:interpolatedStr(term) : term => `(0)\n' + 'section\nnamespace Foo\nend Foo\nend\n' * 800 + 'def d := dbg_trace "{ 1 }"; 0\n', "FORBIDDEN_META_SYNTAX"),
        ("r8_r2_d4b_17global_open_in_800", "".join(f'syntax "g{j}" interpolatedStr(term) : term\n' for j in range(17)) + 'open A in def x := 1\n' * 800, "FORBIDDEN_META_SYNTAX"),
        ("r8_r1_d7_distinct_scoped_toggle_1000", "".join(f'namespace N{j}\nscoped syntax "s{j}" interpolatedStr(term) : term\nend N{j}\nopen N{j} in def x{j} := 0\n' for j in range(1000)), "FORBIDDEN_META_SYNTAX"),
        ("r8_r1_d7_deep_nested_cand_parents_600", "".join(f'namespace P{j}\n' for j in range(600)) + 'scoped syntax "k" interpolatedStr(term) : term\n' + "open P0\n" * 600 + "".join(f'end P{j}\n' for j in reversed(range(600))), "FORBIDDEN_META_SYNTAX"),
        ("r8_d6_attack2d_foo_ns_600", 'def d := dbg_trace "{ 1 }"; 0\n' + 'namespace Foo\nend Foo\n' * 600, "FORBIDDEN_DBG_TRACE"),
        ("r8_d6_attack1_17global_600", "".join(f'syntax "q{j}" interpolatedStr(term) : term\n' for j in range(17)) + 'def d := dbg_trace "{ 1 }"; 0\n' * 600, "FORBIDDEN_META_SYNTAX"),
        ("r8_d6_attack3_scoped_800", "".join(f'namespace S{j}\nscoped macro "a{j}" s:interpolatedStr(term) : term => `(0)\nend S{j}\n' for j in range(800)) + "open S0\n" * 400, "FORBIDDEN_META_SYNTAX"),
        ("r8_d6_attack4c_nested_open_600", "namespace R\nscoped syntax \"z\" interpolatedStr(term) : term\nend R\n" + "(open R in " * 600 + "0" + ")" * 600 + "\n", "FORBIDDEN_META_SYNTAX"),
        ("r10_attr_tactic_2000", "@[" + "simp, " * 2000 + "tactic foo] def e := 0\n", "FORBIDDEN_META_SYNTAX"),
        ("r11_huge_single_atom_r_hashes", 'prefix:max "*r' + "#" * 4000 + '" => id\n', "FORBIDDEN_META_SYNTAX"),
        ("r12_dioph_slashes_4000", 'def x := D' + "/" * 4000 + "-\n", "FORBIDDEN_META_SYNTAX"),
        ("r12_nonident_op_dec_8000", 'def x := G →g1.' + "0" * 8000 + "a\n", "FORBIDDEN_META_SYNTAX"),
        ("r13_after_term_hash_2000", "def x := " + "0#future_cmdaxiom + " * 1000 + "0\n", "FORBIDDEN_META_SYNTAX"),
        ("r13_nonident_0b12_4000", 'def x := G →g0b' + '1' * 4000 + '2' * 4000 + 'r""\n', "FORBIDDEN_META_SYNTAX"),
        ("r13_nonident_0b12_chain_1000", 'def x := ' + 'G →g0b12r"" + ' * 1000 + '0\n', "FORBIDDEN_META_SYNTAX"),
        ("r14_multidot_interp_1000", "def x := " + "1" + "." * 4000 + 's! "a"\n', "FORBIDDEN_META_SYNTAX"),
    )
    for dname, dsrc, dexp in dos_reject_stress:
        t0_d = time.process_time()
        v_d = scan_lean_hygiene(dsrc, mode="impl")
        dt_d = time.process_time() - t0_d
        if not any(v.rule == dexp for v in v_d):
            return False, "HYGIENE_VIOLATION", f"DoS stress payload `{dname}` missed {dexp}", {}
        if dt_d >= 0.15:
            return False, "HYGIENE_VIOLATION", f"Wave r8/r14 O(N^2) DoS regression on `{dname}` ({dt_d:.3f}s >= 0.15s)", {}

    total_checked = len(cases) + len(desync_fixtures) + len(clean_cases) + len(option_a_reject_cases) + len(r11_individual_meta_syntax) + len(r12_individual_exact) + len(r13_individual_exact) + len(r14_individual_exact) + len(r14_fieldidx_desync) + len(pure_stress) + len(dos_reject_stress) + 12
    return True, "OK", f"All {total_checked} Option A pure-math lexer, Wave r8..r14 bypass, retirement, live-repo zero-FP & <0.15s O(N) CPU checks verified", {}


def _st_18(ctx: SuiteContext):
    ok_a, code_a, msg_a, info_a = ctx.scan_audit_file()
    if not ok_a:
        return False, code_a, msg_a, info_a
    audit_src = (ctx.verify_dir / "e2e_audit.lean").read_text(encoding="utf-8")
    missing_prints = [
        d for d in REQUIRED_AUDIT_AXIOM_DECLS
        if f"#print axioms {d}" not in audit_src
    ]
    if missing_prints:
        return False, "MISSING_AXIOM_REPORT", f"e2e_audit.lean missing #print axioms for: {missing_prints}", {"missing": missing_prints}
    if "Mathlib.Data.Real.Sqrt" in audit_src:
        return False, "HYGIENE_VIOLATION", "e2e_audit.lean imports deprecated Mathlib.Data.Real.Sqrt", {}
    pycache_hits = [str(p) for p in ctx.verify_dir.rglob("__pycache__")] + [
        str(p) for p in ctx.verify_dir.rglob("*.pyc")
    ]
    if pycache_hits:
        return False, "HYGIENE_VIOLATION", f"Bytecode pollution inside verify/: {pycache_hits[:3]}", {}
    return True, "OK", "Real verify/e2e_audit.lean passed opaque-box hygiene, all 24 #print axioms present, zero verify/ pollution", {}


def get_self_tests() -> list[TestCase]:
    return [
        TestCase("ST-01", "SELF_TEST", "CONTROL", "Positive hygiene control (comments, nested blocks, strings, decide, leaf import)", _st_01),
        TestCase("ST-02", "SELF_TEST", "MUTATION", "Mutation: live `sorry` detected with exact line numbers", _st_02),
        TestCase("ST-03", "SELF_TEST", "MUTATION", "Mutation: live `admit` detected while `admits_bound` ignored", _st_03),
        TestCase("ST-04", "SELF_TEST", "MUTATION", "Mutation: custom `axiom` & `private axiom` detected while `#print axioms` ignored", _st_04),
        TestCase("ST-05", "SELF_TEST", "MUTATION", "Mutation: unsafe/unsafeCast/lcProof/implemented_by/extern/skipKernelTC caught", _st_05),
        TestCase("ST-06", "SELF_TEST", "MUTATION", "Mutation: native_decide, Lean.ofReduceBool, Lean.trustCompiler & sorryAx caught", _st_06),
        TestCase("ST-07", "SELF_TEST", "MUTATION", "Mutation: #print axioms rejects unauthorized axioms & missing theorems", _st_07),
        TestCase("ST-08", "SELF_TEST", "MUTATION", "Mutation: single cyclic conflict (incl. 0~6 wrap, Trie7, C_7^c^4) caught", _st_08),
        TestCase("ST-09", "SELF_TEST", "MUTATION", "Mutation: duplicate vertex in witness & Trie7 caught", _st_09),
        TestCase("ST-10", "SELF_TEST", "MUTATION", "Mutation: rounded-up truncation, d=500 big-int, ValidTuple & Profile leaks caught", _st_10),
        TestCase("ST-11", "SELF_TEST", "MUTATION", "Mutation: invalid bound ordering, cubic trap & den=0 rejected cleanly", _st_11),
        TestCase("ST-12", "SELF_TEST", "MUTATION", "Mutation: obstruction testbed catches invalid bounds on all 5 graphs", _st_12),
        TestCase("ST-13", "SELF_TEST", "MUTATION", "Mutation: opaque-box & wholesale `import Mathlib` rules enforced", _st_13),
        TestCase("ST-14", "SELF_TEST", "E2E_CTRL", "Subprocess E2E: empty project dir exits 1 with 0 tracebacks & valid 164-test JSON", _st_14),
        TestCase("ST-15", "SELF_TEST", "MUTATION", "Mutation: Main.lean vs RESULTS.md inflation & false exact-solution caught", _st_15),
        TestCase("ST-16", "SELF_TEST", "CLI_CTRL", "Subprocess CLI: exit 2 on invalid flags & exact --list counts (164 + 18)", _st_16),
        TestCase("ST-17", "SELF_TEST", "MUTATION", "Adversarial Lean 4 lexer edge cases (unclosed /- & /-/, s!\"{sorry}\", primes, char escapes)", _st_17),
        TestCase("ST-18", "SELF_TEST", "SELF_AUD", "Self-audit of real verify/e2e_audit.lean (0 violations, 24 #print axioms, 0 pollution)", _st_18),
    ]
