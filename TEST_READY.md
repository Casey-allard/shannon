# E2E Verification Suite Ready (`TEST_READY.md`)

**Status:** READY FOR `M6_Final` EXECUTION (Wave r14 Complete)  
**Track:** `E2E_Track` (Feature F15 — Independent Opaque-Box Verification Suite)  
**Specification:** [`TEST_INFRA.md`](TEST_INFRA.md)  
**Target Toolchain:** `leanprover/lean4:v4.32.2` + `mathlib4@v4.32.2` (Lake `5.0.0`)  
**Runtime Dependencies:** POSIX `bash` + Python 3 standard library only (zero third-party packages, zero network calls)

---

## 1. Suite Inventory & Verified Self-Test Status

| Component | Path | Count | Verification Status |
|---|---|---:|---|
| CLI Wrapper | `verify/run_e2e.sh` | — | Verified (`PYTHONDONTWRITEBYTECODE=1`, dynamic `elan` PATH) |
| Python CLI Driver | `verify/runner.py` | — | Verified (strict exit codes `0` / `1` / `2`, JSON schema v1.0) |
| Shared Harness | `verify/common.py` | — | Verified (Mathlib `.olean` pre-flight guard, `LEAN_NUM_THREADS=2 lake build ShannonC7.Main`, RSS monitoring, zero-traceback boundary) |
| Independent Verifier | `verify/cross_check.py` | — | Verified (single-pass O(N) Lean 4.32.2 fail-closed pure-math lexer, strict axiom whitelist, exact `int`/`Fraction` math, 5-graph obstruction testbed, Option A-Report honesty audit) |
| Opaque-Box Lean Audit | `verify/e2e_audit.lean` | 24 `#print axioms` | Verified (imports ONLY `ShannonC7.Main` + 14 non-deprecated Mathlib leaf modules; independent textbook Fekete equivalence) |
| Tier 1 (Category-Partition) | `verify/tiers/tier1.py` | **70** | `T1-F01-01` .. `T1-F14-05` |
| Tier 2 (BVA & Negative) | `verify/tiers/tier2.py` | **70** | `T2-F01-01` .. `T2-F14-05` |
| Tier 3 (Pairwise Cross-Feature) | `verify/tiers/tier3.py` | **16** | `T3-P01` .. `T3-P16` |
| Tier 4 (Real-World Workloads) | `verify/tiers/tier4.py` | **8** | `T4-W01` .. `T4-W08` |
| **Total E2E Tests** | `verify/tiers/` | **164** | **Ready** |
| Isolated Mutation Self-Tests | `verify/self_test.py` | **18** | **18/18 PASS** (`ST-01` .. `ST-18`, exit 0, 0 bytecode pollution) |

---

## 2. Wave r14 Final Closure Notes

1. **Lake 5.0.0 CLI Compatibility Fix (`verify/common.py`):** Fixed `SuiteContext.run_lean_build()` to invoke `lake build ShannonC7.Main` with `extra_env={"LEAN_NUM_THREADS": "2"}` instead of the unsupported `-j 2` flag (which Lake `5.0.0` rejects with `error: unknown short option '-j'`). Synchronized documentation and test labels in `TEST_INFRA.md` and `verify/tiers/tier{1,3,4}.py`.
2. **Self-Test Verification (`verify/run_e2e.sh --self-test`):** All `18/18` isolated `mktemp -d` positive/negative mutation and CLI control suites pass cleanly with exit code `0` and zero `__pycache__` / `.pyc` pollution.
3. **Pre-M6 Dry Run (`verify/run_e2e.sh --all --no-build`):** `97/164` tests already pass against the 20 built `ShannonC7` modules; all `67/67` remaining failures correspond exclusively to `ShannonC7/Main.lean` and `RESULTS.md` (owned by `M6_Final`).

---

## 3. Execution Commands for `M6_Final`

```bash
# Run isolated self-tests (18/18)
bash verify/run_e2e.sh --self-test

# List exact test inventory (164 E2E + 18 self-tests)
bash verify/run_e2e.sh --list

# Run full 4-tier E2E suite after M6_Final creates ShannonC7/Main.lean & RESULTS.md
bash verify/run_e2e.sh --all --json-out /tmp/e2e_report.json
```
