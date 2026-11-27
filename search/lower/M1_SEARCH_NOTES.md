# M1 (`LowerFrontier`) Search & Optimization Notes

## Summary
Starting from BPZ v2 (`arXiv:2607.29681` / `spectra-research/shannon-capacity-lean`, `3.258827985920007` at `d=500`) and Tandon (`arXiv:2608.30273`, `3.2588326203532663` at `d=500`), we verified all substitution/code tables and finite certificates, extended `HetGao` closure over Tandon's certified left-operators (`L15AX`, `L30L`), and discovered a strictly stronger **`d = 620`** construction achieving:

$$\Theta(C_7) \ge \frac{3258835618853760}{10^{15}} = 3.258835618853760$$

using only `C_1 = 27,488`, `C_2 = 12,839,823`, and `C_4 = 841,760,069,965,664` (avoiding `C_3` and `g40_8`).

## Verified Baseline Progression
| Construction | Dim `d` | 15-Digit Floor | Notes |
|---|---:|---:|---|
| `PortfolioLower.lean` (repo baseline) | 220 | `3.258827798879807` | `prodStd` + `upg1FreeJ` + `pat3`/`pat4` |
| BPZ v2 (`S2a, S3a, S3b, K4a`) | 500 | `3.258827985920007` | 257-digit witness |
| Tandon (`HetGao` + `S3b` + `K4a`) | 500 | `3.258832620353266` | Uses `C_1, C_2, C_3, C_4` |
| Spec Miner `(g15_het, tn11, tn11)` | 500 | `3.258833086477685` | Drops `g30_6`, `g40_8` |
| Spec Miner `(g25_R, tn11, tn11)` | 540 | `3.258834209135061` | Replaces `g40_8` with `g25_R` |
| Spec Miner `(g30_6, tn11, tn11)` | 560 | `3.258834362237710` | Drops `g40_8` |
| **M1 Champion (`S3b(w40_s0, w65_s1, w50_s2)` + `K4a`)** | **620** | **`3.258835618853760`** | Reuses `L30L` + `L15AX` `HetGao` left-ops |

## Explored Avenues & Negative Results (Dead Ends)
1. **Exhaustive 64.5M `Aut(C_7^5)` scan for 10D `T'` (`search_10d_jplus.cpp`, `13.88 s`, 8 threads):**
   Scanned all `64,538,880` automorphisms `T' ∈ Aut(C_7^5)` maximizing `|(T' × T')(I_10) \ N(X_10^0)|`. Global optimum is `27,480`, achieved by Tandon's `T(w) = (2-w_1, w_3, w_0, 2-w_2, w_4)`.
2. **Exhaustive 10D `0`/`1`-tight swap scan on `J^+` (`scan_10d_swaps.cpp`, `0.34 s`, 8 threads):**
   Scanned all `282,475,249` vertices of `C_7^{10}` against `J^+` (`134,753` vertices). Found **0** improving `0`-tight additions or `(1,1)`-swaps beyond `C_1 = 27,488`.
3. **Track S1 — 5D `PortSystem.ofColoring`, Custom `AuxPartition`, Non-367 & `>= 368` (`track_m1_s1.cpp`, 8 threads):**
   - `R_{5,7}` (`b=10`) `PortSystem m ≥ 3` (`V \ N[S]`, `14,637` vertices): max `|X| = 314 < 367`.
   - `R_9` (`b=9`) `PortSystem m ≥ 3` (`V \ N[S]`, `14,798` vertices): max `|X| = 313 < 367`.
   - `R_{5,7}` (`b=10`, `bip=0`) custom `AuxPartition` (`V \ (N[P_0] ∩ N[P_1])`, `15,667` vertices): max `|X| = 322 < 367`.
   - `baseHetero5D` (`b=8`, `bip=1`) custom `AuxPartition` weighted ILS: max `|X| = 321, |O| = 293` (never escaped `322` trap).
   - `C_7^5` MIS probe from `R_{5,7}`: max `|I| = 367` (no `368` found).
   - Non-367 `b >= 8 + 11*(367 - a)`: drop-1 from `R_{5,7}` (`a=366`) peaked at `b = 15 < 19`; drop-1 from `I_5` peaked at `b = 14 < 19`; 8-thread ILS maximizing `11a + b` peaked at `a=321, b=94` (`3625 < 4045`).
4. **Track S2 — `Γ_Q^⊠2` Lifting (`check_gammaQ.py`, CP-SAT 15s):**
   Per-port quotient `Γ_Q` on `baseHetero5D` collapsed to `K = 32` non-empty blocks; exact CP-SAT on `Γ_Q^⊠2` returned `OPTIMAL = 134,689 < 134,753 = |I_10|`.
5. **CP-SAT `K4` / `S3` & Asymmetric `K4a` Polish (`check_k4_cpsat.py`, `search_s3_cpsat.py`, `check_asym_k4a.py`):**
   - CP-SAT arity-4 `Code` on `v31` (`d=620`): `49` words (`diff = 0` vs `K4a`).
   - CP-SAT arity-3 `Subst` (`T_O = ∅`) on `(w40_s0, w65_s1, w50_s2)`: `45` words (`diff = 0` vs `S3b`).
   - Coordinate polish over `1,036` asymmetric `S3b/S3h/S3a..S3g` candidates in `K4a(v0,v1,v2,v3)`: converged cleanly to symmetric `K4a([S3b(w40_s0, w65_s1, w50_s2)]^4)`.
6. **Repository Base Match Check:**
   Verified `polakSchrijver367Trie == Ilist`, `baseP0 == PV5`, `baseP1 == PH5`, `baseX == Xlist` (exact 0-element symmetric difference!).
