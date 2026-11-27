#!/usr/bin/env python3
"""
Generate the self-contained, 100% pure-kernel Lean 4 proof `ShannonC7/AlphaC7Cube.lean`
establishing:
  theorem alpha_c7_pow3_le : (strongPowPi (SimpleGraph.cycleGraph 7) 3).indepNum ≤ 33
  theorem alpha_c7_pow3    : (strongPowPi (SimpleGraph.cycleGraph 7) 3).indepNum = 33

Architecture:
  - 49-bit `Nat` bitmasks (`Nat.land`/`Nat.lor`/`Nat.xor`/`Nat.shiftLeft`/`Nat.shiftRight`
    evaluated at C++ GMP speed in Lean v4.32.2's pure kernel, with strict depth-1 `seqN`
    forcing, zero `native_decide`, zero `sorry`, zero `partial`, standard axioms only).
  - Exact 3-orbit classification of all 980 10-element independent sets of `C_7 ⊠ C_7`
    under `Aut(C_7 ⊠ C_7)` (order 392) via 10 canonical candidates.
  - Depth-10 `Tree10` exact common-forbidden tables `c1Tree` and `c2Tree` (2,016 leaves each),
    scatter-verified over all 980 10-sets via loop-hoisted `forAllAut2` + pruned `checkC1`/`checkC2`.
  - Exact 5-profile algebraic reduction for `|S| >= 34`:
      * P1+P3 `(5,5,5,5,5,5,>=4)`: 3-square clique covers (0 L2)
      * P2    `(4,6,4,6,4,6,4)`  : 3-square clique covers (0 L2)
      * P4    `(4,6,4,6,4,5,5)`  : 630/630 root sparse integer 2D Farkas duals (`Grid49`)
      * P5    `(5,5,5,5,4,6,4)`  : root + s0 sparse integer 3-slice Farkas duals (`Grid49`)
  - Self-contained 33-word witness proving `33 ≤ α(C_7^⊠3)` without importing `SmallPowers`.
"""

from __future__ import annotations

import argparse
import itertools
import time
from typing import Dict, List, Optional, Tuple

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csc_matrix

ALL49 = (1 << 49) - 1
COL_MASKS = [sum(1 << (r * 7 + c) for r in range(7)) for c in range(7)]
ROW_MASKS = [0x7F << (r * 7) for r in range(7)]
COL0 = COL_MASKS[0]
COL6 = COL_MASKS[6]
ROW0 = ROW_MASKS[0]
ROW6 = ROW_MASKS[6]
DIAG0 = sum(1 << (r * 7 + r) for r in range(7))
DIAGS_POS = [sum(1 << (r * 7 + (r + d)) for r in range(7 - d)) for d in range(1, 7)]
DIAGS_NEG = [sum(1 << ((c + d) * 7 + c) for c in range(7 - d)) for d in range(1, 7)]

NBR49 = [0] * 49
for _r in range(7):
    for _c in range(7):
        _m = 0
        for _dr in (-1, 0, 1):
            for _dc in (-1, 0, 1):
                _m |= 1 << (((_r + _dr) % 7) * 7 + ((_c + _dc) % 7))
        NBR49[_r * 7 + _c] = _m

SQ22 = [0] * 49
for _r in range(7):
    for _c in range(7):
        _m = 0
        for _dr in (0, 1):
            for _dc in (0, 1):
                _m |= 1 << (((_r + _dr) % 7) * 7 + ((_c + _dc) % 7))
        SQ22[_r * 7 + _c] = _m

REP_PTS: List[List[Tuple[int, int]]] = [
    [(0, 3), (0, 5), (1, 1), (2, 4), (2, 6), (3, 2), (4, 0), (4, 4), (5, 2), (6, 0)],
    [(0, 3), (0, 5), (1, 0), (2, 3), (2, 5), (3, 1), (4, 4), (4, 6), (5, 2), (6, 0)],
    [(0, 3), (0, 5), (1, 1), (2, 3), (2, 6), (3, 1), (4, 4), (4, 6), (5, 2), (6, 0)],
]


def pts_to_mask(pts: List[Tuple[int, int]]) -> int:
    m = 0
    for r, c in pts:
        m |= 1 << (r * 7 + c)
    return m


REPS = [pts_to_mask(p) for p in REP_PTS]
Aut2 = Tuple[bool, bool, int, bool, int]


def apply_aut2_pt(g: Aut2, r: int, c: int) -> Tuple[int, int]:
    sw, sr, tr, sc, tc = g
    r1 = (-r) % 7 if sr else r
    r2 = (r1 + tr) % 7
    c1 = (-c) % 7 if sc else c
    c2 = (c1 + tc) % 7
    return (c2, r2) if sw else (r2, c2)


def apply_aut2_mask(g: Aut2, m: int) -> int:
    out = 0
    for r in range(7):
        for c in range(7):
            if (m >> (r * 7 + c)) & 1:
                r2, c2 = apply_aut2_pt(g, r, c)
                out |= 1 << (r2 * 7 + c2)
    return out


def inv_aut2(g: Aut2) -> Aut2:
    sw, sr, tr, sc, tc = g
    tr_inv = tr if sr else (-tr) % 7
    tc_inv = tc if sc else (-tc) % 7
    if not sw:
        return (False, sr, tr_inv, sc, tc_inv)
    return (True, sc, tc_inv, sr, tr_inv)


def all_aut2() -> List[Aut2]:
    return [
        (sw, sr, tr, sc, tc)
        for sw in (False, True)
        for sr in (False, True)
        for tr in range(7)
        for sc in (False, True)
        for tc in range(7)
    ]


def half_aut2() -> List[Aut2]:
    return [
        (sw, False, tr, sc, tc)
        for sw in (False, True)
        for tr in range(7)
        for sc in (False, True)
        for tc in range(7)
    ]


def closed_nbr(m: int) -> int:
    out = 0
    x = m
    while x:
        lsb = x & -x
        v = lsb.bit_length() - 1
        out |= NBR49[v]
        x ^= lsb
    return out


def row_nbr7(r: int) -> int:
    return r | ((r << 1) & 127) | (r >> 6) | (r >> 1) | ((r & 1) << 6)


def build_canon10_candidates() -> List[int]:
    indep1 = [1 << c for c in range(7)]
    indep2 = [
        (1 << i) | (1 << j)
        for i in range(7)
        for j in range(i + 1, 7)
        if j != i + 1 and not (i == 0 and j == 6)
    ]
    r0 = 1
    r0n = row_nbr7(r0)
    out = []
    for r1 in (4, 8):
        r1n = row_nbr7(r1)
        for r2 in indep2:
            if r2 & r1n:
                continue
            r2n = row_nbr7(r2)
            for r3 in indep1:
                if r3 & r2n:
                    continue
                r3n = row_nbr7(r3)
                for r4 in indep2:
                    if r4 & r3n:
                        continue
                    r4n = row_nbr7(r4)
                    for r5 in indep1:
                        if r5 & r4n:
                            continue
                        r5n = row_nbr7(r5)
                        for r6 in indep2:
                            if (r6 & r5n) or (r6 & r0n):
                                continue
                            m = r0 | (r1 << 7) | (r2 << 14) | (r3 << 21) | (r4 << 28) | (r5 << 35) | (r6 << 42)
                            out.append(m)
    return out


def subsets_of_list(pts: List[Tuple[int, int]], k: int) -> List[int]:
    if k == 0:
        return [0]
    if not pts:
        return []
    r, c = pts[0]
    bit = 1 << (r * 7 + c)
    with_first = [m | bit for m in subsets_of_list(pts[1:], k - 1)]
    without_first = subsets_of_list(pts[1:], k)
    return with_first + without_first


def halves5(k: int) -> List[int]:
    r0, c0 = REP_PTS[k][0]
    assert (r0, c0) == (0, 3)
    bit0 = 1 << (r0 * 7 + c0)
    return [m | bit0 for m in subsets_of_list(REP_PTS[k][1:], 4)]


def subs4(k: int) -> List[int]:
    return subsets_of_list(REP_PTS[k], 4)


def find_sq3(avail: int) -> Optional[Tuple[int, int, int]]:
    if avail.bit_count() <= 3:
        return None
    cands = sorted(
        {i for i in range(49) if SQ22[i] & avail},
        key=lambda i: -(SQ22[i] & avail).bit_count(),
    )
    for idx_i, a in enumerate(cands):
        rem1 = avail & ~SQ22[a]
        if rem1 == 0:
            return (a, a, a)
        for idx_j in range(idx_i, len(cands)):
            b = cands[idx_j]
            if not (SQ22[b] & rem1):
                continue
            rem2 = rem1 & ~SQ22[b]
            if rem2 == 0:
                return (a, b, b)
            for idx_k in range(idx_j, len(cands)):
                c = cands[idx_k]
                if (rem2 & ~SQ22[c]) == 0:
                    return (a, b, c)
    return None


C2D_MASK: List[int] = []
C2D_RHS: List[int] = []
C2D_LEAN: List[str] = []
for _r in range(7):
    for _c in range(7):
        C2D_MASK.append(SQ22[_r * 7 + _c])
        C2D_RHS.append(1)
        C2D_LEAN.append(f"cS {_r} {_c}")
for _r in range(7):
    _m = 0
    for _dr in (0, 1):
        for _c in range(7):
            _m |= 1 << (((_r + _dr) % 7) * 7 + _c)
    C2D_MASK.append(_m)
    C2D_RHS.append(3)
    C2D_LEAN.append(f"cR {_r}")
for _c in range(7):
    _m = 0
    for _dc in (0, 1):
        for _r in range(7):
            _m |= 1 << (_r * 7 + ((_c + _dc) % 7))
    C2D_MASK.append(_m)
    C2D_RHS.append(3)
    C2D_LEAN.append(f"cC {_c}")
C2D_MASK.append(ALL49)
C2D_RHS.append(10)
C2D_LEAN.append("cA")

A2D = np.array([[(C2D_MASK[i] >> v) & 1 for v in range(49)] for i in range(63)], dtype=float)
RHS2D = C2D_RHS[:63]

ROWS3D = np.zeros((128, 147), dtype=float)
RHS3D = [0] * 128
for _i in range(64):
    for _v in range(49):
        if (C2D_MASK[_i] >> _v) & 1:
            ROWS3D[_i, _v] = 1.0
            ROWS3D[_i, 49 + _v] = 1.0
            ROWS3D[64 + _i, 49 + _v] = 1.0
            ROWS3D[64 + _i, 98 + _v] = 1.0
    RHS3D[_i] = C2D_RHS[_i]
    RHS3D[64 + _i] = C2D_RHS[_i]
A3D_CSC = csc_matrix(ROWS3D)


def solve_int_farkas(
    A_mat, rows_dense: np.ndarray, rhs_list: List[int], act: np.ndarray, target: int
) -> Optional[Tuple[int, List[Tuple[int, int]]]]:
    n_vars = rows_dense.shape[1]
    res = linprog(
        -act.astype(float),
        A_ub=A_mat,
        b_ub=np.array(rhs_list, dtype=float),
        bounds=[(0, None)] * n_vars,
        method="highs",
    )
    if not res.success or (-res.fun) > target - 1e-6:
        return None
    y = np.maximum(-res.ineqlin.marginals, 0.0)
    nz = [i for i in range(len(rhs_list)) if y[i] > 1e-7]
    active_idx = np.where(act > 0)[0]
    for D in (1, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 30, 40, 60, 100, 120, 240, 1000, 10000):
        yi = np.zeros(len(rhs_list), dtype=int)
        for i in nz:
            yi[i] = int(np.ceil(y[i] * D - 1e-6))
        tot_rhs = int(sum(yi[i] * rhs_list[i] for i in nz))
        if tot_rhs >= target * D:
            continue
        cov = yi @ rows_dense
        if np.all(cov[active_idx] >= D):
            for i in nz:
                while yi[i] > 0:
                    yi[i] -= 1
                    cov_try = cov - rows_dense[i]
                    if np.all(cov_try[active_idx] >= D):
                        cov = cov_try
                    else:
                        yi[i] += 1
                        break
            terms = [(i, int(yi[i])) for i in nz if yi[i] > 0]
            assert sum(w * rhs_list[i] for i, w in terms) < target * D
            return (D, terms)
    raise RuntimeError(f"Failed to round Farkas dual (LP={-res.fun:.6f}, target={target})")


def fmt_farkas2d(D: int, terms: List[Tuple[int, int]]) -> str:
    ts = ", ".join(f"({C2D_LEAN[i]}, {w})" for i, w in terms)
    return f"({D}, [{ts}])"


def fmt_farkas3d(D: int, terms: List[Tuple[int, int]]) -> str:
    t0 = [(i, w) for i, w in terms if i < 64]
    t1 = [(i - 64, w) for i, w in terms if i >= 64]
    s0 = ", ".join(f"({C2D_LEAN[i]}, {w})" for i, w in t0)
    s1 = ", ".join(f"({C2D_LEAN[i]}, {w})" for i, w in t1)
    return f"({D}, [{s0}], [{s1}])"


def fmt_tree10_defs(prefix: str, k: int, val_map: Dict[int, int]) -> str:
    pts = REP_PTS[k]

    def rec(idx: int, cur_sz: int, cur_mask: int) -> str:
        if cur_sz > 6 or cur_sz + (10 - idx) < 4:
            return "tE"
        if idx == 10:
            return f"(tL {val_map[cur_mask]})"
        r, c = pts[idx]
        bit = 1 << (r * 7 + c)
        left = rec(idx + 1, cur_sz, cur_mask)
        right = rec(idx + 1, cur_sz + 1, cur_mask | bit)
        return f"(tN {left} {right})"

    r0, c0 = pts[0]
    r1, c1 = pts[1]
    b0 = 1 << (r0 * 7 + c0)
    b1 = 1 << (r1 * 7 + c1)
    q00 = rec(2, 0, 0)
    q01 = rec(2, 1, b1)
    q10 = rec(2, 1, b0)
    q11 = rec(2, 2, b0 | b1)
    return (
        f"private def {prefix}_00 : Tree10 := {q00}\n"
        f"private def {prefix}_01 : Tree10 := {q01}\n"
        f"private def {prefix}_10 : Tree10 := {q10}\n"
        f"private def {prefix}_11 : Tree10 := {q11}\n"
        f"private def {prefix} : Tree10 :=\n"
        f"  tN (tN {prefix}_00 {prefix}_01) (tN {prefix}_10 {prefix}_11)"
    )


def gen_sq22_table() -> str:
    lines = ["private def sq22 (idx : Fin 49) : Nat :=", "  match idx.val with"]
    for idx in range(48):
        lines.append(f"  | {idx} => {SQ22[idx]}")
    lines.append(f"  | _ => {SQ22[48]}")
    return "\n".join(lines)


def collect_aut2_near(k: int, m_min: int) -> List[Tuple[int, Aut2, int]]:
    """Exact same element & prepend order as Lean `nearK k m_min` via `collectAut2`."""
    acc: List[Tuple[int, Aut2, int]] = []
    for k0, half in ((0, False), (1, False), (2, True)):
        srs = (False,) if half else (False, True)
        for sr in srs:
            for tr in range(7):
                for sc in (False, True):
                    for tc in range(7):
                        for sw in (False, True):
                            g: Aut2 = (sw, sr, tr, sc, tc)
                            B = apply_aut2_mask(g, REPS[k0])
                            if (B & REPS[k]).bit_count() >= m_min:
                                acc.append((k0, g, B))
    acc.reverse()
    return acc


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", default="ShannonC7/AlphaC7Cube.lean")
    args = parser.parse_args()
    t0 = time.perf_counter()

    auts_all = all_aut2()
    auts_half = half_aut2()
    sets10_tagged: List[Tuple[int, Aut2, int]] = []
    for g in auts_all:
        sets10_tagged.append((0, g, apply_aut2_mask(g, REPS[0])))
    for g in auts_all:
        sets10_tagged.append((1, g, apply_aut2_mask(g, REPS[1])))
    for g in auts_half:
        sets10_tagged.append((2, g, apply_aut2_mask(g, REPS[2])))
    assert len(sets10_tagged) == 980
    assert len({m for _, _, m in sets10_tagged}) == 980

    mask_to_kg: Dict[int, Tuple[int, Aut2]] = {m: (k, g) for k, g, m in sets10_tagged}
    canon_cands = build_canon10_candidates()
    canon_wits = [mask_to_kg[m] for m in canon_cands]
    print(f"[OK] canon10Candidates count = {len(canon_cands)}")

    near4 = [collect_aut2_near(k, 4) for k in range(3)]
    near5 = [collect_aut2_near(k, 5) for k in range(3)]
    near6 = [collect_aut2_near(k, 6) for k in range(3)]

    ext_all: Dict[int, List[int]] = {}
    for _, _, B in sets10_tagged:
        bits = [v for v in range(49) if (B >> v) & 1]
        for sz in (4, 5, 6):
            for comb in itertools.combinations(bits, sz):
                m = 0
                for v in comb:
                    m |= 1 << v
                ext_all.setdefault(m, []).append(B)

    c1_maps: List[Dict[int, int]] = [{}, {}, {}]
    for k in range(3):
        for sz in (4, 5, 6):
            for X in subsets_of_list(REP_PTS[k], sz):
                c1 = ALL49
                for B in ext_all[X]:
                    c1 &= closed_nbr(B ^ X)
                c1_maps[k][X] = c1

    def eval_c1(m: int) -> int:
        c1 = ALL49
        for B in ext_all[m]:
            c1 &= closed_nbr(B ^ m)
        return c1

    c2_maps: List[Dict[int, int]] = [{}, {}, {}]
    for k in range(3):
        for sz in (4, 5, 6):
            for X in subsets_of_list(REP_PTS[k], sz):
                c2 = ALL49
                for B in ext_all[X]:
                    c2 &= eval_c1(B ^ X)
                c2_maps[k][X] = c2
    print("[OK] Computed exact C1 and C2 trees (2016 entries each)")

    # P1+P3 certs
    p13_certs: List[List[str]] = [[], [], []]
    for k in range(3):
        for S2 in halves5(k):
            S3 = REPS[k] ^ S2
            avail = ALL49 ^ (c2_maps[k][S2] | c2_maps[k][S3])
            if avail.bit_count() <= 3:
                p13_certs[k].append(".pop3")
                continue
            cov = find_sq3(avail)
            if cov is not None:
                p13_certs[k].append(f".sq3 {cov[0]} {cov[1]} {cov[2]}")
                continue
            L1 = [t for t in near5[k] if (S2 & t[2]) == S2]
            R4 = [t for t in near5[k] if (S3 & t[2]) == S3]
            covs = []
            seen = set()
            for k1, g1, _ in L1:
                y1c = REPS[k1] ^ apply_aut2_mask(inv_aut2(g1), S2)
                c1L = apply_aut2_mask(g1, c1_maps[k1][y1c])
                for k4, g4, _ in R4:
                    y4c = REPS[k4] ^ apply_aut2_mask(inv_aut2(g4), S3)
                    c1R = apply_aut2_mask(g4, c1_maps[k4][y4c])
                    av = ALL49 ^ (c1L | c1R)
                    if av.bit_count() <= 3:
                        continue
                    c = find_sq3(av)
                    assert c is not None
                    if c not in seen:
                        seen.add(c)
                        covs.append(c)
            cs = ", ".join(f"({a}, {b}, {c})" for a, b, c in covs)
            p13_certs[k].append(f".splitL1 [{cs}]")

    # P2 certs
    p2_certs: List[List[str]] = [[], [], []]
    for k in range(3):
        for S2 in subs4(k):
            S3 = REPS[k] ^ S2
            avail = ALL49 ^ (c2_maps[k][S2] | c2_maps[k][S3])
            if avail.bit_count() <= 3:
                p2_certs[k].append(".pop3")
                continue
            cov = find_sq3(avail)
            if cov is not None:
                p2_certs[k].append(f".sq3 {cov[0]} {cov[1]} {cov[2]}")
                continue
            L1 = [t for t in near4[k] if (S2 & t[2]) == S2]
            R4 = [t for t in near6[k] if (S3 & t[2]) == S3]
            covs = []
            seen = set()
            for k1, g1, _ in L1:
                y1c = REPS[k1] ^ apply_aut2_mask(inv_aut2(g1), S2)
                c1L = apply_aut2_mask(g1, c1_maps[k1][y1c])
                for k4, g4, _ in R4:
                    y4c = REPS[k4] ^ apply_aut2_mask(inv_aut2(g4), S3)
                    c1R = apply_aut2_mask(g4, c1_maps[k4][y4c])
                    av = ALL49 ^ (c1L | c1R)
                    if av.bit_count() <= 3:
                        continue
                    c = find_sq3(av)
                    assert c is not None
                    if c not in seen:
                        seen.add(c)
                        covs.append(c)
            cs = ", ".join(f"({a}, {b}, {c})" for a, b, c in covs)
            p2_certs[k].append(f".splitL1 [{cs}]")

    # P4 certs
    p4_certs: List[List[str]] = [[], [], []]
    for k in range(3):
        for S2 in subs4(k):
            S1 = REPS[k] ^ S2
            F = c1_maps[k][S1] & c2_maps[k][S2]
            act = np.array([0 if ((F >> v) & 1) else 1 for v in range(49)], dtype=int)
            res = solve_int_farkas(A2D, A2D, RHS2D, act, 10)
            assert res is not None
            p4_certs[k].append(fmt_farkas2d(res[0], res[1]))

    # P5 certs
    def solve_p5_leaf(CL: int, CR: int) -> Optional[Tuple[int, List[Tuple[int, int]]]]:
        act = np.zeros(147, dtype=int)
        for v in range(49):
            if not ((CR >> v) & 1):
                act[v] = 1
            act[49 + v] = 1
            if not ((CL >> v) & 1):
                act[98 + v] = 1
        return solve_int_farkas(A3D_CSC, ROWS3D, RHS3D, act, 14)

    p5_certs: List[List[str]] = [[], [], []]
    p5_stats = [0, 0, 0]
    for k in range(3):
        for S1 in halves5(k):
            S2 = REPS[k] ^ S1
            CL = c1_maps[k][S1]
            CR = c1_maps[k][S2]
            r = solve_p5_leaf(CL, CR)
            if r is not None:
                p5_certs[k].append(f".root {fmt_farkas3d(r[0], r[1])}")
                p5_stats[0] += 1
                continue
            s0_items: List[str] = []
            for _, _, B0 in near5[k]:
                if (S1 & B0) != S1:
                    continue
                n0 = closed_nbr(B0 ^ S1)
                r0 = solve_p5_leaf(n0, CR)
                if r0 is not None:
                    s0_items.append(f".leaf {fmt_farkas3d(r0[0], r0[1])}")
                    p5_stats[1] += 1
                    continue
                s3_items: List[str] = []
                for _, _, B3 in near5[k]:
                    if (S2 & B3) != S2:
                        continue
                    r3 = solve_p5_leaf(n0, closed_nbr(B3 ^ S2))
                    assert r3 is not None
                    s3_items.append(fmt_farkas3d(r3[0], r3[1]))
                    p5_stats[2] += 1
                s0_items.append(f".splitS3 [{', '.join(s3_items)}]")
            p5_certs[k].append(f".splitS0 [{', '.join(s0_items)}]")
    print(f"[OK] P5 certs: root={p5_stats[0]}, s0_leaf={p5_stats[1]}, s3_leaf={p5_stats[2]}")

    def fmt_aut2(g: Aut2) -> str:
        sw, sr, tr, sc, tc = g
        return f"⟨{'true' if sw else 'false'}, {'true' if sr else 'false'}, {tr}, {'true' if sc else 'false'}, {tc}⟩"

    def fmt_list_lines(items: List[str], per_line: int = 1) -> str:
        lines = []
        for i in range(0, len(items), per_line):
            lines.append("  " + ", ".join(items[i:i + per_line]))
        return "[\n" + ",\n".join(lines) + "\n]"

    replacements = {
        "__ALL49__": str(ALL49),
        "__COL0__": str(COL0),
        "__COL6__": str(COL6),
        "__NOT_COL0__": str(ALL49 ^ COL0),
        "__NOT_COL6__": str(ALL49 ^ COL6),
        "__ROW0__": str(ROW0),
        "__ROW6__": str(ROW6),
        "__NOT_ROW0__": str(ALL49 ^ ROW0),
        "__NOT_ROW6__": str(ALL49 ^ ROW6),
        "__RM0__": str(ROW_MASKS[0]), "__RM1__": str(ROW_MASKS[1]), "__RM2__": str(ROW_MASKS[2]),
        "__RM3__": str(ROW_MASKS[3]), "__RM4__": str(ROW_MASKS[4]), "__RM5__": str(ROW_MASKS[5]),
        "__RM6__": str(ROW_MASKS[6]),
        "__CM0__": str(COL_MASKS[0]), "__CM1__": str(COL_MASKS[1]), "__CM2__": str(COL_MASKS[2]),
        "__CM3__": str(COL_MASKS[3]), "__CM4__": str(COL_MASKS[4]), "__CM5__": str(COL_MASKS[5]),
        "__CM6__": str(COL_MASKS[6]),
        "__SRLO1__": str((1 << 42) - 1), "__SRHI1__": str(ALL49 ^ ((1 << 42) - 1)),
        "__SRLO2__": str((1 << 35) - 1), "__SRHI2__": str(ALL49 ^ ((1 << 35) - 1)),
        "__SRLO3__": str((1 << 28) - 1), "__SRHI3__": str(ALL49 ^ ((1 << 28) - 1)),
        "__SRLO4__": str((1 << 21) - 1), "__SRHI4__": str(ALL49 ^ ((1 << 21) - 1)),
        "__SRLO5__": str((1 << 14) - 1), "__SRHI5__": str(ALL49 ^ ((1 << 14) - 1)),
        "__SRLO6__": str((1 << 7) - 1),  "__SRHI6__": str(ALL49 ^ ((1 << 7) - 1)),
        "__SCLO1__": str(sum(COL_MASKS[:6])), "__SCHI1__": str(sum(COL_MASKS[6:])),
        "__SCLO2__": str(sum(COL_MASKS[:5])), "__SCHI2__": str(sum(COL_MASKS[5:])),
        "__SCLO3__": str(sum(COL_MASKS[:4])), "__SCHI3__": str(sum(COL_MASKS[4:])),
        "__SCLO4__": str(sum(COL_MASKS[:3])), "__SCHI4__": str(sum(COL_MASKS[3:])),
        "__SCLO5__": str(sum(COL_MASKS[:2])), "__SCHI5__": str(sum(COL_MASKS[2:])),
        "__SCLO6__": str(sum(COL_MASKS[:1])), "__SCHI6__": str(sum(COL_MASKS[1:])),
        "__DIAG0__": str(DIAG0),
        "__DP1__": str(DIAGS_POS[0]), "__DP2__": str(DIAGS_POS[1]), "__DP3__": str(DIAGS_POS[2]),
        "__DP4__": str(DIAGS_POS[3]), "__DP5__": str(DIAGS_POS[4]), "__DP6__": str(DIAGS_POS[5]),
        "__DN1__": str(DIAGS_NEG[0]), "__DN2__": str(DIAGS_NEG[1]), "__DN3__": str(DIAGS_NEG[2]),
        "__DN4__": str(DIAGS_NEG[3]), "__DN5__": str(DIAGS_NEG[4]), "__DN6__": str(DIAGS_NEG[5]),
        "__REP0__": str(REPS[0]), "__REP1__": str(REPS[1]), "__REP2__": str(REPS[2]),
        "__REPBITS0__": ", ".join(str(1 << (r * 7 + c)) for r, c in REP_PTS[0]),
        "__REPBITS1__": ", ".join(str(1 << (r * 7 + c)) for r, c in REP_PTS[1]),
        "__REPBITS2__": ", ".join(str(1 << (r * 7 + c)) for r, c in REP_PTS[2]),
        "__SQ22_DEF__": gen_sq22_table(),
        "__CANON_WITS__": ",\n  ".join(f"({k}, {fmt_aut2(g)})" for k, g in canon_wits),
        "__C1_TREE_DEFS__": "\n".join(fmt_tree10_defs(f"c1Tree{k}", k, c1_maps[k]) for k in range(3)),
        "__C2_TREE_DEFS__": "\n".join(fmt_tree10_defs(f"c2Tree{k}", k, c2_maps[k]) for k in range(3)),
        "__P13_0__": fmt_list_lines(p13_certs[0], 6),
        "__P13_1__": fmt_list_lines(p13_certs[1], 6),
        "__P13_2__": fmt_list_lines(p13_certs[2], 6),
        "__P2_0__": fmt_list_lines(p2_certs[0], 6),
        "__P2_1__": fmt_list_lines(p2_certs[1], 6),
        "__P2_2__": fmt_list_lines(p2_certs[2], 6),
        "__P4_0__": fmt_list_lines(p4_certs[0], 1),
        "__P4_1__": fmt_list_lines(p4_certs[1], 1),
        "__P4_2__": fmt_list_lines(p4_certs[2], 1),
        "__P5_0__": fmt_list_lines(p5_certs[0], 1),
        "__P5_1__": fmt_list_lines(p5_certs[1], 1),
        "__P5_2__": fmt_list_lines(p5_certs[2], 1),
    }

    text = LEAN_TEMPLATE
    for k_str, v_str in replacements.items():
        assert k_str in text, f"Missing placeholder {k_str}"
        text = text.replace(k_str, v_str)

    with open(args.out, "w") as f:
        f.write(text)
    print(f"[OK] Wrote {args.out} ({len(text) / 1024:.1f} KiB) in {time.perf_counter() - t0:.2f} s")


LEAN_TEMPLATE = r'''import ShannonC7.Defs
import ShannonC7.CycleC7
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Exact Independence Number `α(C₇^⊠3) = 33` (`ShannonC7/AlphaC7Cube.lean`)

Pure-kernel Lean 4 proof (zero `sorry`, zero `native_decide`, zero `partial`, standard axioms
`{propext, Classical.choice, Quot.sound}` only) establishing:
- `alpha_c7_pow3_le : (strongPowPi (SimpleGraph.cycleGraph 7) 3).indepNum ≤ 33`
- `alpha_c7_pow3 : (strongPowPi (SimpleGraph.cycleGraph 7) 3).indepNum = 33`
-/

namespace ShannonC7

noncomputable section

/-! ## Section 1: 49-Bit `Nat` Bitsets, SWAR Popcount & Bit-Permutation Primitives -/

private lemma fin3_cases {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ x : Fin 3, P x
  | ⟨0, _⟩ => h0 | ⟨1, _⟩ => h1 | ⟨2, _⟩ => h2

private lemma fin7_cases {P : Fin 7 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) :
    ∀ x : Fin 7, P x
  | ⟨0, _⟩ => h0 | ⟨1, _⟩ => h1 | ⟨2, _⟩ => h2 | ⟨3, _⟩ => h3
  | ⟨4, _⟩ => h4 | ⟨5, _⟩ => h5 | ⟨6, _⟩ => h6

private def next7 (x : Fin 7) : Fin 7 :=
  match x.val with
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 6 | _ => 0

private def prev7 (x : Fin 7) : Fin 7 :=
  match x.val with
  | 0 => 6 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4 | _ => 5

private def neg7 (x : Fin 7) : Fin 7 :=
  match x.val with
  | 0 => 0 | 1 => 6 | 2 => 5 | 3 => 4 | 4 => 3 | 5 => 2 | _ => 1

private def add7 (x y : Fin 7) : Fin 7 :=
  ⟨(x.val + y.val) % 7, Nat.mod_lt _ (by decide)⟩

private def toZ7 (x : Fin 7) : ZMod 7 := (x.val : ZMod 7)
private def ofZ7 (x : ZMod 7) : Fin 7 := ⟨x.val, x.val_lt⟩

private lemma toZ7_ofZ7 (x : ZMod 7) : toZ7 (ofZ7 x) = x := ZMod.natCast_zmod_val x

private lemma ofZ7_toZ7 : ∀ x : Fin 7, ofZ7 (toZ7 x) = x
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ => rfl

private lemma toZ7_injective : Function.Injective toZ7 := by
  intro a b h
  have := congrArg ofZ7 h
  simpa [ofZ7_toZ7] using this

private lemma toZ7_next7 : ∀ x : Fin 7, toZ7 (next7 x) = toZ7 x + 1 := by decide
private lemma toZ7_prev7 : ∀ x : Fin 7, toZ7 (prev7 x) = toZ7 x - 1 := by decide
private lemma toZ7_neg7 : ∀ x : Fin 7, toZ7 (neg7 x) = -toZ7 x := by decide
private lemma toZ7_add7 : ∀ x y : Fin 7, toZ7 (add7 x y) = toZ7 x + toZ7 y := by decide

private lemma c7Close_iff : ∀ a b : Fin 7,
    (toZ7 a = toZ7 b ∨ C7.Adj (toZ7 a) (toZ7 b)) ↔
      (a = prev7 b ∨ a = b ∨ a = next7 b) := by decide

private lemma d7_inv_left (s : Bool) (t x : Fin 7) :
    add7 (if s then neg7 (add7 (if s then neg7 x else x) t) else add7 (if s then neg7 x else x) t)
      (if s then t else neg7 t) = x := by
  apply toZ7_injective
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, toZ7_add7, toZ7_neg7] <;> ring

private lemma d7_inv_right (s : Bool) (t x : Fin 7) :
    add7 (if s then neg7 (add7 (if s then neg7 x else x) (if s then t else neg7 t))
          else add7 (if s then neg7 x else x) (if s then t else neg7 t)) t = x := by
  apply toZ7_injective
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, toZ7_add7, toZ7_neg7] <;> ring

private lemma d7_comp (s1 s2 : Bool) (t1 t2 x : Fin 7) :
    add7 (if s1 then neg7 (add7 (if s2 then neg7 x else x) t2) else add7 (if s2 then neg7 x else x) t2) t1 =
      add7 (if xor s1 s2 then neg7 x else x) (add7 (if s1 then neg7 t2 else t2) t1) := by
  apply toZ7_injective
  cases s1 <;> cases s2 <;> simp [xor, toZ7_add7, toZ7_neg7] <;> ring

private lemma land_eq (a b : Nat) : Nat.land a b = a &&& b := rfl
private lemma lor_eq (a b : Nat) : Nat.lor a b = a ||| b := rfl
private lemma xor_eq (a b : Nat) : Nat.xor a b = a ^^^ b := rfl
private lemma shl_eq (a b : Nat) : Nat.shiftLeft a b = a <<< b := rfl
private lemma shr_eq (a b : Nat) : Nat.shiftRight a b = a >>> b := rfl
private lemma add_eq (a b : Nat) : Nat.add a b = a + b := rfl
private lemma sub_eq (a b : Nat) : Nat.sub a b = a - b := rfl
private lemma mul_eq (a b : Nat) : Nat.mul a b = a * b := rfl
private lemma beq_eq (a b : Nat) : Nat.beq a b = (a == b) := by
  cases h : Nat.beq a b
  · have hne : a ≠ b := fun heq => by subst heq; simp at h
    exact (beq_false_of_ne hne).symm
  · have heq : a = b := Nat.eq_of_beq_eq_true h
    subst heq; simp

private def ALL49 : Nat := __ALL49__

private def seqN {α : Type} (x : Nat) (k : Nat → α) : α :=
  match Nat.beq x 0 with | true => k 0 | false => k x

private lemma seqN_eq {α : Type} (x : Nat) (k : Nat → α) : seqN x k = k x := by
  unfold seqN; rw [beq_eq]
  cases h : (x == 0)
  · rfl
  · rw [beq_iff_eq.mp h]

private def bit49 (r c : Fin 7) : Nat := Nat.shiftLeft 1 (Nat.add (Nat.mul r.val 7) c.val)
private def get49 (m : Nat) (r c : Fin 7) : Bool := m.testBit (r.val * 7 + c.val)
private def row49 (m : Nat) (r : Fin 7) : Nat := Nat.land (Nat.shiftRight m (Nat.mul r.val 7)) 127
private def not49 (m : Nat) : Nat := Nat.xor ALL49 m
private def diff49 (a b : Nat) : Nat := Nat.land a (Nat.xor ALL49 b)
private def set49 (m : Nat) (r c : Fin 7) : Nat := Nat.lor m (bit49 r c)
private def subset49 (a b : Nat) : Bool := Nat.beq (Nat.land a b) a
private def disjoint49 (a b : Nat) : Bool := Nat.beq (Nat.land a b) 0

private lemma all49_eq : ALL49 = 2 ^ 49 - 1 := rfl

private lemma testBit_all49 (i : Nat) : ALL49.testBit i = decide (i < 49) := by
  rw [all49_eq, Nat.testBit_two_pow_sub_one]

private lemma testBit_all49_lt {i : Nat} (hi : i < 49) : ALL49.testBit i = true := by
  rw [testBit_all49]; exact decide_eq_true hi

private lemma idx_lt49 (r c : Fin 7) : r.val * 7 + c.val < 49 := by omega

private lemma pow2_mono {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h

private lemma testBit_lt49 {m : Nat} (hm : m < 2 ^ 49) {i : Nat} (hi : 49 ≤ i) :
    m.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (pow2_mono hi))

private lemma ext49 {a b : Nat} (ha : a < 2 ^ 49) (hb : b < 2 ^ 49)
    (h : ∀ r c : Fin 7, get49 a r c = get49 b r c) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 49
  · let r : Fin 7 := ⟨i / 7, Nat.div_lt_of_lt_mul hi⟩
    let c : Fin 7 := ⟨i % 7, Nat.mod_lt _ (by decide)⟩
    have heq : r.val * 7 + c.val = i := by
      dsimp [r, c]; omega
    have hr := h r c
    unfold get49 at hr
    rwa [heq] at hr
  · rw [testBit_lt49 ha (by omega), testBit_lt49 hb (by omega)]

private lemma bit49_lt (r c : Fin 7) : bit49 r c < 2 ^ 49 := by
  unfold bit49
  rw [shl_eq, add_eq, mul_eq, Nat.shiftLeft_eq, one_mul]
  exact Nat.pow_lt_pow_right (by decide) (idx_lt49 r c)

private lemma testBit_bit49 (r c r' c' : Fin 7) :
    (bit49 r c).testBit (r'.val * 7 + c'.val) = decide (r' = r ∧ c' = c) := by
  unfold bit49
  rw [shl_eq, add_eq, mul_eq, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
  have hiff : r.val * 7 + c.val = r'.val * 7 + c'.val ↔ r' = r ∧ c' = c := by
    constructor
    · intro h
      have hr : r'.val = r.val := by omega
      have hc : c'.val = c.val := by omega
      exact ⟨Fin.ext hr, Fin.ext hc⟩
    · rintro ⟨rfl, rfl⟩; rfl
  simp only [hiff]

private lemma get49_zero (r c : Fin 7) : get49 0 r c = false := Nat.zero_testBit _
private lemma get49_and (a b : Nat) (r c : Fin 7) : get49 (a &&& b) r c = (get49 a r c && get49 b r c) :=
  Nat.testBit_and a b _
private lemma get49_or (a b : Nat) (r c : Fin 7) : get49 (a ||| b) r c = (get49 a r c || get49 b r c) :=
  Nat.testBit_or a b _
private lemma get49_not (a : Nat) (r c : Fin 7) : get49 (not49 a) r c = !get49 a r c := by
  unfold get49 not49; rw [xor_eq, Nat.testBit_xor, testBit_all49_lt (idx_lt49 r c)]; cases a.testBit _ <;> rfl
private lemma get49_diff (a b : Nat) (r c : Fin 7) : get49 (diff49 a b) r c = (get49 a r c && !get49 b r c) := by
  unfold diff49; rw [land_eq]; change get49 (a &&& not49 b) r c = _; rw [get49_and, get49_not]
private lemma get49_set (a : Nat) (r c r' c' : Fin 7) :
    get49 (set49 a r c) r' c' = (if r' = r ∧ c' = c then true else get49 a r' c') := by
  unfold set49 get49
  rw [lor_eq, Nat.testBit_or, testBit_bit49]
  by_cases h : r' = r ∧ c' = c <;> simp [h]

private lemma and_lt49 {a b : Nat} (hb : b < 2 ^ 49) : a &&& b < 2 ^ 49 := Nat.and_lt_two_pow a hb
private lemma and_lt49_left {a b : Nat} (ha : a < 2 ^ 49) : a &&& b < 2 ^ 49 := by
  rw [Nat.and_comm]; exact Nat.and_lt_two_pow b ha
private lemma or_lt49 {a b : Nat} (ha : a < 2 ^ 49) (hb : b < 2 ^ 49) : a ||| b < 2 ^ 49 :=
  Nat.or_lt_two_pow ha hb
private lemma not49_lt {a : Nat} (ha : a < 2 ^ 49) : not49 a < 2 ^ 49 := by
  unfold not49; rw [xor_eq]; exact Nat.xor_lt_two_pow (by decide) ha
private lemma diff49_lt {a b : Nat} (ha : a < 2 ^ 49) : diff49 a b < 2 ^ 49 := by
  unfold diff49; rw [land_eq]; exact and_lt49_left ha
private lemma set49_lt {a : Nat} (ha : a < 2 ^ 49) (r c : Fin 7) : set49 a r c < 2 ^ 49 := by
  unfold set49; rw [lor_eq]; exact or_lt49 ha (bit49_lt r c)

private lemma subset49_iff {a b : Nat} (ha : a < 2 ^ 49) :
    subset49 a b = true ↔ ∀ r c : Fin 7, get49 a r c = true → get49 b r c = true := by
  unfold subset49
  rw [beq_eq, land_eq, beq_iff_eq]
  constructor
  · intro heq r c h
    have hbit := congrArg (fun x => x.testBit (r.val * 7 + c.val)) heq
    rw [Nat.testBit_and] at hbit
    unfold get49 at h ⊢
    rw [h, Bool.true_and] at hbit
    exact hbit
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    by_cases hi : i < 49
    · let r : Fin 7 := ⟨i / 7, Nat.div_lt_of_lt_mul hi⟩
      let c : Fin 7 := ⟨i % 7, Nat.mod_lt _ (by decide)⟩
      have heq : r.val * 7 + c.val = i := by dsimp [r, c]; omega
      cases ha' : a.testBit i
      · rfl
      · have hb' := h r c (by unfold get49; rwa [heq])
        unfold get49 at hb'; rw [heq] at hb'; rw [hb']; rfl
    · rw [testBit_lt49 ha (by omega)]; rfl

private lemma disjoint49_iff {a b : Nat} (ha : a < 2 ^ 49) :
    disjoint49 a b = true ↔ ∀ r c : Fin 7, get49 a r c = true → get49 b r c = false := by
  unfold disjoint49
  rw [beq_eq, land_eq, beq_iff_eq]
  constructor
  · intro heq r c h
    have hbit := congrArg (fun x => x.testBit (r.val * 7 + c.val)) heq
    rw [Nat.testBit_and, Nat.zero_testBit] at hbit
    unfold get49 at h ⊢
    rw [h, Bool.true_and] at hbit
    exact hbit
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hi : i < 49
    · let r : Fin 7 := ⟨i / 7, Nat.div_lt_of_lt_mul hi⟩
      let c : Fin 7 := ⟨i % 7, Nat.mod_lt _ (by decide)⟩
      have heq : r.val * 7 + c.val = i := by dsimp [r, c]; omega
      cases ha' : a.testBit i
      · rfl
      · have hb' := h r c (by unfold get49; rwa [heq])
        unfold get49 at hb'; rw [heq] at hb'; rw [hb']; rfl
    · rw [testBit_lt49 ha (by omega)]; rfl

private lemma subset49_zero_left (b : Nat) : subset49 0 b = true := by
  unfold subset49; rw [beq_eq, land_eq]; simp

private lemma subset49_trans {a b c : Nat} (ha : a < 2 ^ 49) (hb : b < 2 ^ 49)
    (hab : subset49 a b = true) (hbc : subset49 b c = true) : subset49 a c = true := by
  rw [subset49_iff ha] at hab ⊢
  rw [subset49_iff hb] at hbc
  exact fun r col h => hbc r col (hab r col h)

private def pop7 (x : Nat) : Nat :=
  seqN (Nat.sub x (Nat.land (Nat.shiftRight x 1) 0x55)) fun x1 =>
  seqN (Nat.add (Nat.land x1 0x33) (Nat.land (Nat.shiftRight x1 2) 0x33)) fun x2 =>
  Nat.add (Nat.land x2 0x0F) (Nat.shiftRight x2 4)

private def pop49 (m : Nat) : Nat :=
  Nat.add (pop7 (Nat.land m 127))
  (Nat.add (pop7 (Nat.land (Nat.shiftRight m 7) 127))
  (Nat.add (pop7 (Nat.land (Nat.shiftRight m 14) 127))
  (Nat.add (pop7 (Nat.land (Nat.shiftRight m 21) 127))
  (Nat.add (pop7 (Nat.land (Nat.shiftRight m 28) 127))
  (Nat.add (pop7 (Nat.land (Nat.shiftRight m 35) 127))
           (pop7 (Nat.land (Nat.shiftRight m 42) 127)))))))

private lemma pop7_eq_sum {x : Nat} (hx : x < 128) :
    pop7 x = ∑ c : Fin 7, (x.testBit c.val).toNat := by
  have hall : ∀ y : Fin 128, pop7 y.val = ∑ c : Fin 7, (y.val.testBit c.val).toNat := by decide
  exact hall ⟨x, hx⟩

private lemma row49_lt (m : Nat) (r : Fin 7) : row49 m r < 128 := by
  unfold row49; rw [land_eq]; exact Nat.and_lt_two_pow _ (n := 7) (by decide)

private lemma row49_testBit (m : Nat) (r c : Fin 7) :
    (row49 m r).testBit c.val = get49 m r c := by
  unfold row49 get49
  rw [land_eq, shr_eq, mul_eq, Nat.testBit_and, Nat.testBit_shiftRight]
  have h127 : (127 : Nat).testBit c.val = true := by
    change (2 ^ 7 - 1).testBit c.val = true
    rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true c.isLt
  rw [h127, Bool.and_true]

private lemma pop7_row49_eq_sum (m : Nat) (r : Fin 7) :
    pop7 (row49 m r) = ∑ c : Fin 7, (get49 m r c).toNat := by
  rw [pop7_eq_sum (row49_lt m r)]
  exact Finset.sum_congr rfl fun c _ => congrArg Bool.toNat (row49_testBit m r c)

private lemma pop49_eq_rows (m : Nat) :
    pop49 m = pop7 (row49 m 0) + pop7 (row49 m 1) + pop7 (row49 m 2) +
              pop7 (row49 m 3) + pop7 (row49 m 4) + pop7 (row49 m 5) + pop7 (row49 m 6) := by
  have r0 : row49 m 0 = Nat.land m 127 := by unfold row49; simp
  have r1 : row49 m 1 = Nat.land (Nat.shiftRight m 7) 127 := rfl
  have r2 : row49 m 2 = Nat.land (Nat.shiftRight m 14) 127 := rfl
  have r3 : row49 m 3 = Nat.land (Nat.shiftRight m 21) 127 := rfl
  have r4 : row49 m 4 = Nat.land (Nat.shiftRight m 28) 127 := rfl
  have r5 : row49 m 5 = Nat.land (Nat.shiftRight m 35) 127 := rfl
  have r6 : row49 m 6 = Nat.land (Nat.shiftRight m 42) 127 := rfl
  rw [r0, r1, r2, r3, r4, r5, r6]
  unfold pop49; simp only [add_eq]; omega

private lemma pop49_eq_sum (m : Nat) :
    pop49 m = ∑ r : Fin 7, ∑ c : Fin 7, (get49 m r c).toNat := by
  rw [pop49_eq_rows, Fin.sum_univ_seven]
  simp only [pop7_row49_eq_sum, Nat.add_assoc]

private lemma subset49_pop_le {a b : Nat} (ha : a < 2 ^ 49) (h : subset49 a b = true) :
    pop49 a ≤ pop49 b := by
  rw [subset49_iff ha] at h
  rw [pop49_eq_sum, pop49_eq_sum]
  refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun c _ => ?_
  cases ha' : get49 a r c
  · simp
  · simp [h r c ha']

/-! ### Bit-Permutation & Closed-Neighborhood Lemmas via Masked Shifts -/

private lemma bit_and_masked (m mask i src : Nat) (f : Bool)
    (hmask : mask.testBit i = true → i = src)
    (hflag : mask.testBit i = f) :
    (m &&& mask).testBit i = (f && m.testBit src) := by
  rw [Nat.testBit_and, hflag]
  cases hf : f
  · simp
  · rw [hmask (hflag.trans hf), Bool.true_and, Bool.and_true]

private lemma bit_shiftL_masked (m mask k i src : Nat) (f : Bool)
    (hmask : (decide (k ≤ i) && mask.testBit (i - k)) = true → i - k = src)
    (hflag : (decide (k ≤ i) && mask.testBit (i - k)) = f) :
    ((m &&& mask) <<< k).testBit i = (f && m.testBit src) := by
  rw [Nat.testBit_shiftLeft, Nat.testBit_and]
  have hge : decide (i ≥ k) = decide (k ≤ i) := rfl
  rw [hge]
  cases h1 : decide (k ≤ i) <;> cases h2 : mask.testBit (i - k)
  · have hf : f = false := by simpa [h1, h2] using hflag.symm
    simp [hf]
  · have hf : f = false := by simpa [h1, h2] using hflag.symm
    simp [hf]
  · have hf : f = false := by simpa [h1, h2] using hflag.symm
    simp [hf]
  · have hsrc := hmask (by simp [h1, h2])
    have hf : f = true := by simpa [h1, h2] using hflag.symm
    rw [hsrc, hf]; simp

private lemma bit_shiftR_masked (m mask k i src : Nat) (f : Bool)
    (hmask : mask.testBit (k + i) = true → k + i = src)
    (hflag : mask.testBit (k + i) = f) :
    ((m &&& mask) >>> k).testBit i = (f && m.testBit src) := by
  rw [Nat.testBit_shiftRight, Nat.testBit_and, hflag]
  cases hf : f
  · simp
  · rw [hmask (hflag.trans hf), Bool.true_and, Bool.and_true]

private lemma shiftL_and_lt49 (m mask k : Nat) (h : ∀ i, 49 ≤ i → ((m &&& mask) <<< k).testBit i = false) :
    (m &&& mask) <<< k < 2 ^ 49 := by
  have h1 : ((m &&& mask) <<< k) = ((m &&& mask) <<< k) &&& ALL49 := by
    apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_and, testBit_all49]
    by_cases hi : i < 49
    · simp [hi]
    · simp [hi, h i (by omega)]
  rw [h1]; exact Nat.and_lt_two_pow _ (by decide)

private lemma shiftR_and_lt49 (m mask k : Nat) (hm : mask < 2 ^ 49) :
    (m &&& mask) >>> k < 2 ^ 49 := by
  rw [Nat.shiftRight_eq_div_pow]
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.and_lt_two_pow m hm)

private def hNbr49 (m : Nat) : Nat :=
  let l1 := Nat.lor (Nat.shiftLeft (Nat.land m __NOT_COL6__) 1) (Nat.shiftRight (Nat.land m __COL6__) 6)
  let r1 := Nat.lor (Nat.shiftRight (Nat.land m __NOT_COL0__) 1) (Nat.shiftLeft (Nat.land m __COL0__) 6)
  Nat.lor m (Nat.lor l1 r1)

private def vNbr49 (h : Nat) : Nat :=
  let u1 := Nat.lor (Nat.shiftLeft (Nat.land h __NOT_ROW6__) 7) (Nat.shiftRight (Nat.land h __ROW6__) 42)
  let d1 := Nat.lor (Nat.shiftRight (Nat.land h __NOT_ROW0__) 7) (Nat.shiftLeft (Nat.land h __ROW0__) 42)
  Nat.lor h (Nat.lor u1 d1)

private def closedNbr49 (m : Nat) : Nat :=
  seqN (hNbr49 m) fun h => vNbr49 h

private lemma hNbr49_lt {m : Nat} (hm : m < 2 ^ 49) : hNbr49 m < 2 ^ 49 := by
  unfold hNbr49; simp only [lor_eq, land_eq, shl_eq, shr_eq]
  have h1 : (m &&& __NOT_COL6__) <<< 1 < 2 ^ 49 := shiftL_and_lt49 _ _ 1 fun i hi => by
    rw [Nat.testBit_shiftLeft, Nat.testBit_and]
    have hlt : __NOT_COL6__ < 2 ^ 48 := by decide
    have hb : (__NOT_COL6__ : Nat).testBit (i - 1) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (pow2_mono (by omega)))
    simp [hb]
  have h2 : (m &&& __COL6__) >>> 6 < 2 ^ 49 := shiftR_and_lt49 _ _ 6 (by decide)
  have h3 : (m &&& __NOT_COL0__) >>> 1 < 2 ^ 49 := shiftR_and_lt49 _ _ 1 (by decide)
  have h4 : (m &&& __COL0__) <<< 6 < 2 ^ 49 := shiftL_and_lt49 _ _ 6 fun i hi => by
    rw [Nat.testBit_shiftLeft, Nat.testBit_and]
    have hlt : __COL0__ < 2 ^ 43 := by decide
    have hb : (__COL0__ : Nat).testBit (i - 6) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (pow2_mono (by omega)))
    simp [hb]
  exact or_lt49 hm (or_lt49 (or_lt49 h1 h2) (or_lt49 h3 h4))

private lemma vNbr49_lt {h : Nat} (hh : h < 2 ^ 49) : vNbr49 h < 2 ^ 49 := by
  unfold vNbr49; simp only [lor_eq, land_eq, shl_eq, shr_eq]
  have h1 : (h &&& __NOT_ROW6__) <<< 7 < 2 ^ 49 := shiftL_and_lt49 _ _ 7 fun i hi => by
    rw [Nat.testBit_shiftLeft, Nat.testBit_and]
    have hlt : __NOT_ROW6__ < 2 ^ 42 := by decide
    have hb : (__NOT_ROW6__ : Nat).testBit (i - 7) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (pow2_mono (by omega)))
    simp [hb]
  have h2 : (h &&& __ROW6__) >>> 42 < 2 ^ 49 := shiftR_and_lt49 _ _ 42 (by decide)
  have h3 : (h &&& __NOT_ROW0__) >>> 7 < 2 ^ 49 := shiftR_and_lt49 _ _ 7 (by decide)
  have h4 : (h &&& __ROW0__) <<< 42 < 2 ^ 49 := shiftL_and_lt49 _ _ 42 fun i hi => by
    rw [Nat.testBit_shiftLeft, Nat.testBit_and]
    have hlt : __ROW0__ < 2 ^ 7 := by decide
    have hb : (__ROW0__ : Nat).testBit (i - 42) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (pow2_mono (by omega)))
    simp [hb]
  exact or_lt49 hh (or_lt49 (or_lt49 h1 h2) (or_lt49 h3 h4))

private lemma closedNbr49_lt {m : Nat} (hm : m < 2 ^ 49) : closedNbr49 m < 2 ^ 49 := by
  unfold closedNbr49; rw [seqN_eq]; exact vNbr49_lt (hNbr49_lt hm)

private lemma get49_hNbr (m : Nat) (r c : Fin 7) :
    get49 (hNbr49 m) r c = (get49 m r (prev7 c) || get49 m r c || get49 m r (next7 c)) := by
  unfold get49 hNbr49; simp only [lor_eq, land_eq, shl_eq, shr_eq]
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_or, Nat.testBit_or]
  have e1 := bit_shiftL_masked m __NOT_COL6__ 1 (r.val * 7 + c.val) (r.val * 7 + (prev7 c).val) (decide (c ≠ 0))
    ((by decide : ∀ r c : Fin 7, (decide (1 ≤ r.val * 7 + c.val) && (__NOT_COL6__ : Nat).testBit (r.val * 7 + c.val - 1)) = true → r.val * 7 + c.val - 1 = r.val * 7 + (prev7 c).val) r c)
    ((by decide : ∀ r c : Fin 7, (decide (1 ≤ r.val * 7 + c.val) && (__NOT_COL6__ : Nat).testBit (r.val * 7 + c.val - 1)) = decide (c ≠ 0)) r c)
  have e2 := bit_shiftR_masked m __COL6__ 6 (r.val * 7 + c.val) (r.val * 7 + (prev7 c).val) (decide (c = 0))
    ((by decide : ∀ r c : Fin 7, (__COL6__ : Nat).testBit (6 + (r.val * 7 + c.val)) = true → 6 + (r.val * 7 + c.val) = r.val * 7 + (prev7 c).val) r c)
    ((by decide : ∀ r c : Fin 7, (__COL6__ : Nat).testBit (6 + (r.val * 7 + c.val)) = decide (c = 0)) r c)
  have e3 := bit_shiftR_masked m __NOT_COL0__ 1 (r.val * 7 + c.val) (r.val * 7 + (next7 c).val) (decide (c ≠ 6))
    ((by decide : ∀ r c : Fin 7, (__NOT_COL0__ : Nat).testBit (1 + (r.val * 7 + c.val)) = true → 1 + (r.val * 7 + c.val) = r.val * 7 + (next7 c).val) r c)
    ((by decide : ∀ r c : Fin 7, (__NOT_COL0__ : Nat).testBit (1 + (r.val * 7 + c.val)) = decide (c ≠ 6)) r c)
  have e4 := bit_shiftL_masked m __COL0__ 6 (r.val * 7 + c.val) (r.val * 7 + (next7 c).val) (decide (c = 6))
    ((by decide : ∀ r c : Fin 7, (decide (6 ≤ r.val * 7 + c.val) && (__COL0__ : Nat).testBit (r.val * 7 + c.val - 6)) = true → r.val * 7 + c.val - 6 = r.val * 7 + (next7 c).val) r c)
    ((by decide : ∀ r c : Fin 7, (decide (6 ≤ r.val * 7 + c.val) && (__COL0__ : Nat).testBit (r.val * 7 + c.val - 6)) = decide (c = 6)) r c)
  rw [e1, e2, e3, e4]
  have hbool : ∀ (a b d f0 f6 : Bool),
      (b || (((!f0 && a) || (f0 && a)) || ((!f6 && d) || (f6 && d)))) = (a || b || d) := by decide
  have hf0 : decide (c ≠ 0) = !decide (c = 0) := by by_cases h : c = 0 <;> simp [h]
  have hf6 : decide (c ≠ 6) = !decide (c = 6) := by by_cases h : c = 6 <;> simp [h]
  rw [hf0, hf6]; exact hbool _ _ _ _ _

private lemma get49_vNbr (h : Nat) (r c : Fin 7) :
    get49 (vNbr49 h) r c = (get49 h (prev7 r) c || get49 h r c || get49 h (next7 r) c) := by
  unfold get49 vNbr49; simp only [lor_eq, land_eq, shl_eq, shr_eq]
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_or, Nat.testBit_or]
  have e1 := bit_shiftL_masked h __NOT_ROW6__ 7 (r.val * 7 + c.val) ((prev7 r).val * 7 + c.val) (decide (r ≠ 0))
    ((by decide : ∀ r c : Fin 7, (decide (7 ≤ r.val * 7 + c.val) && (__NOT_ROW6__ : Nat).testBit (r.val * 7 + c.val - 7)) = true → r.val * 7 + c.val - 7 = (prev7 r).val * 7 + c.val) r c)
    ((by decide : ∀ r c : Fin 7, (decide (7 ≤ r.val * 7 + c.val) && (__NOT_ROW6__ : Nat).testBit (r.val * 7 + c.val - 7)) = decide (r ≠ 0)) r c)
  have e2 := bit_shiftR_masked h __ROW6__ 42 (r.val * 7 + c.val) ((prev7 r).val * 7 + c.val) (decide (r = 0))
    ((by decide : ∀ r c : Fin 7, (__ROW6__ : Nat).testBit (42 + (r.val * 7 + c.val)) = true → 42 + (r.val * 7 + c.val) = (prev7 r).val * 7 + c.val) r c)
    ((by decide : ∀ r c : Fin 7, (__ROW6__ : Nat).testBit (42 + (r.val * 7 + c.val)) = decide (r = 0)) r c)
  have e3 := bit_shiftR_masked h __NOT_ROW0__ 7 (r.val * 7 + c.val) ((next7 r).val * 7 + c.val) (decide (r ≠ 6))
    ((by decide : ∀ r c : Fin 7, (__NOT_ROW0__ : Nat).testBit (7 + (r.val * 7 + c.val)) = true → 7 + (r.val * 7 + c.val) = (next7 r).val * 7 + c.val) r c)
    ((by decide : ∀ r c : Fin 7, (__NOT_ROW0__ : Nat).testBit (7 + (r.val * 7 + c.val)) = decide (r ≠ 6)) r c)
  have e4 := bit_shiftL_masked h __ROW0__ 42 (r.val * 7 + c.val) ((next7 r).val * 7 + c.val) (decide (r = 6))
    ((by decide : ∀ r c : Fin 7, (decide (42 ≤ r.val * 7 + c.val) && (__ROW0__ : Nat).testBit (r.val * 7 + c.val - 42)) = true → r.val * 7 + c.val - 42 = (next7 r).val * 7 + c.val) r c)
    ((by decide : ∀ r c : Fin 7, (decide (42 ≤ r.val * 7 + c.val) && (__ROW0__ : Nat).testBit (r.val * 7 + c.val - 42)) = decide (r = 6)) r c)
  rw [e1, e2, e3, e4]
  have hbool : ∀ (a b d f0 f6 : Bool),
      (b || (((!f0 && a) || (f0 && a)) || ((!f6 && d) || (f6 && d)))) = (a || b || d) := by decide
  have hf0 : decide (r ≠ 0) = !decide (r = 0) := by by_cases h : r = 0 <;> simp [h]
  have hf6 : decide (r ≠ 6) = !decide (r = 6) := by by_cases h : r = 6 <;> simp [h]
  rw [hf0, hf6]; exact hbool _ _ _ _ _

private lemma closedNbr49_get (m : Nat) (r c : Fin 7) :
    get49 (closedNbr49 m) r c = true ↔
      ∃ r' c' : Fin 7, get49 m r' c' = true ∧
        (toZ7 r' = toZ7 r ∨ C7.Adj (toZ7 r') (toZ7 r)) ∧
        (toZ7 c' = toZ7 c ∨ C7.Adj (toZ7 c') (toZ7 c)) := by
  unfold closedNbr49; rw [seqN_eq, get49_vNbr, get49_hNbr, get49_hNbr, get49_hNbr]
  simp only [Bool.or_eq_true, c7Close_iff, or_assoc]
  constructor
  · rintro (h | h | h | h | h | h | h | h | h)
    · exact ⟨prev7 r, prev7 c, h, Or.inl rfl, Or.inl rfl⟩
    · exact ⟨prev7 r, c, h, Or.inl rfl, Or.inr (Or.inl rfl)⟩
    · exact ⟨prev7 r, next7 c, h, Or.inl rfl, Or.inr (Or.inr rfl)⟩
    · exact ⟨r, prev7 c, h, Or.inr (Or.inl rfl), Or.inl rfl⟩
    · exact ⟨r, c, h, Or.inr (Or.inl rfl), Or.inr (Or.inl rfl)⟩
    · exact ⟨r, next7 c, h, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
    · exact ⟨next7 r, prev7 c, h, Or.inr (Or.inr rfl), Or.inl rfl⟩
    · exact ⟨next7 r, c, h, Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩
    · exact ⟨next7 r, next7 c, h, Or.inr (Or.inr rfl), Or.inr (Or.inr rfl)⟩
  · rintro ⟨r', c', hm, hr, hc⟩
    rcases hr with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl <;> simp [hm]

private def mkRowFinset (S : Finset (ZMod 7 × ZMod 7)) (r : ZMod 7) : Nat :=
  (if (r, 0) ∈ S then 1 else 0) ||| (if (r, 1) ∈ S then 2 else 0) |||
  (if (r, 2) ∈ S then 4 else 0) ||| (if (r, 3) ∈ S then 8 else 0) |||
  (if (r, 4) ∈ S then 16 else 0) ||| (if (r, 5) ∈ S then 32 else 0) |||
  (if (r, 6) ∈ S then 64 else 0)

private def ofFinset49 (S : Finset (ZMod 7 × ZMod 7)) : Nat :=
  mkRowFinset S 0 ||| (mkRowFinset S 1 <<< 7) ||| (mkRowFinset S 2 <<< 14) |||
  (mkRowFinset S 3 <<< 21) ||| (mkRowFinset S 4 <<< 28) |||
  (mkRowFinset S 5 <<< 35) ||| (mkRowFinset S 6 <<< 42)

private lemma mkRowFinset_lt (S : Finset (ZMod 7 × ZMod 7)) (r : ZMod 7) :
    mkRowFinset S r < 128 := by
  change mkRowFinset S r < 2 ^ 7
  unfold mkRowFinset
  repeat apply Nat.or_lt_two_pow
  all_goals (split_ifs <;> decide)

private lemma ofFinset49_lt (S : Finset (ZMod 7 × ZMod 7)) : ofFinset49 S < 2 ^ 49 := by
  have hsh : ∀ (r : ZMod 7) (k : Nat), k ≤ 42 → mkRowFinset S r <<< k < 2 ^ 49 := by
    intro r k hk
    rw [Nat.shiftLeft_eq]
    have h1 := mkRowFinset_lt S r
    have h2 : 2 ^ k ≤ 2 ^ 42 := pow2_mono hk
    calc mkRowFinset S r * 2 ^ k < 128 * 2 ^ k := Nat.mul_lt_mul_of_pos_right h1 (by positivity)
      _ ≤ 128 * 2 ^ 42 := Nat.mul_le_mul_left 128 h2
      _ = 2 ^ 49 := by decide
  have h0 : mkRowFinset S 0 < 2 ^ 49 := lt_trans (mkRowFinset_lt S 0) (by decide)
  unfold ofFinset49
  exact or_lt49 (or_lt49 (or_lt49 (or_lt49 (or_lt49 (or_lt49 h0 (hsh 1 7 (by decide)))
    (hsh 2 14 (by decide))) (hsh 3 21 (by decide))) (hsh 4 28 (by decide)))
    (hsh 5 35 (by decide))) (hsh 6 42 (by decide))

private lemma mkRowFinset_testBit (S : Finset (ZMod 7 × ZMod 7)) (r : ZMod 7) (c : Fin 7) :
    (mkRowFinset S r).testBit c.val = decide ((r, toZ7 c) ∈ S) := by
  unfold mkRowFinset
  simp only [Nat.testBit_or]
  have hbit : ∀ (b : ZMod 7) (k v : Nat), ((if (r, b) ∈ S then v else 0).testBit k) =
      (decide ((r, b) ∈ S) && v.testBit k) := by
    intro b k v; by_cases h : (r, b) ∈ S <;> simp [h]
  simp only [hbit]
  revert c
  exact fin7_cases
    (by simp [toZ7, show (1:Nat).testBit 0 = true by decide, show (2:Nat).testBit 0 = false by decide,
              show (4:Nat).testBit 0 = false by decide, show (8:Nat).testBit 0 = false by decide,
              show (16:Nat).testBit 0 = false by decide, show (32:Nat).testBit 0 = false by decide,
              show (64:Nat).testBit 0 = false by decide])
    (by simp [toZ7, show (1:Nat).testBit 1 = false by decide, show (2:Nat).testBit 1 = true by decide,
              show (4:Nat).testBit 1 = false by decide, show (8:Nat).testBit 1 = false by decide,
              show (16:Nat).testBit 1 = false by decide, show (32:Nat).testBit 1 = false by decide,
              show (64:Nat).testBit 1 = false by decide])
    (by simp [toZ7, show (1:Nat).testBit 2 = false by decide, show (2:Nat).testBit 2 = false by decide,
              show (4:Nat).testBit 2 = true by decide, show (8:Nat).testBit 2 = false by decide,
              show (16:Nat).testBit 2 = false by decide, show (32:Nat).testBit 2 = false by decide,
              show (64:Nat).testBit 2 = false by decide])
    (by simp [toZ7, show (1:Nat).testBit 3 = false by decide, show (2:Nat).testBit 3 = false by decide,
              show (4:Nat).testBit 3 = false by decide, show (8:Nat).testBit 3 = true by decide,
              show (16:Nat).testBit 3 = false by decide, show (32:Nat).testBit 3 = false by decide,
              show (64:Nat).testBit 3 = false by decide])
    (by simp [toZ7, show (1:Nat).testBit 4 = false by decide, show (2:Nat).testBit 4 = false by decide,
              show (4:Nat).testBit 4 = false by decide, show (8:Nat).testBit 4 = false by decide,
              show (16:Nat).testBit 4 = true by decide, show (32:Nat).testBit 4 = false by decide,
              show (64:Nat).testBit 4 = false by decide])
    (by simp [toZ7, show (1:Nat).testBit 5 = false by decide, show (2:Nat).testBit 5 = false by decide,
              show (4:Nat).testBit 5 = false by decide, show (8:Nat).testBit 5 = false by decide,
              show (16:Nat).testBit 5 = false by decide, show (32:Nat).testBit 5 = true by decide,
              show (64:Nat).testBit 5 = false by decide])
    (by simp [toZ7, show (1:Nat).testBit 6 = false by decide, show (2:Nat).testBit 6 = false by decide,
              show (4:Nat).testBit 6 = false by decide, show (8:Nat).testBit 6 = false by decide,
              show (16:Nat).testBit 6 = false by decide, show (32:Nat).testBit 6 = false by decide,
              show (64:Nat).testBit 6 = true by decide])

private lemma get49_ofFinset (S : Finset (ZMod 7 × ZMod 7)) (r c : Fin 7) :
    get49 (ofFinset49 S) r c = true ↔ (toZ7 r, toZ7 c) ∈ S := by
  have hhi : ∀ (x : ZMod 7) (i : Nat), 7 ≤ i → (mkRowFinset S x).testBit i = false :=
    fun x i hi => Nat.testBit_lt_two_pow (lt_of_lt_of_le (mkRowFinset_lt S x) (pow2_mono hi))
  unfold get49 ofFinset49
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have hcalc : ((mkRowFinset S 0).testBit (r.val * 7 + c.val) ||
      (decide (r.val * 7 + c.val ≥ 7) && (mkRowFinset S 1).testBit (r.val * 7 + c.val - 7)) ||
      (decide (r.val * 7 + c.val ≥ 14) && (mkRowFinset S 2).testBit (r.val * 7 + c.val - 14)) ||
      (decide (r.val * 7 + c.val ≥ 21) && (mkRowFinset S 3).testBit (r.val * 7 + c.val - 21)) ||
      (decide (r.val * 7 + c.val ≥ 28) && (mkRowFinset S 4).testBit (r.val * 7 + c.val - 28)) ||
      (decide (r.val * 7 + c.val ≥ 35) && (mkRowFinset S 5).testBit (r.val * 7 + c.val - 35)) ||
      (decide (r.val * 7 + c.val ≥ 42) && (mkRowFinset S 6).testBit (r.val * 7 + c.val - 42))) =
      (mkRowFinset S (toZ7 r)).testBit c.val := by
    have hc := c.isLt
    rcases r with ⟨rv, hrv⟩
    have hrv' : rv = 0 ∨ rv = 1 ∨ rv = 2 ∨ rv = 3 ∨ rv = 4 ∨ rv = 5 ∨ rv = 6 := by omega
    rcases hrv' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · dsimp only
      simp only [toZ7, Nat.zero_mul, Nat.zero_add, Nat.cast_zero,
        show ¬(c.val ≥ 7) by omega, show ¬(c.val ≥ 14) by omega, show ¬(c.val ≥ 21) by omega,
        show ¬(c.val ≥ 28) by omega, show ¬(c.val ≥ 35) by omega, show ¬(c.val ≥ 42) by omega,
        decide_false, Bool.false_and, Bool.or_false]
    · dsimp only
      simp only [toZ7, Nat.one_mul, Nat.cast_one, hhi 0 (7 + c.val) (by omega),
        show 7 + c.val ≥ 7 by omega, show ¬(7 + c.val ≥ 14) by omega, show ¬(7 + c.val ≥ 21) by omega,
        show ¬(7 + c.val ≥ 28) by omega, show ¬(7 + c.val ≥ 35) by omega, show ¬(7 + c.val ≥ 42) by omega,
        decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false, Nat.add_sub_cancel_left]
    · dsimp only
      simp only [toZ7, show (2 : Nat) * 7 = 14 by decide, show ((2 : Nat) : ZMod 7) = 2 by rfl,
        hhi 0 (14 + c.val) (by omega), hhi 1 (14 + c.val - 7) (by omega),
        show 14 + c.val ≥ 7 by omega, show 14 + c.val ≥ 14 by omega, show ¬(14 + c.val ≥ 21) by omega,
        show ¬(14 + c.val ≥ 28) by omega, show ¬(14 + c.val ≥ 35) by omega, show ¬(14 + c.val ≥ 42) by omega,
        decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false, Nat.add_sub_cancel_left]
    · dsimp only
      simp only [toZ7, show (3 : Nat) * 7 = 21 by decide, show ((3 : Nat) : ZMod 7) = 3 by rfl,
        hhi 0 (21 + c.val) (by omega), hhi 1 (21 + c.val - 7) (by omega), hhi 2 (21 + c.val - 14) (by omega),
        show 21 + c.val ≥ 7 by omega, show 21 + c.val ≥ 14 by omega, show 21 + c.val ≥ 21 by omega,
        show ¬(21 + c.val ≥ 28) by omega, show ¬(21 + c.val ≥ 35) by omega, show ¬(21 + c.val ≥ 42) by omega,
        decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false, Nat.add_sub_cancel_left]
    · dsimp only
      simp only [toZ7, show (4 : Nat) * 7 = 28 by decide, show ((4 : Nat) : ZMod 7) = 4 by rfl,
        hhi 0 (28 + c.val) (by omega), hhi 1 (28 + c.val - 7) (by omega), hhi 2 (28 + c.val - 14) (by omega),
        hhi 3 (28 + c.val - 21) (by omega),
        show 28 + c.val ≥ 7 by omega, show 28 + c.val ≥ 14 by omega, show 28 + c.val ≥ 21 by omega,
        show 28 + c.val ≥ 28 by omega, show ¬(28 + c.val ≥ 35) by omega, show ¬(28 + c.val ≥ 42) by omega,
        decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false, Nat.add_sub_cancel_left]
    · dsimp only
      simp only [toZ7, show (5 : Nat) * 7 = 35 by decide, show ((5 : Nat) : ZMod 7) = 5 by rfl,
        hhi 0 (35 + c.val) (by omega), hhi 1 (35 + c.val - 7) (by omega), hhi 2 (35 + c.val - 14) (by omega),
        hhi 3 (35 + c.val - 21) (by omega), hhi 4 (35 + c.val - 28) (by omega),
        show 35 + c.val ≥ 7 by omega, show 35 + c.val ≥ 14 by omega, show 35 + c.val ≥ 21 by omega,
        show 35 + c.val ≥ 28 by omega, show 35 + c.val ≥ 35 by omega, show ¬(35 + c.val ≥ 42) by omega,
        decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false, Nat.add_sub_cancel_left]
    · dsimp only
      simp only [toZ7, show (6 : Nat) * 7 = 42 by decide, show ((6 : Nat) : ZMod 7) = 6 by rfl,
        hhi 0 (42 + c.val) (by omega), hhi 1 (42 + c.val - 7) (by omega), hhi 2 (42 + c.val - 14) (by omega),
        hhi 3 (42 + c.val - 21) (by omega), hhi 4 (42 + c.val - 28) (by omega), hhi 5 (42 + c.val - 35) (by omega),
        show 42 + c.val ≥ 7 by omega, show 42 + c.val ≥ 14 by omega, show 42 + c.val ≥ 21 by omega,
        show 42 + c.val ≥ 28 by omega, show 42 + c.val ≥ 35 by omega, show 42 + c.val ≥ 42 by omega,
        decide_true, Bool.true_and, Bool.false_or, Nat.add_sub_cancel_left]
  rw [hcalc, mkRowFinset_testBit, decide_eq_true_iff]

private def fin7SqEquivZ7Sq : (Fin 7 × Fin 7) ≃ (ZMod 7 × ZMod 7) :=
  Equiv.mk
    (fun p => (toZ7 p.1, toZ7 p.2))
    (fun q => (ofZ7 q.1, ofZ7 q.2))
    (fun ⟨a, b⟩ => Prod.ext (ofZ7_toZ7 a) (ofZ7_toZ7 b))
    (fun ⟨a, b⟩ => Prod.ext (toZ7_ofZ7 a) (toZ7_ofZ7 b))

private lemma pop49_ofFinset (S : Finset (ZMod 7 × ZMod 7)) :
    pop49 (ofFinset49 S) = S.card := by
  rw [pop49_eq_sum]
  have h1 : (∑ r : Fin 7, ∑ c : Fin 7, (get49 (ofFinset49 S) r c).toNat) =
      ∑ p : Fin 7 × Fin 7, if fin7SqEquivZ7Sq p ∈ S then 1 else 0 := by
    rw [← Fintype.sum_prod_type']
    refine Finset.sum_congr rfl fun p _ => ?_
    change (get49 (ofFinset49 S) p.1 p.2).toNat = if (toZ7 p.1, toZ7 p.2) ∈ S then 1 else 0
    by_cases hp : (toZ7 p.1, toZ7 p.2) ∈ S
    · simp [hp, (get49_ofFinset S p.1 p.2).mpr hp]
    · have hg : get49 (ofFinset49 S) p.1 p.2 = false :=
        Bool.eq_false_iff.mpr fun h => hp ((get49_ofFinset S p.1 p.2).mp h)
      simp [hp, hg]
  rw [h1]
  have h2 : (∑ p : Fin 7 × Fin 7, if fin7SqEquivZ7Sq p ∈ S then 1 else 0) =
      ∑ q : ZMod 7 × ZMod 7, if q ∈ S then 1 else 0 :=
    Equiv.sum_comp fin7SqEquivZ7Sq (fun q => if q ∈ S then 1 else 0)
  rw [h2]; simp

private lemma ofFinset49_union (A B : Finset (ZMod 7 × ZMod 7)) :
    ofFinset49 (A ∪ B) = ofFinset49 A ||| ofFinset49 B := by
  apply ext49 (ofFinset49_lt _) (or_lt49 (ofFinset49_lt _) (ofFinset49_lt _))
  intro r c
  rw [get49_or, Bool.eq_iff_iff, Bool.or_eq_true, get49_ofFinset, get49_ofFinset, get49_ofFinset, Finset.mem_union]

private lemma ofFinset49_sdiff (A B : Finset (ZMod 7 × ZMod 7)) :
    ofFinset49 (A \ B) = diff49 (ofFinset49 A) (ofFinset49 B) := by
  apply ext49 (ofFinset49_lt _) (diff49_lt (ofFinset49_lt _))
  intro r c
  rw [get49_diff, Bool.eq_iff_iff, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
      get49_ofFinset, get49_ofFinset, get49_ofFinset, Finset.mem_sdiff]

private lemma ofFinset49_subset_of_subset {A B : Finset (ZMod 7 × ZMod 7)} (h : A ⊆ B) :
    subset49 (ofFinset49 A) (ofFinset49 B) = true := by
  rw [subset49_iff (ofFinset49_lt _)]
  intro r c ha
  exact (get49_ofFinset B r c).mpr (h ((get49_ofFinset A r c).mp ha))

private lemma disjoint49_closedNbr_of_indep {A B : Finset (ZMod 7 × ZMod 7)}
    (hdisj : Disjoint A B)
    (hind : (C7 ⊠ C7).IsIndepSet ((A ∪ B : Finset (ZMod 7 × ZMod 7)) : Set (ZMod 7 × ZMod 7))) :
    disjoint49 (ofFinset49 B) (closedNbr49 (ofFinset49 A)) = true := by
  rw [disjoint49_iff (ofFinset49_lt _)]
  intro r c hb
  have hb' : (toZ7 r, toZ7 c) ∈ B := (get49_ofFinset B r c).mp hb
  cases hc : get49 (closedNbr49 (ofFinset49 A)) r c
  · rfl
  · exfalso
    obtain ⟨r', c', ha, hr, hc'⟩ := (closedNbr49_get _ r c).mp hc
    have ha' : (toZ7 r', toZ7 c') ∈ A := (get49_ofFinset A r' c').mp ha
    have hne : (toZ7 r', toZ7 c') ≠ (toZ7 r, toZ7 c) := fun heq =>
      Finset.disjoint_left.mp hdisj ha' (heq ▸ hb')
    have hadj : (C7 ⊠ C7).Adj (toZ7 r', toZ7 c') (toZ7 r, toZ7 c) := ⟨hne, hr, hc'⟩
    exact hind (Finset.mem_coe.mpr (Finset.mem_union_left B ha'))
      (Finset.mem_coe.mpr (Finset.mem_union_right A hb')) hne hadj

/-! ## Section 2: `Aut(C₇ ⊠ C₇)` (Order 392) via C++-Speed 49-Bit Permutations -/

private def flipRow49 (m : Nat) : Nat :=
  Nat.lor (Nat.land m __RM0__)
  (Nat.lor (Nat.shiftLeft (Nat.land m __RM1__) 35)
  (Nat.lor (Nat.shiftLeft (Nat.land m __RM2__) 21)
  (Nat.lor (Nat.shiftLeft (Nat.land m __RM3__) 7)
  (Nat.lor (Nat.shiftRight (Nat.land m __RM4__) 7)
  (Nat.lor (Nat.shiftRight (Nat.land m __RM5__) 21)
           (Nat.shiftRight (Nat.land m __RM6__) 35))))))

private def shiftRow49 (t : Fin 7) (m : Nat) : Nat :=
  match t.val with
  | 0 => m
  | 1 => Nat.lor (Nat.shiftLeft (Nat.land m __SRLO1__) 7)  (Nat.shiftRight (Nat.land m __SRHI1__) 42)
  | 2 => Nat.lor (Nat.shiftLeft (Nat.land m __SRLO2__) 14) (Nat.shiftRight (Nat.land m __SRHI2__) 35)
  | 3 => Nat.lor (Nat.shiftLeft (Nat.land m __SRLO3__) 21) (Nat.shiftRight (Nat.land m __SRHI3__) 28)
  | 4 => Nat.lor (Nat.shiftLeft (Nat.land m __SRLO4__) 28) (Nat.shiftRight (Nat.land m __SRHI4__) 21)
  | 5 => Nat.lor (Nat.shiftLeft (Nat.land m __SRLO5__) 35) (Nat.shiftRight (Nat.land m __SRHI5__) 14)
  | _ => Nat.lor (Nat.shiftLeft (Nat.land m __SRLO6__) 42) (Nat.shiftRight (Nat.land m __SRHI6__) 7)

private def flipCol49 (m : Nat) : Nat :=
  Nat.lor (Nat.land m __CM0__)
  (Nat.lor (Nat.shiftLeft (Nat.land m __CM1__) 5)
  (Nat.lor (Nat.shiftLeft (Nat.land m __CM2__) 3)
  (Nat.lor (Nat.shiftLeft (Nat.land m __CM3__) 1)
  (Nat.lor (Nat.shiftRight (Nat.land m __CM4__) 1)
  (Nat.lor (Nat.shiftRight (Nat.land m __CM5__) 3)
           (Nat.shiftRight (Nat.land m __CM6__) 5))))))

private def shiftCol49 (t : Fin 7) (m : Nat) : Nat :=
  match t.val with
  | 0 => m
  | 1 => Nat.lor (Nat.shiftLeft (Nat.land m __SCLO1__) 1) (Nat.shiftRight (Nat.land m __SCHI1__) 6)
  | 2 => Nat.lor (Nat.shiftLeft (Nat.land m __SCLO2__) 2) (Nat.shiftRight (Nat.land m __SCHI2__) 5)
  | 3 => Nat.lor (Nat.shiftLeft (Nat.land m __SCLO3__) 3) (Nat.shiftRight (Nat.land m __SCHI3__) 4)
  | 4 => Nat.lor (Nat.shiftLeft (Nat.land m __SCLO4__) 4) (Nat.shiftRight (Nat.land m __SCHI4__) 3)
  | 5 => Nat.lor (Nat.shiftLeft (Nat.land m __SCLO5__) 5) (Nat.shiftRight (Nat.land m __SCHI5__) 2)
  | _ => Nat.lor (Nat.shiftLeft (Nat.land m __SCLO6__) 6) (Nat.shiftRight (Nat.land m __SCHI6__) 1)

private def transpose49 (m : Nat) : Nat :=
  Nat.lor (Nat.land m __DIAG0__)
  (Nat.lor (Nat.shiftLeft (Nat.land m __DP1__) 6)
  (Nat.lor (Nat.shiftLeft (Nat.land m __DP2__) 12)
  (Nat.lor (Nat.shiftLeft (Nat.land m __DP3__) 18)
  (Nat.lor (Nat.shiftLeft (Nat.land m __DP4__) 24)
  (Nat.lor (Nat.shiftLeft (Nat.land m __DP5__) 30)
  (Nat.lor (Nat.shiftLeft (Nat.land m __DP6__) 36)
  (Nat.lor (Nat.shiftRight (Nat.land m __DN1__) 6)
  (Nat.lor (Nat.shiftRight (Nat.land m __DN2__) 12)
  (Nat.lor (Nat.shiftRight (Nat.land m __DN3__) 18)
  (Nat.lor (Nat.shiftRight (Nat.land m __DN4__) 24)
  (Nat.lor (Nat.shiftRight (Nat.land m __DN5__) 30)
           (Nat.shiftRight (Nat.land m __DN6__) 36))))))))))))

private lemma shiftL_lt_of_mask {m mask k bound : Nat}
    (hm : mask < 2 ^ bound) (hk : bound + k ≤ 49) : (m &&& mask) <<< k < 2 ^ 49 :=
  shiftL_and_lt49 m mask k fun i hi => by
    rw [Nat.testBit_shiftLeft, Nat.testBit_and]
    have hb : mask.testBit (i - k) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (pow2_mono (by omega)))
    simp [hb]

private lemma flipRow49_lt (m : Nat) : flipRow49 m < 2 ^ 49 := by
  unfold flipRow49; simp only [lor_eq, land_eq, shl_eq, shr_eq]
  exact or_lt49 (and_lt49 (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 14) (by decide) (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 21) (by decide) (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 28) (by decide) (by decide))
    (or_lt49 (shiftR_and_lt49 _ _ 7 (by decide))
    (or_lt49 (shiftR_and_lt49 _ _ 21 (by decide))
             (shiftR_and_lt49 _ _ 35 (by decide)))))))

private lemma shiftRow49_lt (t : Fin 7) {m : Nat} (hm : m < 2 ^ 49) : shiftRow49 t m < 2 ^ 49 := by
  unfold shiftRow49
  revert t
  refine fin7_cases hm ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 42) (by decide) (by decide)) (shiftR_and_lt49 _ _ 42 (by decide))
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 35) (by decide) (by decide)) (shiftR_and_lt49 _ _ 35 (by decide))
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 28) (by decide) (by decide)) (shiftR_and_lt49 _ _ 28 (by decide))
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 21) (by decide) (by decide)) (shiftR_and_lt49 _ _ 21 (by decide))
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 14) (by decide) (by decide)) (shiftR_and_lt49 _ _ 14 (by decide))
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 7)  (by decide) (by decide)) (shiftR_and_lt49 _ _ 7  (by decide))

private lemma flipCol49_lt (m : Nat) : flipCol49 m < 2 ^ 49 := by
  unfold flipCol49; simp only [lor_eq, land_eq, shl_eq, shr_eq]
  exact or_lt49 (and_lt49 (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 44) (by decide) (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 45) (by decide) (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 46) (by decide) (by decide))
    (or_lt49 (shiftR_and_lt49 _ _ 1 (by decide))
    (or_lt49 (shiftR_and_lt49 _ _ 3 (by decide))
             (shiftR_and_lt49 _ _ 5 (by decide)))))))

private lemma shiftCol49_lt (t : Fin 7) {m : Nat} (hm : m < 2 ^ 49) : shiftCol49 t m < 2 ^ 49 := by
  unfold shiftCol49
  revert t
  refine fin7_cases hm ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 48) (by decide) (by decide)) (shiftR_and_lt49 _ _ 6 (by decide))
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 47) (by decide) (by decide)) (shiftR_and_lt49 _ _ 5 (by decide))
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 46) (by decide) (by decide)) (shiftR_and_lt49 _ _ 4 (by decide))
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 45) (by decide) (by decide)) (shiftR_and_lt49 _ _ 3 (by decide))
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 44) (by decide) (by decide)) (shiftR_and_lt49 _ _ 2 (by decide))
  · simp only [lor_eq, land_eq, shl_eq, shr_eq]; exact or_lt49 (shiftL_lt_of_mask (bound := 43) (by decide) (by decide)) (shiftR_and_lt49 _ _ 1 (by decide))

private lemma transpose49_lt (m : Nat) : transpose49 m < 2 ^ 49 := by
  unfold transpose49; simp only [lor_eq, land_eq, shl_eq, shr_eq]
  exact or_lt49 (and_lt49 (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 42) (by decide) (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 35) (by decide) (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 28) (by decide) (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 21) (by decide) (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 14) (by decide) (by decide))
    (or_lt49 (shiftL_lt_of_mask (bound := 7)  (by decide) (by decide))
    (or_lt49 (shiftR_and_lt49 _ _ 6  (by decide))
    (or_lt49 (shiftR_and_lt49 _ _ 12 (by decide))
    (or_lt49 (shiftR_and_lt49 _ _ 18 (by decide))
    (or_lt49 (shiftR_and_lt49 _ _ 24 (by decide))
    (or_lt49 (shiftR_and_lt49 _ _ 30 (by decide))
             (shiftR_and_lt49 _ _ 36 (by decide)))))))))))))

private lemma get49_flipRow (m : Nat) (r c : Fin 7) :
    get49 (flipRow49 m) (neg7 r) c = get49 m r c := by
  unfold get49 flipRow49
  let dst := (neg7 r).val * 7 + c.val
  let src := r.val * 7 + c.val
  change ((m &&& __RM0__) ||| (((m &&& __RM1__) <<< 35) ||| (((m &&& __RM2__) <<< 21) |||
    (((m &&& __RM3__) <<< 7) ||| (((m &&& __RM4__) >>> 7) ||| (((m &&& __RM5__) >>> 21) |||
    ((m &&& __RM6__) >>> 35))))))).testBit dst = m.testBit src
  simp only [Nat.testBit_or]
  rw [bit_and_masked m __RM0__ dst src (decide (r = 0))
        ((by decide : ∀ r c : Fin 7, (__RM0__ : Nat).testBit ((neg7 r).val * 7 + c.val) = true → (neg7 r).val * 7 + c.val = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (__RM0__ : Nat).testBit ((neg7 r).val * 7 + c.val) = decide (r = 0)) r c),
      bit_shiftL_masked m __RM1__ 35 dst src (decide (r = 1))
        ((by decide : ∀ r c : Fin 7, (decide (35 ≤ (neg7 r).val * 7 + c.val) && (__RM1__ : Nat).testBit ((neg7 r).val * 7 + c.val - 35)) = true → (neg7 r).val * 7 + c.val - 35 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (35 ≤ (neg7 r).val * 7 + c.val) && (__RM1__ : Nat).testBit ((neg7 r).val * 7 + c.val - 35)) = decide (r = 1)) r c),
      bit_shiftL_masked m __RM2__ 21 dst src (decide (r = 2))
        ((by decide : ∀ r c : Fin 7, (decide (21 ≤ (neg7 r).val * 7 + c.val) && (__RM2__ : Nat).testBit ((neg7 r).val * 7 + c.val - 21)) = true → (neg7 r).val * 7 + c.val - 21 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (21 ≤ (neg7 r).val * 7 + c.val) && (__RM2__ : Nat).testBit ((neg7 r).val * 7 + c.val - 21)) = decide (r = 2)) r c),
      bit_shiftL_masked m __RM3__ 7 dst src (decide (r = 3))
        ((by decide : ∀ r c : Fin 7, (decide (7 ≤ (neg7 r).val * 7 + c.val) && (__RM3__ : Nat).testBit ((neg7 r).val * 7 + c.val - 7)) = true → (neg7 r).val * 7 + c.val - 7 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (7 ≤ (neg7 r).val * 7 + c.val) && (__RM3__ : Nat).testBit ((neg7 r).val * 7 + c.val - 7)) = decide (r = 3)) r c),
      bit_shiftR_masked m __RM4__ 7 dst src (decide (r = 4))
        ((by decide : ∀ r c : Fin 7, (__RM4__ : Nat).testBit (7 + ((neg7 r).val * 7 + c.val)) = true → 7 + ((neg7 r).val * 7 + c.val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (__RM4__ : Nat).testBit (7 + ((neg7 r).val * 7 + c.val)) = decide (r = 4)) r c),
      bit_shiftR_masked m __RM5__ 21 dst src (decide (r = 5))
        ((by decide : ∀ r c : Fin 7, (__RM5__ : Nat).testBit (21 + ((neg7 r).val * 7 + c.val)) = true → 21 + ((neg7 r).val * 7 + c.val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (__RM5__ : Nat).testBit (21 + ((neg7 r).val * 7 + c.val)) = decide (r = 5)) r c),
      bit_shiftR_masked m __RM6__ 35 dst src (decide (r = 6))
        ((by decide : ∀ r c : Fin 7, (__RM6__ : Nat).testBit (35 + ((neg7 r).val * 7 + c.val)) = true → 35 + ((neg7 r).val * 7 + c.val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (__RM6__ : Nat).testBit (35 + ((neg7 r).val * 7 + c.val)) = decide (r = 6)) r c)]
  revert r; refine fin7_cases ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp

private lemma get49_shiftRow_aux (m lo hi : Nat) (t : Fin 7) (kL kR : Nat)
    (h1 : ∀ r c : Fin 7, (decide (kL ≤ (add7 r t).val * 7 + c.val) && lo.testBit ((add7 r t).val * 7 + c.val - kL)) = true →
          (add7 r t).val * 7 + c.val - kL = r.val * 7 + c.val)
    (h2 : ∀ r c : Fin 7, hi.testBit (kR + ((add7 r t).val * 7 + c.val)) = true →
          kR + ((add7 r t).val * 7 + c.val) = r.val * 7 + c.val)
    (h3 : ∀ r c : Fin 7, ((decide (kL ≤ (add7 r t).val * 7 + c.val) && lo.testBit ((add7 r t).val * 7 + c.val - kL)) ||
                          hi.testBit (kR + ((add7 r t).val * 7 + c.val))) = true)
    (r c : Fin 7) :
    get49 (((m &&& lo) <<< kL) ||| ((m &&& hi) >>> kR)) (add7 r t) c = get49 m r c := by
  unfold get49
  rw [Nat.testBit_or,
      bit_shiftL_masked m lo kL ((add7 r t).val * 7 + c.val) (r.val * 7 + c.val) _ (h1 r c) rfl,
      bit_shiftR_masked m hi kR ((add7 r t).val * 7 + c.val) (r.val * 7 + c.val) _ (h2 r c) rfl]
  have hf := h3 r c
  cases a : (decide (kL ≤ (add7 r t).val * 7 + c.val) && lo.testBit ((add7 r t).val * 7 + c.val - kL)) <;>
  cases b : hi.testBit (kR + ((add7 r t).val * 7 + c.val)) <;> simp_all

private lemma get49_shiftRow (t : Fin 7) (m : Nat) (r c : Fin 7) :
    get49 (shiftRow49 t m) (add7 r t) c = get49 m r c := by
  unfold shiftRow49
  revert t
  refine fin7_cases ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have h0 : add7 r 0 = r := (by decide : ∀ x : Fin 7, add7 x 0 = x) r
    rw [h0]; rfl
  · exact get49_shiftRow_aux m __SRLO1__ __SRHI1__ 1 7  42 (by decide) (by decide) (by decide) r c
  · exact get49_shiftRow_aux m __SRLO2__ __SRHI2__ 2 14 35 (by decide) (by decide) (by decide) r c
  · exact get49_shiftRow_aux m __SRLO3__ __SRHI3__ 3 21 28 (by decide) (by decide) (by decide) r c
  · exact get49_shiftRow_aux m __SRLO4__ __SRHI4__ 4 28 21 (by decide) (by decide) (by decide) r c
  · exact get49_shiftRow_aux m __SRLO5__ __SRHI5__ 5 35 14 (by decide) (by decide) (by decide) r c
  · exact get49_shiftRow_aux m __SRLO6__ __SRHI6__ 6 42 7  (by decide) (by decide) (by decide) r c

private lemma get49_flipCol (m : Nat) (r c : Fin 7) :
    get49 (flipCol49 m) r (neg7 c) = get49 m r c := by
  unfold get49 flipCol49
  let dst := r.val * 7 + (neg7 c).val
  let src := r.val * 7 + c.val
  change ((m &&& __CM0__) ||| (((m &&& __CM1__) <<< 5) ||| (((m &&& __CM2__) <<< 3) |||
    (((m &&& __CM3__) <<< 1) ||| (((m &&& __CM4__) >>> 1) ||| (((m &&& __CM5__) >>> 3) |||
    ((m &&& __CM6__) >>> 5))))))).testBit dst = m.testBit src
  simp only [Nat.testBit_or]
  rw [bit_and_masked m __CM0__ dst src (decide (c = 0))
        ((by decide : ∀ r c : Fin 7, (__CM0__ : Nat).testBit (r.val * 7 + (neg7 c).val) = true → r.val * 7 + (neg7 c).val = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (__CM0__ : Nat).testBit (r.val * 7 + (neg7 c).val) = decide (c = 0)) r c),
      bit_shiftL_masked m __CM1__ 5 dst src (decide (c = 1))
        ((by decide : ∀ r c : Fin 7, (decide (5 ≤ r.val * 7 + (neg7 c).val) && (__CM1__ : Nat).testBit (r.val * 7 + (neg7 c).val - 5)) = true → r.val * 7 + (neg7 c).val - 5 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (5 ≤ r.val * 7 + (neg7 c).val) && (__CM1__ : Nat).testBit (r.val * 7 + (neg7 c).val - 5)) = decide (c = 1)) r c),
      bit_shiftL_masked m __CM2__ 3 dst src (decide (c = 2))
        ((by decide : ∀ r c : Fin 7, (decide (3 ≤ r.val * 7 + (neg7 c).val) && (__CM2__ : Nat).testBit (r.val * 7 + (neg7 c).val - 3)) = true → r.val * 7 + (neg7 c).val - 3 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (3 ≤ r.val * 7 + (neg7 c).val) && (__CM2__ : Nat).testBit (r.val * 7 + (neg7 c).val - 3)) = decide (c = 2)) r c),
      bit_shiftL_masked m __CM3__ 1 dst src (decide (c = 3))
        ((by decide : ∀ r c : Fin 7, (decide (1 ≤ r.val * 7 + (neg7 c).val) && (__CM3__ : Nat).testBit (r.val * 7 + (neg7 c).val - 1)) = true → r.val * 7 + (neg7 c).val - 1 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (1 ≤ r.val * 7 + (neg7 c).val) && (__CM3__ : Nat).testBit (r.val * 7 + (neg7 c).val - 1)) = decide (c = 3)) r c),
      bit_shiftR_masked m __CM4__ 1 dst src (decide (c = 4))
        ((by decide : ∀ r c : Fin 7, (__CM4__ : Nat).testBit (1 + (r.val * 7 + (neg7 c).val)) = true → 1 + (r.val * 7 + (neg7 c).val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (__CM4__ : Nat).testBit (1 + (r.val * 7 + (neg7 c).val)) = decide (c = 4)) r c),
      bit_shiftR_masked m __CM5__ 3 dst src (decide (c = 5))
        ((by decide : ∀ r c : Fin 7, (__CM5__ : Nat).testBit (3 + (r.val * 7 + (neg7 c).val)) = true → 3 + (r.val * 7 + (neg7 c).val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (__CM5__ : Nat).testBit (3 + (r.val * 7 + (neg7 c).val)) = decide (c = 5)) r c),
      bit_shiftR_masked m __CM6__ 5 dst src (decide (c = 6))
        ((by decide : ∀ r c : Fin 7, (__CM6__ : Nat).testBit (5 + (r.val * 7 + (neg7 c).val)) = true → 5 + (r.val * 7 + (neg7 c).val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (__CM6__ : Nat).testBit (5 + (r.val * 7 + (neg7 c).val)) = decide (c = 6)) r c)]
  revert c; refine fin7_cases ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp

private lemma get49_shiftCol_aux (m lo hi : Nat) (t : Fin 7) (kL kR : Nat)
    (h1 : ∀ r c : Fin 7, (decide (kL ≤ r.val * 7 + (add7 c t).val) && lo.testBit (r.val * 7 + (add7 c t).val - kL)) = true →
          r.val * 7 + (add7 c t).val - kL = r.val * 7 + c.val)
    (h2 : ∀ r c : Fin 7, hi.testBit (kR + (r.val * 7 + (add7 c t).val)) = true →
          kR + (r.val * 7 + (add7 c t).val) = r.val * 7 + c.val)
    (h3 : ∀ r c : Fin 7, ((decide (kL ≤ r.val * 7 + (add7 c t).val) && lo.testBit (r.val * 7 + (add7 c t).val - kL)) ||
                          hi.testBit (kR + (r.val * 7 + (add7 c t).val))) = true)
    (r c : Fin 7) :
    get49 (((m &&& lo) <<< kL) ||| ((m &&& hi) >>> kR)) r (add7 c t) = get49 m r c := by
  unfold get49
  rw [Nat.testBit_or,
      bit_shiftL_masked m lo kL (r.val * 7 + (add7 c t).val) (r.val * 7 + c.val) _ (h1 r c) rfl,
      bit_shiftR_masked m hi kR (r.val * 7 + (add7 c t).val) (r.val * 7 + c.val) _ (h2 r c) rfl]
  have hf := h3 r c
  cases a : (decide (kL ≤ r.val * 7 + (add7 c t).val) && lo.testBit (r.val * 7 + (add7 c t).val - kL)) <;>
  cases b : hi.testBit (kR + (r.val * 7 + (add7 c t).val)) <;> simp_all

private lemma get49_shiftCol (t : Fin 7) (m : Nat) (r c : Fin 7) :
    get49 (shiftCol49 t m) r (add7 c t) = get49 m r c := by
  unfold shiftCol49
  revert t
  refine fin7_cases ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have h0 : add7 c 0 = c := (by decide : ∀ x : Fin 7, add7 x 0 = x) c
    rw [h0]; rfl
  · exact get49_shiftCol_aux m __SCLO1__ __SCHI1__ 1 1 6 (by decide) (by decide) (by decide) r c
  · exact get49_shiftCol_aux m __SCLO2__ __SCHI2__ 2 2 5 (by decide) (by decide) (by decide) r c
  · exact get49_shiftCol_aux m __SCLO3__ __SCHI3__ 3 3 4 (by decide) (by decide) (by decide) r c
  · exact get49_shiftCol_aux m __SCLO4__ __SCHI4__ 4 4 3 (by decide) (by decide) (by decide) r c
  · exact get49_shiftCol_aux m __SCLO5__ __SCHI5__ 5 5 2 (by decide) (by decide) (by decide) r c
  · exact get49_shiftCol_aux m __SCLO6__ __SCHI6__ 6 6 1 (by decide) (by decide) (by decide) r c

private lemma get49_transpose (m : Nat) (r c : Fin 7) :
    get49 (transpose49 m) c r = get49 m r c := by
  unfold get49 transpose49
  let dst := c.val * 7 + r.val
  let src := r.val * 7 + c.val
  change ((m &&& __DIAG0__) ||| (((m &&& __DP1__) <<< 6) ||| (((m &&& __DP2__) <<< 12) |||
    (((m &&& __DP3__) <<< 18) ||| (((m &&& __DP4__) <<< 24) ||| (((m &&& __DP5__) <<< 30) |||
    (((m &&& __DP6__) <<< 36) ||| (((m &&& __DN1__) >>> 6) ||| (((m &&& __DN2__) >>> 12) |||
    (((m &&& __DN3__) >>> 18) ||| (((m &&& __DN4__) >>> 24) ||| (((m &&& __DN5__) >>> 30) |||
    ((m &&& __DN6__) >>> 36))))))))))))).testBit dst = m.testBit src
  simp only [Nat.testBit_or]
  rw [bit_and_masked m __DIAG0__ dst src (decide (r.val = c.val))
        ((by decide : ∀ r c : Fin 7, (__DIAG0__ : Nat).testBit (c.val * 7 + r.val) = true → c.val * 7 + r.val = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (__DIAG0__ : Nat).testBit (c.val * 7 + r.val) = decide (r.val = c.val)) r c),
      bit_shiftL_masked m __DP1__ 6 dst src (decide (r.val + 1 = c.val))
        ((by decide : ∀ r c : Fin 7, (decide (6 ≤ c.val * 7 + r.val) && (__DP1__ : Nat).testBit (c.val * 7 + r.val - 6)) = true → c.val * 7 + r.val - 6 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (6 ≤ c.val * 7 + r.val) && (__DP1__ : Nat).testBit (c.val * 7 + r.val - 6)) = decide (r.val + 1 = c.val)) r c),
      bit_shiftL_masked m __DP2__ 12 dst src (decide (r.val + 2 = c.val))
        ((by decide : ∀ r c : Fin 7, (decide (12 ≤ c.val * 7 + r.val) && (__DP2__ : Nat).testBit (c.val * 7 + r.val - 12)) = true → c.val * 7 + r.val - 12 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (12 ≤ c.val * 7 + r.val) && (__DP2__ : Nat).testBit (c.val * 7 + r.val - 12)) = decide (r.val + 2 = c.val)) r c),
      bit_shiftL_masked m __DP3__ 18 dst src (decide (r.val + 3 = c.val))
        ((by decide : ∀ r c : Fin 7, (decide (18 ≤ c.val * 7 + r.val) && (__DP3__ : Nat).testBit (c.val * 7 + r.val - 18)) = true → c.val * 7 + r.val - 18 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (18 ≤ c.val * 7 + r.val) && (__DP3__ : Nat).testBit (c.val * 7 + r.val - 18)) = decide (r.val + 3 = c.val)) r c),
      bit_shiftL_masked m __DP4__ 24 dst src (decide (r.val + 4 = c.val))
        ((by decide : ∀ r c : Fin 7, (decide (24 ≤ c.val * 7 + r.val) && (__DP4__ : Nat).testBit (c.val * 7 + r.val - 24)) = true → c.val * 7 + r.val - 24 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (24 ≤ c.val * 7 + r.val) && (__DP4__ : Nat).testBit (c.val * 7 + r.val - 24)) = decide (r.val + 4 = c.val)) r c),
      bit_shiftL_masked m __DP5__ 30 dst src (decide (r.val + 5 = c.val))
        ((by decide : ∀ r c : Fin 7, (decide (30 ≤ c.val * 7 + r.val) && (__DP5__ : Nat).testBit (c.val * 7 + r.val - 30)) = true → c.val * 7 + r.val - 30 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (30 ≤ c.val * 7 + r.val) && (__DP5__ : Nat).testBit (c.val * 7 + r.val - 30)) = decide (r.val + 5 = c.val)) r c),
      bit_shiftL_masked m __DP6__ 36 dst src (decide (r.val + 6 = c.val))
        ((by decide : ∀ r c : Fin 7, (decide (36 ≤ c.val * 7 + r.val) && (__DP6__ : Nat).testBit (c.val * 7 + r.val - 36)) = true → c.val * 7 + r.val - 36 = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (decide (36 ≤ c.val * 7 + r.val) && (__DP6__ : Nat).testBit (c.val * 7 + r.val - 36)) = decide (r.val + 6 = c.val)) r c),
      bit_shiftR_masked m __DN1__ 6 dst src (decide (c.val + 1 = r.val))
        ((by decide : ∀ r c : Fin 7, (__DN1__ : Nat).testBit (6 + (c.val * 7 + r.val)) = true → 6 + (c.val * 7 + r.val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (__DN1__ : Nat).testBit (6 + (c.val * 7 + r.val)) = decide (c.val + 1 = r.val)) r c),
      bit_shiftR_masked m __DN2__ 12 dst src (decide (c.val + 2 = r.val))
        ((by decide : ∀ r c : Fin 7, (__DN2__ : Nat).testBit (12 + (c.val * 7 + r.val)) = true → 12 + (c.val * 7 + r.val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (__DN2__ : Nat).testBit (12 + (c.val * 7 + r.val)) = decide (c.val + 2 = r.val)) r c),
      bit_shiftR_masked m __DN3__ 18 dst src (decide (c.val + 3 = r.val))
        ((by decide : ∀ r c : Fin 7, (__DN3__ : Nat).testBit (18 + (c.val * 7 + r.val)) = true → 18 + (c.val * 7 + r.val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (__DN3__ : Nat).testBit (18 + (c.val * 7 + r.val)) = decide (c.val + 3 = r.val)) r c),
      bit_shiftR_masked m __DN4__ 24 dst src (decide (c.val + 4 = r.val))
        ((by decide : ∀ r c : Fin 7, (__DN4__ : Nat).testBit (24 + (c.val * 7 + r.val)) = true → 24 + (c.val * 7 + r.val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (__DN4__ : Nat).testBit (24 + (c.val * 7 + r.val)) = decide (c.val + 4 = r.val)) r c),
      bit_shiftR_masked m __DN5__ 30 dst src (decide (c.val + 5 = r.val))
        ((by decide : ∀ r c : Fin 7, (__DN5__ : Nat).testBit (30 + (c.val * 7 + r.val)) = true → 30 + (c.val * 7 + r.val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (__DN5__ : Nat).testBit (30 + (c.val * 7 + r.val)) = decide (c.val + 5 = r.val)) r c),
      bit_shiftR_masked m __DN6__ 36 dst src (decide (c.val + 6 = r.val))
        ((by decide : ∀ r c : Fin 7, (__DN6__ : Nat).testBit (36 + (c.val * 7 + r.val)) = true → 36 + (c.val * 7 + r.val) = r.val * 7 + c.val) r c)
        ((by decide : ∀ r c : Fin 7, (__DN6__ : Nat).testBit (36 + (c.val * 7 + r.val)) = decide (c.val + 6 = r.val)) r c)]
  have hdisj : ∀ b : Bool, ∀ a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : Bool,
      (a0 || a1 || a2 || a3 || a4 || a5 || a6 || b1 || b2 || b3 || b4 || b5 || b6) = true →
      ((a0 && b) || ((a1 && b) || ((a2 && b) || ((a3 && b) || ((a4 && b) || ((a5 && b) ||
       ((a6 && b) || ((b1 && b) || ((b2 && b) || ((b3 && b) || ((b4 && b) || ((b5 && b) ||
       (b6 && b))))))))))))) = b := by
    intro b a0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 h
    cases b
    · simp
    · simp only [Bool.and_true]; simp only [Bool.or_assoc] at h ⊢; exact h
  refine hdisj (m.testBit src) _ _ _ _ _ _ _ _ _ _ _ _ _ ?_
  have hcov : ∀ r c : Fin 7,
      (decide (r.val = c.val) || decide (r.val + 1 = c.val) || decide (r.val + 2 = c.val) ||
       decide (r.val + 3 = c.val) || decide (r.val + 4 = c.val) || decide (r.val + 5 = c.val) ||
       decide (r.val + 6 = c.val) || decide (c.val + 1 = r.val) || decide (c.val + 2 = r.val) ||
       decide (c.val + 3 = r.val) || decide (c.val + 4 = r.val) || decide (c.val + 5 = r.val) ||
       decide (c.val + 6 = r.val)) = true := by decide
  exact hcov r c

private structure Aut2 where
  sw : Bool
  sr : Bool
  tr : Fin 7
  sc : Bool
  tc : Fin 7
  deriving DecidableEq

private def Aut2.applyFin (g : Aut2) (p : Fin 7 × Fin 7) : Fin 7 × Fin 7 :=
  let r1 := if g.sr then neg7 p.1 else p.1
  let r2 := add7 r1 g.tr
  let c1 := if g.sc then neg7 p.2 else p.2
  let c2 := add7 c1 g.tc
  if g.sw then (c2, r2) else (r2, c2)

private def Aut2.inv (g : Aut2) : Aut2 :=
  let tr' := if g.sr then g.tr else neg7 g.tr
  let tc' := if g.sc then g.tc else neg7 g.tc
  if g.sw then ⟨true, g.sc, tc', g.sr, tr'⟩ else ⟨false, g.sr, tr', g.sc, tc'⟩

private lemma Aut2.inv_applyFin (g : Aut2) (p : Fin 7 × Fin 7) :
    g.inv.applyFin (g.applyFin p) = p := by
  rcases g with ⟨sw, sr, tr, sc, tc⟩
  rcases p with ⟨r, c⟩
  cases sw <;> simp only [Aut2.applyFin, Aut2.inv, Bool.false_eq_true, ↓reduceIte, d7_inv_left]

private lemma Aut2.applyFin_inv (g : Aut2) (p : Fin 7 × Fin 7) :
    g.applyFin (g.inv.applyFin p) = p := by
  rcases g with ⟨sw, sr, tr, sc, tc⟩
  rcases p with ⟨r, c⟩
  cases sw <;> simp only [Aut2.applyFin, Aut2.inv, Bool.false_eq_true, ↓reduceIte, d7_inv_right]

private def Aut2.toIso (g : Aut2) : (C7 ⊠ C7) ≃g (C7 ⊠ C7) where
  toEquiv := Equiv.mk
    (fun q => let p := g.applyFin (ofZ7 q.1, ofZ7 q.2); (toZ7 p.1, toZ7 p.2))
    (fun q => let p := g.inv.applyFin (ofZ7 q.1, ofZ7 q.2); (toZ7 p.1, toZ7 p.2))
    (fun ⟨a, b⟩ => by
      dsimp only
      rw [ofZ7_toZ7, ofZ7_toZ7, Prod.mk.eta, g.inv_applyFin, toZ7_ofZ7, toZ7_ofZ7])
    (fun ⟨a, b⟩ => by
      dsimp only
      rw [ofZ7_toZ7, ofZ7_toZ7, Prod.mk.eta, g.applyFin_inv, toZ7_ofZ7, toZ7_ofZ7])
  map_rel_iff' := by
    have hd7_adj : ∀ (s : Bool) (t : Fin 7) (a b : ZMod 7),
        C7.Adj (toZ7 (add7 (if s then neg7 (ofZ7 a) else ofZ7 a) t))
               (toZ7 (add7 (if s then neg7 (ofZ7 b) else ofZ7 b) t)) ↔ C7.Adj a b := by
      intro s t a b
      have hsub : ∀ x y : ZMod 7, C7.Adj x y ↔ (x - y = 1 ∨ y - x = 1) := by
        intro x y; unfold C7; exact SimpleGraph.cycleGraph_adj
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, toZ7_add7, toZ7_neg7, toZ7_ofZ7, hsub]
      · constructor
        · rintro (h | h)
          · left; linear_combination h
          · right; linear_combination h
        · rintro (h | h)
          · left; linear_combination h
          · right; linear_combination h
      · constructor
        · rintro (h | h)
          · right; linear_combination h
          · left; linear_combination h
        · rintro (h | h)
          · right; linear_combination h
          · left; linear_combination h
    have hd7_eq : ∀ (s : Bool) (t : Fin 7) (a b : ZMod 7),
        toZ7 (add7 (if s then neg7 (ofZ7 a) else ofZ7 a) t) =
          toZ7 (add7 (if s then neg7 (ofZ7 b) else ofZ7 b) t) ↔ a = b := by
      intro s t a b
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, toZ7_add7, toZ7_neg7, toZ7_ofZ7]
      · exact add_left_inj _
      · simp
    intro ⟨a1, b1⟩ ⟨a2, b2⟩
    rcases g with ⟨sw, sr, tr, sc, tc⟩
    have hsw : ∀ (P1 P2 Q1 Q2 : Prop),
        (¬(P1 ∧ P2) ∧ (P1 ∨ Q1) ∧ (P2 ∨ Q2)) ↔ (¬(P2 ∧ P1) ∧ (P2 ∨ Q2) ∧ (P1 ∨ Q1)) := by
      intro P1 P2 Q1 Q2
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨fun ⟨a, b⟩ => h1 ⟨b, a⟩, h3, h2⟩,
             fun ⟨h1, h2, h3⟩ => ⟨fun ⟨a, b⟩ => h1 ⟨b, a⟩, h3, h2⟩⟩
    cases sw <;> simp only [Equiv.coe_fn_mk, Aut2.applyFin, Bool.false_eq_true, ↓reduceIte,
      strongProd_adj, ne_eq, Prod.mk.injEq, hd7_eq, hd7_adj]
    · exact hsw _ _ _ _

private def Aut2.applyMask (g : Aut2) (m : Nat) : Nat :=
  seqN (match g.sr with | true => flipRow49 m | false => m) fun m1 =>
  seqN (shiftRow49 g.tr m1) fun m2 =>
  seqN (match g.sc with | true => flipCol49 m2 | false => m2) fun m3 =>
  seqN (shiftCol49 g.tc m3) fun m4 =>
  match g.sw with | true => transpose49 m4 | false => m4

private lemma Aut2.applyMask_lt (g : Aut2) {m : Nat} (hm : m < 2 ^ 49) :
    g.applyMask m < 2 ^ 49 := by
  unfold Aut2.applyMask
  simp only [seqN_eq]
  let m1 := match g.sr with | true => flipRow49 m | false => m
  have h1 : m1 < 2 ^ 49 := by
    dsimp only [m1]; cases g.sr
    · exact hm
    · exact flipRow49_lt m
  have h2 : shiftRow49 g.tr m1 < 2 ^ 49 := shiftRow49_lt g.tr h1
  let m3 := match g.sc with | true => flipCol49 (shiftRow49 g.tr m1) | false => shiftRow49 g.tr m1
  have h3 : m3 < 2 ^ 49 := by
    dsimp only [m3]; cases g.sc
    · exact h2
    · exact flipCol49_lt _
  have h4 : shiftCol49 g.tc m3 < 2 ^ 49 := shiftCol49_lt g.tc h3
  cases g.sw
  · exact h4
  · exact transpose49_lt _

private lemma Aut2.get_applyMask (g : Aut2) (m : Nat) (r c : Fin 7) :
    get49 (g.applyMask m) (g.applyFin (r, c)).1 (g.applyFin (r, c)).2 = get49 m r c := by
  rcases g with ⟨sw, sr, tr, sc, tc⟩
  unfold Aut2.applyMask Aut2.applyFin
  simp only [seqN_eq]
  cases sw <;> cases sr <;> cases sc <;>
    simp only [Bool.false_eq_true, ↓reduceIte, get49_transpose, get49_shiftCol, get49_flipCol,
      get49_shiftRow, get49_flipRow]

private lemma Aut2.get_applyMask_eq (g : Aut2) (m : Nat) (r c : Fin 7) :
    get49 (g.applyMask m) r c = get49 m (g.inv.applyFin (r, c)).1 (g.inv.applyFin (r, c)).2 := by
  have h := g.get_applyMask m (g.inv.applyFin (r, c)).1 (g.inv.applyFin (r, c)).2
  rw [Prod.mk.eta, g.applyFin_inv] at h
  exact h

private lemma Aut2.applyMask_inv_left (g : Aut2) {m : Nat} (hm : m < 2 ^ 49) :
    g.inv.applyMask (g.applyMask m) = m := by
  apply ext49 (g.inv.applyMask_lt (g.applyMask_lt hm)) hm
  intro r c
  rw [g.inv.get_applyMask_eq, g.get_applyMask_eq]
  have hinv : g.inv.inv = g := by
    rcases g with ⟨sw, sr, tr, sc, tc⟩
    have hneg : ∀ x : Fin 7, neg7 (neg7 x) = x := by decide
    cases sw <;> cases sr <;> cases sc <;> simp [Aut2.inv, hneg]
  rw [hinv, Prod.mk.eta, g.inv_applyFin]

private lemma Aut2.applyMask_inv_right (g : Aut2) {m : Nat} (hm : m < 2 ^ 49) :
    g.applyMask (g.inv.applyMask m) = m := by
  have hinv : g.inv.inv = g := by
    rcases g with ⟨sw, sr, tr, sc, tc⟩
    have hneg : ∀ x : Fin 7, neg7 (neg7 x) = x := by decide
    cases sw <;> cases sr <;> cases sc <;> simp [Aut2.inv, hneg]
  have h := g.inv.applyMask_inv_left hm
  rwa [hinv] at h

private lemma Aut2.applyMask_diff (g : Aut2) {a b : Nat} (ha : a < 2 ^ 49) :
    g.applyMask (diff49 a b) = diff49 (g.applyMask a) (g.applyMask b) := by
  apply ext49 (g.applyMask_lt (diff49_lt ha)) (diff49_lt (g.applyMask_lt ha))
  intro r c
  rw [g.get_applyMask_eq, get49_diff, get49_diff, g.get_applyMask_eq, g.get_applyMask_eq]

private lemma Aut2.applyMask_subset {g : Aut2} {a b : Nat} (ha : a < 2 ^ 49)
    (h : subset49 a b = true) : subset49 (g.applyMask a) (g.applyMask b) = true := by
  rw [subset49_iff ha] at h
  rw [subset49_iff (g.applyMask_lt ha)]
  intro r c hga
  rw [g.get_applyMask_eq] at hga ⊢
  exact h _ _ hga

private lemma Aut2.applyMask_ofFinset (g : Aut2) (S : Finset (ZMod 7 × ZMod 7)) :
    g.applyMask (ofFinset49 S) = ofFinset49 (S.map g.toIso.toEquiv.toEmbedding) := by
  apply ext49 (g.applyMask_lt (ofFinset49_lt S)) (ofFinset49_lt _)
  intro r c
  rw [Bool.eq_iff_iff, g.get_applyMask_eq, get49_ofFinset, get49_ofFinset, Finset.mem_map]
  constructor
  · intro h
    refine ⟨(toZ7 (g.inv.applyFin (r, c)).1, toZ7 (g.inv.applyFin (r, c)).2), h, ?_⟩
    simp only [Equiv.coe_toEmbedding, Aut2.toIso, Equiv.coe_fn_mk,
      ofZ7_toZ7, Prod.mk.eta, g.applyFin_inv]
  · rintro ⟨⟨a, b⟩, hab, heq⟩
    simp only [Equiv.coe_toEmbedding, Aut2.toIso, Equiv.coe_fn_mk] at heq
    have h1 := congrArg (fun q : ZMod 7 × ZMod 7 => g.inv.applyFin (ofZ7 q.1, ofZ7 q.2)) heq
    dsimp only at h1
    rw [ofZ7_toZ7, ofZ7_toZ7, ofZ7_toZ7, ofZ7_toZ7, Prod.mk.eta, g.inv_applyFin] at h1
    rw [← h1, toZ7_ofZ7, toZ7_ofZ7]
    exact hab

private lemma Aut2.applyMask_closedNbr (g : Aut2) {m : Nat} (hm : m < 2 ^ 49) :
    g.applyMask (closedNbr49 m) = closedNbr49 (g.applyMask m) := by
  apply ext49 (g.applyMask_lt (closedNbr49_lt hm)) (closedNbr49_lt (g.applyMask_lt hm))
  intro r c
  have hclose : ∀ a1 b1 a2 b2 : Fin 7,
      ((toZ7 a1 = toZ7 a2 ∨ C7.Adj (toZ7 a1) (toZ7 a2)) ∧
       (toZ7 b1 = toZ7 b2 ∨ C7.Adj (toZ7 b1) (toZ7 b2))) ↔
      ((toZ7 (g.applyFin (a1, b1)).1 = toZ7 (g.applyFin (a2, b2)).1 ∨
          C7.Adj (toZ7 (g.applyFin (a1, b1)).1) (toZ7 (g.applyFin (a2, b2)).1)) ∧
       (toZ7 (g.applyFin (a1, b1)).2 = toZ7 (g.applyFin (a2, b2)).2 ∨
          C7.Adj (toZ7 (g.applyFin (a1, b1)).2) (toZ7 (g.applyFin (a2, b2)).2))) := by
    have hpair : ∀ (x1 y1 x2 y2 : ZMod 7),
        ((x1, y1) = (x2, y2) ∨ (C7 ⊠ C7).Adj (x1, y1) (x2, y2)) ↔
        ((x1 = x2 ∨ C7.Adj x1 x2) ∧ (y1 = y2 ∨ C7.Adj y1 y2)) := by
      intro x1 y1 x2 y2
      simp only [Prod.mk.injEq, strongProd_adj, ne_eq]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨_, h1, h2⟩)
        · exact ⟨Or.inl rfl, Or.inl rfl⟩
        · exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        by_cases heq : x1 = x2 ∧ y1 = y2
        · exact Or.inl heq
        · exact Or.inr ⟨heq, h1, h2⟩
    intro a1 b1 a2 b2
    have h := hpair (toZ7 a1) (toZ7 b1) (toZ7 a2) (toZ7 b2)
    have h' := hpair (toZ7 (g.applyFin (a1, b1)).1) (toZ7 (g.applyFin (a1, b1)).2)
                     (toZ7 (g.applyFin (a2, b2)).1) (toZ7 (g.applyFin (a2, b2)).2)
    have hg1 : g.toIso (toZ7 a1, toZ7 b1) = (toZ7 (g.applyFin (a1, b1)).1, toZ7 (g.applyFin (a1, b1)).2) := by
      simp [Aut2.toIso, ofZ7_toZ7]
    have hg2 : g.toIso (toZ7 a2, toZ7 b2) = (toZ7 (g.applyFin (a2, b2)).1, toZ7 (g.applyFin (a2, b2)).2) := by
      simp [Aut2.toIso, ofZ7_toZ7]
    have h'' : g.toIso (toZ7 a1, toZ7 b1) = g.toIso (toZ7 a2, toZ7 b2) ∨
        (C7 ⊠ C7).Adj (g.toIso (toZ7 a1, toZ7 b1)) (g.toIso (toZ7 a2, toZ7 b2)) ↔
        (toZ7 (g.applyFin (a1, b1)).1 = toZ7 (g.applyFin (a2, b2)).1 ∨
          C7.Adj (toZ7 (g.applyFin (a1, b1)).1) (toZ7 (g.applyFin (a2, b2)).1)) ∧
        (toZ7 (g.applyFin (a1, b1)).2 = toZ7 (g.applyFin (a2, b2)).2 ∨
          C7.Adj (toZ7 (g.applyFin (a1, b1)).2) (toZ7 (g.applyFin (a2, b2)).2)) := by
      simpa only [hg1, hg2] using h'
    rw [← h, ← h'', g.toIso.injective.eq_iff, g.toIso.map_adj_iff]
  rw [Bool.eq_iff_iff, g.get_applyMask_eq, closedNbr49_get, closedNbr49_get]
  constructor
  · rintro ⟨r', c', hm', hr, hc⟩
    refine ⟨(g.applyFin (r', c')).1, (g.applyFin (r', c')).2, ?_, ?_⟩
    · rw [g.get_applyMask]; exact hm'
    · have hcl := (hclose r' c' (g.inv.applyFin (r, c)).1 (g.inv.applyFin (r, c)).2).mp ⟨hr, hc⟩
      rw [Prod.mk.eta, g.applyFin_inv] at hcl
      exact hcl
  · rintro ⟨r', c', hm', hr, hc⟩
    rw [g.get_applyMask_eq] at hm'
    refine ⟨(g.inv.applyFin (r', c')).1, (g.inv.applyFin (r', c')).2, hm', ?_⟩
    have hcl := (hclose (g.inv.applyFin (r', c')).1 (g.inv.applyFin (r', c')).2
      (g.inv.applyFin (r, c)).1 (g.inv.applyFin (r, c)).2).mpr
      (by rw [Prod.mk.eta, Prod.mk.eta, g.applyFin_inv, g.applyFin_inv]; exact ⟨hr, hc⟩)
    exact hcl

private lemma isIndepSet_map_iso' {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    {S : Finset V} (hS : G.IsIndepSet (S : Set V)) :
    H.IsIndepSet ((S.map e.toEquiv.toEmbedding : Finset W) : Set W) := by
  intro x hx y hy hne hadj
  simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Equiv.coe_toEmbedding,
    RelIso.coe_fn_toEquiv] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact hS ha hb (fun hab => hne (congrArg e hab)) ((e.map_adj_iff).mp hadj)

/-! ## Section 3: Exact 3-Orbit Classification of `I₁₀(C₇ ⊠ C₇)` & Loop-Hoisted Enumeration -/

private def rep (k : Fin 3) : Nat :=
  match k.val with | 0 => __REP0__ | 1 => __REP1__ | _ => __REP2__

private lemma rep_lt (k : Fin 3) : rep k < 2 ^ 49 := by
  revert k; decide

private def repPtsList (k : Fin 3) : List (Fin 7 × Fin 7) :=
  match k.val with
  | 0 => [(0, 3), (0, 5), (1, 1), (2, 4), (2, 6), (3, 2), (4, 0), (4, 4), (5, 2), (6, 0)]
  | 1 => [(0, 3), (0, 5), (1, 0), (2, 3), (2, 5), (3, 1), (4, 4), (4, 6), (5, 2), (6, 0)]
  | _ => [(0, 3), (0, 5), (1, 1), (2, 3), (2, 6), (3, 1), (4, 4), (4, 6), (5, 2), (6, 0)]

private lemma rep_mem_iff : ∀ (k : Fin 3) (r c : Fin 7),
    get49 (rep k) r c = true ↔ (r, c) ∈ repPtsList k := by decide

private lemma repPtsList_nodup : ∀ k : Fin 3, (repPtsList k).Nodup := by decide

private def forAllFin7 (f : Fin 7 → Bool) : Bool :=
  f 0 && f 1 && f 2 && f 3 && f 4 && f 5 && f 6

private lemma forAllFin7_sound {f : Fin 7 → Bool} (h : forAllFin7 f = true) :
    ∀ x : Fin 7, f x = true := by
  unfold forAllFin7 at h
  simp only [Bool.and_eq_true] at h
  exact fun
    | ⟨0, _⟩ => h.1.1.1.1.1.1 | ⟨1, _⟩ => h.1.1.1.1.1.2 | ⟨2, _⟩ => h.1.1.1.1.2
    | ⟨3, _⟩ => h.1.1.1.2     | ⟨4, _⟩ => h.1.1.2       | ⟨5, _⟩ => h.1.2
    | ⟨6, _⟩ => h.2

private def foldFin7 {α : Type} (f : Fin 7 → α → α) (acc : α) : α :=
  f 6 (f 5 (f 4 (f 3 (f 2 (f 1 (f 0 acc))))))

private lemma mem_foldFin7 {α : Type} {y : α} {f : Fin 7 → List α → List α}
    (hmono : ∀ (x : Fin 7) (l : List α), y ∈ l → y ∈ f x l)
    (x0 : Fin 7) (hhit : ∀ l : List α, y ∈ f x0 l) (acc : List α) :
    y ∈ foldFin7 f acc := by
  unfold foldFin7
  revert x0 hhit
  exact fun
    | ⟨0, _⟩, h => hmono 6 _ (hmono 5 _ (hmono 4 _ (hmono 3 _ (hmono 2 _ (hmono 1 _ (h _))))))
    | ⟨1, _⟩, h => hmono 6 _ (hmono 5 _ (hmono 4 _ (hmono 3 _ (hmono 2 _ (h _)))))
    | ⟨2, _⟩, h => hmono 6 _ (hmono 5 _ (hmono 4 _ (hmono 3 _ (h _))))
    | ⟨3, _⟩, h => hmono 6 _ (hmono 5 _ (hmono 4 _ (h _)))
    | ⟨4, _⟩, h => hmono 6 _ (hmono 5 _ (h _))
    | ⟨5, _⟩, h => hmono 6 _ (h _)
    | ⟨6, _⟩, h => h _

private lemma mem_foldFin7_mono {α : Type} {y : α} {f : Fin 7 → List α → List α}
    (hmono : ∀ (x : Fin 7) (l : List α), y ∈ l → y ∈ f x l) {acc : List α} (h : y ∈ acc) :
    y ∈ foldFin7 f acc :=
  hmono 6 _ (hmono 5 _ (hmono 4 _ (hmono 3 _ (hmono 2 _ (hmono 1 _ (hmono 0 _ h))))))

private def forAllAut2 (k0 : Fin 3) (half : Bool) (f : Aut2 → Nat → Bool) : Bool :=
  let base := rep k0
  let goSr (sr : Bool) : Bool :=
    seqN (match sr with | true => flipRow49 base | false => base) fun m1 =>
    forAllFin7 fun tr =>
      seqN (shiftRow49 tr m1) fun m2 =>
      let goSc (sc : Bool) : Bool :=
        seqN (match sc with | true => flipCol49 m2 | false => m2) fun m3 =>
        forAllFin7 fun tc =>
          seqN (shiftCol49 tc m3) fun m4 =>
            f ⟨false, sr, tr, sc, tc⟩ m4 &&
            seqN (transpose49 m4) fun m5 => f ⟨true, sr, tr, sc, tc⟩ m5
      goSc false && goSc true
  match half with
  | true => goSr false
  | false => goSr false && goSr true

private lemma forAllAut2_sound {k0 : Fin 3} {half : Bool} {f : Aut2 → Nat → Bool}
    (h : forAllAut2 k0 half f = true) (g : Aut2) (hsr : half = false ∨ g.sr = false) :
    f g (g.applyMask (rep k0)) = true := by
  rcases g with ⟨sw, sr, tr, sc, tc⟩
  unfold forAllAut2 at h
  simp only [seqN_eq] at h
  cases sr
  · have hgoSr : forAllFin7 (fun tr' =>
        let m2 := shiftRow49 tr' (rep k0)
        let goSc (sc' : Bool) : Bool :=
          let m3 := match sc' with | true => flipCol49 m2 | false => m2
          forAllFin7 fun tc' =>
            let m4 := shiftCol49 tc' m3
            f ⟨false, false, tr', sc', tc'⟩ m4 && f ⟨true, false, tr', sc', tc'⟩ (transpose49 m4)
        goSc false && goSc true) = true := by
      cases half
      · exact (Bool.and_eq_true _ _ |>.mp h).1
      · exact h
    have htr := forAllFin7_sound hgoSr tr
    dsimp only at htr; rw [Bool.and_eq_true] at htr
    unfold Aut2.applyMask; simp only [seqN_eq]
    cases sc
    · have htc := forAllFin7_sound htr.1 tc
      rw [Bool.and_eq_true] at htc
      cases sw
      · exact htc.1
      · exact htc.2
    · have htc := forAllFin7_sound htr.2 tc
      rw [Bool.and_eq_true] at htc
      cases sw
      · exact htc.1
      · exact htc.2
  · have hgoSr : forAllFin7 (fun tr' =>
        let m2 := shiftRow49 tr' (flipRow49 (rep k0))
        let goSc (sc' : Bool) : Bool :=
          let m3 := match sc' with | true => flipCol49 m2 | false => m2
          forAllFin7 fun tc' =>
            let m4 := shiftCol49 tc' m3
            f ⟨false, true, tr', sc', tc'⟩ m4 && f ⟨true, true, tr', sc', tc'⟩ (transpose49 m4)
        goSc false && goSc true) = true := by
      cases half
      · exact (Bool.and_eq_true _ _ |>.mp h).2
      · rcases hsr with hbad | hbad <;> cases hbad
    have htr := forAllFin7_sound hgoSr tr
    dsimp only at htr; rw [Bool.and_eq_true] at htr
    unfold Aut2.applyMask; simp only [seqN_eq]
    cases sc
    · have htc := forAllFin7_sound htr.1 tc
      rw [Bool.and_eq_true] at htc
      cases sw
      · exact htc.1
      · exact htc.2
    · have htc := forAllFin7_sound htr.2 tc
      rw [Bool.and_eq_true] at htc
      cases sw
      · exact htc.1
      · exact htc.2

private def collectAut2 (k0 : Fin 3) (half : Bool) (pred : Nat → Bool)
    (acc : List (Fin 3 × Aut2 × Nat)) : List (Fin 3 × Aut2 × Nat) :=
  let base := rep k0
  let goSr (sr : Bool) (a0 : List (Fin 3 × Aut2 × Nat)) :=
    seqN (match sr with | true => flipRow49 base | false => base) fun m1 =>
    foldFin7 (fun tr a1 =>
      seqN (shiftRow49 tr m1) fun m2 =>
      let goSc (sc : Bool) (a2 : List (Fin 3 × Aut2 × Nat)) :=
        seqN (match sc with | true => flipCol49 m2 | false => m2) fun m3 =>
        foldFin7 (fun tc a3 =>
          seqN (shiftCol49 tc m3) fun m4 =>
          let a4 := match pred m4 with
            | true => (k0, Aut2.mk false sr tr sc tc, m4) :: a3
            | false => a3
          seqN (transpose49 m4) fun m5 =>
          match pred m5 with
            | true => (k0, Aut2.mk true sr tr sc tc, m5) :: a4
            | false => a4) a2
      goSc true (goSc false a1)) a0
  match half with
  | true => goSr false acc
  | false => goSr true (goSr false acc)

private lemma mem_collectAut2_mono {k0 : Fin 3} {half : Bool} {pred : Nat → Bool}
    {y : Fin 3 × Aut2 × Nat} {acc : List (Fin 3 × Aut2 × Nat)} (hy : y ∈ acc) :
    y ∈ collectAut2 k0 half pred acc := by
  have hstep : ∀ (a : Fin 3 × Aut2 × Nat) (b : Bool) (l : List (Fin 3 × Aut2 × Nat)),
      y ∈ l → y ∈ (match b with | true => a :: l | false => l) := by
    intro a b l hl; cases b
    · exact hl
    · exact List.mem_cons_of_mem a hl
  have htc : ∀ sr tr sc (m3 : Nat) (a2 : List _), y ∈ a2 →
      y ∈ foldFin7 (fun tc a3 =>
        let m4 := shiftCol49 tc m3
        let a4 := match pred m4 with | true => (k0, Aut2.mk false sr tr sc tc, m4) :: a3 | false => a3
        let m5 := transpose49 m4
        match pred m5 with | true => (k0, Aut2.mk true sr tr sc tc, m5) :: a4 | false => a4) a2 :=
    fun sr tr sc m3 a2 ha2 => mem_foldFin7_mono (fun tc l hl => hstep _ _ _ (hstep _ _ _ hl)) ha2
  have hsr : ∀ sr (a0 : List _), y ∈ a0 →
      y ∈ foldFin7 (fun tr a1 =>
        let m1 := match sr with | true => flipRow49 (rep k0) | false => rep k0
        let m2 := shiftRow49 tr m1
        let goSc (sc : Bool) (a2 : List _) :=
          let m3 := match sc with | true => flipCol49 m2 | false => m2
          foldFin7 (fun tc a3 =>
            let m4 := shiftCol49 tc m3
            let a4 := match pred m4 with | true => (k0, Aut2.mk false sr tr sc tc, m4) :: a3 | false => a3
            let m5 := transpose49 m4
            match pred m5 with | true => (k0, Aut2.mk true sr tr sc tc, m5) :: a4 | false => a4) a2
        goSc true (goSc false a1)) a0 :=
    fun sr a0 ha0 => mem_foldFin7_mono (fun tr l hl => htc sr tr true _ _ (htc sr tr false _ _ hl)) ha0
  unfold collectAut2; simp only [seqN_eq]
  cases half
  · exact hsr true _ (hsr false acc hy)
  · exact hsr false acc hy

private lemma mem_collectAut2 {k0 : Fin 3} {half : Bool} {pred : Nat → Bool}
    (g : Aut2) (hsr : half = false ∨ g.sr = false)
    (hpred : pred (g.applyMask (rep k0)) = true) (acc : List (Fin 3 × Aut2 × Nat)) :
    (k0, g, g.applyMask (rep k0)) ∈ collectAut2 k0 half pred acc := by
  rcases g with ⟨sw, sr, tr, sc, tc⟩
  have hstep : ∀ (y a : Fin 3 × Aut2 × Nat) (b : Bool) (l : List _),
      y ∈ l → y ∈ (match b with | true => a :: l | false => l) := by
    intro y a b l hl; cases b
    · exact hl
    · exact List.mem_cons_of_mem a hl
  have htc_mono : ∀ (y : Fin 3 × Aut2 × Nat) sr' tr' sc' (x3 : Nat) (a2 : List _), y ∈ a2 →
      y ∈ foldFin7 (fun tc' a3 =>
        let x4 := shiftCol49 tc' x3
        let a4 := match pred x4 with | true => (k0, Aut2.mk false sr' tr' sc' tc', x4) :: a3 | false => a3
        let x5 := transpose49 x4
        match pred x5 with | true => (k0, Aut2.mk true sr' tr' sc' tc', x5) :: a4 | false => a4) a2 :=
    fun y sr' tr' sc' x3 a2 ha2 => mem_foldFin7_mono (fun tc' l hl => hstep y _ _ _ (hstep y _ _ _ hl)) ha2
  have hsr_mono : ∀ (y : Fin 3 × Aut2 × Nat) sr' (a0 : List _), y ∈ a0 →
      y ∈ foldFin7 (fun tr' a1 =>
        let x1 := match sr' with | true => flipRow49 (rep k0) | false => rep k0
        let x2 := shiftRow49 tr' x1
        let goSc (sc' : Bool) (a2 : List _) :=
          let x3 := match sc' with | true => flipCol49 x2 | false => x2
          foldFin7 (fun tc' a3 =>
            let x4 := shiftCol49 tc' x3
            let a4 := match pred x4 with | true => (k0, Aut2.mk false sr' tr' sc' tc', x4) :: a3 | false => a3
            let x5 := transpose49 x4
            match pred x5 with | true => (k0, Aut2.mk true sr' tr' sc' tc', x5) :: a4 | false => a4) a2
        goSc true (goSc false a1)) a0 :=
    fun y sr' a0 ha0 => mem_foldFin7_mono (fun tr' l hl => htc_mono y sr' tr' true _ _ (htc_mono y sr' tr' false _ _ hl)) ha0
  have hhit_tc : ∀ (sr1 sc1 sw1 : Bool) (tr1 tc1 : Fin 7) (x3 : Nat) (a2 : List _),
      pred (match sw1 with | true => transpose49 (shiftCol49 tc1 x3) | false => shiftCol49 tc1 x3) = true →
      (k0, Aut2.mk sw1 sr1 tr1 sc1 tc1,
        match sw1 with | true => transpose49 (shiftCol49 tc1 x3) | false => shiftCol49 tc1 x3) ∈
      foldFin7 (fun tc' a3 =>
        let z4 := shiftCol49 tc' x3
        let a4 := match pred z4 with | true => (k0, Aut2.mk false sr1 tr1 sc1 tc', z4) :: a3 | false => a3
        let z5 := transpose49 z4
        match pred z5 with | true => (k0, Aut2.mk true sr1 tr1 sc1 tc', z5) :: a4 | false => a4) a2 := by
    intro sr1 sc1 sw1 tr1 tc1 x3 a2 hp
    refine mem_foldFin7 (fun tc' l' hl' => hstep _ _ _ _ (hstep _ _ _ _ hl')) tc1 (fun l' => ?_) a2
    cases sw1
    · dsimp only at hp ⊢; rw [hp]; cases pred (transpose49 (shiftCol49 tc1 x3)) <;> simp
    · dsimp only at hp ⊢; rw [hp]; exact List.mem_cons_self ..
  have hhit_sr : ∀ (sr1 sc1 sw1 : Bool) (tr1 tc1 : Fin 7) (a0 : List _),
      let x1 := match sr1 with | true => flipRow49 (rep k0) | false => rep k0
      let x2 := shiftRow49 tr1 x1
      let x3 := match sc1 with | true => flipCol49 x2 | false => x2
      let x4 := shiftCol49 tc1 x3
      let m := match sw1 with | true => transpose49 x4 | false => x4
      pred m = true →
      (k0, Aut2.mk sw1 sr1 tr1 sc1 tc1, m) ∈ foldFin7 (fun tr' a1 =>
        let z1 := match sr1 with | true => flipRow49 (rep k0) | false => rep k0
        let z2 := shiftRow49 tr' z1
        let goSc (sc' : Bool) (a2 : List _) :=
          let z3 := match sc' with | true => flipCol49 z2 | false => z2
          foldFin7 (fun tc' a3 =>
            let z4 := shiftCol49 tc' z3
            let a4 := match pred z4 with | true => (k0, Aut2.mk false sr1 tr' sc' tc', z4) :: a3 | false => a3
            let z5 := transpose49 z4
            match pred z5 with | true => (k0, Aut2.mk true sr1 tr' sc' tc', z5) :: a4 | false => a4) a2
        goSc true (goSc false a1)) a0 := by
    intro sr1 sc1 sw1 tr1 tc1 a0
    dsimp only
    intro hp
    refine mem_foldFin7 (fun tr' l hl => htc_mono _ sr1 tr' true _ _ (htc_mono _ sr1 tr' false _ _ hl)) tr1 (fun l => ?_) a0
    cases sc1
    · exact htc_mono _ sr1 tr1 true _ _ (hhit_tc sr1 false sw1 tr1 tc1 _ l hp)
    · exact hhit_tc sr1 true sw1 tr1 tc1 _ _ hp
  unfold Aut2.applyMask at hpred ⊢
  unfold collectAut2
  simp only [seqN_eq] at hpred ⊢
  cases half
  · cases sr
    · exact hsr_mono _ true _ (hhit_sr false sc sw tr tc acc hpred)
    · exact hhit_sr true sc sw tr tc _ hpred
  · cases sr
    · exact hhit_sr false sc sw tr tc acc hpred
    · rcases hsr with hbad | hbad <;> cases hbad

private lemma rep2_stab_flip (g : Aut2) (hsr : g.sr = true) :
    ∃ g' : Aut2, g'.sr = false ∧ g'.applyMask (rep 2) = g.applyMask (rep 2) := by
  rcases g with ⟨sw, sr, tr, sc, tc⟩
  dsimp only at hsr; subst hsr
  let tr' := add7 (neg7 4) tr
  let tc' := if sc then add7 (neg7 2) tc else add7 2 tc
  refine ⟨⟨sw, false, tr', !sc, tc'⟩, rfl, ?_⟩
  have hinner : (Aut2.mk false true 4 true 2).applyMask (rep 2) = rep 2 := by rfl
  have hcomp : ∀ r c : Fin 7,
      (Aut2.mk sw false tr' (!sc) tc').applyFin (r, c) =
        (Aut2.mk sw true tr sc tc).applyFin ((Aut2.mk false true 4 true 2).applyFin (r, c)) := by
    intro r c
    have hr : add7 r tr' = add7 (neg7 (add7 (neg7 r) 4)) tr := (d7_comp true true tr 4 r).symm
    have hc : add7 (if !sc then neg7 c else c) tc' =
        add7 (if sc then neg7 (add7 (neg7 c) 2) else add7 (neg7 c) 2) tc := by
      have := (d7_comp sc true tc 2 c).symm
      cases sc <;> simpa [tc', Bool.xor] using this
    cases sw <;> simp only [Aut2.applyFin, Bool.false_eq_true, ↓reduceIte, hr, hc]
  apply ext49 (Aut2.applyMask_lt _ (rep_lt 2)) (Aut2.applyMask_lt _ (rep_lt 2))
  intro r c
  let g1 := Aut2.mk sw false tr' (!sc) tc'
  let p := g1.inv.applyFin (r, c)
  have h1 := Aut2.get_applyMask g1 (rep 2) p.1 p.2
  rw [Prod.mk.eta, Aut2.applyFin_inv] at h1
  rw [h1, ← hinner]
  have hp := hcomp p.1 p.2
  rw [Prod.mk.eta, Aut2.applyFin_inv] at hp
  have h2 := Aut2.get_applyMask (Aut2.mk sw true tr sc tc)
    ((Aut2.mk false true 4 true 2).applyMask (rep 2))
    ((Aut2.mk false true 4 true 2).applyFin p).1
    ((Aut2.mk false true 4 true 2).applyFin p).2
  rw [Prod.mk.eta, ← hp] at h2
  rw [h2, Aut2.get_applyMask, hinner]

private def nearK (k : Fin 3) (m : Nat) : List (Fin 3 × Aut2 × Nat) :=
  let pred (B : Nat) : Bool := Nat.ble m (pop49 (Nat.land B (rep k)))
  collectAut2 2 true pred (collectAut2 1 false pred (collectAut2 0 false pred []))

private lemma mem_nearK {k : Fin 3} {m : Nat} {k0 : Fin 3} {g : Aut2}
    (hsr : k0 ≠ 2 ∨ g.sr = false) (hpop : m ≤ pop49 ((g.applyMask (rep k0)) &&& (rep k))) :
    (k0, g, g.applyMask (rep k0)) ∈ nearK k m := by
  have hpred : Nat.ble m (pop49 ((g.applyMask (rep k0)) &&& (rep k))) = true := Nat.ble_eq.mpr hpop
  unfold nearK
  match k0, hsr, hpred with
  | ⟨0, _⟩, _, hp => exact mem_collectAut2_mono (mem_collectAut2_mono (mem_collectAut2 g (Or.inl rfl) hp []))
  | ⟨1, _⟩, _, hp => exact mem_collectAut2_mono (mem_collectAut2 g (Or.inl rfl) hp _)
  | ⟨2, _⟩, hsr, hp => exact mem_collectAut2 g (Or.inr (hsr.resolve_left (fun h => h rfl))) hp _

private lemma alpha_c7_le_three {S : Finset (ZMod 7)} (hS : C7.IsIndepSet (S : Set (ZMod 7))) :
    S.card ≤ 3 := by
  have hsum : 2 * S.card ≤ 7 := by
    have hsplit : ∀ i : ZMod 7,
        (if i ∈ S then 1 else 0) + (if i + 1 ∈ S then 1 else 0) ≤ 1 := by
      intro i
      by_cases h1 : i ∈ S <;> by_cases h2 : i + 1 ∈ S
      · exfalso; exact hS h1 h2 (c7_adj_add_one i).ne (c7_adj_add_one i)
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
    have hcard : S.card = ∑ i : ZMod 7, if i ∈ S then 1 else 0 := by simp
    have hshift : (∑ i : ZMod 7, if i + 1 ∈ S then 1 else 0) =
        ∑ i : ZMod 7, if i ∈ S then 1 else 0 :=
      Equiv.sum_comp (Equiv.addRight (1 : ZMod 7)) (fun i => if i ∈ S then 1 else 0)
    calc 2 * S.card
        = (∑ i : ZMod 7, if i ∈ S then 1 else 0) + (∑ i : ZMod 7, if i + 1 ∈ S then 1 else 0) := by
          rw [hshift, ← hcard]; omega
      _ = ∑ i : ZMod 7, ((if i ∈ S then 1 else 0) + (if i + 1 ∈ S then 1 else 0)) := by
          rw [Finset.sum_add_distrib]
      _ ≤ ∑ _i : ZMod 7, 1 := Finset.sum_le_sum fun i _ => hsplit i
      _ = 7 := by decide
  omega

private def rowNbr7 (x : Nat) : Nat :=
  x ||| ((((x <<< 1) &&& 127) ||| (x >>> 6)) ||| ((x >>> 1) ||| ((x &&& 1) <<< 6)))

private lemma rowNbr7_testBit {x : Nat} (hx : x < 128) (c : Fin 7) :
    (rowNbr7 x).testBit c.val = true ↔
      x.testBit (prev7 c).val = true ∨ x.testBit c.val = true ∨ x.testBit (next7 c).val = true := by
  have hall : ∀ (y : Fin 128) (col : Fin 7),
      (rowNbr7 y.val).testBit col.val =
        (y.val.testBit (prev7 col).val || y.val.testBit col.val || y.val.testBit (next7 col).val) := by
    decide
  rw [hall ⟨x, hx⟩ c, Bool.or_eq_true, Bool.or_eq_true, or_assoc]

private lemma row_indep_adj {B : Finset (ZMod 7 × ZMod 7)}
    (hB : (C7 ⊠ C7).IsIndepSet (B : Set (ZMod 7 × ZMod 7))) (r : Fin 7) :
    ((row49 (ofFinset49 B) r &&& rowNbr7 (row49 (ofFinset49 B) (next7 r))) == 0) = true ∧
    pop7 (row49 (ofFinset49 B) r) + pop7 (row49 (ofFinset49 B) (next7 r)) ≤ 3 := by
  let R (row : Fin 7) : Finset (ZMod 7) := Finset.univ.filter fun c => (toZ7 row, c) ∈ B
  have hmemR : ∀ (row c : Fin 7), (row49 (ofFinset49 B) row).testBit c.val = true ↔ toZ7 c ∈ R row := by
    intro row c
    rw [row49_testBit, get49_ofFinset]
    simp [R]
  have hcardR : ∀ row : Fin 7, pop7 (row49 (ofFinset49 B) row) = (R row).card := by
    intro row
    rw [pop7_row49_eq_sum]
    have h1 : (∑ c : Fin 7, (get49 (ofFinset49 B) row c).toNat) =
        ∑ c : Fin 7, if toZ7 c ∈ R row then 1 else 0 := by
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : toZ7 c ∈ R row
      · have hg : get49 (ofFinset49 B) row c = true := by rw [← row49_testBit]; exact (hmemR row c).mpr hc
        simp [hc, hg]
      · have hg : get49 (ofFinset49 B) row c = false :=
          Bool.eq_false_iff.mpr fun h => hc ((hmemR row c).mp (by rwa [row49_testBit]))
        simp [hc, hg]
    rw [h1]
    let e : Fin 7 ≃ ZMod 7 := Equiv.mk toZ7 ofZ7 ofZ7_toZ7 toZ7_ofZ7
    have h2 : (∑ c : Fin 7, if e c ∈ R row then 1 else 0) = ∑ z : ZMod 7, if z ∈ R row then 1 else 0 :=
      Equiv.sum_comp e (fun z => if z ∈ R row then 1 else 0)
    change (∑ c : Fin 7, if e c ∈ R row then 1 else 0) = (R row).card
    rw [h2]; simp
  have hadjr : C7.Adj (toZ7 r) (toZ7 (next7 r)) := by rw [toZ7_next7]; exact c7_adj_add_one (toZ7 r)
  have hdisjR : Disjoint (R r) (R (next7 r)) := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hc1 hc2
    have hne : (toZ7 r, c) ≠ (toZ7 (next7 r), c) := fun h => hadjr.ne (congrArg Prod.fst h)
    exact hB hc1 hc2 hne ⟨hne, Or.inr hadjr, Or.inl rfl⟩
  have hindR : C7.IsIndepSet ((R r ∪ R (next7 r) : Finset (ZMod 7)) : Set (ZMod 7)) := by
    intro x hx y hy hxy hadjc
    simp only [Finset.mem_coe, Finset.mem_union, R, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · have hne : (toZ7 r, x) ≠ (toZ7 r, y) := fun h => hxy (congrArg Prod.snd h)
      exact hB hx hy hne ⟨hne, Or.inl rfl, Or.inr hadjc⟩
    · have hne : (toZ7 r, x) ≠ (toZ7 (next7 r), y) := fun h => hadjr.ne (congrArg Prod.fst h)
      exact hB hx hy hne ⟨hne, Or.inr hadjr, Or.inr hadjc⟩
    · have hne : (toZ7 (next7 r), x) ≠ (toZ7 r, y) := fun h => hadjr.ne.symm (congrArg Prod.fst h)
      exact hB hx hy hne ⟨hne, Or.inr hadjr.symm, Or.inr hadjc⟩
    · have hne : (toZ7 (next7 r), x) ≠ (toZ7 (next7 r), y) := fun h => hxy (congrArg Prod.snd h)
      exact hB hx hy hne ⟨hne, Or.inl rfl, Or.inr hadjc⟩
  constructor
  · rw [beq_iff_eq]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hi : i < 7
    · let c : Fin 7 := ⟨i, hi⟩
      cases hc : (row49 (ofFinset49 B) r).testBit c.val
      · rfl
      · cases hn : (rowNbr7 (row49 (ofFinset49 B) (next7 r))).testBit c.val
        · rfl
        · exfalso
          have hc' : toZ7 c ∈ R r := (hmemR r c).mp hc
          rcases (rowNbr7_testBit (row49_lt _ _) c).mp hn with h | h | h
          · have h' : toZ7 (prev7 c) ∈ R (next7 r) := (hmemR (next7 r) (prev7 c)).mp h
            have hadjc : C7.Adj (toZ7 c) (toZ7 (prev7 c)) := by
              rw [toZ7_prev7]; have q := (c7_adj_add_one (toZ7 c - 1)).symm; rwa [sub_add_cancel] at q
            exact hindR (Finset.mem_coe.mpr (Finset.mem_union_left _ hc'))
              (Finset.mem_coe.mpr (Finset.mem_union_right _ h')) hadjc.ne hadjc
          · exact Finset.disjoint_left.mp hdisjR hc' ((hmemR (next7 r) c).mp h)
          · have h' : toZ7 (next7 c) ∈ R (next7 r) := (hmemR (next7 r) (next7 c)).mp h
            have hadjc : C7.Adj (toZ7 c) (toZ7 (next7 c)) := by rw [toZ7_next7]; exact c7_adj_add_one _
            exact hindR (Finset.mem_coe.mpr (Finset.mem_union_left _ hc'))
              (Finset.mem_coe.mpr (Finset.mem_union_right _ h')) hadjc.ne hadjc
    · have h0 : (row49 (ofFinset49 B) r).testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (row49_lt _ r) (pow2_mono (a := 7) (by omega)))
      rw [h0]; rfl
  · rw [hcardR, hcardR, ← Finset.card_union_of_disjoint hdisjR]
    exact alpha_c7_le_three hindR

private lemma alpha_c7_pow2_le_internal {B : Finset (ZMod 7 × ZMod 7)}
    (hB : (C7 ⊠ C7).IsIndepSet (B : Set (ZMod 7 × ZMod 7))) : B.card ≤ 10 := by
  have hpop := pop49_ofFinset B
  have h0 : pop7 (row49 (ofFinset49 B) 0) + pop7 (row49 (ofFinset49 B) 1) ≤ 3 := (row_indep_adj hB 0).2
  have h1 : pop7 (row49 (ofFinset49 B) 1) + pop7 (row49 (ofFinset49 B) 2) ≤ 3 := (row_indep_adj hB 1).2
  have h2 : pop7 (row49 (ofFinset49 B) 2) + pop7 (row49 (ofFinset49 B) 3) ≤ 3 := (row_indep_adj hB 2).2
  have h3 : pop7 (row49 (ofFinset49 B) 3) + pop7 (row49 (ofFinset49 B) 4) ≤ 3 := (row_indep_adj hB 3).2
  have h4 : pop7 (row49 (ofFinset49 B) 4) + pop7 (row49 (ofFinset49 B) 5) ≤ 3 := (row_indep_adj hB 4).2
  have h5 : pop7 (row49 (ofFinset49 B) 5) + pop7 (row49 (ofFinset49 B) 6) ≤ 3 := (row_indep_adj hB 5).2
  have h6 : pop7 (row49 (ofFinset49 B) 6) + pop7 (row49 (ofFinset49 B) 0) ≤ 3 := (row_indep_adj hB 6).2
  rw [← hpop, pop49_eq_rows]
  omega

private def indepRows1 : List Nat := [1, 2, 4, 8, 16, 32, 64]
private def indepRows2 : List Nat := [5, 9, 17, 33, 10, 18, 34, 66, 20, 36, 68, 40, 72, 80]

private def isIndepRow7 (r : Nat) : Bool :=
  (r &&& (((r <<< 1) &&& 127) ||| (r >>> 6))) == 0

private lemma row_mem_indepRows1 {row : Nat} (hlt : row < 128) (hpop : pop7 row = 1) :
    row ∈ indepRows1 := by
  have hall : ∀ x : Fin 128, pop7 x.val = 1 → x.val ∈ indepRows1 := by decide
  exact hall ⟨row, hlt⟩ hpop

private lemma row_mem_indepRows2 {row : Nat} (hlt : row < 128) (hpop : pop7 row = 2)
    (hind : ∀ c : Fin 7, row.testBit c.val = true → row.testBit (next7 c).val = false) :
    row ∈ indepRows2 := by
  have his : isIndepRow7 row = true := by
    unfold isIndepRow7
    rw [beq_iff_eq]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hi : i < 7
    · let c : Fin 7 := ⟨i, hi⟩
      change (row.testBit c.val && ((((row <<< 1) &&& 127) ||| (row >>> 6)).testBit c.val)) = false
      cases hc : row.testBit c.val
      · rfl
      · rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Bool.true_and]
        have hprev : row.testBit (prev7 c).val = false := by
          cases hp : row.testBit (prev7 c).val
          · rfl
          · have hn : next7 (prev7 c) = c := (by decide : ∀ x : Fin 7, next7 (prev7 x) = x) c
            have hcontra := hind (prev7 c) hp
            rw [hn, hc] at hcontra; exact absurd hcontra (by decide)
        have hstep : ∀ x : Fin 7, row.testBit (prev7 x).val = false →
            (((decide (x.val ≥ 1) && row.testBit (x.val - 1)) && (127 : Nat).testBit x.val) ||
              row.testBit (6 + x.val)) = false := by
          intro ⟨xv, hxv⟩ hp
          have hhi : ∀ k : Nat, 7 ≤ k → row.testBit k = false :=
            fun k hk => Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (pow2_mono (a := 7) hk))
          have hxv' : xv = 0 ∨ xv = 1 ∨ xv = 2 ∨ xv = 3 ∨ xv = 4 ∨ xv = 5 ∨ xv = 6 := by omega
          rcases hxv' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hp
          · dsimp only; rw [hhi 7 (by decide), Bool.or_false]; change row.testBit 0 = false at hp; simp only [show 1 - 1 = 0 by rfl, hp, Bool.and_false, Bool.false_and]
          · dsimp only; rw [hhi 8 (by decide), Bool.or_false]; change row.testBit 1 = false at hp; simp only [show 2 - 1 = 1 by rfl, hp, Bool.and_false, Bool.false_and]
          · dsimp only; rw [hhi 9 (by decide), Bool.or_false]; change row.testBit 2 = false at hp; simp only [show 3 - 1 = 2 by rfl, hp, Bool.and_false, Bool.false_and]
          · dsimp only; rw [hhi 10 (by decide), Bool.or_false]; change row.testBit 3 = false at hp; simp only [show 4 - 1 = 3 by rfl, hp, Bool.and_false, Bool.false_and]
          · dsimp only; rw [hhi 11 (by decide), Bool.or_false]; change row.testBit 4 = false at hp; simp only [show 5 - 1 = 4 by rfl, hp, Bool.and_false, Bool.false_and]
          · dsimp only; rw [hhi 12 (by decide), Bool.or_false]; change row.testBit 5 = false at hp; simp only [show 6 - 1 = 5 by rfl, hp, Bool.and_false, Bool.false_and]
        exact hstep c hprev
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (pow2_mono (a := 7) (by omega)))]; rfl
  have hall : ∀ x : Fin 128, pop7 x.val = 2 → isIndepRow7 x.val = true → x.val ∈ indepRows2 := by decide
  exact hall ⟨row, hlt⟩ hpop his

private def packRows (r0 r1 r2 r3 r4 r5 r6 : Nat) : Nat :=
  r0 ||| (r1 <<< 7) ||| (r2 <<< 14) ||| (r3 <<< 21) ||| (r4 <<< 28) ||| (r5 <<< 35) ||| (r6 <<< 42)

private lemma packRows_eq {m : Nat} (hm : m < 2 ^ 49) :
    packRows (row49 m 0) (row49 m 1) (row49 m 2) (row49 m 3) (row49 m 4) (row49 m 5) (row49 m 6) = m := by
  have hlt : packRows (row49 m 0) (row49 m 1) (row49 m 2) (row49 m 3) (row49 m 4) (row49 m 5) (row49 m 6) < 2 ^ 49 := by
    have hsh : ∀ (r : Fin 7) (k : Nat), k ≤ 42 → row49 m r <<< k < 2 ^ 49 := fun r k hk => by
      rw [Nat.shiftLeft_eq]
      calc row49 m r * 2 ^ k < 128 * 2 ^ k := Nat.mul_lt_mul_of_pos_right (row49_lt m r) (by positivity)
        _ ≤ 128 * 2 ^ 42 := Nat.mul_le_mul_left 128 (pow2_mono hk)
        _ = 2 ^ 49 := by decide
    have h0 : row49 m 0 < 2 ^ 49 := lt_trans (row49_lt m 0) (by decide)
    unfold packRows
    exact or_lt49 (or_lt49 (or_lt49 (or_lt49 (or_lt49 (or_lt49 h0 (hsh 1 7 (by decide)))
      (hsh 2 14 (by decide))) (hsh 3 21 (by decide))) (hsh 4 28 (by decide)))
      (hsh 5 35 (by decide))) (hsh 6 42 (by decide))
  apply ext49 hlt hm
  intro r c
  have hhi : ∀ (x : Fin 7) (i : Nat), 7 ≤ i → (row49 m x).testBit i = false :=
    fun x i hi => Nat.testBit_lt_two_pow (lt_of_lt_of_le (row49_lt m x) (pow2_mono (a := 7) hi))
  rw [← row49_testBit m r c]
  unfold get49 packRows
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have hc := c.isLt
  rcases r with ⟨rv, hrv⟩
  have hrv' : rv = 0 ∨ rv = 1 ∨ rv = 2 ∨ rv = 3 ∨ rv = 4 ∨ rv = 5 ∨ rv = 6 := by omega
  rcases hrv' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · dsimp only; simp only [Nat.zero_mul, Nat.zero_add,
      show ¬(c.val ≥ 7) by omega, show ¬(c.val ≥ 14) by omega, show ¬(c.val ≥ 21) by omega,
      show ¬(c.val ≥ 28) by omega, show ¬(c.val ≥ 35) by omega, show ¬(c.val ≥ 42) by omega,
      decide_false, Bool.false_and, Bool.or_false]; rfl
  · dsimp only; simp only [Nat.one_mul, hhi 0 (7 + c.val) (by omega),
      show 7 + c.val ≥ 7 by omega, show ¬(7 + c.val ≥ 14) by omega, show ¬(7 + c.val ≥ 21) by omega,
      show ¬(7 + c.val ≥ 28) by omega, show ¬(7 + c.val ≥ 35) by omega, show ¬(7 + c.val ≥ 42) by omega,
      decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false, Nat.add_sub_cancel_left]; rfl
  · dsimp only; simp only [show (2 : Nat) * 7 = 14 by decide, hhi 0 (14 + c.val) (by omega), hhi 1 (14 + c.val - 7) (by omega),
      show 14 + c.val ≥ 7 by omega, show 14 + c.val ≥ 14 by omega, show ¬(14 + c.val ≥ 21) by omega,
      show ¬(14 + c.val ≥ 28) by omega, show ¬(14 + c.val ≥ 35) by omega, show ¬(14 + c.val ≥ 42) by omega,
      decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false, Nat.add_sub_cancel_left]; rfl
  · dsimp only; simp only [show (3 : Nat) * 7 = 21 by decide, hhi 0 (21 + c.val) (by omega), hhi 1 (21 + c.val - 7) (by omega),
      hhi 2 (21 + c.val - 14) (by omega), show 21 + c.val ≥ 7 by omega, show 21 + c.val ≥ 14 by omega,
      show 21 + c.val ≥ 21 by omega, show ¬(21 + c.val ≥ 28) by omega, show ¬(21 + c.val ≥ 35) by omega,
      show ¬(21 + c.val ≥ 42) by omega, decide_true, decide_false, Bool.true_and, Bool.false_and,
      Bool.false_or, Bool.or_false, Nat.add_sub_cancel_left]; rfl
  · dsimp only; simp only [show (4 : Nat) * 7 = 28 by decide, hhi 0 (28 + c.val) (by omega), hhi 1 (28 + c.val - 7) (by omega),
      hhi 2 (28 + c.val - 14) (by omega), hhi 3 (28 + c.val - 21) (by omega), show 28 + c.val ≥ 7 by omega,
      show 28 + c.val ≥ 14 by omega, show 28 + c.val ≥ 21 by omega, show 28 + c.val ≥ 28 by omega,
      show ¬(28 + c.val ≥ 35) by omega, show ¬(28 + c.val ≥ 42) by omega, decide_true, decide_false,
      Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false, Nat.add_sub_cancel_left]; rfl
  · dsimp only; simp only [show (5 : Nat) * 7 = 35 by decide, hhi 0 (35 + c.val) (by omega), hhi 1 (35 + c.val - 7) (by omega),
      hhi 2 (35 + c.val - 14) (by omega), hhi 3 (35 + c.val - 21) (by omega), hhi 4 (35 + c.val - 28) (by omega),
      show 35 + c.val ≥ 7 by omega, show 35 + c.val ≥ 14 by omega, show 35 + c.val ≥ 21 by omega,
      show 35 + c.val ≥ 28 by omega, show 35 + c.val ≥ 35 by omega, show ¬(35 + c.val ≥ 42) by omega,
      decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false, Nat.add_sub_cancel_left]; rfl
  · dsimp only; simp only [show (6 : Nat) * 7 = 42 by decide, hhi 0 (42 + c.val) (by omega), hhi 1 (42 + c.val - 7) (by omega),
      hhi 2 (42 + c.val - 14) (by omega), hhi 3 (42 + c.val - 21) (by omega), hhi 4 (42 + c.val - 28) (by omega),
      hhi 5 (42 + c.val - 35) (by omega), show 42 + c.val ≥ 7 by omega, show 42 + c.val ≥ 14 by omega,
      show 42 + c.val ≥ 21 by omega, show 42 + c.val ≥ 28 by omega, show 42 + c.val ≥ 35 by omega,
      show 42 + c.val ≥ 42 by omega, decide_true, Bool.true_and, Bool.false_or, Nat.add_sub_cancel_left]; rfl

private def canon10Candidates : List Nat :=
  let r0 := 1
  let r0n := rowNbr7 r0
  ([4, 8]).flatMap fun r1 =>
    let r1n := rowNbr7 r1
    (indepRows2.filter fun r2 => (r2 &&& r1n) == 0).flatMap fun r2 =>
      let r2n := rowNbr7 r2
      (indepRows1.filter fun r3 => (r3 &&& r2n) == 0).flatMap fun r3 =>
        let r3n := rowNbr7 r3
        (indepRows2.filter fun r4 => (r4 &&& r3n) == 0).flatMap fun r4 =>
          let r4n := rowNbr7 r4
          (indepRows1.filter fun r5 => (r5 &&& r4n) == 0).flatMap fun r5 =>
            let r5n := rowNbr7 r5
            (indepRows2.filter fun r6 => ((r6 &&& r5n) == 0) && ((r6 &&& r0n) == 0)).map fun r6 =>
              packRows r0 r1 r2 r3 r4 r5 r6

private def canon10Witnesses : List (Fin 3 × Aut2) := [
  __CANON_WITS__
]

private def checkAll {α β : Type} (f : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && checkAll f as bs
  | _, _ => false

private lemma checkAll_sound {α β : Type} {f : α → β → Bool}
    {as : List α} {bs : List β} (h : checkAll f as bs = true) :
    ∀ a ∈ as, ∃ b ∈ bs, f a b = true := by
  induction as generalizing bs with
  | nil => intro a ha; cases ha
  | cons a0 as ih =>
    cases bs with
    | nil => simp [checkAll] at h
    | cons b0 bs =>
      simp only [checkAll, Bool.and_eq_true] at h
      intro a ha
      rcases List.mem_cons.mp ha with rfl | hmem
      · exact ⟨b0, List.mem_cons.mpr (Or.inl rfl), h.1⟩
      · obtain ⟨b, hb, hfb⟩ := ih h.2 a hmem
        exact ⟨b, List.mem_cons.mpr (Or.inr hb), hfb⟩

private def checkAll4 {α β : Type} (f : α → β → Bool) (as : List α) (bs : List β) : Bool :=
  checkAll f (as.take 60) (bs.take 60) &&
  checkAll f ((as.drop 60).take 60) ((bs.drop 60).take 60) &&
  checkAll f ((as.drop 120).take 60) ((bs.drop 120).take 60) &&
  checkAll f (as.drop 180) (bs.drop 180)

private lemma checkAll4_sound {α β : Type} {f : α → β → Bool}
    {as : List α} {bs : List β} (h : checkAll4 f as bs = true) :
    ∀ a ∈ as, ∃ b ∈ bs, f a b = true := by
  unfold checkAll4 at h
  simp only [Bool.and_eq_true] at h
  intro a ha
  have h1 : a ∈ as.take 60 ∨ a ∈ as.drop 60 := by
    rw [← List.mem_append, List.take_append_drop]; exact ha
  rcases h1 with h1 | h1
  · obtain ⟨b, hb, hf⟩ := checkAll_sound h.1.1.1 a h1
    exact ⟨b, List.mem_of_mem_take hb, hf⟩
  · have h2 : a ∈ (as.drop 60).take 60 ∨ a ∈ as.drop 120 := by
      have : (as.drop 60).drop 60 = as.drop 120 := by rw [List.drop_drop]
      rw [← this, ← List.mem_append, List.take_append_drop]; exact h1
    rcases h2 with h2 | h2
    · obtain ⟨b, hb, hf⟩ := checkAll_sound h.1.1.2 a h2
      exact ⟨b, List.mem_of_mem_drop (List.mem_of_mem_take hb), hf⟩
    · have h3 : a ∈ (as.drop 120).take 60 ∨ a ∈ as.drop 180 := by
        have : (as.drop 120).drop 60 = as.drop 180 := by rw [List.drop_drop]
        rw [← this, ← List.mem_append, List.take_append_drop]; exact h2
      rcases h3 with h3 | h3
      · obtain ⟨b, hb, hf⟩ := checkAll_sound h.1.2 a h3
        exact ⟨b, List.mem_of_mem_drop (List.mem_of_mem_take hb), hf⟩
      · obtain ⟨b, hb, hf⟩ := checkAll_sound h.2 a h3
        exact ⟨b, List.mem_of_mem_drop hb, hf⟩

private theorem canon10_in_orbits_ok :
    checkAll (fun m (p : Fin 3 × Aut2) => (p.2.applyMask (rep p.1)) == m)
      canon10Candidates canon10Witnesses = true := by rfl

private lemma tenSet_shift_profile (p0 p1 p2 p3 p4 p5 p6 : Nat)
    (hsum : p0 + p1 + p2 + p3 + p4 + p5 + p6 = 10)
    (b0 : p0 + p1 ≤ 3) (b1 : p1 + p2 ≤ 3) (b2 : p2 + p3 ≤ 3) (b3 : p3 + p4 ≤ 3)
    (b4 : p4 + p5 ≤ 3) (b5 : p5 + p6 ≤ 3) (b6 : p6 + p0 ≤ 3) :
    (p0 = 1 ∧ p1 = 1 ∧ p2 = 2 ∧ p3 = 1 ∧ p4 = 2 ∧ p5 = 1 ∧ p6 = 2) ∨
    (p1 = 1 ∧ p2 = 1 ∧ p3 = 2 ∧ p4 = 1 ∧ p5 = 2 ∧ p6 = 1 ∧ p0 = 2) ∨
    (p2 = 1 ∧ p3 = 1 ∧ p4 = 2 ∧ p5 = 1 ∧ p6 = 2 ∧ p0 = 1 ∧ p1 = 2) ∨
    (p3 = 1 ∧ p4 = 1 ∧ p5 = 2 ∧ p6 = 1 ∧ p0 = 2 ∧ p1 = 1 ∧ p2 = 2) ∨
    (p4 = 1 ∧ p5 = 1 ∧ p6 = 2 ∧ p0 = 1 ∧ p1 = 2 ∧ p2 = 1 ∧ p3 = 2) ∨
    (p5 = 1 ∧ p6 = 1 ∧ p0 = 2 ∧ p1 = 1 ∧ p2 = 2 ∧ p3 = 1 ∧ p4 = 2) ∨
    (p6 = 1 ∧ p0 = 1 ∧ p1 = 2 ∧ p2 = 1 ∧ p3 = 2 ∧ p4 = 1 ∧ p5 = 2) := by
  have hd : (3 - (p0 + p1)) + (3 - (p1 + p2)) + (3 - (p2 + p3)) + (3 - (p3 + p4)) +
      (3 - (p4 + p5)) + (3 - (p5 + p6)) + (3 - (p6 + p0)) = 1 := by omega
  by_cases c0 : p0 + p1 = 2
  · left; omega
  by_cases c1 : p1 + p2 = 2
  · right; left; omega
  by_cases c2 : p2 + p3 = 2
  · right; right; left; omega
  by_cases c3 : p3 + p4 = 2
  · right; right; right; left; omega
  by_cases c4 : p4 + p5 = 2
  · right; right; right; right; left; omega
  by_cases c5 : p5 + p6 = 2
  · right; right; right; right; right; left; omega
  · right; right; right; right; right; right; omega

private lemma row49_shiftRow (t : Fin 7) (m : Nat) (r : Fin 7) :
    row49 (shiftRow49 t m) (add7 r t) = row49 m r := by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < 7
  · let c : Fin 7 := ⟨i, hi⟩
    change (row49 (shiftRow49 t m) (add7 r t)).testBit c.val = (row49 m r).testBit c.val
    rw [row49_testBit, row49_testBit, get49_shiftRow]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (row49_lt _ _) (pow2_mono (a := 7) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (row49_lt _ _) (pow2_mono (a := 7) (by omega)))]

private lemma pop7_row49_shiftCol (t : Fin 7) (m : Nat) (r : Fin 7) :
    pop7 (row49 (shiftCol49 t m) r) = pop7 (row49 m r) := by
  rw [pop7_row49_eq_sum, pop7_row49_eq_sum]
  let e : Fin 7 ≃ Fin 7 := Equiv.mk (fun c => add7 c t) (fun c => add7 c (neg7 t))
    (fun c => (by decide : ∀ t c : Fin 7, add7 (add7 c t) (neg7 t) = c) t c)
    (fun c => (by decide : ∀ t c : Fin 7, add7 (add7 c (neg7 t)) t = c) t c)
  rw [← Equiv.sum_comp e (fun c => (get49 (shiftCol49 t m) r c).toNat)]
  exact Finset.sum_congr rfl fun c _ => congrArg Bool.toNat (get49_shiftCol t m r c)

private lemma pop7_row49_flipCol (m : Nat) (r : Fin 7) :
    pop7 (row49 (flipCol49 m) r) = pop7 (row49 m r) := by
  rw [pop7_row49_eq_sum, pop7_row49_eq_sum]
  let e : Fin 7 ≃ Fin 7 := Equiv.mk neg7 neg7 (by decide) (by decide)
  rw [← Equiv.sum_comp e (fun c => (get49 (flipCol49 m) r c).toNat)]
  exact Finset.sum_congr rfl fun c _ => congrArg Bool.toNat (get49_flipCol m r c)

private theorem tenSet_in_three_orbits {B : Finset (ZMod 7 × ZMod 7)}
    (hB : (C7 ⊠ C7).IsIndepSet (B : Set (ZMod 7 × ZMod 7))) (hcard : B.card = 10) :
    ∃ (k : Fin 3) (g : Aut2), ofFinset49 B = g.applyMask (rep k) := by
  have hpop : pop49 (ofFinset49 B) = 10 := by rw [pop49_ofFinset, hcard]
  rw [pop49_eq_rows] at hpop
  have h0 := (row_indep_adj hB 0).2; have h1 := (row_indep_adj hB 1).2
  have h2 := (row_indep_adj hB 2).2; have h3 := (row_indep_adj hB 3).2
  have h4 := (row_indep_adj hB 4).2; have h5 := (row_indep_adj hB 5).2
  have h6 := (row_indep_adj hB 6).2
  have hprof := tenSet_shift_profile _ _ _ _ _ _ _ hpop h0 h1 h2 h3 h4 h5 h6
  have hex_shift : ∃ tr : Fin 7,
      let m1 := ofFinset49 (B.map (Aut2.mk false false tr false 0).toIso.toEquiv.toEmbedding)
      pop7 (row49 m1 0) = 1 ∧ pop7 (row49 m1 1) = 1 ∧ pop7 (row49 m1 2) = 2 ∧
      pop7 (row49 m1 3) = 1 ∧ pop7 (row49 m1 4) = 2 ∧ pop7 (row49 m1 5) = 1 ∧ pop7 (row49 m1 6) = 2 := by
    have hshift_eq : ∀ tr : Fin 7,
        ofFinset49 (B.map (Aut2.mk false false tr false 0).toIso.toEquiv.toEmbedding) =
          shiftRow49 tr (ofFinset49 B) := by
      intro tr; rw [← Aut2.applyMask_ofFinset]; unfold Aut2.applyMask; simp only [seqN_eq]; rfl
    have hrow_sh : ∀ (tr r : Fin 7),
        row49 (shiftRow49 tr (ofFinset49 B)) r = row49 (ofFinset49 B) (add7 r (neg7 tr)) := by
      intro tr r
      have hback : add7 (add7 r (neg7 tr)) tr = r := (by decide : ∀ t r : Fin 7, add7 (add7 r (neg7 t)) t = r) tr r
      conv_lhs => rw [← hback]
      exact row49_shiftRow tr (ofFinset49 B) (add7 r (neg7 tr))
    rcases hprof with hp | hp | hp | hp | hp | hp | hp
    · exact ⟨0, by dsimp only; rw [hshift_eq 0]; simp only [hrow_sh]; exact hp⟩
    · exact ⟨6, by dsimp only; rw [hshift_eq 6]; simp only [hrow_sh]; exact hp⟩
    · exact ⟨5, by dsimp only; rw [hshift_eq 5]; simp only [hrow_sh]; exact hp⟩
    · exact ⟨4, by dsimp only; rw [hshift_eq 4]; simp only [hrow_sh]; exact hp⟩
    · exact ⟨3, by dsimp only; rw [hshift_eq 3]; simp only [hrow_sh]; exact hp⟩
    · exact ⟨2, by dsimp only; rw [hshift_eq 2]; simp only [hrow_sh]; exact hp⟩
    · exact ⟨1, by dsimp only; rw [hshift_eq 1]; simp only [hrow_sh]; exact hp⟩
  obtain ⟨tr, htr⟩ := hex_shift
  let gR : Aut2 := ⟨false, false, tr, false, 0⟩
  let B1 := B.map gR.toIso.toEquiv.toEmbedding
  have hB1 : (C7 ⊠ C7).IsIndepSet (B1 : Set (ZMod 7 × ZMod 7)) := isIndepSet_map_iso' gR.toIso hB
  have hr0_mem := row_mem_indepRows1 (row49_lt _ 0) htr.1
  have hex_tc : ∃ tc : Fin 7, row49 (shiftCol49 tc (ofFinset49 B1)) 0 = 1 := by
    have hshift1 : ∀ (m : Nat) (c0 tc : Fin 7), row49 m 0 = 2 ^ c0.val → add7 c0 tc = 0 →
        row49 (shiftCol49 tc m) 0 = 1 := by
      intro m c0 tc hr0 hadd
      apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < 7
      · let c : Fin 7 := ⟨i, hi⟩
        have hback : add7 (add7 c (neg7 tc)) tc = c := (by decide : ∀ t c : Fin 7, add7 (add7 c (neg7 t)) t = c) tc c
        change (row49 (shiftCol49 tc m) 0).testBit c.val = (1 : Nat).testBit c.val
        rw [row49_testBit]; conv_lhs => rw [← hback]
        rw [get49_shiftCol, ← row49_testBit, hr0, Nat.testBit_two_pow]
        have h1bit : (1 : Nat).testBit c.val = decide (0 = c.val) := by
          simpa using (Nat.testBit_two_pow (n := 0) (m := c.val))
        rw [h1bit]
        have hiff : c0.val = (add7 c (neg7 tc)).val ↔ 0 = c.val := by
          have h1 : ∀ a b t : Fin 7, add7 a t = 0 → (a = add7 b (neg7 t) ↔ (0 : Fin 7) = b) := by decide
          have := h1 c0 c tc hadd
          constructor
          · intro he; exact congrArg Fin.val (this.mp (Fin.ext he))
          · intro he; exact congrArg Fin.val (this.mpr (Fin.ext he))
        simp only [hiff]
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (row49_lt _ 0) (pow2_mono (a := 7) (by omega)))]
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (show (1 : Nat) < 2 ^ 7 by decide) (pow2_mono (a := 7) (by omega)))]
    simp only [indepRows1, List.mem_cons, List.not_mem_nil, or_false] at hr0_mem
    rcases hr0_mem with h | h | h | h | h | h | h
    · exact ⟨0, hshift1 _ 0 0 h rfl⟩
    · exact ⟨6, hshift1 _ 1 6 h rfl⟩
    · exact ⟨5, hshift1 _ 2 5 h rfl⟩
    · exact ⟨4, hshift1 _ 3 4 h rfl⟩
    · exact ⟨3, hshift1 _ 4 3 h rfl⟩
    · exact ⟨2, hshift1 _ 5 2 h rfl⟩
    · exact ⟨1, hshift1 _ 6 1 h rfl⟩
  obtain ⟨tc, htc⟩ := hex_tc
  let gC : Aut2 := ⟨false, false, 0, false, tc⟩
  let B2 := B1.map gC.toIso.toEquiv.toEmbedding
  have hB2 : (C7 ⊠ C7).IsIndepSet (B2 : Set (ZMod 7 × ZMod 7)) := isIndepSet_map_iso' gC.toIso hB1
  have hm2_eq : ofFinset49 B2 = shiftCol49 tc (ofFinset49 B1) := by
    rw [← Aut2.applyMask_ofFinset]; unfold Aut2.applyMask; simp only [seqN_eq]; rfl
  have hr2_pops : row49 (ofFinset49 B2) 0 = 1 ∧
      pop7 (row49 (ofFinset49 B2) 1) = 1 ∧ pop7 (row49 (ofFinset49 B2) 2) = 2 ∧
      pop7 (row49 (ofFinset49 B2) 3) = 1 ∧ pop7 (row49 (ofFinset49 B2) 4) = 2 ∧
      pop7 (row49 (ofFinset49 B2) 5) = 1 ∧ pop7 (row49 (ofFinset49 B2) 6) = 2 := by
    rw [hm2_eq]
    exact ⟨htc, by rw [pop7_row49_shiftCol]; exact htr.2.1, by rw [pop7_row49_shiftCol]; exact htr.2.2.1,
      by rw [pop7_row49_shiftCol]; exact htr.2.2.2.1, by rw [pop7_row49_shiftCol]; exact htr.2.2.2.2.1,
      by rw [pop7_row49_shiftCol]; exact htr.2.2.2.2.2.1, by rw [pop7_row49_shiftCol]; exact htr.2.2.2.2.2.2⟩
  have hr1_disj0 : ((1 &&& rowNbr7 (row49 (ofFinset49 B2) 1)) == 0) = true := by
    have h := (row_indep_adj hB2 0).1
    change ((row49 (ofFinset49 B2) 0 &&& rowNbr7 (row49 (ofFinset49 B2) 1)) == 0) = true at h
    rwa [hr2_pops.1] at h
  have hr1_mem := row_mem_indepRows1 (row49_lt _ 1) hr2_pops.2.1
  have hflip_pow2 : ∀ (m : Nat) (r c0 : Fin 7), row49 m r = 2 ^ c0.val →
      row49 (flipCol49 m) r = 2 ^ (neg7 c0).val := by
    intro m r c0 hv
    apply Nat.eq_of_testBit_eq; intro i
    by_cases hi : i < 7
    · let c : Fin 7 := ⟨i, hi⟩
      have hnn : neg7 (neg7 c) = c := (by decide : ∀ x : Fin 7, neg7 (neg7 x) = x) c
      change (row49 (flipCol49 m) r).testBit c.val = (2 ^ (neg7 c0).val).testBit c.val
      rw [row49_testBit]; conv_lhs => rw [← hnn]
      rw [get49_flipCol, ← row49_testBit, hv, Nat.testBit_two_pow, Nat.testBit_two_pow]
      have hiff : c0.val = (neg7 c).val ↔ (neg7 c0).val = c.val := by
        have h1 : ∀ a b : Fin 7, a = neg7 b ↔ neg7 a = b := by decide
        have := h1 c0 c
        constructor
        · intro he; exact congrArg Fin.val (this.mp (Fin.ext he))
        · intro he; exact congrArg Fin.val (this.mpr (Fin.ext he))
      simp only [hiff]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (row49_lt _ r) (pow2_mono (a := 7) (by omega)))]
      have hlt : 2 ^ (neg7 c0).val < 2 ^ 7 := Nat.pow_lt_pow_right (by decide) (neg7 c0).isLt
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (pow2_mono (a := 7) (by omega)))]
  have hex_sc : ∃ sc : Bool,
      let r1' := row49 (if sc then flipCol49 (ofFinset49 B2) else ofFinset49 B2) 1
      r1' = 4 ∨ r1' = 8 := by
    simp only [indepRows1, List.mem_cons, List.not_mem_nil, or_false] at hr1_mem
    rcases hr1_mem with h | h | h | h | h | h | h
    · rw [h] at hr1_disj0; exact absurd hr1_disj0 (by decide)
    · rw [h] at hr1_disj0; exact absurd hr1_disj0 (by decide)
    · exact ⟨false, Or.inl h⟩
    · exact ⟨false, Or.inr h⟩
    · exact ⟨true, Or.inr (hflip_pow2 _ 1 4 h)⟩
    · exact ⟨true, Or.inl (hflip_pow2 _ 1 5 h)⟩
    · rw [h] at hr1_disj0; exact absurd hr1_disj0 (by decide)
  obtain ⟨sc, hsc⟩ := hex_sc
  let gF : Aut2 := ⟨false, false, 0, sc, 0⟩
  let B3 := B2.map gF.toIso.toEquiv.toEmbedding
  have hB3 : (C7 ⊠ C7).IsIndepSet (B3 : Set (ZMod 7 × ZMod 7)) := isIndepSet_map_iso' gF.toIso hB2
  have hm3_eq : ofFinset49 B3 = if sc then flipCol49 (ofFinset49 B2) else ofFinset49 B2 := by
    rw [← Aut2.applyMask_ofFinset]; unfold Aut2.applyMask; simp only [seqN_eq]; cases sc <;> rfl
  have hcand : ofFinset49 B3 ∈ canon10Candidates := by
    have hdisj_symm : ∀ {a b : Nat}, a < 128 → b < 128 →
        ((a &&& rowNbr7 b) == 0) = true → ((b &&& rowNbr7 a) == 0) = true := by
      intro a b ha hb h
      rw [beq_iff_eq] at h ⊢
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_and, Nat.zero_testBit]
      by_cases hi : i < 7
      · let c : Fin 7 := ⟨i, hi⟩
        cases hbc : b.testBit c.val
        · rfl
        · cases hna : (rowNbr7 a).testBit c.val
          · rfl
          · exfalso
            have hab0 : ∀ k : Fin 7, (a.testBit k.val && (rowNbr7 b).testBit k.val) = false := fun k => by
              have := congrArg (fun x => x.testBit k.val) h
              simpa [Nat.testBit_and] using this
            rcases (rowNbr7_testBit ha c).mp hna with h1 | h1 | h1
            · have h2 := hab0 (prev7 c)
              have hbn : (rowNbr7 b).testBit (prev7 c).val = true :=
                (rowNbr7_testBit hb (prev7 c)).mpr (Or.inr (Or.inr (by
                  have : next7 (prev7 c) = c := (by decide : ∀ x : Fin 7, next7 (prev7 x) = x) c
                  rwa [this])))
              rw [h1, hbn] at h2; exact absurd h2 (by decide)
            · have h2 := hab0 c
              have hbn : (rowNbr7 b).testBit c.val = true :=
                (rowNbr7_testBit hb c).mpr (Or.inr (Or.inl hbc))
              rw [h1, hbn] at h2; exact absurd h2 (by decide)
            · have h2 := hab0 (next7 c)
              have hbn : (rowNbr7 b).testBit (next7 c).val = true :=
                (rowNbr7_testBit hb (next7 c)).mpr (Or.inl (by
                  have : prev7 (next7 c) = c := (by decide : ∀ x : Fin 7, prev7 (next7 x) = x) c
                  rwa [this]))
              rw [h1, hbn] at h2; exact absurd h2 (by decide)
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (pow2_mono (a := 7) (by omega)))]; rfl
    have d12 := hdisj_symm (row49_lt _ 1) (row49_lt _ 2) (row_indep_adj hB3 1).1
    have d23 := hdisj_symm (row49_lt _ 2) (row49_lt _ 3) (row_indep_adj hB3 2).1
    have d34 := hdisj_symm (row49_lt _ 3) (row49_lt _ 4) (row_indep_adj hB3 3).1
    have d45 := hdisj_symm (row49_lt _ 4) (row49_lt _ 5) (row_indep_adj hB3 4).1
    have d56 := hdisj_symm (row49_lt _ 5) (row49_lt _ 6) (row_indep_adj hB3 5).1
    have d60 : ((row49 (ofFinset49 B3) 6 &&& rowNbr7 (row49 (ofFinset49 B3) 0)) == 0) = true :=
      (row_indep_adj hB3 6).1
    have h0eq : row49 (ofFinset49 B3) 0 = 1 := by
      rw [hm3_eq]; cases sc
      · exact hr2_pops.1
      · exact hflip_pow2 _ 0 0 hr2_pops.1
    have h1eq : row49 (ofFinset49 B3) 1 = 4 ∨ row49 (ofFinset49 B3) 1 = 8 := by
      rw [hm3_eq]; exact hsc
    have hrow_ind : ∀ r : Fin 7, ∀ c : Fin 7,
        (row49 (ofFinset49 B3) r).testBit c.val = true →
        (row49 (ofFinset49 B3) r).testBit (next7 c).val = false := by
      intro r c hc
      cases hn : (row49 (ofFinset49 B3) r).testBit (next7 c).val
      · rfl
      · exfalso
        rw [row49_testBit, get49_ofFinset] at hc hn
        have hadjc : C7.Adj (toZ7 c) (toZ7 (next7 c)) := by rw [toZ7_next7]; exact c7_adj_add_one _
        have hne : (toZ7 r, toZ7 c) ≠ (toZ7 r, toZ7 (next7 c)) := fun h => hadjc.ne (congrArg Prod.snd h)
        exact hB3 hc hn hne ⟨hne, Or.inl rfl, Or.inr hadjc⟩
    have hpop3 : ∀ r : Fin 7, pop7 (row49 (ofFinset49 B3) r) = pop7 (row49 (ofFinset49 B2) r) := by
      intro r; rw [hm3_eq]; cases sc
      · rfl
      · exact pop7_row49_flipCol _ r
    have m2 : row49 (ofFinset49 B3) 2 ∈ indepRows2 :=
      row_mem_indepRows2 (row49_lt _ 2) (by rw [hpop3, hr2_pops.2.2.1]) (hrow_ind 2)
    have m3 : row49 (ofFinset49 B3) 3 ∈ indepRows1 :=
      row_mem_indepRows1 (row49_lt _ 3) (by rw [hpop3, hr2_pops.2.2.2.1])
    have m4 : row49 (ofFinset49 B3) 4 ∈ indepRows2 :=
      row_mem_indepRows2 (row49_lt _ 4) (by rw [hpop3, hr2_pops.2.2.2.2.1]) (hrow_ind 4)
    have m5 : row49 (ofFinset49 B3) 5 ∈ indepRows1 :=
      row_mem_indepRows1 (row49_lt _ 5) (by rw [hpop3, hr2_pops.2.2.2.2.2.1])
    have m6 : row49 (ofFinset49 B3) 6 ∈ indepRows2 :=
      row_mem_indepRows2 (row49_lt _ 6) (by rw [hpop3, hr2_pops.2.2.2.2.2.2]) (hrow_ind 6)
    have hpack := (packRows_eq (ofFinset49_lt B3)).symm
    rw [hpack]
    unfold canon10Candidates
    simp only [List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_cons, List.not_mem_nil,
      or_false, Bool.and_eq_true]
    exact ⟨row49 (ofFinset49 B3) 1, h1eq,
      row49 (ofFinset49 B3) 2, ⟨m2, d12⟩,
      row49 (ofFinset49 B3) 3, ⟨m3, d23⟩,
      row49 (ofFinset49 B3) 4, ⟨m4, d34⟩,
      row49 (ofFinset49 B3) 5, ⟨m5, d45⟩,
      row49 (ofFinset49 B3) 6, ⟨m6, d56, by rwa [h0eq] at d60⟩,
      by rw [h0eq]⟩
  obtain ⟨⟨k, g0⟩, _, hmatch⟩ := checkAll_sound canon10_in_orbits_ok _ hcand
  have hB3_eq : ofFinset49 B3 = g0.applyMask (rep k) := (beq_iff_eq.mp hmatch).symm
  have hcomp_mask : ∀ (a b : Aut2) (m : Nat), m < 2 ^ 49 →
      ∃ c : Aut2, a.applyMask (b.applyMask m) = c.applyMask m := by
    intro a b m hm
    rcases a with ⟨swa, sra, tra, sca, tca⟩
    rcases b with ⟨swb, srb, trb, scb, tcb⟩
    have hgen : ∃ c : Aut2, ∀ p : Fin 7 × Fin 7,
        (Aut2.mk swa sra tra sca tca).applyFin ((Aut2.mk swb srb trb scb tcb).applyFin p) = c.applyFin p := by
      cases swb <;> cases swa
      · refine ⟨⟨false, xor sra srb, add7 (if sra then neg7 trb else trb) tra,
          xor sca scb, add7 (if sca then neg7 tcb else tcb) tca⟩, fun ⟨r, c⟩ => ?_⟩
        simp only [Aut2.applyFin, Bool.false_eq_true, ↓reduceIte, d7_comp]
      · refine ⟨⟨true, xor sra srb, add7 (if sra then neg7 trb else trb) tra,
          xor sca scb, add7 (if sca then neg7 tcb else tcb) tca⟩, fun ⟨r, c⟩ => ?_⟩
        simp only [Aut2.applyFin, Bool.false_eq_true, ↓reduceIte, d7_comp]
      · refine ⟨⟨true, xor sca srb, add7 (if sca then neg7 trb else trb) tca,
          xor sra scb, add7 (if sra then neg7 tcb else tcb) tra⟩, fun ⟨r, c⟩ => ?_⟩
        simp only [Aut2.applyFin, Bool.false_eq_true, ↓reduceIte, d7_comp]
      · refine ⟨⟨false, xor sca srb, add7 (if sca then neg7 trb else trb) tca,
          xor sra scb, add7 (if sra then neg7 tcb else tcb) tra⟩, fun ⟨r, c⟩ => ?_⟩
        simp only [Aut2.applyFin, Bool.false_eq_true, ↓reduceIte, d7_comp]
    obtain ⟨c, hc⟩ := hgen
    refine ⟨c, ?_⟩
    apply ext49 (Aut2.applyMask_lt _ (Aut2.applyMask_lt _ hm)) (Aut2.applyMask_lt _ hm)
    intro r c'
    let p := c.inv.applyFin (r, c')
    have h1 := Aut2.get_applyMask c m p.1 p.2
    rw [Prod.mk.eta, c.applyFin_inv] at h1
    rw [h1]
    have h2 := hc p
    rw [c.applyFin_inv] at h2
    have h3 := Aut2.get_applyMask (Aut2.mk swa sra tra sca tca)
      ((Aut2.mk swb srb trb scb tcb).applyMask m)
      ((Aut2.mk swb srb trb scb tcb).applyFin p).1
      ((Aut2.mk swb srb trb scb tcb).applyFin p).2
    rw [Prod.mk.eta, h2] at h3
    rw [h3, Aut2.get_applyMask]
  have hpull : ofFinset49 B = gR.inv.applyMask (gC.inv.applyMask (gF.inv.applyMask (g0.applyMask (rep k)))) := by
    have h1 : ofFinset49 B3 = gF.applyMask (ofFinset49 B2) := (Aut2.applyMask_ofFinset gF B2).symm
    have h2 : ofFinset49 B2 = gC.applyMask (ofFinset49 B1) := (Aut2.applyMask_ofFinset gC B1).symm
    have h3 : ofFinset49 B1 = gR.applyMask (ofFinset49 B) := (Aut2.applyMask_ofFinset gR B).symm
    rw [← hB3_eq, h1, gF.applyMask_inv_left (ofFinset49_lt _),
        h2, gC.applyMask_inv_left (ofFinset49_lt _),
        h3, gR.applyMask_inv_left (ofFinset49_lt _)]
  obtain ⟨g1, hg1⟩ := hcomp_mask gF.inv g0 (rep k) (rep_lt k)
  obtain ⟨g2, hg2⟩ := hcomp_mask gC.inv g1 (rep k) (rep_lt k)
  obtain ⟨g3, hg3⟩ := hcomp_mask gR.inv g2 (rep k) (rep_lt k)
  refine ⟨k, g3, ?_⟩
  rw [hpull, hg1, hg2, hg3]

private theorem tenSet_canon_half {B : Finset (ZMod 7 × ZMod 7)}
    (hB : (C7 ⊠ C7).IsIndepSet (B : Set (ZMod 7 × ZMod 7))) (hcard : B.card = 10) :
    ∃ (k : Fin 3) (g : Aut2), (k ≠ 2 ∨ g.sr = false) ∧ ofFinset49 B = g.applyMask (rep k) := by
  obtain ⟨k, g, hEq⟩ := tenSet_in_three_orbits hB hcard
  revert g hEq; revert k
  refine fin3_cases ?_ ?_ ?_
  · intro g hEq; exact ⟨0, g, Or.inl (by decide), hEq⟩
  · intro g hEq; exact ⟨1, g, Or.inl (by decide), hEq⟩
  · intro g hEq
    cases hsr : g.sr
    · exact ⟨2, g, Or.inr hsr, hEq⟩
    · obtain ⟨g', hg'sr, hg'eq⟩ := rep2_stab_flip g hsr
      exact ⟨2, g', Or.inr hg'sr, by rw [hEq, ← hg'eq]⟩

/-! ## Section 4: `Tree10` & Verified `C1`/`C2` Common-Forbidden Tables (49-Bit `Nat`) -/

private inductive Tree10 where
  | tE : Tree10
  | tL : Nat → Tree10
  | tN : Tree10 → Tree10 → Tree10

private def repBits : Fin 3 → List Nat
  | ⟨0, _⟩ => [__REPBITS0__]
  | ⟨1, _⟩ => [__REPBITS1__]
  | ⟨2, _⟩ => [__REPBITS2__]

private def ptsToBits : List (Fin 7 × Fin 7) → List Nat
  | [] => []
  | (r, c) :: rest => bit49 r c :: ptsToBits rest

private lemma repBits_eq (k : Fin 3) : repBits k = ptsToBits (repPtsList k) := by
  revert k; exact fin3_cases rfl rfl rfl

open Tree10 in
private def Tree10.getAux : Tree10 → List Nat → Nat → Nat
  | tE, _, _ => 0
  | tL v, _, _ => v
  | tN l r, bit :: rest, m =>
      match Nat.beq (Nat.land m bit) 0 with
      | true => l.getAux rest m
      | false => r.getAux rest m
  | tN _ _, [], _ => 0

private lemma land_bit49_eq_zero (m : Nat) (r c : Fin 7) :
    Nat.beq (Nat.land m (bit49 r c)) 0 = !get49 m r c := by
  rw [beq_eq, land_eq]
  unfold get49
  cases h : m.testBit (r.val * 7 + c.val)
  · rw [Bool.not_false, beq_iff_eq]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    unfold bit49; rw [shl_eq, add_eq, mul_eq, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
    by_cases hi : r.val * 7 + c.val = i
    · rw [← hi, h]; rfl
    · simp [hi]
  · rw [Bool.not_true, Bool.eq_false_iff]
    intro heq
    have h0 := beq_iff_eq.mp heq
    have hb := congrArg (fun x => x.testBit (r.val * 7 + c.val)) h0
    rw [Nat.testBit_and, Nat.zero_testBit, h] at hb
    unfold bit49 at hb; rw [shl_eq, add_eq, mul_eq, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow] at hb
    simp at hb

private def countHits (B : Nat) : List (Fin 7 × Fin 7) → Nat
  | [] => 0
  | (r, c) :: rest => (get49 B r c).toNat + countHits B rest

private lemma pop49_le_add_countHits {B X sub : Nat} (hX : X < 2 ^ 49) (hXB : subset49 X B = true)
    (pts : List (Fin 7 × Fin 7))
    (hcov : ∀ p : Fin 7 × Fin 7, get49 X p.1 p.2 = true → get49 sub p.1 p.2 = true ∨ p ∈ pts) :
    pop49 X ≤ pop49 sub + countHits B pts := by
  have h1 : ∀ l : List (Fin 7 × Fin 7),
      (∑ p : Fin 7 × Fin 7, if p ∈ l then (get49 B p.1 p.2).toNat else 0) ≤ countHits B l := by
    intro l
    induction l with
    | nil => simp [countHits]
    | cons p0 rest ih =>
      simp only [countHits, List.mem_cons]
      have hsplit : (∑ p : Fin 7 × Fin 7, if p = p0 ∨ p ∈ rest then (get49 B p.1 p.2).toNat else 0) ≤
          (get49 B p0.1 p0.2).toNat + ∑ p : Fin 7 × Fin 7, if p ∈ rest then (get49 B p.1 p.2).toNat else 0 := by
        have hstep : (∑ p : Fin 7 × Fin 7, if p = p0 ∨ p ∈ rest then (get49 B p.1 p.2).toNat else 0) ≤
            ∑ p : Fin 7 × Fin 7, ((if p = p0 then (get49 B p.1 p.2).toNat else 0) +
              (if p ∈ rest then (get49 B p.1 p.2).toNat else 0)) := by
          refine Finset.sum_le_sum fun p _ => ?_
          by_cases h1 : p = p0 <;> by_cases h2 : p ∈ rest <;> simp [h1, h2]
        rw [Finset.sum_add_distrib] at hstep
        simpa using hstep
      omega
  rw [pop49_eq_sum, pop49_eq_sum, ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  have hle : (∑ p : Fin 7 × Fin 7, (get49 X p.1 p.2).toNat) ≤
      (∑ p : Fin 7 × Fin 7, (get49 sub p.1 p.2).toNat) +
      (∑ p : Fin 7 × Fin 7, if p ∈ pts then (get49 B p.1 p.2).toNat else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p _ => ?_
    cases hXp : get49 X p.1 p.2
    · simp
    · rcases hcov p hXp with hs | hm
      · simp [hs]
      · have hBp : get49 B p.1 p.2 = true := (subset49_iff hX).mp hXB p.1 p.2 hXp
        simp [hm, hBp]
  exact le_trans hle (Nat.add_le_add_left (h1 pts) _)

private lemma pop49_set49_of_false {sub : Nat} {r c : Fin 7} (h : get49 sub r c = false) :
    pop49 (set49 sub r c) = pop49 sub + 1 := by
  rw [pop49_eq_sum, pop49_eq_sum, ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  have hsplit : ∀ f : Fin 7 × Fin 7 → Nat,
      (∑ q : Fin 7 × Fin 7, f q) = f (r, c) + ∑ q ∈ Finset.univ.erase (r, c), f q :=
    fun f => (Finset.add_sum_erase _ f (Finset.mem_univ (r, c))).symm
  rw [hsplit, hsplit]
  have hrest : (∑ q ∈ Finset.univ.erase (r, c), (get49 (set49 sub r c) q.1 q.2).toNat) =
      ∑ q ∈ Finset.univ.erase (r, c), (get49 sub q.1 q.2).toNat := by
    refine Finset.sum_congr rfl fun ⟨r', c'⟩ hq => ?_
    have hne : ¬ (r' = r ∧ c' = c) := fun ⟨h1, h2⟩ => (Finset.mem_erase.mp hq).1 (Prod.ext h1 h2)
    rw [get49_set, if_neg hne]
  rw [hrest, get49_set, if_pos ⟨rfl, rfl⟩, h]; simp [Nat.add_comm]

private lemma countHits_repPtsList (k : Fin 3) (B : Nat) :
    countHits B (repPtsList k) = pop49 (B &&& rep k) := by
  rw [pop49_eq_sum, ← Fintype.sum_prod_type']
  have haux : ∀ (l : List (Fin 7 × Fin 7)), l.Nodup →
      countHits B l = ∑ p : Fin 7 × Fin 7, if p ∈ l then (get49 B p.1 p.2).toNat else 0 := by
    intro l hnd
    induction l with
    | nil => simp [countHits]
    | cons p0 rest ih =>
      have ⟨hp0, hrest⟩ := List.nodup_cons.mp hnd
      simp only [countHits, ih hrest]
      have hsplit := (Finset.add_sum_erase (Finset.univ : Finset (Fin 7 × Fin 7))
        (fun p => if p ∈ p0 :: rest then (get49 B p.1 p.2).toNat else 0) (Finset.mem_univ p0)).symm
      rw [hsplit]
      have hsplit2 := (Finset.add_sum_erase (Finset.univ : Finset (Fin 7 × Fin 7))
        (fun p => if p ∈ rest then (get49 B p.1 p.2).toNat else 0) (Finset.mem_univ p0)).symm
      rw [hsplit2, if_neg hp0, zero_add, if_pos (List.mem_cons_self ..)]
      exact congrArg ((get49 B p0.1 p0.2).toNat + ·) (Finset.sum_congr rfl fun p hp => by
        have hne : p ≠ p0 := (Finset.mem_erase.mp hp).1
        simp [List.mem_cons, hne])
  rw [haux _ (repPtsList_nodup k)]
  refine Finset.sum_congr rfl fun ⟨r, c⟩ _ => ?_
  rw [get49_and]
  by_cases hm : (r, c) ∈ repPtsList k
  · have hrep := (rep_mem_iff k r c).mpr hm
    simp [hm, hrep]
  · have hrep : get49 (rep k) r c = false := Bool.eq_false_iff.mpr fun h => hm ((rep_mem_iff k r c).mp h)
    simp [hm, hrep]

section TreeOps
open Tree10

private def Tree10.checkC1 (B : Nat) :
    Tree10 → List Nat → Nat → Nat → Nat → Bool
  | tE, _, _, _, _ => true
  | tL v, [], sub, _, _ =>
      seqN (Nat.land B (Nat.xor ALL49 sub)) fun d =>
      seqN (closedNbr49 d) fun cn =>
      Nat.beq (Nat.land v cn) v
  | tL _, _ :: _, _, _, _ => false
  | tN l r, bit :: rest, sub, sz, rem =>
      match Nat.beq (Nat.land B bit) 0 with
      | true =>
          match Nat.blt (Nat.add sz rem) 4 with
          | true => true
          | false => l.checkC1 B rest sub sz rem
      | false =>
          let rem1 := Nat.sub rem 1
          let okL := match Nat.blt (Nat.add sz rem1) 4 with
                     | true => true
                     | false => l.checkC1 B rest sub sz rem1
          okL && seqN (Nat.lor sub bit) fun s2 => r.checkC1 B rest s2 (Nat.add sz 1) rem1
  | tN _ _, [], _, _, _ => false

private lemma Tree10.checkC1_sound {B X : Nat} (hX : X < 2 ^ 49) (hXpop4 : 4 ≤ pop49 X)
    (hXB : subset49 X B = true) :
    ∀ (t : Tree10) (pts : List (Fin 7 × Fin 7)) (sub : Nat),
      sub < 2 ^ 49 →
      t.checkC1 B (ptsToBits pts) sub (pop49 sub) (countHits B pts) = true →
      (∀ p, get49 X p.1 p.2 = true → get49 sub p.1 p.2 = true ∨ p ∈ pts) →
      (∀ p, get49 sub p.1 p.2 = true → get49 X p.1 p.2 = true ∧ p ∉ pts) →
      pts.Nodup →
      subset49 (t.getAux (ptsToBits pts) X) (closedNbr49 (diff49 B X)) = true := by
  intro t
  induction t with
  | tE => intro _ _ _ _ _ _ _; exact subset49_zero_left _
  | tL v =>
    intro pts sub hsub_lt hchk hcov hsub _
    cases pts with
    | cons _ _ => simp [ptsToBits, Tree10.checkC1] at hchk
    | nil =>
      simp only [ptsToBits, Tree10.checkC1, seqN_eq] at hchk
      have hXeq : X = sub := by
        apply ext49 hX hsub_lt
        intro r c
        cases hx : get49 X r c
        · cases hs : get49 sub r c
          · rfl
          · exact absurd (hsub (r, c) hs).1 (by simp [hx])
        · rcases hcov (r, c) hx with hs | hnil
          · exact hs.symm
          · cases hnil
      subst hXeq; exact hchk
  | tN l r ihl ihr =>
    intro pts sub hsub_lt hchk hcov hsub hnd
    cases pts with
    | nil => simp [ptsToBits, Tree10.checkC1] at hchk
    | cons p rest =>
      rcases p with ⟨row, col⟩
      have ⟨hp_not_rest, hrest_nd⟩ := List.nodup_cons.mp hnd
      simp only [ptsToBits] at hchk ⊢
      unfold Tree10.checkC1 at hchk
      dsimp only at hchk
      rw [land_bit49_eq_zero B row col] at hchk
      unfold Tree10.getAux
      rw [land_bit49_eq_zero X row col]
      cases hBp : get49 B row col
      · rw [hBp] at hchk
        have hXp : get49 X row col = false := by
          cases hx : get49 X row col
          · rfl
          · exact absurd ((subset49_iff hX).mp hXB row col hx) (by simp [hBp])
        rw [hXp]
        have hcnt : countHits B ((row, col) :: rest) = countHits B rest := by simp [countHits, hBp]
        have hcov' : ∀ q, get49 X q.1 q.2 = true → get49 sub q.1 q.2 = true ∨ q ∈ rest := by
          intro q hq
          rcases hcov q hq with hs | hmem
          · exact Or.inl hs
          · rcases List.mem_cons.mp hmem with rfl | hr
            · exact absurd hq (by simp [hXp])
            · exact Or.inr hr
        have hsub' : ∀ q, get49 sub q.1 q.2 = true → get49 X q.1 q.2 = true ∧ q ∉ rest := by
          intro q hq; have ⟨h1, h2⟩ := hsub q hq
          exact ⟨h1, fun hr => h2 (List.mem_cons_of_mem _ hr)⟩
        have hge4 : 4 ≤ pop49 sub + countHits B rest :=
          hXpop4.trans (pop49_le_add_countHits hX hXB rest hcov')
        have hblt : Nat.blt (pop49 sub + countHits B rest) 4 = false := by
          cases h : Nat.blt (pop49 sub + countHits B rest) 4
          · rfl
          · exfalso; have := Nat.blt_eq.mp h; omega
        simp only [add_eq, Bool.not_false, hcnt, hblt] at hchk
        exact ihl rest sub hsub_lt hchk hcov' hsub' hrest_nd
      · rw [hBp] at hchk
        have hcnt : countHits B ((row, col) :: rest) - 1 = countHits B rest := by simp [countHits, hBp]
        simp only [add_eq, sub_eq, Bool.not_true, Bool.and_eq_true, seqN_eq] at hchk
        cases hXp : get49 X row col
        · have hcov' : ∀ q, get49 X q.1 q.2 = true → get49 sub q.1 q.2 = true ∨ q ∈ rest := by
            intro q hq
            rcases hcov q hq with hs | hmem
            · exact Or.inl hs
            · rcases List.mem_cons.mp hmem with rfl | hr
              · exact absurd hq (by simp [hXp])
              · exact Or.inr hr
          have hsub' : ∀ q, get49 sub q.1 q.2 = true → get49 X q.1 q.2 = true ∧ q ∉ rest := by
            intro q hq; have ⟨h1, h2⟩ := hsub q hq
            exact ⟨h1, fun hr => h2 (List.mem_cons_of_mem _ hr)⟩
          have hge4 : 4 ≤ pop49 sub + countHits B rest :=
            hXpop4.trans (pop49_le_add_countHits hX hXB rest hcov')
          have hblt : Nat.blt (pop49 sub + countHits B rest) 4 = false := by
            cases h : Nat.blt (pop49 sub + countHits B rest) 4
            · rfl
            · exfalso; have := Nat.blt_eq.mp h; omega
          have hL := hchk.1
          rw [hcnt, hblt] at hL
          exact ihl rest sub hsub_lt hL hcov' hsub' hrest_nd
        · have hsub_f : get49 sub row col = false := by
            cases hs : get49 sub row col
            · rfl
            · exact absurd (List.mem_cons_self ..) (hsub (row, col) hs).2
          have hpop_set : pop49 (set49 sub row col) = pop49 sub + 1 := pop49_set49_of_false hsub_f
          have hR := hchk.2
          change r.checkC1 B (ptsToBits rest) (set49 sub row col) (pop49 sub + 1) (countHits B ((row, col) :: rest) - 1) = true at hR
          rw [← hpop_set, hcnt] at hR
          refine ihr rest (set49 sub row col) (set49_lt hsub_lt row col) hR ?_ ?_ hrest_nd
          · intro q hq
            rcases hcov q hq with hs | hmem
            · left; rw [get49_set]; split <;> [rfl; exact hs]
            · rcases List.mem_cons.mp hmem with rfl | hr
              · left; rw [get49_set]; simp
              · exact Or.inr hr
          · intro q hq
            rw [get49_set] at hq
            split at hq
            · rename_i heq
              rcases q with ⟨qr, qc⟩; dsimp only at heq
              rw [heq.1, heq.2]
              exact ⟨hXp, hp_not_rest⟩
            · have ⟨h1, h2⟩ := hsub q hq
              exact ⟨h1, fun hr => h2 (List.mem_cons_of_mem _ hr)⟩

__C1_TREE_DEFS__

__C2_TREE_DEFS__

private def c1Tree : Fin 3 → Tree10
  | ⟨0, _⟩ => c1Tree0 | ⟨1, _⟩ => c1Tree1 | ⟨2, _⟩ => c1Tree2

private def c2Tree : Fin 3 → Tree10
  | ⟨0, _⟩ => c2Tree0 | ⟨1, _⟩ => c2Tree1 | ⟨2, _⟩ => c2Tree2

private def Tree10.allLt49 : Tree10 → Bool
  | tE => true
  | tL v => Nat.blt v (2 ^ 49)
  | tN l r => l.allLt49 && r.allLt49

private lemma Tree10.getAux_lt49 {t : Tree10} (ht : t.allLt49 = true) (bits : List Nat) (m : Nat) :
    t.getAux bits m < 2 ^ 49 := by
  induction t generalizing bits with
  | tE => simp [Tree10.getAux]
  | tL v => exact Nat.blt_eq.mp ht
  | tN l r ihl ihr =>
    simp only [Tree10.allLt49, Bool.and_eq_true] at ht
    cases bits with
    | nil => simp [Tree10.getAux]
    | cons bit rest =>
      unfold Tree10.getAux
      cases Nat.beq (Nat.land m bit) 0
      · exact ihr ht.2 rest
      · exact ihl ht.1 rest

private theorem c1Tree_lt49_0 : c1Tree0.allLt49 = true := by rfl
private theorem c1Tree_lt49_1 : c1Tree1.allLt49 = true := by rfl
private theorem c1Tree_lt49_2 : c1Tree2.allLt49 = true := by rfl
private theorem c2Tree_lt49_0 : c2Tree0.allLt49 = true := by rfl
private theorem c2Tree_lt49_1 : c2Tree1.allLt49 = true := by rfl
private theorem c2Tree_lt49_2 : c2Tree2.allLt49 = true := by rfl

private lemma c1Tree_get_lt49 (k : Fin 3) (m : Nat) :
    (c1Tree k).getAux (repBits k) m < 2 ^ 49 := by
  have hall : (c1Tree k).allLt49 = true :=
    match k with | ⟨0, _⟩ => c1Tree_lt49_0 | ⟨1, _⟩ => c1Tree_lt49_1 | ⟨2, _⟩ => c1Tree_lt49_2
  exact Tree10.getAux_lt49 hall _ _

private lemma c2Tree_get_lt49 (k : Fin 3) (m : Nat) :
    (c2Tree k).getAux (repBits k) m < 2 ^ 49 := by
  have hall : (c2Tree k).allLt49 = true :=
    match k with | ⟨0, _⟩ => c2Tree_lt49_0 | ⟨1, _⟩ => c2Tree_lt49_1 | ⟨2, _⟩ => c2Tree_lt49_2
  exact Tree10.getAux_lt49 hall _ _

private def checkC2Aux (rK1 : Nat) (tK1 : Tree10) (bK1 : List Nat) (g1 g1Inv : Aut2) (B1 : Nat) :
    Tree10 → List Nat → Nat → Nat → Nat → Bool
  | tE, _, _, _, _ => true
  | tL v, [], sub, _, _ =>
      seqN (g1Inv.applyMask sub) fun subC =>
      seqN (Nat.land rK1 (Nat.xor ALL49 subC)) fun yCanon =>
      seqN (tK1.getAux bK1 yCanon) fun c1Y =>
      seqN (g1.applyMask c1Y) fun img =>
      Nat.beq (Nat.land v img) v
  | tL _, _ :: _, _, _, _ => false
  | tN l r, bit :: rest, sub, sz, rem =>
      match Nat.beq (Nat.land B1 bit) 0 with
      | true =>
          match Nat.blt (Nat.add sz rem) 4 with
          | true => true
          | false => checkC2Aux rK1 tK1 bK1 g1 g1Inv B1 l rest sub sz rem
      | false =>
          let rem1 := Nat.sub rem 1
          let okL := match Nat.blt (Nat.add sz rem1) 4 with
                     | true => true
                     | false => checkC2Aux rK1 tK1 bK1 g1 g1Inv B1 l rest sub sz rem1
          okL && seqN (Nat.lor sub bit) fun s2 => checkC2Aux rK1 tK1 bK1 g1 g1Inv B1 r rest s2 (Nat.add sz 1) rem1
  | tN _ _, [], _, _, _ => false

private lemma checkC2Aux_sound {k1 : Fin 3} {g1 : Aut2} {B1 X : Nat}
    (hX : X < 2 ^ 49) (hXpop4 : 4 ≤ pop49 X) (hXB : subset49 X B1 = true) :
    ∀ (t : Tree10) (pts : List (Fin 7 × Fin 7)) (sub : Nat),
      sub < 2 ^ 49 →
      checkC2Aux (rep k1) (c1Tree k1) (repBits k1) g1 g1.inv B1 t (ptsToBits pts) sub (pop49 sub) (countHits B1 pts) = true →
      (∀ p, get49 X p.1 p.2 = true → get49 sub p.1 p.2 = true ∨ p ∈ pts) →
      (∀ p, get49 sub p.1 p.2 = true → get49 X p.1 p.2 = true ∧ p ∉ pts) →
      pts.Nodup →
      subset49 (t.getAux (ptsToBits pts) X)
        (g1.applyMask ((c1Tree k1).getAux (repBits k1) (diff49 (rep k1) (g1.inv.applyMask X)))) = true := by
  intro t
  induction t with
  | tE => intro _ _ _ _ _ _ _; exact subset49_zero_left _
  | tL v =>
    intro pts sub hsub_lt hchk hcov hsub _
    cases pts with
    | cons _ _ => simp [ptsToBits, checkC2Aux] at hchk
    | nil =>
      simp only [ptsToBits, checkC2Aux, seqN_eq] at hchk
      have hXeq : X = sub := by
        apply ext49 hX hsub_lt
        intro r c
        cases hx : get49 X r c
        · cases hs : get49 sub r c
          · rfl
          · exact absurd (hsub (r, c) hs).1 (by simp [hx])
        · rcases hcov (r, c) hx with hs | hnil
          · exact hs.symm
          · cases hnil
      subst hXeq; exact hchk
  | tN l r ihl ihr =>
    intro pts sub hsub_lt hchk hcov hsub hnd
    cases pts with
    | nil => simp [ptsToBits, checkC2Aux] at hchk
    | cons p rest =>
      rcases p with ⟨row, col⟩
      have ⟨hp_not_rest, hrest_nd⟩ := List.nodup_cons.mp hnd
      simp only [ptsToBits] at hchk ⊢
      unfold checkC2Aux at hchk
      dsimp only at hchk
      rw [land_bit49_eq_zero B1 row col] at hchk
      conv_lhs => arg 1; unfold Tree10.getAux
      rw [land_bit49_eq_zero X row col]
      cases hBp : get49 B1 row col
      · rw [hBp] at hchk
        have hXp : get49 X row col = false := by
          cases hx : get49 X row col
          · rfl
          · exact absurd ((subset49_iff hX).mp hXB row col hx) (by simp [hBp])
        rw [hXp]
        have hcnt : countHits B1 ((row, col) :: rest) = countHits B1 rest := by simp [countHits, hBp]
        have hcov' : ∀ q, get49 X q.1 q.2 = true → get49 sub q.1 q.2 = true ∨ q ∈ rest := by
          intro q hq
          rcases hcov q hq with hs | hmem
          · exact Or.inl hs
          · rcases List.mem_cons.mp hmem with rfl | hr
            · exact absurd hq (by simp [hXp])
            · exact Or.inr hr
        have hsub' : ∀ q, get49 sub q.1 q.2 = true → get49 X q.1 q.2 = true ∧ q ∉ rest := by
          intro q hq; have ⟨h1, h2⟩ := hsub q hq
          exact ⟨h1, fun hr => h2 (List.mem_cons_of_mem _ hr)⟩
        have hge4 : 4 ≤ pop49 sub + countHits B1 rest :=
          hXpop4.trans (pop49_le_add_countHits hX hXB rest hcov')
        have hblt : Nat.blt (pop49 sub + countHits B1 rest) 4 = false := by
          cases h : Nat.blt (pop49 sub + countHits B1 rest) 4
          · rfl
          · exfalso; have := Nat.blt_eq.mp h; omega
        simp only [add_eq, Bool.not_false, hcnt, hblt] at hchk
        exact ihl rest sub hsub_lt hchk hcov' hsub' hrest_nd
      · rw [hBp] at hchk
        have hcnt : countHits B1 ((row, col) :: rest) - 1 = countHits B1 rest := by simp [countHits, hBp]
        simp only [add_eq, sub_eq, Bool.not_true, Bool.and_eq_true, seqN_eq] at hchk
        cases hXp : get49 X row col
        · have hcov' : ∀ q, get49 X q.1 q.2 = true → get49 sub q.1 q.2 = true ∨ q ∈ rest := by
            intro q hq
            rcases hcov q hq with hs | hmem
            · exact Or.inl hs
            · rcases List.mem_cons.mp hmem with rfl | hr
              · exact absurd hq (by simp [hXp])
              · exact Or.inr hr
          have hsub' : ∀ q, get49 sub q.1 q.2 = true → get49 X q.1 q.2 = true ∧ q ∉ rest := by
            intro q hq; have ⟨h1, h2⟩ := hsub q hq
            exact ⟨h1, fun hr => h2 (List.mem_cons_of_mem _ hr)⟩
          have hge4 : 4 ≤ pop49 sub + countHits B1 rest :=
            hXpop4.trans (pop49_le_add_countHits hX hXB rest hcov')
          have hblt : Nat.blt (pop49 sub + countHits B1 rest) 4 = false := by
            cases h : Nat.blt (pop49 sub + countHits B1 rest) 4
            · rfl
            · exfalso; have := Nat.blt_eq.mp h; omega
          have hL := hchk.1
          rw [hcnt, hblt] at hL
          exact ihl rest sub hsub_lt hL hcov' hsub' hrest_nd
        · have hsub_f : get49 sub row col = false := by
            cases hs : get49 sub row col
            · rfl
            · exact absurd (List.mem_cons_self ..) (hsub (row, col) hs).2
          have hpop_set : pop49 (set49 sub row col) = pop49 sub + 1 := pop49_set49_of_false hsub_f
          have hR := hchk.2
          change checkC2Aux (rep k1) (c1Tree k1) (repBits k1) g1 g1.inv B1 r (ptsToBits rest) (set49 sub row col) (pop49 sub + 1) (countHits B1 ((row, col) :: rest) - 1) = true at hR
          rw [← hpop_set, hcnt] at hR
          refine ihr rest (set49 sub row col) (set49_lt hsub_lt row col) hR ?_ ?_ hrest_nd
          · intro q hq
            rcases hcov q hq with hs | hmem
            · left; rw [get49_set]; split <;> [rfl; exact hs]
            · rcases List.mem_cons.mp hmem with rfl | hr
              · left; rw [get49_set]; simp
              · exact Or.inr hr
          · intro q hq
            rw [get49_set] at hq
            split at hq
            · rename_i heq
              rcases q with ⟨qr, qc⟩; dsimp only at heq
              rw [heq.1, heq.2]
              exact ⟨hXp, hp_not_rest⟩
            · have ⟨h1, h2⟩ := hsub q hq
              exact ⟨h1, fun hr => h2 (List.mem_cons_of_mem _ hr)⟩

end TreeOps

private def checkC1Pair (k k0 : Fin 3) (half : Bool) : Bool :=
  let tK := c1Tree k
  let bK := repBits k
  let rK := rep k
  forAllAut2 k0 half fun _ B =>
    seqN (pop49 (Nat.land B rK)) fun ov =>
    match Nat.blt ov 4 with
    | true => true
    | false => tK.checkC1 B bK 0 0 ov

private def checkC2Pair (k k0 : Fin 3) (half : Bool) : Bool :=
  let rK0 := rep k0
  let tK0 := c1Tree k0
  let bK0 := repBits k0
  let tK  := c2Tree k
  let bK  := repBits k
  let rK  := rep k
  forAllAut2 k0 half fun g1 B1 =>
    seqN (pop49 (Nat.land B1 rK)) fun ov =>
    match Nat.blt ov 4 with
    | true => true
    | false =>
        match g1.inv with
        | g1Inv => checkC2Aux rK0 tK0 bK0 g1 g1Inv B1 tK bK 0 0 ov

private theorem checkC1_00 : checkC1Pair 0 0 false = true := by rfl
private theorem checkC1_01 : checkC1Pair 0 1 false = true := by rfl
private theorem checkC1_02 : checkC1Pair 0 2 true  = true := by rfl
private theorem checkC1_10 : checkC1Pair 1 0 false = true := by rfl
private theorem checkC1_11 : checkC1Pair 1 1 false = true := by rfl
private theorem checkC1_12 : checkC1Pair 1 2 true  = true := by rfl
private theorem checkC1_20 : checkC1Pair 2 0 false = true := by rfl
private theorem checkC1_21 : checkC1Pair 2 1 false = true := by rfl
private theorem checkC1_22 : checkC1Pair 2 2 true  = true := by rfl

private theorem checkC2_00 : checkC2Pair 0 0 false = true := by rfl
private theorem checkC2_01 : checkC2Pair 0 1 false = true := by rfl
private theorem checkC2_02 : checkC2Pair 0 2 true  = true := by rfl
private theorem checkC2_10 : checkC2Pair 1 0 false = true := by rfl
private theorem checkC2_11 : checkC2Pair 1 1 false = true := by rfl
private theorem checkC2_12 : checkC2Pair 1 2 true  = true := by rfl
private theorem checkC2_20 : checkC2Pair 2 0 false = true := by rfl
private theorem checkC2_21 : checkC2Pair 2 1 false = true := by rfl
private theorem checkC2_22 : checkC2Pair 2 2 true  = true := by rfl

private lemma checkC1Pair_all (k k0 : Fin 3) : checkC1Pair k k0 (k0 == 2) = true := by
  revert k k0
  exact fin3_cases
    (fin3_cases checkC1_00 checkC1_01 checkC1_02)
    (fin3_cases checkC1_10 checkC1_11 checkC1_12)
    (fin3_cases checkC1_20 checkC1_21 checkC1_22)

private lemma checkC2Pair_all (k k0 : Fin 3) : checkC2Pair k k0 (k0 == 2) = true := by
  revert k k0
  exact fin3_cases
    (fin3_cases checkC2_00 checkC2_01 checkC2_02)
    (fin3_cases checkC2_10 checkC2_11 checkC2_12)
    (fin3_cases checkC2_20 checkC2_21 checkC2_22)

private lemma c1Tree_sound {k : Fin 3} {X : Nat} {B : Finset (ZMod 7 × ZMod 7)}
    (hX : X < 2 ^ 49) (hXrep : subset49 X (rep k) = true) (hXpop : 4 ≤ pop49 X)
    (hB : (C7 ⊠ C7).IsIndepSet (B : Set (ZMod 7 × ZMod 7))) (hBcard : B.card = 10)
    (hXB : subset49 X (ofFinset49 B) = true) :
    subset49 ((c1Tree k).getAux (repBits k) X) (closedNbr49 (diff49 (ofFinset49 B) X)) = true := by
  obtain ⟨kB, gB, hsr, hBeq⟩ := tenSet_canon_half hB hBcard
  have hsr' : (kB == 2) = false ∨ gB.sr = false := by
    rcases hsr with hne | h0
    · left; exact beq_false_of_ne hne
    · exact Or.inr h0
  have hpair := checkC1Pair_all k kB
  unfold checkC1Pair at hpair
  dsimp only at hpair
  have hall := forAllAut2_sound hpair gB hsr'
  simp only [seqN_eq, land_eq] at hall
  rw [← hBeq] at hall
  have hpop4 : 4 ≤ pop49 (ofFinset49 B &&& rep k) := by
    have hsub : subset49 X (ofFinset49 B &&& rep k) = true := by
      rw [subset49_iff hX] at hXB hXrep ⊢
      intro r c hx; rw [get49_and, hXB r c hx, hXrep r c hx]; rfl
    exact hXpop.trans (subset49_pop_le hX hsub)
  have hblt : Nat.blt (pop49 (ofFinset49 B &&& rep k)) 4 = false := by
    cases h : Nat.blt (pop49 (ofFinset49 B &&& rep k)) 4
    · rfl
    · exfalso; have := Nat.blt_eq.mp h; omega
  rw [hblt] at hall
  dsimp only at hall
  have hpop0 : pop49 0 = 0 := by decide
  have hall' : (c1Tree k).checkC1 (ofFinset49 B) (ptsToBits (repPtsList k)) 0 (pop49 0)
      (countHits (ofFinset49 B) (repPtsList k)) = true := by
    have heq : (c1Tree k).checkC1 (ofFinset49 B) (ptsToBits (repPtsList k)) 0 (pop49 0)
        (countHits (ofFinset49 B) (repPtsList k)) =
      (c1Tree k).checkC1 (ofFinset49 B) (repBits k) 0 0 (pop49 (ofFinset49 B &&& rep k)) := by
      rw [← repBits_eq k, hpop0, countHits_repPtsList k (ofFinset49 B)]
    rw [heq]; exact hall
  rw [repBits_eq]
  refine Tree10.checkC1_sound hX hXpop hXB (c1Tree k) (repPtsList k) 0 (by decide) hall' ?_ ?_ (repPtsList_nodup k)
  · intro p hp
    exact Or.inr ((rep_mem_iff k p.1 p.2).mp ((subset49_iff hX).mp hXrep p.1 p.2 hp))
  · intro p hp; rw [get49_zero] at hp; exact absurd hp (by decide)

private lemma c1Tree_equivariant {k : Fin 3} {g : Aut2} {X : Nat}
    {B : Finset (ZMod 7 × ZMod 7)}
    (hX : X < 2 ^ 49) (hXrep : subset49 X (rep k) = true) (hXpop : 4 ≤ pop49 X)
    (hB : (C7 ⊠ C7).IsIndepSet (B : Set (ZMod 7 × ZMod 7))) (hBcard : B.card = 10)
    (hXB : subset49 (g.applyMask X) (ofFinset49 B) = true) :
    subset49 (g.applyMask ((c1Tree k).getAux (repBits k) X))
      (closedNbr49 (diff49 (ofFinset49 B) (g.applyMask X))) = true := by
  let B' := B.map g.inv.toIso.toEquiv.toEmbedding
  have hB' : (C7 ⊠ C7).IsIndepSet (B' : Set (ZMod 7 × ZMod 7)) := isIndepSet_map_iso' g.inv.toIso hB
  have hB'card : B'.card = 10 := by rw [Finset.card_map, hBcard]
  have hB'mask : ofFinset49 B' = g.inv.applyMask (ofFinset49 B) := (Aut2.applyMask_ofFinset g.inv B).symm
  have hXB' : subset49 X (ofFinset49 B') = true := by
    rw [hB'mask, ← Aut2.applyMask_inv_left g hX]
    exact Aut2.applyMask_subset (g.applyMask_lt hX) hXB
  have hsub := c1Tree_sound hX hXrep hXpop hB' hB'card hXB'
  have hsub2 := Aut2.applyMask_subset (g := g) (c1Tree_get_lt49 k X) hsub
  rw [Aut2.applyMask_closedNbr g (diff49_lt (ofFinset49_lt _)),
      Aut2.applyMask_diff g (ofFinset49_lt _),
      hB'mask, Aut2.applyMask_inv_right g (ofFinset49_lt _)] at hsub2
  exact hsub2

private lemma pop49_applyMask (g : Aut2) (m : Nat) : pop49 (g.applyMask m) = pop49 m := by
  rw [pop49_eq_sum, pop49_eq_sum, ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  let e : (Fin 7 × Fin 7) ≃ (Fin 7 × Fin 7) := Equiv.mk g.applyFin g.inv.applyFin g.inv_applyFin g.applyFin_inv
  rw [← Equiv.sum_comp e (fun p => (get49 (g.applyMask m) p.1 p.2).toNat)]
  refine Finset.sum_congr rfl fun ⟨r, c⟩ _ => by simp [e, Aut2.get_applyMask]

private lemma c2Tree_sound {k : Fin 3} {X : Nat}
    {B1 B0 : Finset (ZMod 7 × ZMod 7)}
    (hX : X < 2 ^ 49) (hXrep : subset49 X (rep k) = true) (hXpop : 4 ≤ pop49 X) (hXle6 : pop49 X ≤ 6)
    (hB1 : (C7 ⊠ C7).IsIndepSet (B1 : Set (ZMod 7 × ZMod 7))) (hB1card : B1.card = 10)
    (hXB1 : subset49 X (ofFinset49 B1) = true)
    (hB0 : (C7 ⊠ C7).IsIndepSet (B0 : Set (ZMod 7 × ZMod 7))) (hB0card : B0.card = 10)
    (hYB0 : subset49 (diff49 (ofFinset49 B1) X) (ofFinset49 B0) = true) :
    subset49 ((c2Tree k).getAux (repBits k) X)
      (closedNbr49 (diff49 (ofFinset49 B0) (diff49 (ofFinset49 B1) X))) = true := by
  obtain ⟨k1, g1, hsr1, hB1eq⟩ := tenSet_canon_half hB1 hB1card
  have hsr1' : (k1 == 2) = false ∨ g1.sr = false := by
    rcases hsr1 with hne | h0
    · left; exact beq_false_of_ne hne
    · exact Or.inr h0
  have hpair := checkC2Pair_all k k1
  unfold checkC2Pair at hpair
  dsimp only at hpair
  have hall := forAllAut2_sound hpair g1 hsr1'
  simp only [seqN_eq, land_eq] at hall
  rw [← hB1eq] at hall
  have hpop4 : 4 ≤ pop49 (ofFinset49 B1 &&& rep k) := by
    have hsub : subset49 X (ofFinset49 B1 &&& rep k) = true := by
      rw [subset49_iff hX] at hXB1 hXrep ⊢
      intro r c hx; rw [get49_and, hXB1 r c hx, hXrep r c hx]; rfl
    exact hXpop.trans (subset49_pop_le hX hsub)
  have hblt : Nat.blt (pop49 (ofFinset49 B1 &&& rep k)) 4 = false := by
    cases h : Nat.blt (pop49 (ofFinset49 B1 &&& rep k)) 4
    · rfl
    · exfalso; have := Nat.blt_eq.mp h; omega
  rw [hblt] at hall
  dsimp only at hall
  have hpop0 : pop49 0 = 0 := by decide
  have hall' : checkC2Aux (rep k1) (c1Tree k1) (repBits k1) g1 g1.inv (ofFinset49 B1)
      (c2Tree k) (ptsToBits (repPtsList k)) 0 (pop49 0)
      (countHits (ofFinset49 B1) (repPtsList k)) = true := by
    have heq : checkC2Aux (rep k1) (c1Tree k1) (repBits k1) g1 g1.inv (ofFinset49 B1)
        (c2Tree k) (ptsToBits (repPtsList k)) 0 (pop49 0)
        (countHits (ofFinset49 B1) (repPtsList k)) =
      checkC2Aux (rep k1) (c1Tree k1) (repBits k1) g1 g1.inv (ofFinset49 B1)
        (c2Tree k) (repBits k) 0 0 (pop49 (ofFinset49 B1 &&& rep k)) := by
      rw [← repBits_eq k, hpop0, countHits_repPtsList k (ofFinset49 B1)]
    rw [heq]; exact hall
  have hstep1 := checkC2Aux_sound hX hXpop hXB1 (c2Tree k) (repPtsList k) 0 (by decide) hall'
    (fun p hp => Or.inr ((rep_mem_iff k p.1 p.2).mp ((subset49_iff hX).mp hXrep p.1 p.2 hp)))
    (fun p hp => by rw [get49_zero] at hp; exact absurd hp (by decide))
    (repPtsList_nodup k)
  rw [← repBits_eq k] at hstep1
  let yCanon := diff49 (rep k1) (g1.inv.applyMask X)
  have hyLt : yCanon < 2 ^ 49 := diff49_lt (rep_lt k1)
  have hyImg : g1.applyMask yCanon = diff49 (ofFinset49 B1) X := by
    rw [Aut2.applyMask_diff g1 (rep_lt k1), ← hB1eq,
        Aut2.applyMask_inv_right g1 hX]
  have hyRep : subset49 yCanon (rep k1) = true := by
    rw [subset49_iff hyLt]; intro r c h
    rw [get49_diff] at h; exact (Bool.and_eq_true _ _ |>.mp h).1
  have hyPop : 4 ≤ pop49 yCanon := by
    have hsum : pop49 (diff49 (ofFinset49 B1) X) + pop49 X = pop49 (ofFinset49 B1) := by
      rw [pop49_eq_sum, pop49_eq_sum, pop49_eq_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [get49_diff]
      cases hx : get49 X r c
      · simp
      · have hbx := (subset49_iff hX).mp hXB1 r c hx
        simp [hbx]
    have hpopB1 : pop49 (ofFinset49 B1) = 10 := by rw [pop49_ofFinset, hB1card]
    have hyEq : pop49 yCanon = pop49 (diff49 (ofFinset49 B1) X) := by
      rw [← pop49_applyMask g1, hyImg]
    omega
  have hstep2 := c1Tree_equivariant (g := g1) hyLt hyRep hyPop hB0 hB0card (by rw [hyImg]; exact hYB0)
  rw [hyImg] at hstep2
  exact subset49_trans (c2Tree_get_lt49 k X) (g1.applyMask_lt (c1Tree_get_lt49 k1 yCanon)) hstep1 hstep2

/-! ## Section 5: Leaf Certificate Soundness (3-Square Cover, 2D & 3D `Grid49` Farkas Duals) -/

__SQ22_DEF__

private lemma sq22_lt (idx : Fin 49) : sq22 idx < 2 ^ 49 := by revert idx; decide

private lemma sq22_get_imp : ∀ (idx : Fin 49) (r' c' : Fin 7),
    get49 (sq22 idx) r' c' = true →
      let r : Fin 7 := ⟨idx.val / 7, Nat.div_lt_of_lt_mul idx.isLt⟩
      let c : Fin 7 := ⟨idx.val % 7, Nat.mod_lt _ (by decide)⟩
      (r' = r ∨ r' = next7 r) ∧ (c' = c ∨ c' = next7 c) := by decide

private lemma sq22_card_le_one (idx : Fin 49) {S : Finset (ZMod 7 × ZMod 7)}
    (hS : (C7 ⊠ C7).IsIndepSet (S : Set (ZMod 7 × ZMod 7))) :
    pop49 (ofFinset49 S &&& sq22 idx) ≤ 1 := by
  let r : Fin 7 := ⟨idx.val / 7, Nat.div_lt_of_lt_mul idx.isLt⟩
  let c : Fin 7 := ⟨idx.val % 7, Nat.mod_lt _ (by decide)⟩
  have hsq := sq22_get_imp idx
  let T := S.filter fun p => get49 (sq22 idx) (ofZ7 p.1) (ofZ7 p.2) = true
  have hpop : pop49 (ofFinset49 S &&& sq22 idx) = T.card := by
    rw [← pop49_ofFinset T]
    congr 1
    apply ext49 (and_lt49 (sq22_lt idx)) (ofFinset49_lt T)
    intro r' c'
    rw [get49_and]
    by_cases h1 : (toZ7 r', toZ7 c') ∈ S <;> by_cases h2 : get49 (sq22 idx) r' c' = true
    · have ht : (toZ7 r', toZ7 c') ∈ T := Finset.mem_filter.mpr ⟨h1, by simpa [ofZ7_toZ7] using h2⟩
      simp [(get49_ofFinset S r' c').mpr h1, h2, (get49_ofFinset T r' c').mpr ht]
    · have h2f : get49 (sq22 idx) r' c' = false := Bool.eq_false_iff.mpr h2
      have hnt : (toZ7 r', toZ7 c') ∉ T := by simp [T, ofZ7_toZ7, h2f]
      have htf : get49 (ofFinset49 T) r' c' = false := Bool.eq_false_iff.mpr fun ht => hnt ((get49_ofFinset T r' c').mp ht)
      simp [h2f, htf]
    · have h1f : get49 (ofFinset49 S) r' c' = false := Bool.eq_false_iff.mpr fun hs => h1 ((get49_ofFinset S r' c').mp hs)
      have hnt : (toZ7 r', toZ7 c') ∉ T := by simp [T, h1]
      have htf : get49 (ofFinset49 T) r' c' = false := Bool.eq_false_iff.mpr fun ht => hnt ((get49_ofFinset T r' c').mp ht)
      simp [h1f, htf]
    · have h1f : get49 (ofFinset49 S) r' c' = false := Bool.eq_false_iff.mpr fun hs => h1 ((get49_ofFinset S r' c').mp hs)
      have hnt : (toZ7 r', toZ7 c') ∉ T := by simp [T, h1]
      have htf : get49 (ofFinset49 T) r' c' = false := Bool.eq_false_iff.mpr fun ht => hnt ((get49_ofFinset T r' c').mp ht)
      simp [h1f, htf]
  rw [hpop]
  refine Finset.card_le_one.mpr fun p hp q hq => ?_
  by_contra hpq
  have ⟨hpS, hpsq⟩ := Finset.mem_filter.mp hp
  have ⟨hqS, hqsq⟩ := Finset.mem_filter.mp hq
  have ⟨hpr, hpc⟩ := hsq (ofZ7 p.1) (ofZ7 p.2) hpsq
  have ⟨hqr, hqc⟩ := hsq (ofZ7 q.1) (ofZ7 q.2) hqsq
  have hclose : ∀ {x y a : Fin 7}, (x = a ∨ x = next7 a) → (y = a ∨ y = next7 a) →
      toZ7 x = toZ7 y ∨ C7.Adj (toZ7 x) (toZ7 y) := by
    intro x y a hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Or.inl rfl
    · right; rw [toZ7_next7]; exact c7_adj_add_one _
    · right; rw [toZ7_next7]; exact (c7_adj_add_one _).symm
    · exact Or.inl rfl
  have hr_adj := hclose hpr hqr
  have hc_adj := hclose hpc hqc
  rw [toZ7_ofZ7, toZ7_ofZ7] at hr_adj hc_adj
  exact hS hpS hqS hpq ⟨hpq, hr_adj, hc_adj⟩

private def checkAvailSq3 (avail : Nat) (a b c : Fin 49) : Bool :=
  subset49 avail (Nat.lor (Nat.lor (sq22 a) (sq22 b)) (sq22 c))

private lemma card_le_three_of_sq3_cover {S : Finset (ZMod 7 × ZMod 7)} {avail : Nat}
    {a b c : Fin 49} (hS : (C7 ⊠ C7).IsIndepSet (S : Set (ZMod 7 × ZMod 7)))
    (hsub : subset49 (ofFinset49 S) avail = true) (hcov : checkAvailSq3 avail a b c = true)
    (hav : avail < 2 ^ 49) : S.card ≤ 3 := by
  have hSa := sq22_card_le_one a hS
  have hSb := sq22_card_le_one b hS
  have hSc := sq22_card_le_one c hS
  have hcovS : subset49 (ofFinset49 S) ((sq22 a ||| sq22 b) ||| sq22 c) = true :=
    subset49_trans (ofFinset49_lt S) hav hsub hcov
  rw [subset49_iff (ofFinset49_lt S)] at hcovS
  have hle : pop49 (ofFinset49 S) ≤
      pop49 (ofFinset49 S &&& sq22 a) + pop49 (ofFinset49 S &&& sq22 b) + pop49 (ofFinset49 S &&& sq22 c) := by
    rw [pop49_eq_sum, pop49_eq_sum, pop49_eq_sum, pop49_eq_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun r _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun col _ => ?_
    rw [get49_and, get49_and, get49_and]
    cases hs : get49 (ofFinset49 S) r col
    · simp
    · have h3 := hcovS r col hs
      rw [get49_or, get49_or, Bool.or_eq_true, Bool.or_eq_true] at h3
      rcases h3 with (h | h) | h <;> simp [h] <;> omega
  rw [pop49_ofFinset] at hle
  omega

private structure Row7N where
  n0 : Nat
  n1 : Nat
  n2 : Nat
  n3 : Nat
  n4 : Nat
  n5 : Nat
  n6 : Nat

private def Row7N.zero : Row7N := ⟨0, 0, 0, 0, 0, 0, 0⟩
private def Row7N.get (r : Row7N) (c : Fin 7) : Nat :=
  match c.val with | 0 => r.n0 | 1 => r.n1 | 2 => r.n2 | 3 => r.n3 | 4 => r.n4 | 5 => r.n5 | _ => r.n6
private def Row7N.addAll (w : Nat) (r : Row7N) : Row7N :=
  ⟨r.n0+w, r.n1+w, r.n2+w, r.n3+w, r.n4+w, r.n5+w, r.n6+w⟩
private def Row7N.addPair (c : Fin 7) (w : Nat) (r : Row7N) : Row7N :=
  match c.val with
  | 0 => ⟨r.n0+w, r.n1+w, r.n2, r.n3, r.n4, r.n5, r.n6⟩
  | 1 => ⟨r.n0, r.n1+w, r.n2+w, r.n3, r.n4, r.n5, r.n6⟩
  | 2 => ⟨r.n0, r.n1, r.n2+w, r.n3+w, r.n4, r.n5, r.n6⟩
  | 3 => ⟨r.n0, r.n1, r.n2, r.n3+w, r.n4+w, r.n5, r.n6⟩
  | 4 => ⟨r.n0, r.n1, r.n2, r.n3, r.n4+w, r.n5+w, r.n6⟩
  | 5 => ⟨r.n0, r.n1, r.n2, r.n3, r.n4, r.n5+w, r.n6+w⟩
  | _ => ⟨r.n0+w, r.n1, r.n2, r.n3, r.n4, r.n5, r.n6+w⟩
private def Row7N.add (a b : Row7N) : Row7N :=
  ⟨a.n0+b.n0, a.n1+b.n1, a.n2+b.n2, a.n3+b.n3, a.n4+b.n4, a.n5+b.n5, a.n6+b.n6⟩
private def Row7N.geMask (r : Row7N) (fr : Nat) (D : Nat) : Bool :=
  (!Nat.beq (Nat.land fr 1) 0  || Nat.ble D r.n0) &&
  (!Nat.beq (Nat.land fr 2) 0  || Nat.ble D r.n1) &&
  (!Nat.beq (Nat.land fr 4) 0  || Nat.ble D r.n2) &&
  (!Nat.beq (Nat.land fr 8) 0  || Nat.ble D r.n3) &&
  (!Nat.beq (Nat.land fr 16) 0 || Nat.ble D r.n4) &&
  (!Nat.beq (Nat.land fr 32) 0 || Nat.ble D r.n5) &&
  (!Nat.beq (Nat.land fr 64) 0 || Nat.ble D r.n6)

private structure Grid49 where
  r0 : Row7N
  r1 : Row7N
  r2 : Row7N
  r3 : Row7N
  r4 : Row7N
  r5 : Row7N
  r6 : Row7N

private def Grid49.zero : Grid49 :=
  ⟨Row7N.zero, Row7N.zero, Row7N.zero, Row7N.zero, Row7N.zero, Row7N.zero, Row7N.zero⟩
private def Grid49.row (g : Grid49) (r : Fin 7) : Row7N :=
  match r.val with | 0 => g.r0 | 1 => g.r1 | 2 => g.r2 | 3 => g.r3 | 4 => g.r4 | 5 => g.r5 | _ => g.r6
private def Grid49.get (g : Grid49) (r c : Fin 7) : Nat := (g.row r).get c
private def Grid49.add (a b : Grid49) : Grid49 :=
  ⟨a.r0.add b.r0, a.r1.add b.r1, a.r2.add b.r2, a.r3.add b.r3, a.r4.add b.r4, a.r5.add b.r5, a.r6.add b.r6⟩
private def Grid49.addRowPair (r : Fin 7) (f : Row7N → Row7N) (g : Grid49) : Grid49 :=
  match r.val with
  | 0 => ⟨f g.r0, f g.r1, g.r2, g.r3, g.r4, g.r5, g.r6⟩
  | 1 => ⟨g.r0, f g.r1, f g.r2, g.r3, g.r4, g.r5, g.r6⟩
  | 2 => ⟨g.r0, g.r1, f g.r2, f g.r3, g.r4, g.r5, g.r6⟩
  | 3 => ⟨g.r0, g.r1, g.r2, f g.r3, f g.r4, g.r5, g.r6⟩
  | 4 => ⟨g.r0, g.r1, g.r2, g.r3, f g.r4, f g.r5, g.r6⟩
  | 5 => ⟨g.r0, g.r1, g.r2, g.r3, g.r4, f g.r5, f g.r6⟩
  | _ => ⟨f g.r0, g.r1, g.r2, g.r3, g.r4, g.r5, f g.r6⟩
private def Grid49.mapRows (f : Row7N → Row7N) (g : Grid49) : Grid49 :=
  ⟨f g.r0, f g.r1, f g.r2, f g.r3, f g.r4, f g.r5, f g.r6⟩
private def Grid49.geMask (g : Grid49) (F : Nat) (D : Nat) : Bool :=
  g.r0.geMask (Nat.land F 127) D &&
  g.r1.geMask (Nat.land (Nat.shiftRight F 7) 127) D &&
  g.r2.geMask (Nat.land (Nat.shiftRight F 14) 127) D &&
  g.r3.geMask (Nat.land (Nat.shiftRight F 21) 127) D &&
  g.r4.geMask (Nat.land (Nat.shiftRight F 28) 127) D &&
  g.r5.geMask (Nat.land (Nat.shiftRight F 35) 127) D &&
  g.r6.geMask (Nat.land (Nat.shiftRight F 42) 127) D

private inductive Constr2D where
  | sq (r c : Fin 7)
  | row (r : Fin 7)
  | col (c : Fin 7)
  | all

private abbrev cS := Constr2D.sq
private abbrev cR := Constr2D.row
private abbrev cC := Constr2D.col
private abbrev cA := Constr2D.all

private def Constr2D.rhs : Constr2D → Nat
  | .sq _ _ => 1 | .row _ => 3 | .col _ => 3 | .all => 10

private def Constr2D.mem : Constr2D → Fin 7 → Fin 7 → Bool
  | .sq r c, r0, c0 => (r0 == r || r0 == next7 r) && (c0 == c || c0 == next7 c)
  | .row r, r0, _ => r0 == r || r0 == next7 r
  | .col c, _, c0 => c0 == c || c0 == next7 c
  | .all, _, _ => true

private def Grid49.addConstr (ct : Constr2D) (w : Nat) (g : Grid49) : Grid49 :=
  match ct with
  | .sq r c => g.addRowPair r (Row7N.addPair c w)
  | .row r => g.addRowPair r (Row7N.addAll w)
  | .col c => g.mapRows (Row7N.addPair c w)
  | .all => g.mapRows (Row7N.addAll w)

private def accumGrid : List (Constr2D × Nat) → Grid49
  | [] => Grid49.zero
  | (ct, w) :: rest => (accumGrid rest).addConstr ct w

private def rhsSum : List (Constr2D × Nat) → Nat
  | [] => 0
  | (ct, w) :: rest => w * ct.rhs + rhsSum rest

private def checkFarkas2D (F : Nat) (cert : Nat × List (Constr2D × Nat)) : Bool :=
  let (D, terms) := cert
  Nat.blt 0 D && Nat.blt (rhsSum terms) (10 * D) && (accumGrid terms).geMask F D

private def checkFarkas3D (CR CL : Nat)
    (cert : Nat × List (Constr2D × Nat) × List (Constr2D × Nat)) : Bool :=
  let (D, t0, t1) := cert
  let g0 := accumGrid t0
  let g1 := accumGrid t1
  let gMid := g0.add g1
  Nat.blt 0 D && Nat.blt (rhsSum t0 + rhsSum t1) (14 * D) &&
  g0.geMask CR D && gMid.geMask 0 D && g1.geMask CL D

private lemma Row7N.get_zero : ∀ c : Fin 7, Row7N.zero.get c = 0
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ => rfl
private lemma Row7N.get_addAll (w : Nat) (row : Row7N) : ∀ c : Fin 7,
    (row.addAll w).get c = row.get c + w
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ => rfl
private lemma Row7N.get_add (a b : Row7N) : ∀ c : Fin 7, (a.add b).get c = a.get c + b.get c
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ => rfl

private lemma Row7N.get_addPair (c : Fin 7) (w : Nat) (row : Row7N) (c0 : Fin 7) :
    (row.addPair c w).get c0 = row.get c0 + if (c0 == c || c0 == next7 c) then w else 0 := by
  revert c c0
  exact fin7_cases
    (fin7_cases rfl rfl rfl rfl rfl rfl rfl) (fin7_cases rfl rfl rfl rfl rfl rfl rfl)
    (fin7_cases rfl rfl rfl rfl rfl rfl rfl) (fin7_cases rfl rfl rfl rfl rfl rfl rfl)
    (fin7_cases rfl rfl rfl rfl rfl rfl rfl) (fin7_cases rfl rfl rfl rfl rfl rfl rfl)
    (fin7_cases rfl rfl rfl rfl rfl rfl rfl)

private lemma Grid49.get_zero : ∀ r c : Fin 7, Grid49.zero.get r c = 0
  | ⟨0, _⟩, c | ⟨1, _⟩, c | ⟨2, _⟩, c | ⟨3, _⟩, c | ⟨4, _⟩, c | ⟨5, _⟩, c | ⟨6, _⟩, c => Row7N.get_zero c

private lemma Grid49.get_add (a b : Grid49) : ∀ r c : Fin 7,
    (a.add b).get r c = a.get r c + b.get r c
  | ⟨0, _⟩, c | ⟨1, _⟩, c | ⟨2, _⟩, c | ⟨3, _⟩, c | ⟨4, _⟩, c | ⟨5, _⟩, c | ⟨6, _⟩, c => Row7N.get_add _ _ c

private lemma Grid49.row_addRowPair (f : Row7N → Row7N) (g : Grid49) (r r0 : Fin 7) :
    (g.addRowPair r f).row r0 = if (r0 == r || r0 == next7 r) then f (g.row r0) else g.row r0 := by
  revert r r0
  exact fin7_cases
    (fin7_cases rfl rfl rfl rfl rfl rfl rfl) (fin7_cases rfl rfl rfl rfl rfl rfl rfl)
    (fin7_cases rfl rfl rfl rfl rfl rfl rfl) (fin7_cases rfl rfl rfl rfl rfl rfl rfl)
    (fin7_cases rfl rfl rfl rfl rfl rfl rfl) (fin7_cases rfl rfl rfl rfl rfl rfl rfl)
    (fin7_cases rfl rfl rfl rfl rfl rfl rfl)

private lemma Grid49.get_addRowPair (r : Fin 7) (f : Row7N → Row7N) (g : Grid49) (r0 c0 : Fin 7) :
    (g.addRowPair r f).get r0 c0 =
      if (r0 == r || r0 == next7 r) then (f (g.row r0)).get c0 else g.get r0 c0 := by
  simp only [Grid49.get, Grid49.row_addRowPair]
  cases (r0 == r || r0 == next7 r) <;> rfl

private lemma Grid49.get_mapRows (f : Row7N → Row7N) (g : Grid49) : ∀ r0 c0 : Fin 7,
    (g.mapRows f).get r0 c0 = (f (g.row r0)).get c0
  | ⟨0, _⟩, _ | ⟨1, _⟩, _ | ⟨2, _⟩, _ | ⟨3, _⟩, _ | ⟨4, _⟩, _ | ⟨5, _⟩, _ | ⟨6, _⟩, _ => rfl

private lemma Grid49.get_addConstr (ct : Constr2D) (w : Nat) (g : Grid49) (r0 c0 : Fin 7) :
    (g.addConstr ct w).get r0 c0 = g.get r0 c0 + if ct.mem r0 c0 then w else 0 := by
  cases ct with
  | sq r c =>
    rw [Grid49.addConstr, Grid49.get_addRowPair, Row7N.get_addPair, Constr2D.mem]
    change (if (r0 == r || r0 == next7 r) = true then g.get r0 c0 + (if (c0 == c || c0 == next7 c) = true then w else 0) else g.get r0 c0) = _
    cases (r0 == r || r0 == next7 r) <;> cases (c0 == c || c0 == next7 c) <;> simp
  | row r =>
    rw [Grid49.addConstr, Grid49.get_addRowPair, Row7N.get_addAll, Constr2D.mem]
    change (if (r0 == r || r0 == next7 r) = true then g.get r0 c0 + w else g.get r0 c0) = _
    cases (r0 == r || r0 == next7 r) <;> simp
  | col c => rw [Grid49.addConstr, Grid49.get_mapRows, Row7N.get_addPair, Constr2D.mem]; rfl
  | all => rw [Grid49.addConstr, Grid49.get_mapRows, Row7N.get_addAll, Constr2D.mem]; rfl

private lemma Grid49.geMask_sound {g : Grid49} {F : Nat} {D : Nat}
    (h : g.geMask F D = true) (r c : Fin 7) (hF : get49 F r c = false) :
    D ≤ g.get r c := by
  have hbit7 : ∀ (x : Nat) (k : Fin 7), x < 128 →
      (!((x &&& (1 <<< k.val)) == 0)) = x.testBit k.val := by
    intro x k hx
    have hall : ∀ (y : Fin 128) (j : Fin 7), (!((y.val &&& (1 <<< j.val)) == 0)) = y.val.testBit j.val := by
      decide
    exact hall ⟨x, hx⟩ k
  have hrow : ∀ (row : Row7N) (fr : Nat), fr < 128 → row.geMask fr D = true →
      ∀ col : Fin 7, fr.testBit col.val = false → D ≤ row.get col := by
    intro row fr hfr hrg
    cases row
    unfold Row7N.geMask at hrg
    simp only [beq_eq, land_eq, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq] at hrg
    have step : ∀ {k : Fin 7} {n : Nat},
        ((!((fr &&& (1 <<< k.val)) == 0)) = true ∨ D ≤ n) → fr.testBit k.val = false → D ≤ n := by
      intro k n h1 h2
      rw [hbit7 fr k hfr, h2] at h1
      exact h1.resolve_left (by decide)
    exact fun
      | ⟨0, _⟩ => step (k := 0) hrg.1.1.1.1.1.1 | ⟨1, _⟩ => step (k := 1) hrg.1.1.1.1.1.2
      | ⟨2, _⟩ => step (k := 2) hrg.1.1.1.1.2   | ⟨3, _⟩ => step (k := 3) hrg.1.1.1.2
      | ⟨4, _⟩ => step (k := 4) hrg.1.1.2       | ⟨5, _⟩ => step (k := 5) hrg.1.2
      | ⟨6, _⟩ => step (k := 6) hrg.2
  cases g
  unfold Grid49.geMask at h
  simp only [Bool.and_eq_true] at h
  have hF' : (row49 F r).testBit c.val = false := by rw [row49_testBit]; exact hF
  clear hF
  revert r hF'
  exact fun
    | ⟨0, _⟩ => hrow _ (row49 F 0) (row49_lt F 0) h.1.1.1.1.1.1 c
    | ⟨1, _⟩ => hrow _ (row49 F 1) (row49_lt F 1) h.1.1.1.1.1.2 c
    | ⟨2, _⟩ => hrow _ (row49 F 2) (row49_lt F 2) h.1.1.1.1.2 c
    | ⟨3, _⟩ => hrow _ (row49 F 3) (row49_lt F 3) h.1.1.1.2 c
    | ⟨4, _⟩ => hrow _ (row49 F 4) (row49_lt F 4) h.1.1.2 c
    | ⟨5, _⟩ => hrow _ (row49 F 5) (row49_lt F 5) h.1.2 c
    | ⟨6, _⟩ => hrow _ (row49 F 6) (row49_lt F 6) h.2 c

private lemma constr2D_sq_eq : ∀ r c r0 c0 : Fin 7,
    (Constr2D.sq r c).mem r0 c0 = get49 (sq22 ⟨r.val * 7 + c.val, by omega⟩) r0 c0 := by decide

private lemma constr2D_row_card_le (r : Fin 7) {B : Finset (ZMod 7 × ZMod 7)}
    (hB : (C7 ⊠ C7).IsIndepSet (B : Set (ZMod 7 × ZMod 7))) :
    (∑ p ∈ B, if (Constr2D.row r).mem (ofZ7 p.1) (ofZ7 p.2) then 1 else 0) ≤ 3 := by
  have hle := (row_indep_adj hB r).2
  have hne : r ≠ next7 r := (by decide : ∀ x : Fin 7, x ≠ next7 x) r
  have h1 : (∑ p ∈ B, if (Constr2D.row r).mem (ofZ7 p.1) (ofZ7 p.2) then 1 else 0) =
      ∑ p : Fin 7 × Fin 7, if p.1 = r ∨ p.1 = next7 r then (get49 (ofFinset49 B) p.1 p.2).toNat else 0 := by
    have h2 : (∑ p ∈ B, if (Constr2D.row r).mem (ofZ7 p.1) (ofZ7 p.2) then 1 else 0) =
        ∑ q : ZMod 7 × ZMod 7, if q ∈ B then (if (Constr2D.row r).mem (ofZ7 q.1) (ofZ7 q.2) then 1 else 0) else 0 := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [h2, ← Equiv.sum_comp fin7SqEquivZ7Sq]
    refine Finset.sum_congr rfl fun ⟨r', c'⟩ _ => ?_
    simp only [fin7SqEquivZ7Sq, Equiv.coe_fn_mk, ofZ7_toZ7, Constr2D.mem, Bool.or_eq_true, beq_iff_eq]
    by_cases hmem : (toZ7 r', toZ7 c') ∈ B
    · have hb' := (get49_ofFinset B r' c').mpr hmem
      by_cases hr : r' = r ∨ r' = next7 r <;> simp [hmem, hb', hr]
    · have hb' : get49 (ofFinset49 B) r' c' = false :=
        Bool.eq_false_iff.mpr fun h => hmem ((get49_ofFinset B r' c').mp h)
      simp [hmem, hb']
  rw [h1, Fintype.sum_prod_type]
  have hstep : (∑ x : Fin 7, ∑ y : Fin 7, if x = r ∨ x = next7 r then (get49 (ofFinset49 B) x y).toNat else 0) =
      ∑ x : Fin 7, if x = r ∨ x = next7 r then (∑ y : Fin 7, (get49 (ofFinset49 B) x y).toNat) else 0 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x = r ∨ x = next7 r <;> simp [hx]
  rw [hstep]
  have hdisj : Disjoint ({r} : Finset (Fin 7)) {next7 r} := Finset.disjoint_singleton.mpr hne
  have hfilt : Finset.univ.filter (fun x : Fin 7 => x = r ∨ x = next7 r) = {r} ∪ {next7 r} := by
    ext x; simp
  rw [← Finset.sum_filter, hfilt, Finset.sum_union hdisj, Finset.sum_singleton, Finset.sum_singleton]
  simpa only [pop7_row49_eq_sum] using hle

private lemma constr2D_card_le (ct : Constr2D) {B : Finset (ZMod 7 × ZMod 7)}
    (hB : (C7 ⊠ C7).IsIndepSet (B : Set (ZMod 7 × ZMod 7))) :
    (∑ p ∈ B, if ct.mem (ofZ7 p.1) (ofZ7 p.2) then 1 else 0) ≤ ct.rhs := by
  cases ct with
  | sq r c =>
    let idx : Fin 49 := ⟨r.val * 7 + c.val, by omega⟩
    have hpop := sq22_card_le_one idx hB
    have hsum_eq : (∑ p ∈ B, if (Constr2D.sq r c).mem (ofZ7 p.1) (ofZ7 p.2) then 1 else 0) =
        pop49 (ofFinset49 B &&& sq22 idx) := by
      rw [pop49_eq_sum, ← Fintype.sum_prod_type']
      have h1 : (∑ p : Fin 7 × Fin 7, (get49 (ofFinset49 B &&& sq22 idx) p.1 p.2).toNat) =
          ∑ q : ZMod 7 × ZMod 7, if q ∈ B then (if get49 (sq22 idx) (ofZ7 q.1) (ofZ7 q.2) then 1 else 0) else 0 := by
        rw [← Equiv.sum_comp fin7SqEquivZ7Sq]
        refine Finset.sum_congr rfl fun ⟨r', c'⟩ _ => ?_
        rw [get49_and]
        simp only [fin7SqEquivZ7Sq, Equiv.coe_fn_mk, ofZ7_toZ7]
        by_cases hmem : (toZ7 r', toZ7 c') ∈ B
        · have hb' := (get49_ofFinset B r' c').mpr hmem
          cases hsq : get49 (sq22 idx) r' c' <;> simp [hmem, hb']
        · have hb' : get49 (ofFinset49 B) r' c' = false :=
            Bool.eq_false_iff.mpr fun h => hmem ((get49_ofFinset B r' c').mp h)
          simp [hmem, hb']
      rw [h1, Finset.sum_ite_mem, Finset.univ_inter]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [constr2D_sq_eq r c (ofZ7 p.1) (ofZ7 p.2)]
    rw [hsum_eq]; exact hpop
  | row r => exact constr2D_row_card_le r hB
  | col c =>
    let gSw : Aut2 := ⟨true, false, 0, false, 0⟩
    let B' := B.map gSw.toIso.toEquiv.toEmbedding
    have hB' : (C7 ⊠ C7).IsIndepSet (B' : Set (ZMod 7 × ZMod 7)) := isIndepSet_map_iso' gSw.toIso hB
    have hsum_eq : (∑ p ∈ B, if (Constr2D.col c).mem (ofZ7 p.1) (ofZ7 p.2) then 1 else 0) =
        ∑ q ∈ B', if (Constr2D.row c).mem (ofZ7 q.1) (ofZ7 q.2) then 1 else 0 := by
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun ⟨a, b⟩ _ => ?_
      have hg : gSw.toIso (a, b) = (b, a) := by
        have h0 : ∀ x : Fin 7, add7 x 0 = x := by decide
        exact Prod.ext
          (by change toZ7 (add7 (ofZ7 b) 0) = b; rw [h0, toZ7_ofZ7])
          (by change toZ7 (add7 (ofZ7 a) 0) = a; rw [h0, toZ7_ofZ7])
      simp only [Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv, hg, Constr2D.mem]; rfl
    rw [hsum_eq]
    exact constr2D_row_card_le c hB'
  | all =>
    simp only [Constr2D.mem, ↓reduceIte, Finset.sum_const, smul_eq_mul, mul_one, Constr2D.rhs]
    exact alpha_c7_pow2_le_internal hB

private lemma accumGrid_sum_le (terms : List (Constr2D × Nat)) {B : Finset (ZMod 7 × ZMod 7)}
    (hB : (C7 ⊠ C7).IsIndepSet (B : Set (ZMod 7 × ZMod 7))) :
    (∑ p ∈ B, (accumGrid terms).get (ofZ7 p.1) (ofZ7 p.2)) ≤ rhsSum terms := by
  induction terms with
  | nil => simp [accumGrid, rhsSum, Grid49.get_zero]
  | cons hd rest ih =>
    rcases hd with ⟨ct, w⟩
    simp only [accumGrid, rhsSum, Grid49.get_addConstr, Finset.sum_add_distrib]
    have hct : (∑ p ∈ B, if ct.mem (ofZ7 p.1) (ofZ7 p.2) then w else 0) =
        w * (∑ p ∈ B, if ct.mem (ofZ7 p.1) (ofZ7 p.2) then 1 else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => by split_ifs <;> simp
    rw [hct]
    have hle := Nat.mul_le_mul_left w (constr2D_card_le ct hB)
    omega

private lemma checkFarkas2D_sound {F : Nat} {cert : Nat × List (Constr2D × Nat)}
    {B : Finset (ZMod 7 × ZMod 7)} (hchk : checkFarkas2D F cert = true)
    (hB : (C7 ⊠ C7).IsIndepSet (B : Set (ZMod 7 × ZMod 7)))
    (hdisj : disjoint49 (ofFinset49 B) F = true) : B.card ≤ 9 := by
  rcases cert with ⟨D, terms⟩
  simp only [checkFarkas2D, Bool.and_eq_true, Nat.blt_eq] at hchk
  rcases hchk with ⟨⟨hDpos, hrhs⟩, hge⟩
  rw [disjoint49_iff (ofFinset49_lt B)] at hdisj
  have hlow : B.card * D ≤ ∑ p ∈ B, (accumGrid terms).get (ofZ7 p.1) (ofZ7 p.2) := by
    calc B.card * D = ∑ _p ∈ B, D := by simp
      _ ≤ ∑ p ∈ B, (accumGrid terms).get (ofZ7 p.1) (ofZ7 p.2) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hF : get49 F (ofZ7 p.1) (ofZ7 p.2) = false :=
          hdisj (ofZ7 p.1) (ofZ7 p.2) ((get49_ofFinset B (ofZ7 p.1) (ofZ7 p.2)).mpr (by simpa [toZ7_ofZ7] using hp))
        exact Grid49.geMask_sound hge (ofZ7 p.1) (ofZ7 p.2) hF
  have hup := accumGrid_sum_le terms hB
  have hlt : B.card * D < 10 * D := lt_of_le_of_lt (le_trans hlow hup) hrhs
  have hcard_lt : B.card < 10 := Nat.lt_of_mul_lt_mul_right hlt
  omega

private lemma checkFarkas3D_sound {CR CL : Nat}
    {cert : Nat × List (Constr2D × Nat) × List (Constr2D × Nat)}
    {S4 S5 S6 : Finset (ZMod 7 × ZMod 7)} (hchk : checkFarkas3D CR CL cert = true)
    (hd45 : Disjoint S4 S5) (h45 : (C7 ⊠ C7).IsIndepSet ((S4 ∪ S5 : Finset _) : Set _))
    (hd56 : Disjoint S5 S6) (h56 : (C7 ⊠ C7).IsIndepSet ((S5 ∪ S6 : Finset _) : Set _))
    (hdisj4 : disjoint49 (ofFinset49 S4) CR = true)
    (hdisj6 : disjoint49 (ofFinset49 S6) CL = true) :
    S4.card + S5.card + S6.card ≤ 13 := by
  rcases cert with ⟨D, t0, t1⟩
  simp only [checkFarkas3D, Bool.and_eq_true, Nat.blt_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨hDpos, hrhs⟩, hge0⟩, hgeMid⟩, hge1⟩
  rw [disjoint49_iff (ofFinset49_lt S4)] at hdisj4
  rw [disjoint49_iff (ofFinset49_lt S6)] at hdisj6
  have hup0 := accumGrid_sum_le t0 h45
  have hup1 := accumGrid_sum_le t1 h56
  rw [Finset.sum_union hd45] at hup0
  rw [Finset.sum_union hd56] at hup1
  have hlow4 : S4.card * D ≤ ∑ p ∈ S4, (accumGrid t0).get (ofZ7 p.1) (ofZ7 p.2) := by
    calc S4.card * D = ∑ _p ∈ S4, D := by simp
      _ ≤ _ := Finset.sum_le_sum fun p hp =>
        Grid49.geMask_sound hge0 (ofZ7 p.1) (ofZ7 p.2)
          (hdisj4 _ _ ((get49_ofFinset S4 _ _).mpr (by simpa [toZ7_ofZ7] using hp)))
  have hlow5 : S5.card * D ≤
      (∑ p ∈ S5, (accumGrid t0).get (ofZ7 p.1) (ofZ7 p.2)) +
      (∑ p ∈ S5, (accumGrid t1).get (ofZ7 p.1) (ofZ7 p.2)) := by
    rw [← Finset.sum_add_distrib]
    calc S5.card * D = ∑ _p ∈ S5, D := by simp
      _ ≤ ∑ p ∈ S5, ((accumGrid t0).add (accumGrid t1)).get (ofZ7 p.1) (ofZ7 p.2) :=
        Finset.sum_le_sum fun p _ => Grid49.geMask_sound hgeMid (ofZ7 p.1) (ofZ7 p.2) (get49_zero _ _)
      _ = _ := Finset.sum_congr rfl fun p _ => Grid49.get_add _ _ _ _
  have hlow6 : S6.card * D ≤ ∑ p ∈ S6, (accumGrid t1).get (ofZ7 p.1) (ofZ7 p.2) := by
    calc S6.card * D = ∑ _p ∈ S6, D := by simp
      _ ≤ _ := Finset.sum_le_sum fun p hp =>
        Grid49.geMask_sound hge1 (ofZ7 p.1) (ofZ7 p.2)
          (hdisj6 _ _ ((get49_ofFinset S6 _ _).mpr (by simpa [toZ7_ofZ7] using hp)))
  have htot : (S4.card + S5.card + S6.card) * D < 14 * D := by
    have hsum_le : (S4.card + S5.card + S6.card) * D ≤ rhsSum t0 + rhsSum t1 := by
      have : (S4.card + S5.card + S6.card) * D = S4.card * D + S5.card * D + S6.card * D := by ring
      omega
    exact lt_of_le_of_lt hsum_le hrhs
  have hlt : S4.card + S5.card + S6.card < 14 := Nat.lt_of_mul_lt_mul_right htot
  omega

/-! ## Section 6: Canonical Subset Generators & Certificate Tables (P1+P3, P2, P4, P5) -/

private def subsetsOfList : List (Fin 7 × Fin 7) → Nat → List Nat
  | _, 0 => [0]
  | [], _ + 1 => []
  | (r, c) :: rest, k + 1 =>
      (subsetsOfList rest k).map (fun m => set49 m r c) ++ subsetsOfList rest (k + 1)

private lemma mem_subsetsOfList (pts : List (Fin 7 × Fin 7)) (hnd : pts.Nodup) :
    ∀ (X : Nat), X < 2 ^ 49 → (∀ r c : Fin 7, get49 X r c = true → (r, c) ∈ pts) →
      X ∈ subsetsOfList pts (pop49 X) := by
  induction pts with
  | nil =>
    intro X hX h
    have hX0 : X = 0 := by
      apply ext49 hX (by decide)
      intro r c
      cases hx : get49 X r c
      · exact (get49_zero r c).symm
      · exact absurd (h r c hx) (by simp)
    subst hX0; simp [subsetsOfList, show pop49 0 = 0 by decide]
  | cons p0 rest ih =>
    rcases p0 with ⟨r0, c0⟩
    have ⟨hp0_not_rest, hrest_nd⟩ := List.nodup_cons.mp hnd
    intro X hX hXsub
    cases hXp : get49 X r0 c0
    · have hXrest : ∀ r c : Fin 7, get49 X r c = true → (r, c) ∈ rest := by
        intro r c h
        rcases List.mem_cons.mp (hXsub r c h) with heq | hr
        · injection heq with h1 h2; subst h1 h2; rw [hXp] at h; exact absurd h (by decide)
        · exact hr
      have hmem := ih hrest_nd X hX hXrest
      cases hk : pop49 X
      · rw [hk] at hmem
        simp only [subsetsOfList, List.mem_cons, List.not_mem_nil, or_false] at hmem ⊢
        exact hmem
      · rw [hk] at hmem
        exact List.mem_append_right _ hmem
    · let X' := diff49 X (bit49 r0 c0)
      have hX'lt : X' < 2 ^ 49 := diff49_lt hX
      have hX'get : ∀ r c : Fin 7, get49 X' r c = (if r = r0 ∧ c = c0 then false else get49 X r c) := by
        intro r c; unfold X'; rw [get49_diff]
        have hb : get49 (bit49 r0 c0) r c = decide (r = r0 ∧ c = c0) := testBit_bit49 r0 c0 r c
        rw [hb]; split_ifs with h <;> simp [h]
      have hXeq : X = set49 X' r0 c0 := by
        apply ext49 hX (set49_lt hX'lt r0 c0)
        intro r c; rw [get49_set, hX'get]
        split_ifs with h
        · exact h.1 ▸ h.2 ▸ hXp
        · rfl
      have hpop : pop49 X = pop49 X' + 1 := by
        rw [hXeq]; exact pop49_set49_of_false (by rw [hX'get]; simp)
      have hX'rest : ∀ r c : Fin 7, get49 X' r c = true → (r, c) ∈ rest := by
        intro r c h
        rw [hX'get] at h
        split_ifs at h with heq
        rcases List.mem_cons.mp (hXsub r c h) with heq2 | hr
        · injection heq2 with h1 h2; exact absurd ⟨h1, h2⟩ heq
        · exact hr
      have hmem := ih hrest_nd X' hX'lt hX'rest
      rw [hpop]
      exact List.mem_append_left _ (List.mem_map.mpr ⟨X', hmem, hXeq.symm⟩)

private def halves5 (k : Fin 3) : List Nat :=
  (subsetsOfList (repPtsList k).tail 4).map (fun m => set49 m 0 3)

private def subs4 (k : Fin 3) : List Nat :=
  subsetsOfList (repPtsList k) 4

private lemma mem_halves5 {k : Fin 3} {X : Nat} (hX : X < 2 ^ 49)
    (hXrep : subset49 X (rep k) = true) (hXpop : pop49 X = 5) (h03 : get49 X 0 3 = true) :
    X ∈ halves5 k := by
  have hhead : repPtsList k = (0, 3) :: (repPtsList k).tail :=
    match k with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl
  have hnd := repPtsList_nodup k
  rw [hhead] at hnd
  have ⟨_, hrest_nd⟩ := List.nodup_cons.mp hnd
  let X' := diff49 X (bit49 0 3)
  have hX'lt : X' < 2 ^ 49 := diff49_lt hX
  have hX'get : ∀ r c : Fin 7, get49 X' r c = (if r = 0 ∧ c = 3 then false else get49 X r c) := by
    intro r c; unfold X'; rw [get49_diff]
    have hb : get49 (bit49 0 3) r c = decide (r = 0 ∧ c = 3) := testBit_bit49 0 3 r c
    rw [hb]; split_ifs with h <;> simp [h]
  have hXeq : X = set49 X' 0 3 := by
    apply ext49 hX (set49_lt hX'lt 0 3)
    intro r c; rw [get49_set, hX'get]
    split_ifs with h
    · exact h.1 ▸ h.2 ▸ h03
    · rfl
  have hX'pop : pop49 X' = 4 := by
    have hpop : pop49 X = pop49 X' + 1 := by
      rw [hXeq]; exact pop49_set49_of_false (by rw [hX'get]; simp)
    omega
  have hX'rest : ∀ r c : Fin 7, get49 X' r c = true → (r, c) ∈ (repPtsList k).tail := by
    intro r c h
    rw [hX'get] at h
    split_ifs at h with heq
    have hmem : (r, c) ∈ repPtsList k := (rep_mem_iff k r c).mp ((subset49_iff hX).mp hXrep r c h)
    rw [hhead] at hmem
    rcases List.mem_cons.mp hmem with heq2 | hr
    · injection heq2 with h1 h2; exact absurd ⟨h1, h2⟩ heq
    · exact hr
  have hmem := mem_subsetsOfList _ hrest_nd X' hX'lt hX'rest
  rw [hX'pop] at hmem
  exact List.mem_map.mpr ⟨X', hmem, hXeq.symm⟩

private lemma mem_subs4 {k : Fin 3} {X : Nat} (hX : X < 2 ^ 49)
    (hXrep : subset49 X (rep k) = true) (hXpop : pop49 X = 4) :
    X ∈ subs4 k := by
  have hmem := mem_subsetsOfList (repPtsList k) (repPtsList_nodup k) X hX
    (fun r c h => (rep_mem_iff k r c).mp ((subset49_iff hX).mp hXrep r c h))
  rw [hXpop] at hmem
  exact hmem

private def near4 (k : Fin 3) : List (Fin 3 × Aut2 × Nat) := nearK k 4
private def near5 (k : Fin 3) : List (Fin 3 × Aut2 × Nat) := nearK k 5
private def near6 (k : Fin 3) : List (Fin 3 × Aut2 × Nat) := nearK k 6

private lemma mem_near_of_subset {k : Fin 3} {m : Nat} {X : Nat}
    {k0 : Fin 3} {g : Aut2} (hX : X < 2 ^ 49) (hsr : k0 ≠ 2 ∨ g.sr = false)
    (hXrep : subset49 X (rep k) = true) (hXB : subset49 X (g.applyMask (rep k0)) = true) (hm : m ≤ pop49 X) :
    (k0, g, g.applyMask (rep k0)) ∈ nearK k m := by
  refine mem_nearK hsr ?_
  have hsub : subset49 X ((g.applyMask (rep k0)) &&& (rep k)) = true := by
    rw [subset49_iff hX] at hXB hXrep ⊢
    intro r c hx; rw [get49_and, hXB r c hx, hXrep r c hx]; rfl
  exact hm.trans (subset49_pop_le hX hsub)

private inductive SqCert where
  | pop3 : SqCert
  | sq3 (a b c : Fin 49) : SqCert
  | splitL1 (covs : List (Fin 49 × Fin 49 × Fin 49)) : SqCert

private def checkSqCase (k : Fin 3) (nL nR : List (Fin 3 × Aut2 × Nat))
    (S2 : Nat) (cert : SqCert) : Bool :=
  seqN (diff49 (rep k) S2) fun S3 =>
  match cert with
  | .pop3 =>
      let CL := (c2Tree k).getAux (repBits k) S2
      let CR := (c2Tree k).getAux (repBits k) S3
      Nat.ble (pop49 (not49 (Nat.lor CL CR))) 3
  | .sq3 a b c =>
      let CL := (c2Tree k).getAux (repBits k) S2
      let CR := (c2Tree k).getAux (repBits k) S3
      seqN (not49 (Nat.lor CL CR)) fun avail => checkAvailSq3 avail a b c
  | .splitL1 covs =>
      let L1 := nL.filter fun t => subset49 S2 t.2.2
      let R4 := nR.filter fun t => subset49 S3 t.2.2
      L1.all fun t1 =>
        seqN (diff49 (rep t1.1) (t1.2.1.inv.applyMask S2)) fun y1Canon =>
        seqN (t1.2.1.applyMask ((c1Tree t1.1).getAux (repBits t1.1) y1Canon)) fun c1L =>
        R4.all fun t4 =>
          seqN (diff49 (rep t4.1) (t4.2.1.inv.applyMask S3)) fun y4Canon =>
          seqN (t4.2.1.applyMask ((c1Tree t4.1).getAux (repBits t4.1) y4Canon)) fun c1R =>
          seqN (not49 (Nat.lor c1L c1R)) fun avail =>
          Nat.ble (pop49 avail) 3 || covs.any fun (a, b, c) => checkAvailSq3 avail a b c

private def checkP4Case (k : Fin 3) (S2 : Nat) (cert : Nat × List (Constr2D × Nat)) : Bool :=
  seqN (diff49 (rep k) S2) fun S1 =>
  let CL := (c1Tree k).getAux (repBits k) S1
  let CR := (c2Tree k).getAux (repBits k) S2
  seqN (Nat.land CL CR) fun F => checkFarkas2D F cert

private inductive P5S0Cert where
  | leaf (f : Nat × List (Constr2D × Nat) × List (Constr2D × Nat))
  | splitS3 (f3s : List (Nat × List (Constr2D × Nat) × List (Constr2D × Nat)))

private inductive P5Cert where
  | root (f : Nat × List (Constr2D × Nat) × List (Constr2D × Nat))
  | splitS0 (f0s : List P5S0Cert)

private def checkP5Case (k : Fin 3) (n5 : List (Fin 3 × Aut2 × Nat))
    (S1 : Nat) (cert : P5Cert) : Bool :=
  seqN (diff49 (rep k) S1) fun S2 =>
  let CL := (c1Tree k).getAux (repBits k) S1
  let CR := (c1Tree k).getAux (repBits k) S2
  match cert with
  | .root f => checkFarkas3D CR CL f
  | .splitS0 f0s =>
      let L0 := n5.filter fun t => subset49 S1 t.2.2
      let R3 := n5.filter fun t => subset49 S2 t.2.2
      checkAll (fun t0 c0 =>
        seqN (diff49 t0.2.2 S1) fun d0 =>
        seqN (closedNbr49 d0) fun n0 =>
        match c0 with
        | .leaf f => checkFarkas3D CR n0 f
        | .splitS3 f3s =>
            checkAll (fun t3 f3 =>
              seqN (diff49 t3.2.2 S2) fun d3 =>
              seqN (closedNbr49 d3) fun n3 =>
              checkFarkas3D n3 n0 f3) R3 f3s) L0 f0s

private def p13Certs0 : List SqCert := __P13_0__
private def p13Certs1 : List SqCert := __P13_1__
private def p13Certs2 : List SqCert := __P13_2__

private def p2Certs0 : List SqCert := __P2_0__
private def p2Certs1 : List SqCert := __P2_1__
private def p2Certs2 : List SqCert := __P2_2__

private def p4Certs0 : List (Nat × List (Constr2D × Nat)) := __P4_0__
private def p4Certs1 : List (Nat × List (Constr2D × Nat)) := __P4_1__
private def p4Certs2 : List (Nat × List (Constr2D × Nat)) := __P4_2__

private def p5Certs0 : List P5Cert := __P5_0__
private def p5Certs1 : List P5Cert := __P5_1__
private def p5Certs2 : List P5Cert := __P5_2__

private def checkP13Orbit (k : Fin 3) (certs : List SqCert) : Bool :=
  let n5 := near5 k
  checkAll4 (checkSqCase k n5 n5) (halves5 k) certs

private def checkP2Orbit (k : Fin 3) (certs : List SqCert) : Bool :=
  let n4 := near4 k
  let n6 := near6 k
  checkAll4 (checkSqCase k n4 n6) (subs4 k) certs

private def checkP5Orbit (k : Fin 3) (certs : List P5Cert) : Bool :=
  let n5 := near5 k
  checkAll4 (checkP5Case k n5) (halves5 k) certs

private theorem checkP13_0_ok : checkP13Orbit 0 p13Certs0 = true := by rfl
private theorem checkP13_1_ok : checkP13Orbit 1 p13Certs1 = true := by rfl
private theorem checkP13_2_ok : checkP13Orbit 2 p13Certs2 = true := by rfl

private theorem checkP2_0_ok : checkP2Orbit 0 p2Certs0 = true := by rfl
private theorem checkP2_1_ok : checkP2Orbit 1 p2Certs1 = true := by rfl
private theorem checkP2_2_ok : checkP2Orbit 2 p2Certs2 = true := by rfl

private theorem checkP4_0_ok : checkAll4 (checkP4Case 0) (subs4 0) p4Certs0 = true := by rfl
private theorem checkP4_1_ok : checkAll4 (checkP4Case 1) (subs4 1) p4Certs1 = true := by rfl
private theorem checkP4_2_ok : checkAll4 (checkP4Case 2) (subs4 2) p4Certs2 = true := by rfl

private theorem checkP5_0_ok : checkP5Orbit 0 p5Certs0 = true := by rfl
private theorem checkP5_1_ok : checkP5Orbit 1 p5Certs1 = true := by rfl
private theorem checkP5_2_ok : checkP5Orbit 2 p5Certs2 = true := by rfl

/-! ## Section 7: Refutation of All 4 Centered Profile Families -/

private structure CubeSlices where
  s : ZMod 7 → Finset (ZMod 7 × ZMod 7)
  disj : ∀ i : ZMod 7, Disjoint (s i) (s (i + 1))
  indep : ∀ i : ZMod 7, (C7 ⊠ C7).IsIndepSet ((s i ∪ s (i + 1) : Finset _) : Set _)

private def CubeSlices.ofIndep {S : Finset (ZMod 7 × (ZMod 7 × ZMod 7))}
    (hS : (C7 ⊠ (C7 ⊠ C7)).IsIndepSet (S : Set _)) : CubeSlices where
  s := fun i => (S.filter fun p => p.1 = i).image Prod.snd
  disj := fun i => by
    rw [Finset.disjoint_left]
    intro w h1 h2
    simp only [Finset.mem_image, Finset.mem_filter] at h1 h2
    obtain ⟨⟨a1, w1⟩, ⟨h1', ha1⟩, hw1⟩ := h1
    obtain ⟨⟨a2, w2⟩, ⟨h2', ha2⟩, hw2⟩ := h2
    dsimp only at ha1 ha2 hw1 hw2
    rw [ha1, hw1] at h1'
    rw [ha2, hw2] at h2'
    have hadj := c7_adj_add_one i
    have hne : (i, w) ≠ (i + 1, w) := fun h => hadj.ne (congrArg Prod.fst h)
    exact hS h1' h2' hne ⟨hne, Or.inr hadj, Or.inl rfl⟩
  indep := fun i => by
    intro u hu v hv huv hH
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hu hv
    have hu' : ∃ a : ZMod 7, (a = i ∨ a = i + 1) ∧ (a, u) ∈ S := by
      rcases hu with ⟨⟨a, u1⟩, ⟨h, ha⟩, hu1⟩ | ⟨⟨a, u1⟩, ⟨h, ha⟩, hu1⟩
      · dsimp only at ha hu1; subst hu1; exact ⟨a, Or.inl ha, h⟩
      · dsimp only at ha hu1; subst hu1; exact ⟨a, Or.inr ha, h⟩
    have hv' : ∃ b : ZMod 7, (b = i ∨ b = i + 1) ∧ (b, v) ∈ S := by
      rcases hv with ⟨⟨b, v1⟩, ⟨h, hb⟩, hv1⟩ | ⟨⟨b, v1⟩, ⟨h, hb⟩, hv1⟩
      · dsimp only at hb hv1; subst hv1; exact ⟨b, Or.inl hb, h⟩
      · dsimp only at hb hv1; subst hv1; exact ⟨b, Or.inr hb, h⟩
    rcases hu' with ⟨a, ha, hau⟩; rcases hv' with ⟨b, hb, hbv⟩
    have hab : a = b ∨ C7.Adj a b := by
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
      · exact Or.inl rfl
      · exact Or.inr (c7_adj_add_one i)
      · exact Or.inr (c7_adj_add_one i).symm
      · exact Or.inl rfl
    have hne : (a, u) ≠ (b, v) := fun h => huv (congrArg Prod.snd h)
    exact hS hau hbv hne ⟨hne, hab, Or.inr hH⟩

private lemma CubeSlices.sum_card {S : Finset (ZMod 7 × (ZMod 7 × ZMod 7))}
    (hS : (C7 ⊠ (C7 ⊠ C7)).IsIndepSet (S : Set _)) :
    (∑ i : ZMod 7, ((CubeSlices.ofIndep hS).s i).card) = S.card := by
  have hc : ∀ i : ZMod 7, ((CubeSlices.ofIndep hS).s i).card = (S.filter fun p => p.1 = i).card := by
    intro i
    apply Finset.card_image_of_injOn
    rintro ⟨a1, b1⟩ h1 ⟨a2, b2⟩ h2 hb
    simp only [Finset.mem_coe, Finset.mem_filter] at h1 h2
    exact Prod.ext (h1.2.trans h2.2.symm) hb
  simp_rw [hc]
  exact (Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := S) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)).symm

private def CubeSlices.shift (cs : CubeSlices) (t : ZMod 7) : CubeSlices where
  s := fun i => cs.s (i + t)
  disj := fun i => by simpa [add_assoc, add_comm t 1] using cs.disj (i + t)
  indep := fun i => by simpa [add_assoc, add_comm t 1] using cs.indep (i + t)

private def CubeSlices.rev (cs : CubeSlices) (c : ZMod 7) : CubeSlices where
  s := fun i => cs.s (c - i)
  disj := fun i => by
    have h := cs.disj (c - i - 1)
    rw [sub_add_cancel] at h
    have heq2 : c - (i + 1) = c - i - 1 := by ring
    rw [heq2]; exact h.symm
  indep := fun i => by
    have h := cs.indep (c - i - 1)
    rw [sub_add_cancel] at h
    have heq2 : c - (i + 1) = c - i - 1 := by ring
    rw [heq2, Finset.union_comm]; exact h

private def CubeSlices.mapAut2 (cs : CubeSlices) (g : Aut2) : CubeSlices where
  s := fun i => (cs.s i).map g.toIso.toEquiv.toEmbedding
  disj := fun i => Finset.disjoint_left.mpr fun x h1 h2 => by
    rcases Finset.mem_map.mp h1 with ⟨a, ha, rfl⟩
    rcases Finset.mem_map.mp h2 with ⟨b, hb, hab⟩
    exact Finset.disjoint_left.mp (cs.disj i) ha ((g.toIso.injective hab) ▸ hb)
  indep := fun i => by
    rw [← Finset.map_union]
    exact isIndepSet_map_iso' g.toIso (cs.indep i)

private lemma CubeSlices.band_card (cs : CubeSlices) (i : ZMod 7) :
    (cs.s i ∪ cs.s (i + 1)).card = (cs.s i).card + (cs.s (i + 1)).card :=
  Finset.card_union_of_disjoint (cs.disj i)

private lemma CubeSlices.band_card_le (cs : CubeSlices) (i : ZMod 7) :
    (cs.s i).card + (cs.s (i + 1)).card ≤ 10 := by
  rw [← cs.band_card i]; exact alpha_c7_pow2_le_internal (cs.indep i)

private lemma CubeSlices.sdiff_eq_other (cs : CubeSlices) (i : ZMod 7) :
    diff49 (ofFinset49 (cs.s i ∪ cs.s (i + 1))) (ofFinset49 (cs.s i)) =
      ofFinset49 (cs.s (i + 1)) := by
  rw [← ofFinset49_sdiff, Finset.union_sdiff_cancel_left (cs.disj i)]

private lemma CubeSlices.sdiff_eq_first (cs : CubeSlices) (i : ZMod 7) :
    diff49 (ofFinset49 (cs.s i ∪ cs.s (i + 1))) (ofFinset49 (cs.s (i + 1))) =
      ofFinset49 (cs.s i) := by
  rw [← ofFinset49_sdiff, Finset.union_sdiff_cancel_right (cs.disj i)]

private lemma CubeSlices.disj' (cs : CubeSlices) (i j : ZMod 7) (hj : i + 1 = j := by decide) :
    Disjoint (cs.s i) (cs.s j) := hj ▸ cs.disj i
private lemma CubeSlices.indep' (cs : CubeSlices) (i j : ZMod 7) (hj : i + 1 = j := by decide) :
    (C7 ⊠ C7).IsIndepSet ((cs.s i ∪ cs.s j : Finset _) : Set _) := hj ▸ cs.indep i
private lemma CubeSlices.band_card' (cs : CubeSlices) (i j : ZMod 7) (hj : i + 1 = j := by decide) :
    (cs.s i ∪ cs.s j).card = (cs.s i).card + (cs.s j).card := hj ▸ cs.band_card i
private lemma CubeSlices.sdiff_other' (cs : CubeSlices) (i j : ZMod 7) (hj : i + 1 = j := by decide) :
    diff49 (ofFinset49 (cs.s i ∪ cs.s j)) (ofFinset49 (cs.s i)) = ofFinset49 (cs.s j) := hj ▸ cs.sdiff_eq_other i
private lemma CubeSlices.sdiff_first' (cs : CubeSlices) (i j : ZMod 7) (hj : i + 1 = j := by decide) :
    diff49 (ofFinset49 (cs.s i ∪ cs.s j)) (ofFinset49 (cs.s j)) = ofFinset49 (cs.s i) := hj ▸ cs.sdiff_eq_first i

private lemma CubeSlices.disj_of_sub_nbr {cs : CubeSlices} {i : ZMod 7} {M : Nat}
    (hMlt : M < 2 ^ 49) (hM : subset49 M (closedNbr49 (ofFinset49 (cs.s i))) = true) :
    disjoint49 (ofFinset49 (cs.s (i + 1))) M = true ∧
    disjoint49 (ofFinset49 (cs.s (i - 1))) M = true := by
  have hd1 := disjoint49_closedNbr_of_indep (cs.disj i) (cs.indep i)
  have hd2 : disjoint49 (ofFinset49 (cs.s (i - 1))) (closedNbr49 (ofFinset49 (cs.s i))) = true := by
    have h := cs.disj (i - 1); have hi := cs.indep (i - 1)
    rw [sub_add_cancel] at h hi
    rw [Finset.union_comm] at hi
    exact disjoint49_closedNbr_of_indep h.symm hi
  have sub_disj : ∀ {A B C : Nat}, A < 2 ^ 49 → B < 2 ^ 49 →
      disjoint49 A C = true → subset49 B C = true → disjoint49 A B = true := by
    intro A B C hAlt hBlt hAC hBC
    rw [disjoint49_iff hAlt] at hAC ⊢
    rw [subset49_iff hBlt] at hBC
    intro r c ha
    cases hb : get49 B r c
    · rfl
    · exact absurd (hBC r c hb) (by simp [hAC r c ha])
  exact ⟨sub_disj (ofFinset49_lt _) hMlt hd1 hM, sub_disj (ofFinset49_lt _) hMlt hd2 hM⟩

private lemma CubeSlices.subset_not_or {S : Finset (ZMod 7 × ZMod 7)} {A B : Nat}
    (hA : disjoint49 (ofFinset49 S) A = true)
    (hB : disjoint49 (ofFinset49 S) B = true) :
    subset49 (ofFinset49 S) (not49 (A ||| B)) = true := by
  rw [disjoint49_iff (ofFinset49_lt S)] at hA hB
  rw [subset49_iff (ofFinset49_lt S)]
  intro r c hS
  rw [get49_not, get49_or, hA r c hS, hB r c hS]; rfl

private lemma refute_sq_core {cs : CubeSlices} {k : Fin 3} {mL mR : Nat}
    (hB2eq : ofFinset49 (cs.s 2 ∪ cs.s 3) = rep k)
    (hmL : mL = (cs.s 2).card) (hmR : mR = (cs.s 3).card)
    (hmL4 : 4 ≤ mL) (hmL6 : mL ≤ 6) (hmR4 : 4 ≤ mR) (hmR6 : mR ≤ 6)
    (hb0 : (cs.s 0).card + (cs.s 1).card = 10)
    (hb1 : (cs.s 1).card + (cs.s 2).card = 10)
    (hb3 : (cs.s 3).card + (cs.s 4).card = 10)
    (hb4 : (cs.s 4).card + (cs.s 5).card = 10)
    (hs6 : 4 ≤ (cs.s 6).card)
    {cert : SqCert}
    (hchk : checkSqCase k (nearK k mL) (nearK k mR)
      (ofFinset49 (cs.s 2)) cert = true) : False := by
  have hS2rep : subset49 (ofFinset49 (cs.s 2)) (rep k) = true := by
    rw [← hB2eq]; exact ofFinset49_subset_of_subset Finset.subset_union_left
  have hS3eq : diff49 (rep k) (ofFinset49 (cs.s 2)) = ofFinset49 (cs.s 3) := by
    rw [← hB2eq]; exact cs.sdiff_other' 2 3
  have hS3rep : subset49 (ofFinset49 (cs.s 3)) (rep k) = true := by
    rw [← hB2eq]; exact ofFinset49_subset_of_subset Finset.subset_union_right
  have hS2pop : pop49 (ofFinset49 (cs.s 2)) = mL := by rw [pop49_ofFinset, hmL]
  have hS3pop : pop49 (ofFinset49 (cs.s 3)) = mR := by rw [pop49_ofFinset, hmR]
  have hB0card : (cs.s 0 ∪ cs.s 1).card = 10 := by rw [cs.band_card' 0 1, hb0]
  have hB1card : (cs.s 1 ∪ cs.s 2).card = 10 := by rw [cs.band_card' 1 2, hb1]
  have hB3card : (cs.s 3 ∪ cs.s 4).card = 10 := by rw [cs.band_card' 3 4, hb3]
  have hB4card : (cs.s 4 ∪ cs.s 5).card = 10 := by rw [cs.band_card' 4 5, hb4]
  have hS6ind : (C7 ⊠ C7).IsIndepSet ((cs.s 6 : Finset _) : Set _) :=
    (cs.indep 6).mono (Finset.coe_subset.mpr Finset.subset_union_left)
  have hCL_sub : subset49 ((c2Tree k).getAux (repBits k) (ofFinset49 (cs.s 2)))
      (closedNbr49 (ofFinset49 (cs.s 0))) = true := by
    have h := c2Tree_sound (ofFinset49_lt _) hS2rep (by omega) (by omega) (cs.indep' 1 2) hB1card
      (ofFinset49_subset_of_subset Finset.subset_union_right)
      (cs.indep' 0 1) hB0card
      (by rw [cs.sdiff_first' 1 2]; exact ofFinset49_subset_of_subset Finset.subset_union_right)
    rwa [cs.sdiff_first' 1 2, cs.sdiff_first' 0 1] at h
  have hCR_sub : subset49 ((c2Tree k).getAux (repBits k) (ofFinset49 (cs.s 3)))
      (closedNbr49 (ofFinset49 (cs.s 5))) = true := by
    have h := c2Tree_sound (ofFinset49_lt _) hS3rep (by omega) (by omega) (cs.indep' 3 4) hB3card
      (ofFinset49_subset_of_subset Finset.subset_union_left)
      (cs.indep' 4 5) hB4card
      (by rw [cs.sdiff_other' 3 4]; exact ofFinset49_subset_of_subset Finset.subset_union_left)
    rwa [cs.sdiff_other' 3 4, cs.sdiff_other' 4 5] at h
  have hdisj6_0 : ∀ {M : Nat}, M < 2 ^ 49 → subset49 M (closedNbr49 (ofFinset49 (cs.s 0))) = true →
      disjoint49 (ofFinset49 (cs.s 6)) M = true := by
    intro M hMlt hM
    have h := (cs.disj_of_sub_nbr (i := 0) hMlt hM).2
    rwa [show (0 : ZMod 7) - 1 = 6 by decide] at h
  have hdisj6_5 : ∀ {M : Nat}, M < 2 ^ 49 → subset49 M (closedNbr49 (ofFinset49 (cs.s 5))) = true →
      disjoint49 (ofFinset49 (cs.s 6)) M = true := by
    intro M hMlt hM
    have h := (cs.disj_of_sub_nbr (i := 5) hMlt hM).1
    rwa [show (5 : ZMod 7) + 1 = 6 by decide] at h
  unfold checkSqCase at hchk
  simp only [seqN_eq] at hchk
  rw [hS3eq] at hchk
  cases cert with
  | pop3 =>
    dsimp only at hchk
    have hle3 : pop49 (not49 ((c2Tree k).getAux (repBits k) (ofFinset49 (cs.s 2)) |||
        (c2Tree k).getAux (repBits k) (ofFinset49 (cs.s 3)))) ≤ 3 := Nat.ble_eq.mp hchk
    have hsub := CubeSlices.subset_not_or
      (hdisj6_0 (c2Tree_get_lt49 k _) hCL_sub) (hdisj6_5 (c2Tree_get_lt49 k _) hCR_sub)
    have hle := subset49_pop_le (ofFinset49_lt _) hsub
    rw [pop49_ofFinset] at hle
    omega
  | sq3 a b c =>
    dsimp only at hchk
    have hsub := CubeSlices.subset_not_or
      (hdisj6_0 (c2Tree_get_lt49 k _) hCL_sub) (hdisj6_5 (c2Tree_get_lt49 k _) hCR_sub)
    have hav : not49 ((c2Tree k).getAux (repBits k) (ofFinset49 (cs.s 2)) |||
        (c2Tree k).getAux (repBits k) (ofFinset49 (cs.s 3))) < 2 ^ 49 :=
      not49_lt (or_lt49 (c2Tree_get_lt49 k _) (c2Tree_get_lt49 k _))
    have hle := card_le_three_of_sq3_cover hS6ind hsub hchk hav
    omega
  | splitL1 covs =>
    dsimp only at hchk
    obtain ⟨k1, g1, hsr1, hB1eq⟩ := tenSet_canon_half (cs.indep' 1 2) hB1card
    obtain ⟨k4, g4, hsr4, hB4eq⟩ := tenSet_canon_half (cs.indep' 3 4) hB3card
    have hL1mem : (k1, g1, ofFinset49 (cs.s 1 ∪ cs.s 2)) ∈
        (nearK k mL).filter fun t => subset49 (ofFinset49 (cs.s 2)) t.2.2 := by
      rw [hB1eq]
      exact List.mem_filter.mpr ⟨mem_near_of_subset (ofFinset49_lt _) hsr1 hS2rep
        (by rw [← hB1eq]; exact ofFinset49_subset_of_subset Finset.subset_union_right) (by omega),
        by rw [← hB1eq]; exact ofFinset49_subset_of_subset Finset.subset_union_right⟩
    have hR4mem : (k4, g4, ofFinset49 (cs.s 3 ∪ cs.s 4)) ∈
        (nearK k mR).filter fun t => subset49 (ofFinset49 (cs.s 3)) t.2.2 := by
      rw [hB4eq]
      exact List.mem_filter.mpr ⟨mem_near_of_subset (ofFinset49_lt _) hsr4 hS3rep
        (by rw [← hB4eq]; exact ofFinset49_subset_of_subset Finset.subset_union_left) (by omega),
        by rw [← hB4eq]; exact ofFinset49_subset_of_subset Finset.subset_union_left⟩
    have hpair := List.all_eq_true.mp (List.all_eq_true.mp hchk _ hL1mem) _ hR4mem
    let y1Canon := diff49 (rep k1) (g1.inv.applyMask (ofFinset49 (cs.s 2)))
    let y4Canon := diff49 (rep k4) (g4.inv.applyMask (ofFinset49 (cs.s 3)))
    have hy1lt : y1Canon < 2 ^ 49 := diff49_lt (rep_lt k1)
    have hy4lt : y4Canon < 2 ^ 49 := diff49_lt (rep_lt k4)
    have hy1img : g1.applyMask y1Canon = ofFinset49 (cs.s 1) := by
      rw [Aut2.applyMask_diff g1 (rep_lt k1), ← hB1eq,
          Aut2.applyMask_inv_right g1 (ofFinset49_lt _), cs.sdiff_first' 1 2]
    have hy4img : g4.applyMask y4Canon = ofFinset49 (cs.s 4) := by
      rw [Aut2.applyMask_diff g4 (rep_lt k4), ← hB4eq,
          Aut2.applyMask_inv_right g4 (ofFinset49_lt _), cs.sdiff_other' 3 4]
    have hy1rep : subset49 y1Canon (rep k1) = true := by
      rw [subset49_iff hy1lt]; intro r c h; rw [get49_diff] at h; exact (Bool.and_eq_true _ _ |>.mp h).1
    have hy4rep : subset49 y4Canon (rep k4) = true := by
      rw [subset49_iff hy4lt]; intro r c h; rw [get49_diff] at h; exact (Bool.and_eq_true _ _ |>.mp h).1
    have hy1pop : 4 ≤ pop49 y1Canon := by
      have : pop49 y1Canon = (cs.s 1).card := by rw [← pop49_applyMask g1, hy1img, pop49_ofFinset]
      omega
    have hy4pop : 4 ≤ pop49 y4Canon := by
      have : pop49 y4Canon = (cs.s 4).card := by rw [← pop49_applyMask g4, hy4img, pop49_ofFinset]
      omega
    have hc1L : subset49 (g1.applyMask ((c1Tree k1).getAux (repBits k1) y1Canon))
        (closedNbr49 (ofFinset49 (cs.s 0))) = true := by
      have h := c1Tree_equivariant (g := g1) hy1lt hy1rep hy1pop (cs.indep' 0 1) hB0card
        (by rw [hy1img]; exact ofFinset49_subset_of_subset Finset.subset_union_right)
      rwa [hy1img, cs.sdiff_first' 0 1] at h
    have hc1R : subset49 (g4.applyMask ((c1Tree k4).getAux (repBits k4) y4Canon))
        (closedNbr49 (ofFinset49 (cs.s 5))) = true := by
      have h := c1Tree_equivariant (g := g4) hy4lt hy4rep hy4pop (cs.indep' 4 5) hB4card
        (by rw [hy4img]; exact ofFinset49_subset_of_subset Finset.subset_union_left)
      rwa [hy4img, cs.sdiff_other' 4 5] at h
    have hsub := CubeSlices.subset_not_or
      (hdisj6_0 (g1.applyMask_lt (c1Tree_get_lt49 k1 y1Canon)) hc1L)
      (hdisj6_5 (g4.applyMask_lt (c1Tree_get_lt49 k4 y4Canon)) hc1R)
    have hav : not49 (g1.applyMask ((c1Tree k1).getAux (repBits k1) y1Canon) |||
        g4.applyMask ((c1Tree k4).getAux (repBits k4) y4Canon)) < 2 ^ 49 :=
      not49_lt (or_lt49 (g1.applyMask_lt (c1Tree_get_lt49 k1 y1Canon)) (g4.applyMask_lt (c1Tree_get_lt49 k4 y4Canon)))
    simp only [lor_eq, Bool.or_eq_true, Nat.ble_eq, List.any_eq_true] at hpair
    rcases hpair with hpop3 | ⟨⟨a, b, c⟩, _, hcov⟩
    · have hle := subset49_pop_le (ofFinset49_lt _) hsub
      rw [pop49_ofFinset] at hle
      have hpop3' : pop49 (not49 (g1.applyMask ((c1Tree k1).getAux (repBits k1) y1Canon) |||
          g4.applyMask ((c1Tree k4).getAux (repBits k4) y4Canon))) ≤ 3 := hpop3
      omega
    · have hle := card_le_three_of_sq3_cover hS6ind hsub hcov hav
      omega

private lemma refute_P13 {cs : CubeSlices}
    (hs0 : (cs.s 0).card = 5) (hs1 : (cs.s 1).card = 5) (hs2 : (cs.s 2).card = 5)
    (hs3 : (cs.s 3).card = 5) (hs4 : (cs.s 4).card = 5) (hs5 : (cs.s 5).card = 5)
    (hs6 : 4 ≤ (cs.s 6).card) : False := by
  have hB2card : (cs.s 2 ∪ cs.s 3).card = 10 := by rw [cs.band_card' 2 3, hs2, hs3]
  obtain ⟨k, g, hB2eq⟩ := tenSet_in_three_orbits (cs.indep' 2 3) hB2card
  let cs1 := cs.mapAut2 g.inv
  have hB2_1 : ofFinset49 (cs1.s 2 ∪ cs1.s 3) = rep k := by
    change ofFinset49 ((cs.s 2).map _ ∪ (cs.s 3).map _) = rep k
    rw [← Finset.map_union, ← Aut2.applyMask_ofFinset, hB2eq, Aut2.applyMask_inv_left g (rep_lt k)]
  have h03 : get49 (rep k) 0 3 = true := (by decide : ∀ j : Fin 3, get49 (rep j) 0 3 = true) k
  have hcard1 : ∀ i, (cs1.s i).card = (cs.s i).card := fun i => Finset.card_map _
  have hex : ∃ cs2 : CubeSlices,
      ofFinset49 (cs2.s 2 ∪ cs2.s 3) = rep k ∧
      get49 (ofFinset49 (cs2.s 2)) 0 3 = true ∧
      (cs2.s 0).card = 5 ∧ (cs2.s 1).card = 5 ∧ (cs2.s 2).card = 5 ∧
      (cs2.s 3).card = 5 ∧ (cs2.s 4).card = 5 ∧ (cs2.s 5).card = 5 ∧
      4 ≤ (cs2.s 6).card := by
    cases hget : get49 (ofFinset49 (cs1.s 2)) 0 3
    · refine ⟨cs1.rev 5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · change ofFinset49 (cs1.s (5 - 2) ∪ cs1.s (5 - 3)) = rep k
        rw [show (5 : ZMod 7) - 2 = 3 by decide, show (5 : ZMod 7) - 3 = 2 by decide, Finset.union_comm]
        exact hB2_1
      · change get49 (ofFinset49 (cs1.s (5 - 2))) 0 3 = true
        rw [show (5 : ZMod 7) - 2 = 3 by decide]
        rw [← hB2_1, ofFinset49_union, get49_or, hget] at h03
        simpa using h03
      · change (cs1.s (5 - 0)).card = 5; rw [show (5 : ZMod 7) - 0 = 5 by decide, hcard1, hs5]
      · change (cs1.s (5 - 1)).card = 5; rw [show (5 : ZMod 7) - 1 = 4 by decide, hcard1, hs4]
      · change (cs1.s (5 - 2)).card = 5; rw [show (5 : ZMod 7) - 2 = 3 by decide, hcard1, hs3]
      · change (cs1.s (5 - 3)).card = 5; rw [show (5 : ZMod 7) - 3 = 2 by decide, hcard1, hs2]
      · change (cs1.s (5 - 4)).card = 5; rw [show (5 : ZMod 7) - 4 = 1 by decide, hcard1, hs1]
      · change (cs1.s (5 - 5)).card = 5; rw [show (5 : ZMod 7) - 5 = 0 by decide, hcard1, hs0]
      · change 4 ≤ (cs1.s (5 - 6)).card; rw [show (5 : ZMod 7) - 6 = 6 by decide, hcard1]; exact hs6
    · exact ⟨cs1, hB2_1, hget, by rw [hcard1, hs0], by rw [hcard1, hs1], by rw [hcard1, hs2],
        by rw [hcard1, hs3], by rw [hcard1, hs4], by rw [hcard1, hs5], by rw [hcard1]; exact hs6⟩
  obtain ⟨cs2, hB2, h03_2, c0, c1, c2, c3, c4, c5, c6⟩ := hex
  have hS2rep : subset49 (ofFinset49 (cs2.s 2)) (rep k) = true := by
    rw [← hB2]; exact ofFinset49_subset_of_subset Finset.subset_union_left
  have hmem : ofFinset49 (cs2.s 2) ∈ halves5 k :=
    mem_halves5 (ofFinset49_lt _) hS2rep (by rw [pop49_ofFinset, c2]) h03_2
  have hcert : ∀ j : Fin 3, ∀ m ∈ halves5 j, ∃ cert, checkSqCase j (near5 j) (near5 j) m cert = true :=
    fin3_cases
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP13_0_ok m hm; ⟨c, h⟩)
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP13_1_ok m hm; ⟨c, h⟩)
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP13_2_ok m hm; ⟨c, h⟩)
  obtain ⟨cert, hchk⟩ := hcert k _ hmem
  exact refute_sq_core hB2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) c6 hchk

private lemma refute_P2 {cs : CubeSlices}
    (hs0 : (cs.s 0).card = 4) (hs1 : (cs.s 1).card = 6) (hs2 : (cs.s 2).card = 4)
    (hs3 : (cs.s 3).card = 6) (hs4 : (cs.s 4).card = 4) (hs5 : (cs.s 5).card = 6)
    (hs6 : (cs.s 6).card = 4) : False := by
  have hB2card : (cs.s 2 ∪ cs.s 3).card = 10 := by rw [cs.band_card' 2 3, hs2, hs3]
  obtain ⟨k, g, hB2eq⟩ := tenSet_in_three_orbits (cs.indep' 2 3) hB2card
  let cs1 := cs.mapAut2 g.inv
  have hB2_1 : ofFinset49 (cs1.s 2 ∪ cs1.s 3) = rep k := by
    change ofFinset49 ((cs.s 2).map _ ∪ (cs.s 3).map _) = rep k
    rw [← Finset.map_union, ← Aut2.applyMask_ofFinset, hB2eq, Aut2.applyMask_inv_left g (rep_lt k)]
  have hcard1 : ∀ i, (cs1.s i).card = (cs.s i).card := fun i => Finset.card_map _
  have hS2rep : subset49 (ofFinset49 (cs1.s 2)) (rep k) = true := by
    rw [← hB2_1]; exact ofFinset49_subset_of_subset Finset.subset_union_left
  have hmem : ofFinset49 (cs1.s 2) ∈ subs4 k :=
    mem_subs4 (ofFinset49_lt _) hS2rep (by rw [pop49_ofFinset, hcard1, hs2])
  have hcert : ∀ j : Fin 3, ∀ m ∈ subs4 j, ∃ cert, checkSqCase j (near4 j) (near6 j) m cert = true :=
    fin3_cases
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP2_0_ok m hm; ⟨c, h⟩)
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP2_1_ok m hm; ⟨c, h⟩)
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP2_2_ok m hm; ⟨c, h⟩)
  obtain ⟨cert, hchk⟩ := hcert k _ hmem
  exact refute_sq_core hB2_1 (by rw [hcard1, hs2]) (by rw [hcard1, hs3])
    (by omega) (by omega) (by omega) (by omega)
    (by rw [hcard1, hcard1, hs0, hs1]) (by rw [hcard1, hcard1, hs1, hs2])
    (by rw [hcard1, hcard1, hs3, hs4]) (by rw [hcard1, hcard1, hs4, hs5])
    (by rw [hcard1, hs6]) hchk

private lemma refute_P4 {cs : CubeSlices}
    (hs0 : (cs.s 0).card = 4) (hs1 : (cs.s 1).card = 6) (hs2 : (cs.s 2).card = 4)
    (hs3 : (cs.s 3).card = 6) (hs4 : (cs.s 4).card = 4) (hs5 : (cs.s 5).card = 5)
    (hs6 : (cs.s 6).card = 5) : False := by
  have hB1card : (cs.s 1 ∪ cs.s 2).card = 10 := by rw [cs.band_card' 1 2, hs1, hs2]
  obtain ⟨k, g, hB1eq⟩ := tenSet_in_three_orbits (cs.indep' 1 2) hB1card
  let cs1 := cs.mapAut2 g.inv
  have hB1_1 : ofFinset49 (cs1.s 1 ∪ cs1.s 2) = rep k := by
    change ofFinset49 ((cs.s 1).map _ ∪ (cs.s 2).map _) = rep k
    rw [← Finset.map_union, ← Aut2.applyMask_ofFinset, hB1eq, Aut2.applyMask_inv_left g (rep_lt k)]
  have hcard1 : ∀ i, (cs1.s i).card = (cs.s i).card := fun i => Finset.card_map _
  have hS2rep : subset49 (ofFinset49 (cs1.s 2)) (rep k) = true := by
    rw [← hB1_1]; exact ofFinset49_subset_of_subset Finset.subset_union_right
  have hS1eq : diff49 (rep k) (ofFinset49 (cs1.s 2)) = ofFinset49 (cs1.s 1) := by
    rw [← hB1_1]; exact cs1.sdiff_first' 1 2
  have hS1rep : subset49 (ofFinset49 (cs1.s 1)) (rep k) = true := by
    rw [← hB1_1]; exact ofFinset49_subset_of_subset Finset.subset_union_left
  have hmem : ofFinset49 (cs1.s 2) ∈ subs4 k :=
    mem_subs4 (ofFinset49_lt _) hS2rep (by rw [pop49_ofFinset, hcard1, hs2])
  have hcert : ∀ j : Fin 3, ∀ m ∈ subs4 j, ∃ cert, checkP4Case j m cert = true :=
    fin3_cases
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP4_0_ok m hm; ⟨c, h⟩)
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP4_1_ok m hm; ⟨c, h⟩)
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP4_2_ok m hm; ⟨c, h⟩)
  obtain ⟨cert, hchk⟩ := hcert k _ hmem
  unfold checkP4Case at hchk; simp only [seqN_eq] at hchk; rw [hS1eq] at hchk
  have hCL : subset49 ((c1Tree k).getAux (repBits k) (ofFinset49 (cs1.s 1)))
      (closedNbr49 (ofFinset49 (cs1.s 0))) = true := by
    have h := c1Tree_sound (ofFinset49_lt _) hS1rep (by rw [pop49_ofFinset, hcard1, hs1]; omega)
      (cs1.indep' 0 1) (by rw [cs1.band_card' 0 1, hcard1, hcard1, hs0, hs1])
      (ofFinset49_subset_of_subset Finset.subset_union_right)
    rwa [cs1.sdiff_first' 0 1] at h
  have hCR : subset49 ((c2Tree k).getAux (repBits k) (ofFinset49 (cs1.s 2)))
      (closedNbr49 (ofFinset49 (cs1.s 4))) = true := by
    have h := c2Tree_sound (ofFinset49_lt _) hS2rep (by rw [pop49_ofFinset, hcard1, hs2])
      (by rw [pop49_ofFinset, hcard1, hs2]; omega)
      (cs1.indep' 2 3) (by rw [cs1.band_card' 2 3, hcard1, hcard1, hs2, hs3])
      (ofFinset49_subset_of_subset Finset.subset_union_left)
      (cs1.indep' 3 4) (by rw [cs1.band_card' 3 4, hcard1, hcard1, hs3, hs4])
      (by rw [cs1.sdiff_other' 2 3]; exact ofFinset49_subset_of_subset Finset.subset_union_left)
    rwa [cs1.sdiff_other' 2 3, cs1.sdiff_other' 3 4] at h
  have hd5 : disjoint49 (ofFinset49 (cs1.s 5))
      (((c1Tree k).getAux (repBits k) (ofFinset49 (cs1.s 1))) &&&
       ((c2Tree k).getAux (repBits k) (ofFinset49 (cs1.s 2)))) = true := by
    have h5 := (cs1.disj_of_sub_nbr (i := 4) (c2Tree_get_lt49 k _) hCR).1
    rw [show (4 : ZMod 7) + 1 = 5 by decide] at h5
    rw [disjoint49_iff (ofFinset49_lt _)] at h5 ⊢
    intro r c hm; rw [get49_and, h5 r c hm, Bool.and_false]
  have hd6 : disjoint49 (ofFinset49 (cs1.s 6))
      (((c1Tree k).getAux (repBits k) (ofFinset49 (cs1.s 1))) &&&
       ((c2Tree k).getAux (repBits k) (ofFinset49 (cs1.s 2)))) = true := by
    have h6 := (cs1.disj_of_sub_nbr (i := 0) (c1Tree_get_lt49 k _) hCL).2
    rw [show (0 : ZMod 7) - 1 = 6 by decide] at h6
    rw [disjoint49_iff (ofFinset49_lt _)] at h6 ⊢
    intro r c hm; rw [get49_and, h6 r c hm, Bool.false_and]
  have hd56 : disjoint49 (ofFinset49 (cs1.s 5 ∪ cs1.s 6))
      (((c1Tree k).getAux (repBits k) (ofFinset49 (cs1.s 1))) &&&
       ((c2Tree k).getAux (repBits k) (ofFinset49 (cs1.s 2)))) = true := by
    rw [ofFinset49_union, disjoint49_iff (or_lt49 (ofFinset49_lt _) (ofFinset49_lt _))]
    rw [disjoint49_iff (ofFinset49_lt _)] at hd5 hd6
    intro r c h; rw [get49_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact hd5 r c h
    · exact hd6 r c h
  have hle := checkFarkas2D_sound hchk (cs1.indep' 5 6) hd56
  rw [cs1.band_card' 5 6, hcard1, hcard1, hs5, hs6] at hle
  omega

private lemma refute_P5 {cs : CubeSlices}
    (hs0 : (cs.s 0).card = 5) (hs1 : (cs.s 1).card = 5) (hs2 : (cs.s 2).card = 5)
    (hs3 : (cs.s 3).card = 5) (hs4 : (cs.s 4).card = 4) (hs5 : (cs.s 5).card = 6)
    (hs6 : (cs.s 6).card = 4) : False := by
  have hB1card : (cs.s 1 ∪ cs.s 2).card = 10 := by rw [cs.band_card' 1 2, hs1, hs2]
  obtain ⟨k, g, hB1eq⟩ := tenSet_in_three_orbits (cs.indep' 1 2) hB1card
  let cs1 := cs.mapAut2 g.inv
  have hB1_1 : ofFinset49 (cs1.s 1 ∪ cs1.s 2) = rep k := by
    change ofFinset49 ((cs.s 1).map _ ∪ (cs.s 2).map _) = rep k
    rw [← Finset.map_union, ← Aut2.applyMask_ofFinset, hB1eq, Aut2.applyMask_inv_left g (rep_lt k)]
  have h03 : get49 (rep k) 0 3 = true := (by decide : ∀ j : Fin 3, get49 (rep j) 0 3 = true) k
  have hcard1 : ∀ i, (cs1.s i).card = (cs.s i).card := fun i => Finset.card_map _
  have hex : ∃ cs2 : CubeSlices,
      ofFinset49 (cs2.s 1 ∪ cs2.s 2) = rep k ∧
      get49 (ofFinset49 (cs2.s 1)) 0 3 = true ∧
      (cs2.s 0).card = 5 ∧ (cs2.s 1).card = 5 ∧ (cs2.s 2).card = 5 ∧
      (cs2.s 3).card = 5 ∧ (cs2.s 4).card = 4 ∧ (cs2.s 5).card = 6 ∧
      (cs2.s 6).card = 4 := by
    cases hget : get49 (ofFinset49 (cs1.s 1)) 0 3
    · refine ⟨cs1.rev 3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · change ofFinset49 (cs1.s (3 - 1) ∪ cs1.s (3 - 2)) = rep k
        rw [show (3 : ZMod 7) - 1 = 2 by decide, show (3 : ZMod 7) - 2 = 1 by decide, Finset.union_comm]
        exact hB1_1
      · change get49 (ofFinset49 (cs1.s (3 - 1))) 0 3 = true
        rw [show (3 : ZMod 7) - 1 = 2 by decide]
        rw [← hB1_1, ofFinset49_union, get49_or, hget] at h03
        simpa using h03
      · change (cs1.s (3 - 0)).card = 5; rw [show (3 : ZMod 7) - 0 = 3 by decide, hcard1, hs3]
      · change (cs1.s (3 - 1)).card = 5; rw [show (3 : ZMod 7) - 1 = 2 by decide, hcard1, hs2]
      · change (cs1.s (3 - 2)).card = 5; rw [show (3 : ZMod 7) - 2 = 1 by decide, hcard1, hs1]
      · change (cs1.s (3 - 3)).card = 5; rw [show (3 : ZMod 7) - 3 = 0 by decide, hcard1, hs0]
      · change (cs1.s (3 - 4)).card = 4; rw [show (3 : ZMod 7) - 4 = 6 by decide, hcard1, hs6]
      · change (cs1.s (3 - 5)).card = 6; rw [show (3 : ZMod 7) - 5 = 5 by decide, hcard1, hs5]
      · change (cs1.s (3 - 6)).card = 4; rw [show (3 : ZMod 7) - 6 = 4 by decide, hcard1, hs4]
    · exact ⟨cs1, hB1_1, hget, by rw [hcard1, hs0], by rw [hcard1, hs1], by rw [hcard1, hs2],
        by rw [hcard1, hs3], by rw [hcard1, hs4], by rw [hcard1, hs5], by rw [hcard1, hs6]⟩
  obtain ⟨cs2, hB1, h03_2, c0, c1, c2, c3, c4, c5, c6⟩ := hex
  have hS1rep : subset49 (ofFinset49 (cs2.s 1)) (rep k) = true := by
    rw [← hB1]; exact ofFinset49_subset_of_subset Finset.subset_union_left
  have hS2eq : diff49 (rep k) (ofFinset49 (cs2.s 1)) = ofFinset49 (cs2.s 2) := by
    rw [← hB1]; exact cs2.sdiff_other' 1 2
  have hS2rep : subset49 (ofFinset49 (cs2.s 2)) (rep k) = true := by
    rw [← hB1]; exact ofFinset49_subset_of_subset Finset.subset_union_right
  have hmem : ofFinset49 (cs2.s 1) ∈ halves5 k :=
    mem_halves5 (ofFinset49_lt _) hS1rep (by rw [pop49_ofFinset, c1]) h03_2
  have hcert : ∀ j : Fin 3, ∀ m ∈ halves5 j, ∃ cert, checkP5Case j (near5 j) m cert = true :=
    fin3_cases
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP5_0_ok m hm; ⟨c, h⟩)
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP5_1_ok m hm; ⟨c, h⟩)
      (fun m hm => let ⟨c, _, h⟩ := checkAll4_sound checkP5_2_ok m hm; ⟨c, h⟩)
  obtain ⟨cert, hchk⟩ := hcert k _ hmem
  unfold checkP5Case at hchk; simp only [seqN_eq] at hchk; rw [hS2eq] at hchk
  have hB0card : (cs2.s 0 ∪ cs2.s 1).card = 10 := by rw [cs2.band_card' 0 1, c0, c1]
  have hB2card : (cs2.s 2 ∪ cs2.s 3).card = 10 := by rw [cs2.band_card' 2 3, c2, c3]
  have hCL : subset49 ((c1Tree k).getAux (repBits k) (ofFinset49 (cs2.s 1)))
      (closedNbr49 (ofFinset49 (cs2.s 0))) = true := by
    have h := c1Tree_sound (ofFinset49_lt _) hS1rep (by rw [pop49_ofFinset, c1]; omega)
      (cs2.indep' 0 1) hB0card (ofFinset49_subset_of_subset Finset.subset_union_right)
    rwa [cs2.sdiff_first' 0 1] at h
  have hCR : subset49 ((c1Tree k).getAux (repBits k) (ofFinset49 (cs2.s 2)))
      (closedNbr49 (ofFinset49 (cs2.s 3))) = true := by
    have h := c1Tree_sound (ofFinset49_lt _) hS2rep (by rw [pop49_ofFinset, c2]; omega)
      (cs2.indep' 2 3) hB2card (ofFinset49_subset_of_subset Finset.subset_union_left)
    rwa [cs2.sdiff_other' 2 3] at h
  have hd4_CR : disjoint49 (ofFinset49 (cs2.s 4))
      ((c1Tree k).getAux (repBits k) (ofFinset49 (cs2.s 2))) = true := by
    have h := (cs2.disj_of_sub_nbr (i := 3) (c1Tree_get_lt49 k _) hCR).1
    rwa [show (3 : ZMod 7) + 1 = 4 by decide] at h
  have hd6_CL : disjoint49 (ofFinset49 (cs2.s 6))
      ((c1Tree k).getAux (repBits k) (ofFinset49 (cs2.s 1))) = true := by
    have h := (cs2.disj_of_sub_nbr (i := 0) (c1Tree_get_lt49 k _) hCL).2
    rwa [show (0 : ZMod 7) - 1 = 6 by decide] at h
  have hd4_n3 : disjoint49 (ofFinset49 (cs2.s 4)) (closedNbr49 (ofFinset49 (cs2.s 3))) = true :=
    disjoint49_closedNbr_of_indep (cs2.disj' 3 4) (cs2.indep' 3 4)
  have hd6_n0 : disjoint49 (ofFinset49 (cs2.s 6)) (closedNbr49 (ofFinset49 (cs2.s 0))) = true := by
    have h := cs2.disj' 6 0; have hi := cs2.indep' 6 0
    rw [Finset.union_comm] at hi
    exact disjoint49_closedNbr_of_indep h.symm hi
  cases cert with
  | root f =>
    dsimp only at hchk
    have hle := checkFarkas3D_sound hchk (cs2.disj' 4 5) (cs2.indep' 4 5) (cs2.disj' 5 6) (cs2.indep' 5 6) hd4_CR hd6_CL
    omega
  | splitS0 f0s =>
    dsimp only at hchk
    obtain ⟨k0, g0, hsr0, hB0eq⟩ := tenSet_canon_half (cs2.indep' 0 1) hB0card
    have hL0mem : (k0, g0, ofFinset49 (cs2.s 0 ∪ cs2.s 1)) ∈
        (near5 k).filter fun t => subset49 (ofFinset49 (cs2.s 1)) t.2.2 := by
      rw [hB0eq]
      exact List.mem_filter.mpr ⟨mem_near_of_subset (ofFinset49_lt _) hsr0 hS1rep
        (by rw [← hB0eq]; exact ofFinset49_subset_of_subset Finset.subset_union_right)
        (by rw [pop49_ofFinset, c1]),
        by rw [← hB0eq]; exact ofFinset49_subset_of_subset Finset.subset_union_right⟩
    obtain ⟨c0cert, _, hc0chk⟩ := checkAll_sound hchk _ hL0mem
    dsimp only at hc0chk; rw [cs2.sdiff_first' 0 1] at hc0chk
    cases c0cert with
    | leaf f =>
      have hle := checkFarkas3D_sound hc0chk (cs2.disj' 4 5) (cs2.indep' 4 5) (cs2.disj' 5 6) (cs2.indep' 5 6) hd4_CR hd6_n0
      omega
    | splitS3 f3s =>
      obtain ⟨k3, g3, hsr3, hB3eq⟩ := tenSet_canon_half (cs2.indep' 2 3) hB2card
      have hR3mem : (k3, g3, ofFinset49 (cs2.s 2 ∪ cs2.s 3)) ∈
          (near5 k).filter fun t => subset49 (ofFinset49 (cs2.s 2)) t.2.2 := by
        rw [hB3eq]
        exact List.mem_filter.mpr ⟨mem_near_of_subset (ofFinset49_lt _) hsr3 hS2rep
          (by rw [← hB3eq]; exact ofFinset49_subset_of_subset Finset.subset_union_left)
          (by rw [pop49_ofFinset, c2]),
          by rw [← hB3eq]; exact ofFinset49_subset_of_subset Finset.subset_union_left⟩
      obtain ⟨f3, _, hf3chk⟩ := checkAll_sound hc0chk _ hR3mem
      dsimp only at hf3chk; rw [cs2.sdiff_other' 2 3] at hf3chk
      have hle := checkFarkas3D_sound hf3chk (cs2.disj' 4 5) (cs2.indep' 4 5) (cs2.disj' 5 6) (cs2.indep' 5 6) hd4_n3 hd6_n0
      omega

/-! ## Section 8: Exact 5-Profile Algebraic Reduction & Final Theorems -/

private def isProf34 (a0 a1 a2 a3 a4 a5 a6 : Nat) : Prop :=
  (a0 = 5 ∧ a1 = 5 ∧ a2 = 5 ∧ a3 = 5 ∧ a4 = 5 ∧ a5 = 5 ∧ 4 ≤ a6) ∨
  (a0 = 4 ∧ a1 = 6 ∧ a2 = 4 ∧ a3 = 6 ∧ a4 = 4 ∧ a5 = 6 ∧ a6 = 4) ∨
  (a0 = 4 ∧ a1 = 6 ∧ a2 = 4 ∧ a3 = 6 ∧ a4 = 4 ∧ a5 = 5 ∧ a6 = 5) ∨
  (a0 = 5 ∧ a1 = 5 ∧ a2 = 5 ∧ a3 = 5 ∧ a4 = 4 ∧ a5 = 6 ∧ a6 = 4)

private lemma prof_P13 (a0 a1 a2 a3 a4 a5 a6 : Nat)
    (h0 : a0 + a1 = 10) (h1 : a1 + a2 = 10) (h2 : a2 + a3 = 10) (h3 : a3 + a4 = 10)
    (h4 : a4 + a5 = 10) (h5 : a5 + a6 ≤ 10) (h6 : a6 + a0 ≤ 10)
    (hs : 34 ≤ a0 + a1 + a2 + a3 + a4 + a5 + a6) :
    isProf34 a0 a1 a2 a3 a4 a5 a6 ∨ isProf34 a6 a0 a1 a2 a3 a4 a5 := by
  by_cases ha0 : a0 = 5
  · left; left; omega
  · by_cases ha4 : a0 = 4
    · left; right; left; omega
    · right; right; left; omega

private lemma prof_P2 {a0 a1 a2 a3 a4 a5 a6 : Nat}
    (h0 : a0 + a1 = 10) (h1 : a1 + a2 = 10) (h2 : a2 + a3 = 10) (h3 : a3 + a4 = 10)
    (h4 : a4 + a5 = 10) (h5 : a5 + a6 = 10) (h6 : a6 + a0 = 8) :
    isProf34 a0 a1 a2 a3 a4 a5 a6 := by
  right; left; omega

private lemma prof_P4 {a0 a1 a2 a3 a4 a5 a6 : Nat}
    (h0 : a0 + a1 = 10) (h1 : a1 + a2 = 10) (h2 : a2 + a3 = 10) (h3 : a3 + a4 = 10)
    (h4 : a4 + a5 = 9)  (h5 : a5 + a6 = 10) (h6 : a6 + a0 = 9) :
    isProf34 a0 a1 a2 a3 a4 a5 a6 := by
  right; right; left; omega

private lemma prof_P5 {a0 a1 a2 a3 a4 a5 a6 : Nat}
    (h0 : a0 + a1 = 10) (h1 : a1 + a2 = 10) (h2 : a2 + a3 = 10) (h3 : a3 + a4 = 9)
    (h4 : a4 + a5 = 10) (h5 : a5 + a6 = 10) (h6 : a6 + a0 = 9) :
    isProf34 a0 a1 a2 a3 a4 a5 a6 := by
  right; right; right; omega

private lemma exists_profile_arith (s0 s1 s2 s3 s4 s5 s6 : Nat)
    (hsum : 34 ≤ s0 + s1 + s2 + s3 + s4 + s5 + s6)
    (b0 : s0 + s1 ≤ 10) (b1 : s1 + s2 ≤ 10) (b2 : s2 + s3 ≤ 10) (b3 : s3 + s4 ≤ 10)
    (b4 : s4 + s5 ≤ 10) (b5 : s5 + s6 ≤ 10) (b6 : s6 + s0 ≤ 10) :
    isProf34 s0 s1 s2 s3 s4 s5 s6 ∨ isProf34 s1 s2 s3 s4 s5 s6 s0 ∨
    isProf34 s2 s3 s4 s5 s6 s0 s1 ∨ isProf34 s3 s4 s5 s6 s0 s1 s2 ∨
    isProf34 s4 s5 s6 s0 s1 s2 s3 ∨ isProf34 s5 s6 s0 s1 s2 s3 s4 ∨
    isProf34 s6 s0 s1 s2 s3 s4 s5 := by
  let d0 := 10 - (s0 + s1); let d1 := 10 - (s1 + s2); let d2 := 10 - (s2 + s3)
  let d3 := 10 - (s3 + s4); let d4 := 10 - (s4 + s5); let d5 := 10 - (s5 + s6)
  let d6 := 10 - (s6 + s0)
  have hdef : d0 + d1 + d2 + d3 + d4 + d5 + d6 ≤ 2 := by omega
  by_cases h0 : d0 = 0
  · by_cases h1 : d1 = 0
    · by_cases h2 : d2 = 0
      · by_cases h3 : d3 = 0
        · by_cases h4 : d4 = 0
          · rcases prof_P13 s0 s1 s2 s3 s4 s5 s6 (by omega) (by omega) (by omega) (by omega) (by omega) b5 b6 hsum with hp | hp
            · exact Or.inl hp
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hp)))))
          · by_cases h5 : d5 = 0
            · by_cases h6 : d6 = 0
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prof_P2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))))))
              · exact Or.inl (prof_P4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
            · rcases prof_P13 s6 s0 s1 s2 s3 s4 s5 (by omega) (by omega) (by omega) (by omega) (by omega) b4 b5 (by omega) with hp | hp
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hp)))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp)))))
        · by_cases h4 : d4 = 0
          · by_cases h5 : d5 = 0
            · by_cases h6 : d6 = 0
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prof_P2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))))))
              · exact Or.inl (prof_P5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (prof_P4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))))))
          · rcases prof_P13 s5 s6 s0 s1 s2 s3 s4 (by omega) (by omega) (by omega) (by omega) (by omega) b3 b4 (by omega) with hp | hp
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp)))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp))))
      · by_cases h3 : d3 = 0
        · by_cases h4 : d4 = 0
          · by_cases h5 : d5 = 0
            · by_cases h6 : d6 = 0
              · exact Or.inr (Or.inr (Or.inr (Or.inl (prof_P2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))))
              · exact Or.inr (Or.inr (Or.inr (Or.inl (prof_P5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (prof_P5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prof_P4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))))))
        · rcases prof_P13 s4 s5 s6 s0 s1 s2 s3 (by omega) (by omega) (by omega) (by omega) (by omega) b2 b3 (by omega) with hp | hp
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp))))
          · exact Or.inr (Or.inr (Or.inr (Or.inl hp)))
    · by_cases h2 : d2 = 0
      · by_cases h3 : d3 = 0
        · by_cases h4 : d4 = 0
          · by_cases h5 : d5 = 0
            · by_cases h6 : d6 = 0
              · exact Or.inr (Or.inr (Or.inl (prof_P2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))))
              · exact Or.inr (Or.inr (Or.inl (prof_P4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))))
            · exact Or.inr (Or.inr (Or.inl (prof_P5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prof_P5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prof_P4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))))))
      · rcases prof_P13 s3 s4 s5 s6 s0 s1 s2 (by omega) (by omega) (by omega) (by omega) (by omega) b1 b2 (by omega) with hp | hp
        · exact Or.inr (Or.inr (Or.inr (Or.inl hp)))
        · exact Or.inr (Or.inr (Or.inl hp))
  · by_cases h1 : d1 = 0
    · by_cases h2 : d2 = 0
      · by_cases h3 : d3 = 0
        · by_cases h4 : d4 = 0
          · by_cases h5 : d5 = 0
            · by_cases h6 : d6 = 0
              · exact Or.inr (Or.inl (prof_P2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
              · rcases prof_P13 s1 s2 s3 s4 s5 s6 s0 (by omega) (by omega) (by omega) (by omega) (by omega) b6 b0 (by omega) with hp | hp
                · exact Or.inr (Or.inl hp)
                · exact Or.inl hp
            · exact Or.inr (Or.inl (prof_P4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
          · exact Or.inr (Or.inl (prof_P5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (prof_P5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (prof_P4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))))
    · rcases prof_P13 s2 s3 s4 s5 s6 s0 s1 (by omega) (by omega) (by omega) (by omega) (by omega) b0 b1 (by omega) with hp | hp
      · exact Or.inr (Or.inr (Or.inl hp))
      · exact Or.inr (Or.inl hp)

private lemma refute_cubeSlices_prof {cs : CubeSlices}
    (hp : isProf34 (cs.s 0).card (cs.s 1).card (cs.s 2).card (cs.s 3).card
      (cs.s 4).card (cs.s 5).card (cs.s 6).card) : False := by
  rcases hp with ⟨h0, h1, h2, h3, h4, h5, h6⟩ | ⟨h0, h1, h2, h3, h4, h5, h6⟩ |
                 ⟨h0, h1, h2, h3, h4, h5, h6⟩ | ⟨h0, h1, h2, h3, h4, h5, h6⟩
  · exact refute_P13 h0 h1 h2 h3 h4 h5 h6
  · exact refute_P2 h0 h1 h2 h3 h4 h5 h6
  · exact refute_P4 h0 h1 h2 h3 h4 h5 h6
  · exact refute_P5 h0 h1 h2 h3 h4 h5 h6

private lemma no_indep_34_cube {S : Finset (ZMod 7 × (ZMod 7 × ZMod 7))}
    (hS : (C7 ⊠ (C7 ⊠ C7)).IsIndepSet (S : Set _)) (hcard : 34 ≤ S.card) : False := by
  let cs := CubeSlices.ofIndep hS
  have hsum : (cs.s 0).card + (cs.s 1).card + (cs.s 2).card + (cs.s 3).card +
      (cs.s 4).card + (cs.s 5).card + (cs.s 6).card = S.card := by
    have h := CubeSlices.sum_card hS
    let e : Fin 7 ≃ ZMod 7 := Equiv.mk toZ7 ofZ7 ofZ7_toZ7 toZ7_ofZ7
    have h' : (∑ i : Fin 7, (cs.s (e i)).card) = ∑ i : ZMod 7, (cs.s i).card :=
      Equiv.sum_comp e (fun i => (cs.s i).card)
    rw [← h', Fin.sum_univ_seven] at h
    exact h
  have hprof := exists_profile_arith (cs.s 0).card (cs.s 1).card (cs.s 2).card (cs.s 3).card
    (cs.s 4).card (cs.s 5).card (cs.s 6).card (by omega)
    (cs.band_card_le 0) (cs.band_card_le 1) (cs.band_card_le 2) (cs.band_card_le 3)
    (cs.band_card_le 4) (cs.band_card_le 5) (cs.band_card_le 6)
  rcases hprof with h | h | h | h | h | h | h
  · exact refute_cubeSlices_prof (cs := cs) h
  · exact refute_cubeSlices_prof (cs := cs.shift 1) (by
      change isProf34 (cs.s (0 + 1)).card (cs.s (1 + 1)).card (cs.s (2 + 1)).card (cs.s (3 + 1)).card
        (cs.s (4 + 1)).card (cs.s (5 + 1)).card (cs.s (6 + 1)).card
      have e0 : (0 : ZMod 7) + 1 = 1 := by decide
      have e1 : (1 : ZMod 7) + 1 = 2 := by decide
      have e2 : (2 : ZMod 7) + 1 = 3 := by decide
      have e3 : (3 : ZMod 7) + 1 = 4 := by decide
      have e4 : (4 : ZMod 7) + 1 = 5 := by decide
      have e5 : (5 : ZMod 7) + 1 = 6 := by decide
      have e6 : (6 : ZMod 7) + 1 = 0 := by decide
      rw [e0, e1, e2, e3, e4, e5, e6]; exact h)
  · exact refute_cubeSlices_prof (cs := cs.shift 2) (by
      change isProf34 (cs.s (0 + 2)).card (cs.s (1 + 2)).card (cs.s (2 + 2)).card (cs.s (3 + 2)).card
        (cs.s (4 + 2)).card (cs.s (5 + 2)).card (cs.s (6 + 2)).card
      have e0 : (0 : ZMod 7) + 2 = 2 := by decide
      have e1 : (1 : ZMod 7) + 2 = 3 := by decide
      have e2 : (2 : ZMod 7) + 2 = 4 := by decide
      have e3 : (3 : ZMod 7) + 2 = 5 := by decide
      have e4 : (4 : ZMod 7) + 2 = 6 := by decide
      have e5 : (5 : ZMod 7) + 2 = 0 := by decide
      have e6 : (6 : ZMod 7) + 2 = 1 := by decide
      rw [e0, e1, e2, e3, e4, e5, e6]; exact h)
  · exact refute_cubeSlices_prof (cs := cs.shift 3) (by
      change isProf34 (cs.s (0 + 3)).card (cs.s (1 + 3)).card (cs.s (2 + 3)).card (cs.s (3 + 3)).card
        (cs.s (4 + 3)).card (cs.s (5 + 3)).card (cs.s (6 + 3)).card
      have e0 : (0 : ZMod 7) + 3 = 3 := by decide
      have e1 : (1 : ZMod 7) + 3 = 4 := by decide
      have e2 : (2 : ZMod 7) + 3 = 5 := by decide
      have e3 : (3 : ZMod 7) + 3 = 6 := by decide
      have e4 : (4 : ZMod 7) + 3 = 0 := by decide
      have e5 : (5 : ZMod 7) + 3 = 1 := by decide
      have e6 : (6 : ZMod 7) + 3 = 2 := by decide
      rw [e0, e1, e2, e3, e4, e5, e6]; exact h)
  · exact refute_cubeSlices_prof (cs := cs.shift 4) (by
      change isProf34 (cs.s (0 + 4)).card (cs.s (1 + 4)).card (cs.s (2 + 4)).card (cs.s (3 + 4)).card
        (cs.s (4 + 4)).card (cs.s (5 + 4)).card (cs.s (6 + 4)).card
      have e0 : (0 : ZMod 7) + 4 = 4 := by decide
      have e1 : (1 : ZMod 7) + 4 = 5 := by decide
      have e2 : (2 : ZMod 7) + 4 = 6 := by decide
      have e3 : (3 : ZMod 7) + 4 = 0 := by decide
      have e4 : (4 : ZMod 7) + 4 = 1 := by decide
      have e5 : (5 : ZMod 7) + 4 = 2 := by decide
      have e6 : (6 : ZMod 7) + 4 = 3 := by decide
      rw [e0, e1, e2, e3, e4, e5, e6]; exact h)
  · exact refute_cubeSlices_prof (cs := cs.shift 5) (by
      change isProf34 (cs.s (0 + 5)).card (cs.s (1 + 5)).card (cs.s (2 + 5)).card (cs.s (3 + 5)).card
        (cs.s (4 + 5)).card (cs.s (5 + 5)).card (cs.s (6 + 5)).card
      have e0 : (0 : ZMod 7) + 5 = 5 := by decide
      have e1 : (1 : ZMod 7) + 5 = 6 := by decide
      have e2 : (2 : ZMod 7) + 5 = 0 := by decide
      have e3 : (3 : ZMod 7) + 5 = 1 := by decide
      have e4 : (4 : ZMod 7) + 5 = 2 := by decide
      have e5 : (5 : ZMod 7) + 5 = 3 := by decide
      have e6 : (6 : ZMod 7) + 5 = 4 := by decide
      rw [e0, e1, e2, e3, e4, e5, e6]; exact h)
  · exact refute_cubeSlices_prof (cs := cs.shift 6) (by
      change isProf34 (cs.s (0 + 6)).card (cs.s (1 + 6)).card (cs.s (2 + 6)).card (cs.s (3 + 6)).card
        (cs.s (4 + 6)).card (cs.s (5 + 6)).card (cs.s (6 + 6)).card
      have e0 : (0 : ZMod 7) + 6 = 6 := by decide
      have e1 : (1 : ZMod 7) + 6 = 0 := by decide
      have e2 : (2 : ZMod 7) + 6 = 1 := by decide
      have e3 : (3 : ZMod 7) + 6 = 2 := by decide
      have e4 : (4 : ZMod 7) + 6 = 3 := by decide
      have e5 : (5 : ZMod 7) + 6 = 4 := by decide
      have e6 : (6 : ZMod 7) + 6 = 5 := by decide
      rw [e0, e1, e2, e3, e4, e5, e6]; exact h)

private def tripleToFin3 (p : ZMod 7 × (ZMod 7 × ZMod 7)) : Fin 3 → ZMod 7
  | ⟨0, _⟩ => p.1 | ⟨1, _⟩ => p.2.1 | ⟨2, _⟩ => p.2.2

private def c7CubeIsoPi : (C7 ⊠ (C7 ⊠ C7)) ≃g strongPowPi (SimpleGraph.cycleGraph 7) 3 := by
  have hfin3 : ∀ P : Fin 3 → Prop, (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 :=
    fun P => ⟨fun h => ⟨h 0, h 1, h 2⟩, fun ⟨h0, h1, h2⟩ => fin3_cases h0 h1 h2⟩
  have e1 : (C7 ⊠ (C7 ⊠ C7)) ≃g strongPowPi C7 3 :=
    { toEquiv := Equiv.mk
        tripleToFin3
        (fun f => (f 0, f 1, f 2))
        (fun ⟨_, _, _⟩ => rfl)
        (fun f => by ext i; revert i; exact fin3_cases rfl rfl rfl)
      map_rel_iff' := by
        intro ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩
        simp only [Equiv.coe_fn_mk, strongPowPi_adj, strongProd_adj, hfin3,
          tripleToFin3, ne_eq]
        constructor
        · rintro ⟨hne, h0, h1, h2⟩
          refine ⟨fun h => hne (by cases h; rfl), h0, ?_⟩
          by_cases hbc : (b1, c1) = (b2, c2)
          · exact Or.inl hbc
          · exact Or.inr ⟨hbc, h1, h2⟩
        · rintro ⟨hne, h0, hbc⟩
          refine ⟨fun h => hne ?_, h0, ?_, ?_⟩
          · have e0 : a1 = a2 := congrFun h 0
            have e1 : b1 = b2 := congrFun h 1
            have e2 : c1 = c2 := congrFun h 2
            exact Prod.ext e0 (Prod.ext e1 e2)
          · rcases hbc with hbc | ⟨_, h1, _⟩
            · exact Or.inl (congrArg Prod.fst hbc)
            · exact h1
          · rcases hbc with hbc | ⟨_, _, h2⟩
            · exact Or.inl (congrArg Prod.snd hbc)
            · exact h2 }
  have e2 : strongPowPi C7 3 ≃g strongPowPi (SimpleGraph.cycleGraph 7) 3 :=
    (strongPowEquivPi C7 3).symm.trans ((strongPowCongr c7IsoCycleGraph 3).trans (strongPowEquivPi _ 3))
  exact e1.trans e2

/-- Exact upper bound `α(C₇^⊠3) ≤ 33` proved in the pure Lean 4 kernel. -/
theorem alpha_c7_pow3_le : (strongPowPi (SimpleGraph.cycleGraph 7) 3).indepNum ≤ 33 := by
  rw [← iso_indepNum_eq c7CubeIsoPi]
  obtain ⟨S, hS, hScard⟩ := (C7 ⊠ (C7 ⊠ C7)).exists_isNIndepSet_indepNum
  by_contra hgt
  exact no_indep_34_cube hS (by omega)

/-! ## Section 9: Self-Contained 33-Word Witness (`33 ≤ α(C₇^⊠3)`) -/

private def witness33 (i : Fin 33) : Fin 3 → ZMod 7 :=
  match i.val with
  | 0  => ![0, 1, 1] | 1  => ![0, 4, 2] | 2  => ![0, 4, 4]
  | 3  => ![0, 6, 0] | 4  => ![0, 6, 5] | 5  => ![1, 1, 4]
  | 6  => ![1, 1, 6] | 7  => ![1, 3, 0] | 8  => ![1, 6, 3]
  | 9  => ![2, 1, 2] | 10 => ![2, 3, 3] | 11 => ![2, 3, 5]
  | 12 => ![2, 5, 6] | 13 => ![2, 6, 1] | 14 => ![3, 0, 4]
  | 15 => ![3, 0, 6] | 16 => ![3, 2, 0] | 17 => ![3, 4, 1]
  | 18 => ![3, 5, 4] | 19 => ![4, 0, 2] | 20 => ![4, 2, 5]
  | 21 => ![4, 3, 3] | 22 => ![4, 4, 6] | 23 => ![5, 0, 5]
  | 24 => ![5, 1, 0] | 25 => ![5, 3, 1] | 26 => ![5, 5, 2]
  | 27 => ![5, 5, 4] | 28 => ![5, 6, 0] | 29 => ![6, 0, 3]
  | 30 => ![6, 2, 3] | 31 => ![6, 2, 5] | _  => ![6, 4, 6]

private lemma witness33_inj_and_indep :
    (∀ i j : Fin 33, i ≠ j → witness33 i ≠ witness33 j) ∧
    (∀ i j : Fin 33, i ≠ j → ¬ (strongPowPi C7 3).Adj (witness33 i) (witness33 j)) := by
  decide

private theorem alpha_c7_pow3_ge_cube :
    33 ≤ (strongPowPi (SimpleGraph.cycleGraph 7) 3).indepNum := by
  have e2 : strongPowPi C7 3 ≃g strongPowPi (SimpleGraph.cycleGraph 7) 3 :=
    (strongPowEquivPi C7 3).symm.trans ((strongPowCongr c7IsoCycleGraph 3).trans (strongPowEquivPi _ 3))
  rw [← iso_indepNum_eq e2]
  let S : Finset (Fin 3 → ZMod 7) := Finset.univ.image witness33
  have hcard : S.card = 33 := by
    rw [Finset.card_image_of_injective _ (fun i j hij => by
      by_contra hne; exact witness33_inj_and_indep.1 i j hne hij)]
    simp
  have hind : (strongPowPi C7 3).IsIndepSet (S : Set (Fin 3 → ZMod 7)) := by
    intro u hu v hv huv hadj
    simp only [S, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ, true_and] at hu hv
    obtain ⟨i, rfl⟩ := hu
    obtain ⟨j, rfl⟩ := hv
    exact witness33_inj_and_indep.2 i j (fun h => huv (congrArg witness33 h)) hadj
  calc 33 = S.card := hcard.symm
    _ ≤ (strongPowPi C7 3).indepNum := hind.card_le_indepNum

/-- Exact independence number `α(C₇^⊠3) = 33` proved in the pure Lean 4 kernel. -/
theorem alpha_c7_pow3 : (strongPowPi (SimpleGraph.cycleGraph 7) 3).indepNum = 33 :=
  le_antisymm alpha_c7_pow3_le alpha_c7_pow3_ge_cube

end

end ShannonC7
'''

if __name__ == "__main__":
    main()
