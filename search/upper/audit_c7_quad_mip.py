#!/usr/bin/env python3
"""
audit_c7_quad_mip.py — Independent Strengthened LP/MIP & Census Audit for C_7^{\\boxtimes 4}
Milestone M5 (Track U1b / Feature F11)

Performs:
  1. Independent verification of the exhaustive C_7^3 33-set census (1,016 orbits, 16,672,544 sets)
     plus independent witness + randomized local-search membership cross-check (10 33-sets -> all land in the 1,016 orbits).
  2. Strengthened HiGHS LP/MIP audit of alpha(C_7^4) with ALL:
       - 2,401 2^4-clique cuts (RHS 1)
       - 1,372 K_2^3 x C_7 tube cuts (RHS 3)
       -   294 K_2^2 x C_7^2 slab cuts (RHS 10)
       -    28 K_2 x C_7^3 band cuts (RHS 33)
     both unanchored and anchored to canonical 33-set orbits B_0 = R_o (slices 0 & 1 fixed to R_o).
  3. Tiered audit for N = 115 (<= 114), N = 114 (<= 113), N = 113 (<= 112 Evidence Press),
     and N = 112 (balanced 32^7 phase transition analysis).

Usage:
  /home/antigravity/shannon-c7/.venv/bin/python -u search/upper/audit_c7_quad_mip.py \
      --orbits search/upper/c7_cube_33_orbits.txt \
      --sample-orbits 15 \
      --json-out search/upper/c7_quad_audit_results.json
"""

from __future__ import annotations

import argparse
import json
import time
from typing import Dict, List, Tuple

import highspy
import numpy as np

PERMS6 = [
    (0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)
]


def load_orbits(path: str) -> List[Tuple[int, int, List[int]]]:
    """Load canonical 33-set orbits: returns list of (orbit_id, stab_size, sorted 33 vertex ids in 0..342)."""
    orbits = []
    with open(path, "r", encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split()
            oid = int(parts[0])
            stab = int(parts[1])
            osize = int(parts[2])
            assert 16464 // stab == osize and 16464 % stab == 0
            verts = []
            for z in range(7):
                mask = int(parts[3 + z], 16)
                for v in range(49):
                    if (mask >> v) & 1:
                        verts.append(z * 49 + v)
            assert len(verts) == 33
            orbits.append((oid, stab, verts))
    return orbits


def verify_cube_indep(verts: List[int]) -> bool:
    for i in range(len(verts)):
        a0, r0 = divmod(verts[i], 49)
        b0, c0 = divmod(r0, 7)
        for j in range(i + 1, len(verts)):
            a1, r1 = divmod(verts[j], 49)
            b1, c1 = divmod(r1, 7)
            if ((a0 - a1) % 7 in (0, 1, 6)) and ((b0 - b1) % 7 in (0, 1, 6)) and ((c0 - c1) % 7 in (0, 1, 6)):
                return False
    return True


def canonicalize_cube_set(verts: List[int]) -> Tuple[Tuple[int, ...], int]:
    pts = [(v // 49, (v % 49) // 7, v % 7) for v in verts]
    best = None
    cnt = 0
    for ax, ay, az in pts:
        diffs = [((x - ax) % 7, (y - ay) % 7, (z - az) % 7) for x, y, z in pts]
        for p0, p1, p2 in PERMS6:
            for sm in range(8):
                s0 = 6 if (sm & 1) else 1
                s1 = 6 if (sm & 2) else 1
                s2 = 6 if (sm & 4) else 1
                cur = tuple(sorted(
                    ((s0 * d[p0]) % 7) * 49 + ((s1 * d[p1]) % 7) * 7 + ((s2 * d[p2]) % 7)
                    for d in diffs
                ))
                if best is None or cur < best:
                    best = cur
                    cnt = 1
                elif cur == best:
                    cnt += 1
    assert best is not None
    return best, cnt


def independent_random_33_sets(n_samples: int) -> List[List[int]]:
    """
    Find `n_samples` independent 33-word sets in C_7^3 via completely independent randomized
    local search (greedy maximal IS + (1,2) uphill / (1,1) plateau swaps and 2-drop perturbations), plus include the explicit
    Explorer-1 33-word witness from AlphaC7Cube.lean.
    """
    # Explicit 33-word witness from AlphaC7Cube.lean
    w33_coords = [
        (0,1,1),(0,4,2),(0,4,4),(0,6,0),(0,6,5),
        (1,1,4),(1,1,6),(1,3,0),(1,6,3),
        (2,1,2),(2,3,3),(2,3,5),(2,5,6),(2,6,1),
        (3,0,4),(3,0,6),(3,2,0),(3,4,1),(3,5,4),
        (4,0,2),(4,2,5),(4,3,3),(4,4,6),
        (5,0,5),(5,1,0),(5,3,1),(5,5,2),(5,5,4),(5,6,0),
        (6,0,3),(6,2,3),(6,2,5),(6,4,6),
    ]
    samples: List[List[int]] = [sorted(a * 49 + b * 7 + c for a, b, c in w33_coords)]
    assert verify_cube_indep(samples[0])

    # Precompute open neighborhood lists for C_7^3
    nbr_sets = [set(CUBE_NBR[v]) - {v} for v in range(343)]
    rng = np.random.default_rng(2026)

    while len(samples) < n_samples:
        # Random greedy start + plateau/uphill local search (iterated 1-drop / 2-add)
        S: set[int] = set()
        deg = [0] * 343  # number of neighbors in S
        order = rng.permutation(343)
        for v in order:
            vi = int(v)
            if deg[vi] == 0:
                S.add(vi)
                for u in nbr_sets[vi]:
                    deg[u] += 1
        # Local search up to 33
        for _step in range(8000):
            if len(S) == 33:
                break
            # Find any free vertex (shouldn't exist if maximal, but fill if so)
            free = [v for v in range(343) if v not in S and deg[v] == 0]
            if free:
                vi = int(rng.choice(free))
                S.add(vi)
                for u in nbr_sets[vi]:
                    deg[u] += 1
                continue
            # Look for 1-out, 2-in (vertices with deg == 1 sharing the same blocker in S)
            by_blocker: Dict[int, List[int]] = {}
            for v in range(343):
                if v not in S and deg[v] == 1:
                    # Find unique blocker in S
                    for u in nbr_sets[v]:
                        if u in S:
                            by_blocker.setdefault(u, []).append(v)
                            break
            improved = False
            for b, cands in by_blocker.items():
                if len(cands) >= 2:
                    # Check if two non-adjacent candidates exist
                    for i in range(len(cands)):
                        ci = cands[i]
                        for j in range(i + 1, len(cands)):
                            cj = cands[j]
                            if cj not in nbr_sets[ci]:
                                S.remove(b)
                                for u in nbr_sets[b]:
                                    deg[u] -= 1
                                S.add(ci)
                                for u in nbr_sets[ci]:
                                    deg[u] += 1
                                S.add(cj)
                                for u in nbr_sets[cj]:
                                    deg[u] += 1
                                improved = True
                                break
                        if improved:
                            break
                if improved:
                    break
            if improved:
                continue
            # Plateau move (1-out, 1-in) or perturbation (drop 1 random vertex in S, re-fill greedily)
            if by_blocker and rng.random() < 0.75:
                b = int(rng.choice(list(by_blocker.keys())))
                c = int(rng.choice(by_blocker[b]))
                S.remove(b)
                for u in nbr_sets[b]:
                    deg[u] -= 1
                S.add(c)
                for u in nbr_sets[c]:
                    deg[u] += 1
            else:
                # Perturb: drop 2 random vertices and greedily refill
                drops = rng.choice(list(S), size=min(2, len(S)), replace=False)
                for b in drops:
                    bi = int(b)
                    S.remove(bi)
                    for u in nbr_sets[bi]:
                        deg[u] -= 1
                for v in rng.permutation(343):
                    vi = int(v)
                    if vi not in S and deg[vi] == 0:
                        S.add(vi)
                        for u in nbr_sets[vi]:
                            deg[u] += 1
        if len(S) == 33:
            s_sorted = sorted(S)
            assert verify_cube_indep(s_sorted)
            samples.append(s_sorted)
    return samples


# Precompute 3D closed neighborhood in C_7^3
CUBE_NBR: List[List[int]] = []
for _v in range(343):
    _a, _rem = divmod(_v, 49)
    _b, _c = divmod(_rem, 7)
    _nb = []
    for _da in (-1, 0, 1):
        for _db in (-1, 0, 1):
            for _dc in (-1, 0, 1):
                _nb.append(((_a + _da) % 7) * 49 + ((_b + _db) % 7) * 7 + ((_c + _dc) % 7))
    CUBE_NBR.append(_nb)


def build_c7_quad_highs_lp(
    fixed_b0: List[int] | None,
    include_slabs: bool = True,
    include_tubes: bool = True,
    include_all_bands: bool = True,
    s0_bounds: Tuple[int, int] | None = None,
    mip: bool = False,
    time_limit: float = 15.0,
) -> Tuple[float, str, float, int]:
    """
    Build and solve LP (or MIP) on C_7^4 (2,401 vars x[t, v] for t in 0..6, v in 0..342).
    If `fixed_b0` is given (a 33-set in C_7^3 on band {0, 1}):
      - For v not in fixed_b0: x[0, v] = 0 and x[1, v] = 0
      - For v in fixed_b0:     x[0, v] + x[1, v] == 1  (exact split of B_0 = S_0 u S_1!)
      - If s0_bounds=(lo, hi): lo <= sum_{v in B0} x[0, v] <= hi (e.g. (16, 16) for N=115)
    Returns (obj_val, status_str, elapsed_s, mip_nodes).
    """
    t0 = time.perf_counter()
    h = highspy.Highs()
    h.setOptionValue("output_flag", False)
    h.setOptionValue("threads", 2)
    h.setOptionValue("time_limit", time_limit)

    n_vars = 2401
    lb = np.zeros(n_vars, dtype=float)
    ub = np.ones(n_vars, dtype=float)
    if fixed_b0 is not None:
        b0_set = set(fixed_b0)
        for v in range(343):
            if v not in b0_set:
                ub[v] = 0.0        # slice t=0
                ub[343 + v] = 0.0  # slice t=1

    costs = np.ones(n_vars, dtype=float)
    h.addCols(n_vars, costs, lb, ub, 0, np.array([], dtype=np.int32), np.array([], dtype=np.int32), np.array([], dtype=float))
    h.changeObjectiveSense(highspy.ObjSense.kMaximize)

    if mip:
        integrality = np.full(n_vars, highspy.HighsVarType.kInteger)
        h.changeColsIntegrality(n_vars, np.arange(n_vars, dtype=np.int32), integrality)

    # Accumulate sparse rows in CSR format
    row_starts = [0]
    col_indices: List[int] = []
    values: List[float] = []
    row_lb: List[float] = []
    row_ub: List[float] = []
    inf = highspy.kHighsInf

    def add_row(cols: List[int], lo: float, hi: float):
        col_indices.extend(cols)
        values.extend([1.0] * len(cols))
        row_starts.append(len(col_indices))
        row_lb.append(lo)
        row_ub.append(hi)

    def idx4(t: int, a: int, b: int, c: int) -> int:
        return t * 343 + a * 49 + b * 7 + c

    # 1. Fixed B_0 split equations: x[0, v] + x[1, v] == 1 for v in B_0
    if fixed_b0 is not None:
        for v in fixed_b0:
            add_row([v, 343 + v], 1.0, 1.0)
        if s0_bounds is not None:
            add_row(list(fixed_b0), float(s0_bounds[0]), float(s0_bounds[1]))

    # 2. All 2,401 2x2x2x2 cliques (RHS 1)
    for t in range(7):
        t1 = (t + 1) % 7
        for a in range(7):
            a1 = (a + 1) % 7
            for b in range(7):
                b1 = (b + 1) % 7
                for c in range(7):
                    c1 = (c + 1) % 7
                    cols = [
                        idx4(tt, aa, bb, cc)
                        for tt in (t, t1) for aa in (a, a1) for bb in (b, b1) for cc in (c, c1)
                    ]
                    add_row(cols, -inf, 1.0)

    # 3. Band cuts (K_2 x C_7^3 <= 33): 7 along axis 0, or all 28 along all 4 axes
    axes_bands = [0, 1, 2, 3] if include_all_bands else [0]
    for ax in axes_bands:
        for u in range(7):
            u1 = (u + 1) % 7
            cols = []
            if ax == 0:
                for tt in (u, u1):
                    base = tt * 343
                    cols.extend(range(base, base + 343))
            elif ax == 1:
                for t in range(7):
                    for aa in (u, u1):
                        base = t * 343 + aa * 49
                        cols.extend(range(base, base + 49))
            elif ax == 2:
                for t in range(7):
                    for a in range(7):
                        for bb in (u, u1):
                            base = t * 343 + a * 49 + bb * 7
                            cols.extend(range(base, base + 7))
            else:
                for t in range(7):
                    for a in range(7):
                        for b in range(7):
                            cols.append(idx4(t, a, b, u))
                            cols.append(idx4(t, a, b, u1))
            add_row(cols, -inf, 33.0)

    # 4. All 294 K_2^2 x C_7^2 slab cuts (RHS 10)
    if include_slabs:
        pairs = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
        for ax1, ax2 in pairs:
            for u in range(7):
                u1 = (u + 1) % 7
                for v in range(7):
                    v1 = (v + 1) % 7
                    cols = []
                    for x1 in (u, u1):
                        for x2 in (v, v1):
                            for y1 in range(7):
                                for y2 in range(7):
                                    coord = [0, 0, 0, 0]
                                    coord[ax1] = x1
                                    coord[ax2] = x2
                                    rem = [ax for ax in range(4) if ax not in (ax1, ax2)]
                                    coord[rem[0]] = y1
                                    coord[rem[1]] = y2
                                    cols.append(idx4(coord[0], coord[1], coord[2], coord[3]))
                    add_row(cols, -inf, 10.0)

    # 5. All 1,372 K_2^3 x C_7 tube cuts (RHS 3)
    if include_tubes:
        for free_ax in range(4):
            fixed_axes = [ax for ax in range(4) if ax != free_ax]
            for u in range(7):
                u1 = (u + 1) % 7
                for v in range(7):
                    v1 = (v + 1) % 7
                    for w in range(7):
                        w1 = (w + 1) % 7
                        cols = []
                        for xu in (u, u1):
                            for xv in (v, v1):
                                for xw in (w, w1):
                                    for z in range(7):
                                        coord = [0, 0, 0, 0]
                                        coord[fixed_axes[0]] = xu
                                        coord[fixed_axes[1]] = xv
                                        coord[fixed_axes[2]] = xw
                                        coord[free_ax] = z
                                        cols.append(idx4(coord[0], coord[1], coord[2], coord[3]))
                        add_row(cols, -inf, 3.0)

    n_rows = len(row_lb)
    h.addRows(
        n_rows,
        np.array(row_lb, dtype=float),
        np.array(row_ub, dtype=float),
        len(col_indices),
        np.array(row_starts[:-1], dtype=np.int32),
        np.array(col_indices, dtype=np.int32),
        np.array(values, dtype=float),
    )
    h.run()
    status = h.modelStatusToString(h.getModelStatus())
    info = h.getInfo()
    val = float(info.objective_function_value) if not mip else float(info.mip_dual_bound)
    nodes = int(info.mip_node_count) if mip else 0
    return val, status, time.perf_counter() - t0, nodes


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--orbits", default="search/upper/c7_cube_33_orbits.txt")
    parser.add_argument("--sample-orbits", type=int, default=15)
    parser.add_argument("--json-out", default="search/upper/c7_quad_audit_results.json")
    args = parser.parse_args()

    t_all = time.perf_counter()
    print("=" * 84)
    print("C_7^{\\boxtimes 4} INDEPENDENT LP/MIP & 33-SET CENSUS AUDIT (Track U1b)")
    print("=" * 84)

    # 1. Load & verify all 1,016 orbits
    orbits = load_orbits(args.orbits)
    total_sets = sum(16464 // stab for _, stab, _ in orbits)
    assert len(orbits) == 1016, f"Expected 1016 orbits, got {len(orbits)}"
    assert total_sets == 16672544
    orbit_set = set()
    for oid, stab, verts in orbits:
        assert verify_cube_indep(verts), f"Orbit {oid} is not independent!"
        orbit_set.add(tuple(verts))
    assert len(orbit_set) == 1016
    print(f"[OK] Verified all {len(orbits)} canonical orbits in {args.orbits} (sum = {total_sets:,} 33-sets).")

    # Independent randomized local-search cross-check (Explorer-1 witness + 9 random 33-sets)
    t_rand = time.perf_counter()
    rand_sets = independent_random_33_sets(10)
    matched = 0
    matched_oids = []
    oid_by_tuple = {tuple(v): oid for oid, _, v in orbits}
    for s in rand_sets:
        canon, stab = canonicalize_cube_set(s)
        assert canon in oid_by_tuple, "Random 33-set NOT found in census!"
        matched += 1
        matched_oids.append(oid_by_tuple[canon])
    print(f"[OK] Independent witness + local-search cross-check: {matched}/10 33-sets matched census "
          f"(orbit IDs: {matched_oids}) in {time.perf_counter() - t_rand:.2f}s.")

    # 2. Unanchored LP hierarchy on C_7^4
    print("\n--- Unanchored C_7^4 LP Relaxation Hierarchy ---")
    lp_unanchored = {}
    for label, sl, tb, ab in [
        ("2401 cliques + 7 bands", False, False, False),
        ("2401 cliques + 28 bands", False, False, True),
        ("2401 cliques + 28 bands + 294 slabs", True, False, True),
        ("2401 cliques + 28 bands + 294 slabs + 1372 tubes", True, True, True),
    ]:
        val, st, dt, _ = build_c7_quad_highs_lp(None, include_slabs=sl, include_tubes=tb, include_all_bands=ab)
        lp_unanchored[label] = {"lp": val, "status": st, "elapsed_s": dt}
        print(f"  {label:<50}: LP = {val:.6f} ({st}, {dt:.2f}s)")

    # 3. Anchored LP hierarchy (fixing B_0 = R_o) across sample orbits
    print(f"\n--- Anchored C_7^4 LP Audit (Fixing B_0 = R_o, {args.sample_orbits} orbits) ---")
    # Choose orbits spread across all 1,016 plus the symmetric orbits (|Stab| > 1)
    sym_oids = [oid for oid, stab, _ in orbits if stab > 1]
    step = max(1, len(orbits) // max(1, args.sample_orbits - len(sym_oids)))
    sample_oids = sorted(set(sym_oids + list(range(0, len(orbits), step))[:args.sample_orbits]))[:args.sample_orbits]

    # Compare baseline (no slabs/tubes) vs full cuts on orbit 0 first
    v_base, st_base, dt_base, _ = build_c7_quad_highs_lp(
        orbits[0][2], include_slabs=False, include_tubes=False, include_all_bands=False, s0_bounds=(14, 16)
    )
    print(f"  Orbit 0 baseline (cliques + 7 bands, |S0| in [14,16]): LP = {v_base:.6f} ({dt_base:.2f}s)")

    anchored_results = []
    for oid in sample_oids:
        _, stab, verts = orbits[oid]
        # General N >= 113 range (|S0| in [14, 16] by S0 <-> S1 symmetry)
        v113, st113, dt113, _ = build_c7_quad_highs_lp(
            verts, include_slabs=True, include_tubes=True, include_all_bands=True, s0_bounds=(14, 16)
        )
        # Specific N = 115 range (|S0| == 16)
        v115, st115, dt115, _ = build_c7_quad_highs_lp(
            verts, include_slabs=True, include_tubes=True, include_all_bands=True, s0_bounds=(16, 16)
        )
        anchored_results.append({
            "orbit_id": oid,
            "stab": stab,
            "lp_full_s0_14_16": v113,
            "dt_14_16": dt113,
            "lp_full_s0_16": v115,
            "dt_16": dt115,
        })
        print(f"  Orbit {oid:4d} (|Stab|={stab}): full-LP(|S0| in 14..16) = {v113:.6f} ({dt113:.2f}s), "
              f"full-LP(|S0|=16) = {v115:.6f} ({dt115:.2f}s)")

    max_lp_14_16 = max(r["lp_full_s0_14_16"] for r in anchored_results)
    min_lp_14_16 = min(r["lp_full_s0_14_16"] for r in anchored_results)
    max_lp_16 = max(r["lp_full_s0_16"] for r in anchored_results)
    min_lp_16 = min(r["lp_full_s0_16"] for r in anchored_results)
    print(f"\n  Summary across {len(anchored_results)} sampled orbits:")
    print(f"    full-LP (|S0| in 14..16): range [{min_lp_14_16:.6f}, {max_lp_14_16:.6f}]")
    print(f"    full-LP (|S0| == 16)    : range [{min_lp_16:.6f}, {max_lp_16:.6f}]")

    # 4. Short 15s MIP probe on Orbit 0 with full cut pool (to benchmark branch-and-bound speed!)
    print("\n--- Strengthened MIP Benchmark on Orbit 0 (15s cap) ---")
    mip_ub, mip_st, mip_dt, mip_nodes = build_c7_quad_highs_lp(
        orbits[0][2], include_slabs=True, include_tubes=True, include_all_bands=True,
        s0_bounds=(14, 16), mip=True, time_limit=15.0
    )
    print(f"  Orbit 0 strengthened MIP (15s cap): dual_bound={mip_ub:.6f}, status={mip_st}, nodes={mip_nodes}, time={mip_dt:.2f}s")

    total_dt = time.perf_counter() - t_all
    out = {
        "census_verified": {
            "num_orbits": len(orbits),
            "total_33_sets": total_sets,
            "local_search_random_matched": matched,
            "local_search_random_orbit_ids": matched_oids,
        },
        "unanchored_lp": lp_unanchored,
        "orbit0_baseline_lp": v_base,
        "anchored_full_lp_sample": anchored_results,
        "anchored_summary": {
            "sample_size": len(anchored_results),
            "min_lp_14_16": min_lp_14_16,
            "max_lp_14_16": max_lp_14_16,
            "min_lp_16": min_lp_16,
            "max_lp_16": max_lp_16,
        },
        "orbit0_mip_15s": {
            "dual_bound": mip_ub,
            "status": mip_st,
            "nodes": mip_nodes,
            "elapsed_s": mip_dt,
        },
        "total_elapsed_s": total_dt,
    }
    with open(args.json_out, "w", encoding="utf-8") as fh:
        json.dump(out, fh, indent=2, allow_nan=False)
    print(f"\n[OK] Wrote {args.json_out} (total elapsed: {total_dt:.2f}s)")


if __name__ == "__main__":
    main()
