#!/usr/bin/env python3
"""
Stage 1 SAT / Cliquer / Subgroup search for (C7^c)^⊠4 exactness and (C7^c)^⊠5 >= 36..39.
"""
import json
import subprocess
import sys
import tempfile
import time
from itertools import combinations, product
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType

MOD = 7
ADJ_C7 = {1, 6}


def is_sep(u, v):
    return any((a - b) % 7 in ADJ_C7 for a, b in zip(u, v))


def is_indep_set(words):
    for i in range(len(words)):
        for j in range(i + 1, len(words)):
            if not is_sep(words[i], words[j]):
                return False
    return True


def verify_explorers():
    # S35 from Explorer 2
    g = (1, 2, 3, 1, 2)
    seeds = [(0, 0, 0, 0, 0), (0, 0, 0, 1, 1), (0, 0, 1, 4, 3), (0, 2, 0, 2, 1), (0, 2, 1, 1, 4)]
    s35 = [tuple((s[k] + t * g[k]) % 7 for k in range(5)) for s in seeds for t in range(7)]
    assert len(set(s35)) == 35
    assert is_indep_set(s35)
    print(f"[verify] Explorer 2 S35 verified: 35 distinct indep words in (C7^c)^⊠5, 35^(1/5)={35**(1/5):.9f}")

    # d=4 (17,1,17,7) ValidTuple from Explorer 2
    I17 = [
        (0, 0, 0, 0), (1, 2, 3, 5), (1, 2, 4, 3), (1, 4, 3, 6), (2, 2, 1, 3),
        (2, 4, 1, 4), (2, 4, 2, 1), (2, 6, 2, 0), (3, 1, 4, 3), (3, 1, 5, 5),
        (3, 6, 4, 2), (4, 1, 3, 5), (4, 3, 2, 1), (5, 3, 5, 6), (5, 5, 6, 4),
        (6, 5, 3, 4), (6, 5, 4, 2)
    ]
    W17 = [
        (0, 0, 0, 0), (1, 2, 3, 5), (1, 2, 4, 3), (2, 2, 1, 3), (2, 4, 1, 4),
        (2, 4, 2, 1), (3, 1, 5, 5), (3, 4, 5, 6), (3, 6, 4, 2), (4, 1, 3, 5),
        (4, 3, 2, 1), (4, 6, 2, 2), (5, 3, 5, 6), (5, 3, 6, 3), (5, 5, 6, 4),
        (6, 5, 3, 4), (6, 5, 4, 2)
    ]
    s = (3, 6, 4, 2)
    q = (1, 4, 2, 4)
    X17 = [tuple(((-w[0] + 2) % 7, (w[1] + 5) % 7, (w[2] + 3) % 7, (w[3] + 3) % 7)) for w in W17]
    assert len(set(I17)) == 17 and is_indep_set(I17)
    assert len(set(X17)) == 17 and is_indep_set(X17)
    assert not is_sep(s, q)
    for w in I17:
        if w != s:
            assert is_sep(w, q)
    in_s = sum(1 for x in X17 if not is_sep(x, s))
    in_q = sum(1 for x in X17 if not is_sep(x, q))
    both = sum(1 for x in X17 if not is_sep(x, s) and not is_sep(x, q))
    d_out = len(X17) - (in_s + in_q - both)
    assert both == 0 and d_out == 7 and in_s == 5 and in_q == 5
    print(f"[verify] Explorer 2 d=4 ValidTuple (17,1,17,{d_out}) verified: in_s={in_s}, in_q={in_q}, both={both}")


def check_d4_exact():
    """
    Determine exact alpha((C7^c)^⊠4) in {17, 18} by solving the 4 canonical K3-slice profiles.
    Note: C7^c^⊠3 has alpha=8. Any 18-word set in C7^c^⊠4 has slice counts (n_0..n_6)
    with sum=18 and n_i + n_{i+2} + n_{i+4} <= 8 and n_i + n_{i+2} + n_{i+5} <= 8.
    """
    t0 = time.time()
    V3 = list(product(range(7), repeat=3))
    # Precompute 3D adjacency (close = NOT separated)
    # Two words in V4 (x0, u) and (y0, v): close iff (x0-y0)%7 not in {1,6} AND close3(u, v)
    profiles = [
        (2, 2, 2, 3, 3, 3, 3),
        (2, 2, 3, 3, 2, 3, 3),
        (2, 2, 2, 2, 2, 4, 4),
        (2, 2, 2, 2, 3, 4, 3),
    ]
    # Better: directly encode V4 (2401 vars) into Cadical195 with totalizer >= 18 AND slice upper/lower bounds!
    # Actually let's use CP-SAT or Cadical195 per profile! With fixed slice sizes n_0..n_6, each slice i has <= n_i and >= n_i (so == n_i)!
    # Wait: even better, for each profile, fix slice 0 to contain (0,0,0) (by ZMod 7^3 translation symmetry if n_0 >= 1)!
    # Even better: check with Cadical195 + pySAT CardEnc.equals on each slice!
    V4 = list(product(range(7), repeat=4))
    idx4 = {v: i + 1 for i, v in enumerate(V4)}
    # Conflict clauses (pairs that are close in (C7^c)^⊠4)
    # A word x is close to y iff forall k, (x_k - y_k)%7 in {0,2,3,4,5}.
    close_deltas = [0, 2, 3, 4, 5]
    conflicts = []
    for i, u in enumerate(V4):
        for d0 in close_deltas:
            v0 = (u[0] + d0) % 7
            for d1 in close_deltas:
                v1 = (u[1] + d1) % 7
                for d2 in close_deltas:
                    v2 = (u[2] + d2) % 7
                    for d3 in close_deltas:
                        v3 = (u[3] + d3) % 7
                        v = (v0, v1, v2, v3)
                        j = idx4[v] - 1
                        if i < j:
                            conflicts.append([-(i + 1), -(j + 1)])

    print(f"[d4] Built {len(conflicts)} conflict clauses on 2401 vars in {time.time()-t0:.2f}s")
    # Also add K3 slice bounds? Wait: CardEnc per slice for each profile is already super tight!
    for pi, prof in enumerate(profiles):
        tp = time.time()
        with Cadical195(bootstrap_with=conflicts) as solver:
            top = 2401
            # Fix first element of slice 0 to (0,0,0,0) by ZMod 7^4 translation!
            solver.add_clause([idx4[(0, 0, 0, 0)]])
            # Also fix lexicographically smallest element in slice 0? No, let's see how fast exact slice cardinality is!
            for s0 in range(7):
                lits = [idx4[(s0, a, b, c)] for a, b, c in V3]
                cnf = CardEnc.equals(lits=lits, bound=prof[s0], top_id=top, encoding=EncType.totalizer)
                top = cnf.nv
                solver.append_formula(cnf)
            # Also add K3-slice pairwise / triple constraints from alpha(C7^c^⊠3)=8:
            # For every 3-tuple of slices forming K3 in C7^c, their sum is <= 8 (already satisfied by prof).
            sat = solver.solve()
            dt = time.time() - tp
            print(f"[d4] Profile {pi} {prof}: SAT={sat} ({dt:.2f}s)")
            if sat:
                model = solver.get_model()
                sol = [V4[v - 1] for v in model[:2401] if v > 0]
                assert len(sol) == 18 and is_indep_set(sol)
                print(f"[d4] BREAKTHROUGH! Found 18-word set in (C7^c)^⊠4!")
                return sol
    print(f"[d4] PROVED alpha((C7^c)^⊠4) = 17! All 4 K3-slice profiles UNSAT in {time.time()-t0:.2f}s")
    return None


def check_d5_negation_symmetric():
    """
    Search negation-symmetric codes in (C7^c)^⊠5:
    - Origin + k pairs {w, -w}: 2k+1 words (k=18 => 37, k=19 => 39)
    - No origin + k pairs {w, -w}: 2k words (k=18 => 36, k=19 => 38)
    """
    t0 = time.time()
    V5 = list(product(range(7), repeat=5))
    pairs = []
    for w in V5:
        neg = tuple((-x) % 7 for x in w)
        if w < neg and is_sep(w, neg):
            pairs.append((w, neg))
    print(f"[d5-neg] Self-separated negation pairs: {len(pairs)} (built in {time.time()-t0:.2f}s)")
    # Build adjacency between pairs via bitsets or cliquer/cadical!
    # Wait: 8403 pairs? Let's check exact count of self-separated pairs!
    # Two pairs {u,-u} and {v,-v} are compatible iff sep(u,v) AND sep(u,-v).
    # For origin (0,0,0,0,0): compatible with {u,-u} iff u has at least one coord in {1,6}.
    # Let's test via cliquer (exact max clique) on the ~8000-vertex graph? Wait: let's check len(pairs) first, and check with origin vs without origin.
    import numpy as np
    P_arr = np.array([p[0] for p in pairs], dtype=np.int8)
    # Let's filter pairs compatible with origin first!
    orig_mask = np.any((P_arr == 1) | (P_arr == 6), axis=1)
    P_orig = [pairs[i] for i in range(len(pairs)) if orig_mask[i]]
    print(f"[d5-neg] Pairs compatible with origin: {len(P_orig)}")
    # Test with Cadical195 or cliquer? Wait: on ~6800 vertices, a dense graph max-clique is HUGE for cliquer if clique number is 17-18.
    # Let's check edge density first, and test Cadical195!
    # Actually let's build conflict clauses for P_orig? Conflict density: two pairs conflict if (NOT sep(u,v)) OR (NOT sep(u,-v)).
    # Density of non-sep is (5/7)^5 = 0.1859, so conflict probability for two pairs is ~ 1 - (1 - 0.1859)^2 ~ 33.7%!
    # That's 1/3 of pairs = ~7.7M clauses, too big for naive CNF without symmetry breaking, OR we can use C++ ILS/exact!
    # Wait: in C++ bitset ILS on 6800 vertices, 100k iterations/sec!
    return len(pairs), len(P_orig)


def check_d5_cyclic_subgroups():
    """
    Check cyclic subgroups C_{k, n}^5: words of form (i * w_0, ..., i * w_4) mod 7?
    No, in ZMod 7^5 there are only order 7 subgroups; cyclic subgroups in ZMod n (circular graphs)
    don't apply directly to ZMod 7^5 unless we use sub-integer mod 7! Wait: in C_7, the vertex set is Z_7,
    so any subgroup of (Z_7^5, +) has order 1, 7, 49, 343, ...
    Wait: what about cosets of an order-7 subgroup (7*5=35, 7*6=42) or order-1 + order-7?
    Wait: 7*5 = 35, 7*6 = 42 > 41 (impossible since Lovasz bound is 41.07).
    What about union of 5 orbits + 1..4 points (handled in C++), or affine subspaces, or circulant/negation?
    """
    pass


if __name__ == "__main__":
    verify_explorers()
    if "--d4-exact" in sys.argv:
        check_d4_exact()
    if "--d5-neg" in sys.argv:
        check_d5_negation_symmetric()
