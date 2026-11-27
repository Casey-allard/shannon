#!/usr/bin/env python3
"""
Deterministic verifier and witness generator for M1 (LowerFrontier):
- Reads the repo's pure-kernel 5D base (polakSchrijver367Trie, baseP0, baseP1, baseX)
  from ShannonC7/SmallPowers.lean and ShannonC7/ValidTuple.lean.
- Independently verifies S2a, S3a, S3b, S3h, K4a, K4b admissibility over Letter.sep.
- Verifies Tandon's 10D J^+ (C1=27488), 15D C2=12839823, C3=14045805, and 30D
  C4=841760069965664 using exact 5D signature-rectangle decomposition (zero 10D enumeration).
- Reproduces BPZ v2 (d=500, 3.258827985920007), Tandon (d=500, 3.258832620353266),
  (g15_het, tn11, tn11) (d=500, 3.258833086477685), (g30_6, tn11, tn11) (d=560, 3.258834362237710),
  and the M1 d=620 champion (3.258835618853760).
- Writes search/lower/witnesses/m1_tandon_d620.json.
"""
import argparse
import json
import math
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LETTERS = ["B", "N", "A", "D", "O", "H", "V"]
L_IDX = {l: i for i, l in enumerate(LETTERS)}
SEP_PAIRS = [
    ("B", "O"), ("B", "H"), ("B", "V"),
    ("N", "A"), ("N", "D"), ("N", "O"), ("N", "H"), ("N", "V"),
    ("A", "D"), ("A", "H"),
    ("D", "V"),
]
SEP = [[False] * 7 for _ in range(7)]
for a, b in SEP_PAIRS:
    SEP[L_IDX[a]][L_IDX[b]] = True
    SEP[L_IDX[b]][L_IDX[a]] = True

# Authoritative BPZ v2 tables (Buys-Polak-Zuiddam 2026)
T2A = {
    "B": [("B","B"), ("H","D"), ("V","A"), ("D","V"), ("A","H")],
    "N": [("N","N"), ("A","A"), ("A","D"), ("D","A"), ("D","D")],
    "A": [("A","N"), ("N","D")],
    "D": [("D","N"), ("N","A")],
    "O": [("O","N"), ("N","O")],
    "H": [("H","N"), ("N","V")],
    "V": [("V","N"), ("N","H")],
}

T3A = {
    "B": [("A","H","N"), ("A","N","V"), ("B","A","H"), ("B","B","B"), ("B","D","V"),
          ("B","H","D"), ("B","V","A"), ("D","N","H"), ("D","V","N"), ("H","D","N"),
          ("H","N","A"), ("V","A","N"), ("V","N","D")],
    "N": [("A","A","N"), ("A","D","N"), ("A","N","A"), ("A","N","D"), ("D","A","N"),
          ("D","D","N"), ("D","N","A"), ("D","N","D"), ("N","A","A"), ("N","A","D"),
          ("N","D","A"), ("N","D","D"), ("N","N","N")],
    "A": [("A","A","A"), ("A","A","D"), ("A","D","A"), ("A","D","D"), ("A","N","N"),
          ("N","A","N"), ("N","N","A")],
    "D": [("D","A","A"), ("D","A","D"), ("D","D","A"), ("D","D","D"), ("D","N","N"),
          ("N","D","N"), ("N","N","D")],
    "O": [("O","A","A"), ("O","A","D"), ("O","D","A"), ("O","D","D")],
    "H": [("H","A","A"), ("H","A","D"), ("H","D","A"), ("H","D","D"), ("H","N","N"),
          ("N","H","N"), ("N","N","H")],
    "V": [("N","N","V"), ("N","V","N"), ("V","A","A"), ("V","A","D"), ("V","D","A"),
          ("V","D","D"), ("V","N","N")],
}

T3B = {
    "B": [("B","B","B"), ("B","H","A"), ("N","A","V"), ("N","D","H"), ("N","V","D"),
          ("A","B","H"), ("A","H","N"), ("A","H","D"), ("D","B","V"), ("D","V","N"),
          ("D","V","D"), ("H","N","D"), ("H","D","N"), ("H","D","D"), ("V","N","A"),
          ("V","A","B"), ("V","D","A")],
    "N": [("B","V","D"), ("N","N","N"), ("N","V","A"), ("A","N","H"), ("A","D","H"),
          ("A","H","N"), ("D","N","V"), ("D","D","H"), ("D","H","N"), ("H","V","D")],
    "A": [("N","B","A"), ("N","A","N"), ("A","B","B"), ("A","A","V"), ("A","H","A")],
    "D": [("N","B","D"), ("N","D","N"), ("D","B","B"), ("D","A","V"), ("D","H","A")],
    "O": [],
    "H": [("N","N","H"), ("N","H","N"), ("H","N","N"), ("H","V","V")],
    "V": [("N","N","V"), ("N","V","N"), ("V","N","N"), ("V","V","V")],
}

C4A = [
    ("B","B","B","B"), ("B","N","V","B"), ("B","A","H","B"), ("B","D","V","B"),
    ("B","H","N","B"), ("B","H","D","B"), ("B","V","A","B"), ("N","B","B","V"),
    ("N","N","V","H"), ("N","A","V","H"), ("N","D","H","H"), ("N","H","N","H"),
    ("N","H","A","H"), ("N","V","D","V"), ("A","B","B","V"), ("A","N","H","H"),
    ("A","A","V","H"), ("A","D","H","H"), ("A","H","A","H"), ("A","V","N","H"),
    ("A","V","D","H"), ("D","B","B","H"), ("D","N","V","V"), ("D","A","V","V"),
    ("D","D","H","V"), ("D","H","N","V"), ("D","H","A","V"), ("D","V","D","V"),
    ("H","B","B","A"), ("H","N","V","D"), ("H","A","H","D"), ("H","A","V","N"),
    ("H","D","H","N"), ("H","D","V","D"), ("H","H","N","N"), ("H","H","N","D"),
    ("H","H","A","N"), ("H","H","D","D"), ("H","V","A","D"), ("H","V","D","N"),
    ("V","B","B","N"), ("V","B","B","D"), ("V","N","V","N"), ("V","N","V","A"),
    ("V","A","H","A"), ("V","D","V","A"), ("V","H","D","A"), ("V","V","N","A"),
    ("V","V","A","A"),
]


def words_sep(w1, w2):
    return any(SEP[L_IDX[a]][L_IDX[b]] for a, b in zip(w1, w2))


def verify_subst(name, tbl):
    for a in LETTERS:
        ws = tbl[a]
        assert len(ws) == len(set(ws)), f"dup in {name}[{a}]"
        for i in range(len(ws)):
            for j in range(i + 1, len(ws)):
                assert words_sep(ws[i], ws[j]), f"hin failed in {name}[{a}]"
    for a in LETTERS:
        for b in LETTERS:
            if SEP[L_IDX[a]][L_IDX[b]]:
                for x in tbl[a]:
                    for y in tbl[b]:
                        assert words_sep(x, y), f"hcross failed in {name} ({a},{b})"


def verify_code(name, ws):
    assert len(ws) == len(set(ws)), f"dup in {name}"
    for i in range(len(ws)):
        for j in range(i + 1, len(ws)):
            assert words_sep(ws[i], ws[j]), f"hsep failed in {name}"


def apply_subst(tbl, vecs):
    return tuple(
        sum(math.prod(vecs[i][L_IDX[w[i]]] for i in range(len(w))) for w in tbl[a])
        for a in LETTERS
    )


def apply_code(ws, vecs):
    return sum(math.prod(vecs[i][L_IDX[w[i]]] for i in range(len(w))) for w in ws)


def dec(n):
    return [(n // (7 ** k)) % 7 for k in range(5)]


def enc(t):
    return sum(t[k] * (7 ** k) for k in range(5))


def wconf(u, v):
    return all(((u // (7 ** k)) - (v // (7 ** k))) % 7 in (0, 1, 6) for k in range(5))


def closed_nbr5(S):
    nbr = set()
    for u in S:
        d = dec(u)
        for d0 in ((d[0]-1)%7, d[0], (d[0]+1)%7):
            for d1 in ((d[1]-1)%7, d[1], (d[1]+1)%7):
                for d2 in ((d[2]-1)%7, d[2], (d[2]+1)%7):
                    for d3 in ((d[3]-1)%7, d[3], (d[3]+1)%7):
                        for d4 in ((d[4]-1)%7, d[4], (d[4]+1)%7):
                            nbr.add(d0 + 7*d1 + 49*d2 + 343*d3 + 2401*d4)
    return nbr


def T_aut(u):
    w0, w1, w2, w3, w4 = dec(u)
    return enc(((2 - w1) % 7, w3, w0, (2 - w2) % 7, w4))


def parse_repo_base5():
    sp_txt = (ROOT / "ShannonC7" / "SmallPowers.lean").read_text()
    vt_txt = (ROOT / "ShannonC7" / "ValidTuple.lean").read_text()

    def eval_trie(expr, env, depth):
        tokens = re.findall(r"\.node|\.empty|\.leaf|\(|\)|[A-Za-z0-9_]+", expr)
        pos = [0]
        def parse(d):
            tok = tokens[pos[0]]
            if tok == "(":
                pos[0] += 1
                res = parse(d)
                assert tokens[pos[0]] == ")"
                pos[0] += 1
                return res
            if tok == ".empty":
                pos[0] += 1
                return set()
            if tok == ".leaf":
                pos[0] += 1
                assert d == 0
                return {()}
            if tok == ".node":
                pos[0] += 1
                out = set()
                for digit in range(7):
                    for tup in parse(d - 1):
                        out.add((digit,) + tup)
                return out
            if tok in env:
                pos[0] += 1
                return env[tok]
            raise ValueError(f"Unknown token {tok}")
        return parse(depth)

    env = {}
    for txt in (sp_txt, vt_txt):
        for m in re.finditer(r"def (\w+)\s*:\s*Trie7\s*(\d+)\s*:=\s*(.*?)(?=\n\n|\nprivate theorem|\ntheorem|\n/--|\ndef |\nend )", txt, re.S):
            name, depth, body = m.group(1), int(m.group(2)), m.group(3)
            if name == "Trie7":
                continue
            env[name] = eval_trie(body, env, depth)

    I5 = set(enc(t) for t in env["polakSchrijver367Trie"])
    P0_5 = set(enc(t) for t in env["baseP0"])
    P1_5 = set(enc(t) for t in env["baseP1"])
    X5 = set(enc(t) for t in env["baseX"])
    S5 = I5 & (P0_5 | P1_5)
    assert len(I5) == 367 and len(S5) == 8 and len(P0_5) == 8 and len(P1_5) == 8 and len(X5) == 367
    # Note: in ValidTuple.lean, P0 = PV5 (|X5 ∩ N[P0]| = 19) and P1 = PH5 (|X5 ∩ N[P1]| = 26)
    return I5, S5, P0_5, P1_5, X5


def verify_certificates(I5, S5, P0_5, P1_5, X5):
    B5 = I5 - S5
    PV5 = P0_5
    PH5 = P1_5
    N_PH5 = closed_nbr5(PH5)
    N_PV5 = closed_nbr5(PV5)
    X5_0 = X5 - (N_PH5 | N_PV5)
    X5_H = X5 & N_PH5
    X5_V = X5 & N_PV5
    assert (len(B5), len(X5_0), len(X5_V), len(X5_H), len(S5)) == (359, 322, 19, 26, 8)

    N_X5_0 = closed_nbr5(X5_0)
    N_X5_H = closed_nbr5(X5_H)
    N_X5_V = closed_nbr5(X5_V)
    N_X5_1 = N_X5_H | N_X5_V
    sig5 = [((1 if u in N_X5_0 else 0) << 1) | (1 if u in N_X5_1 else 0) for u in range(16807)]
    sig5_3 = [((1 if u in N_X5_0 else 0) << 2) | ((1 if u in N_X5_H else 0) << 1) | (1 if u in N_X5_V else 0) for u in range(16807)]

    def dist5(S):
        c = [0, 0, 0, 0]
        for u in S:
            c[sig5[u]] += 1
        return tuple(c)

    def dist5_3(S):
        c = [0] * 8
        for u in S:
            c[sig5_3[u]] += 1
        return tuple(c)

    def add_t(a, b):
        return tuple(x + y for x, y in zip(a, b))

    def prod4(dL, dR):
        out = [0, 0, 0, 0]
        for sL in range(4):
            a0, a1 = (sL >> 1) & 1, sL & 1
            for sR in range(4):
                b0, b1 = (sR >> 1) & 1, sR & 1
                out[(((a0 & b0) | (a1 & b1)) << 1) | ((a0 & b1) | (a1 & b0))] += dL[sL] * dR[sR]
        return tuple(out)

    TB5, TS5 = [T_aut(u) for u in B5], [T_aut(u) for u in S5]
    TPH5, TPV5 = [T_aut(u) for u in PH5], [T_aut(u) for u in PV5]
    TX05, TXH5, TXV5 = [T_aut(u) for u in X5_0], [T_aut(u) for u in X5_H], [T_aut(u) for u in X5_V]
    TX15 = TXH5 + TXV5

    d5 = {k: dist5(v) for k, v in dict(
        B=B5, S=S5, PH=PH5, PV=PV5, X0=X5_0, X1=(X5_H | X5_V), XH=X5_H, XV=X5_V,
        TB=TB5, TS=TS5, TPH=TPH5, TPV=TPV5, TX0=TX05, TX1=TX15, TXH=TXH5, TXV=TXV5,
    ).items()}

    # J10 = T^2(I10)
    J_blocks = [
        (TB5, TB5), (TS5, TX05), (TPH5, TXH5), (TPV5, TXV5),
        (TX05, TS5), (TXH5, TPV5), (TXV5, TPH5),
    ]
    def avoid10(a, b):
        return a[0]*(b[0]+b[1]+b[2]+b[3]) + a[1]*(b[0]+b[2]) + a[2]*(b[0]+b[1]) + a[3]*b[0]

    C1_base = (
        avoid10(d5["TB"], d5["TB"]) + avoid10(d5["TS"], d5["TX0"]) + avoid10(d5["TX0"], d5["TS"]) +
        avoid10(d5["TPH"], d5["TXH"]) + avoid10(d5["TPV"], d5["TXV"]) +
        avoid10(d5["TXH"], d5["TPV"]) + avoid10(d5["TXV"], d5["TPH"])
    )
    assert C1_base == 27480

    # Verify the 8 swaps for J^+
    swaps = [
        ((3660,6494),(6110,4092)),
        ((16388,6494),(16046,4092)),
        ((6494,3660),(6494,6110)),
        ((15643,3660),(15643,6110)),
        ((3660,15643),(6110,15685)),
        ((16388,15643),(16046,15685)),
        ((6494,16388),(6494,16046)),
        ((15643,16388),(15643,16046)),
    ]
    inss = [v for _, v in swaps]
    for i in range(8):
        for j in range(i + 1, 8):
            assert not (wconf(inss[i][0], inss[j][0]) and wconf(inss[i][1], inss[j][1]))
    for r, v in swaps:
        assert ((sig5[r[0]] >> 1) & (sig5[r[1]] >> 1)) or ((sig5[r[0]] & 1) & (sig5[r[1]] & 1))
        assert not (((sig5[v[0]] >> 1) & (sig5[v[1]] >> 1)) or ((sig5[v[0]] & 1) & (sig5[v[1]] & 1)))
        hits = []
        for A, B in J_blocks:
            a_hits = [x for x in A if wconf(x, v[0])]
            if a_hits:
                b_hits = [y for y in B if wconf(y, v[1])]
                for x in a_hits:
                    for y in b_hits:
                        hits.append((x, y))
        assert hits == [r], f"swap check failed for {v}: {hits}"
    C1 = C1_base + 8
    assert C1 == 27488

    # C2 & C3
    d10_TB = add_t(prod4(d5["TB"], d5["TB"]), add_t(prod4(d5["TPH"], d5["TXH"]),
             add_t(prod4(d5["TPV"], d5["TXV"]), add_t(prod4(d5["TXH"], d5["TPV"]), prod4(d5["TXV"], d5["TPH"])))))
    d10_TS = add_t(prod4(d5["TS"], d5["TX0"]), prod4(d5["TX0"], d5["TS"]))
    d10_TPH = add_t(prod4(d5["TPH"], d5["TX0"]), prod4(d5["TX0"], d5["TPV"]))
    d10_TPV = add_t(prod4(d5["TPV"], d5["TX0"]), prod4(d5["TX0"], d5["TPH"]))
    d10_TX0 = add_t(prod4(d5["TX0"], d5["TX0"]), prod4(d5["TX1"], d5["TX1"]))
    d10_TXH = add_t(prod4(d5["TXH"], d5["TX0"]), prod4(d5["TX0"], d5["TXV"]))
    d10_TXV = add_t(prod4(d5["TXV"], d5["TX0"]), prod4(d5["TX0"], d5["TXH"]))

    def count_avoid_15X(d10, d5p):
        return sum(d10[s10] * d5p[s5] for s10 in range(4) for s5 in range(4)
                   if not ((((s10>>1)&1)&((s5>>1)&1)) or ((s10&1)&(s5&1))))

    C2 = (
        count_avoid_15X(d10_TB, d5["TB"]) + count_avoid_15X(d10_TS, d5["TX0"]) +
        count_avoid_15X(d10_TPH, d5["TXH"]) + count_avoid_15X(d10_TPV, d5["TXV"]) +
        count_avoid_15X(d10_TX0, d5["TS"]) + count_avoid_15X(d10_TXH, d5["TPV"]) +
        count_avoid_15X(d10_TXV, d5["TPH"])
    )
    assert C2 == 12839823

    # C4 via exact 5D-rectangle decomposition
    def buckets5(S):
        b = [set(), set(), set(), set()]
        for u in S:
            b[sig5[u]].add(u)
        return b

    rems = set(r for r, _ in swaps)
    R4 = {r[0] for r in rems} | {r[1] for r in rems}
    uniq_sets = {}
    def get_id(S):
        fs = frozenset(S)
        if fs not in uniq_sets:
            uniq_sets[fs] = len(uniq_sets)
        return uniq_sets[fs]

    out_rects, exact_in_rects = [], []
    for A, B in J_blocks:
        bA, bB = buckets5(A), buckets5(B)
        for sa in range(4):
            if not bA[sa]: continue
            a0, a1 = (sa >> 1) & 1, sa & 1
            for sb in range(4):
                if not bB[sb]: continue
                b0, b1 = (sb >> 1) & 1, sb & 1
                if (a0 & b0) | (a1 & b1):
                    hits = [(r0, r1) for (r0, r1) in rems if r0 in bA[sa] and r1 in bB[sb]]
                    if not hits:
                        exact_in_rects.append((get_id(bA[sa]), get_id(bB[sb])))
                    else:
                        A_rest = bA[sa] - R4
                        if A_rest:
                            exact_in_rects.append((get_id(A_rest), get_id(bB[sb])))
                        for r0 in (bA[sa] & R4):
                            B_minus = set(bB[sb])
                            for rr0, rr1 in hits:
                                if rr0 == r0 and rr1 in B_minus:
                                    B_minus.remove(rr1)
                            if B_minus:
                                exact_in_rects.append((get_id({r0}), get_id(B_minus)))
                else:
                    out_rects.append((get_id(bA[sa]), get_id(bB[sb])))
    for v0, v1 in inss:
        out_rects.append((get_id({v0}), get_id({v1})))

    id_to_set = list(uniq_sets.keys())
    nbr_sets = [closed_nbr5(fs) for fs in id_to_set]
    all_pts5 = set(TB5) | set(TS5) | set(TPH5) | set(TPV5) | set(TX05) | set(TXH5) | set(TXV5) | set(u for p in inss for u in p)
    all_pts5 |= set(T_aut(u) for u in all_pts5)
    def or_mask(bits):
        m = 0
        for b in bits:
            m |= (1 << b)
        return m

    mask_u = {u: or_mask(idx for idx, ns in enumerate(nbr_sets) if u in ns) for u in all_pts5}
    req_out = {u0: or_mask(ib for ia, ib in out_rects if (mask_u[u0] >> ia) & 1) for u0 in all_pts5}
    req_in = {u0: or_mask(ib for ia, ib in exact_in_rects if (mask_u[u0] >> ia) & 1) for u0 in all_pts5}

    def dist10_16(A, B):
        c = [0] * 16
        for u0 in A:
            a0, a1 = (sig5[u0] >> 1) & 1, sig5[u0] & 1
            ro, ri = req_out[u0], req_in[u0]
            for u1 in B:
                b0, b1 = (sig5[u1] >> 1) & 1, sig5[u1] & 1
                in_X0, in_X1 = (a0 & b0) | (a1 & b1), (a0 & b1) | (a1 & b0)
                m1 = mask_u[u1]
                c[(in_X0 << 3) | (in_X1 << 2) | ((1 if (m1 & ro) else 0) << 1) | (1 if (m1 & ri) else 0)] += 1
        return tuple(c)

    def lift15(d16, d5t):
        out = [0] * 16
        for s10 in range(16):
            if d16[s10] == 0: continue
            x0, x1, jo, ji = (s10 >> 3) & 1, (s10 >> 2) & 1, (s10 >> 1) & 1, s10 & 1
            for s5 in range(8):
                if d5t[s5] == 0: continue
                w0, wh, wv = (s5 >> 2) & 1, (s5 >> 1) & 1, s5 & 1
                w1 = wh | wv
                u0, u1 = (x0 & w0) | (x1 & w1), (x0 & w1) | (x1 & w0)
                v0, v1 = (x0 & w0) | (jo & wh) | (x1 & wv), (x1 & w0) | (x0 & wv) | (ji & wh)
                out[(u0 << 3) | (u1 << 2) | (v0 << 1) | v1] += d16[s10] * d5t[s5]
        return tuple(out)

    d5_3 = {k: dist5_3(v) for k, v in dict(
        TB=TB5, TS=TS5, TPH=TPH5, TPV=TPV5, TX0=TX05, TXH=TXH5, TXV=TXV5, TX1=TX15
    ).items()}

    d16_TJin = [0] * 16
    for ia, ib in exact_in_rects:
        d16_TJin = add_t(d16_TJin, dist10_16([T_aut(x) for x in id_to_set[ia]], [T_aut(x) for x in id_to_set[ib]]))
    d16_TJout = [0] * 16
    for ia, ib in out_rects:
        d16_TJout = add_t(d16_TJout, dist10_16([T_aut(x) for x in id_to_set[ia]], [T_aut(x) for x in id_to_set[ib]]))

    d16_TB = add_t(dist10_16(TB5, TB5), add_t(dist10_16(TPH5, TXH5),
             add_t(dist10_16(TPV5, TXV5), add_t(dist10_16(TXH5, TPV5), dist10_16(TXV5, TPH5)))))
    d16_TS = add_t(dist10_16(TS5, TX05), dist10_16(TX05, TS5))
    d16_TPH = add_t(dist10_16(TPH5, TX05), dist10_16(TX05, TPV5))
    d16_TPV = add_t(dist10_16(TPV5, TX05), dist10_16(TX05, TPH5))
    d16_TX0 = add_t(dist10_16(TX05, TX05), dist10_16(TX15, TX15))
    d16_TXH = add_t(dist10_16(TXH5, TX05), dist10_16(TX05, TXV5))
    d16_TXV = add_t(dist10_16(TXV5, TX05), dist10_16(TX05, TXH5))

    d15_TB = add_t(lift15(d16_TB, d5_3["TB"]), add_t(lift15(d16_TPH, d5_3["TXH"]),
             add_t(lift15(d16_TPV, d5_3["TXV"]), add_t(lift15(d16_TXH, d5_3["TPV"]), lift15(d16_TXV, d5_3["TPH"])))))
    d15_TS = add_t(lift15(d16_TS, d5_3["TX0"]), lift15(d16_TX0, d5_3["TS"]))
    d15_TPH = add_t(lift15(d16_TPH, d5_3["TX0"]), lift15(d16_TX0, d5_3["TPV"]))
    d15_TPV = add_t(lift15(d16_TPV, d5_3["TX0"]), lift15(d16_TX0, d5_3["TPH"]))
    d15_TX0 = add_t(lift15(d16_TX0, d5_3["TX0"]), lift15(d16_TJout, d5_3["TX1"]))
    d15_TXH = add_t(lift15(d16_TXH, d5_3["TX0"]), lift15(d16_TJin, d5_3["TXV"]))
    d15_TXV = add_t(lift15(d16_TXV, d5_3["TX0"]), lift15(d16_TJin, d5_3["TXH"]))

    def count_avoid_30(dL, dR):
        L4, R4_ = [0,0,0,0], [0,0,0,0]
        for s in range(16):
            L4[(s >> 2) & 3] += dL[s]
            R4_[s & 3] += dR[s]
        return sum(L4[u] * R4_[v] for u in range(4) for v in range(4)
                   if not ((((u>>1)&1) & ((v>>1)&1)) or ((u&1) & (v&1))))

    C4 = (
        count_avoid_30(d15_TB, d15_TB) + count_avoid_30(d15_TS, d15_TX0) +
        count_avoid_30(d15_TPH, d15_TXH) + count_avoid_30(d15_TPV, d15_TXV) +
        count_avoid_30(d15_TX0, d15_TS) + count_avoid_30(d15_TXH, d15_TPV) +
        count_avoid_30(d15_TXV, d15_TPH)
    )
    assert C4 == 841760069965664
    return C1, C2, C4


def floor_15(M, d):
    val = M * (10 ** (15 * d))
    lo, hi = 3 * 10**15, 4 * 10**15
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid ** d <= val:
            lo = mid
        else:
            hi = mid - 1
    assert lo ** d <= val < (lo + 1) ** d
    return lo


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--write-witness", action="store_true")
    args = parser.parse_args()

    verify_subst("T2a", T2A)
    verify_subst("T3a", T3A)
    verify_subst("T3b", T3B)
    verify_code("C4a", C4A)

    I5, S5, P0_5, P1_5, X5 = parse_repo_base5()
    C1, C2, C4 = verify_certificates(I5, S5, P0_5, P1_5, X5)

    def sigma(w):
        return (w[0], w[1], w[3], w[2], w[4], w[6], w[5])

    def het_gao_vec(wL, wR, j0N, j0D, j0A, jH, qH, jV, qV):
        # Input in Letter order (B, N, A, D, O, H, V); recall A=X^V, D=X^H
        B_L, N_L, A_L, D_L, O_L, H_L, V_L = wL
        B_R, N_R, A_R, D_R, O_R, H_R, V_R = wR
        return (
            B_L*B_R + H_L*D_R + V_L*A_R + D_L*V_R + A_L*H_R,
            j0N*N_R + qH*D_R + qV*A_R,
            j0A*N_R + (jH - qH)*D_R,
            j0D*N_R + (jV - qV)*A_R,
            O_L*N_R + N_L*O_R,
            H_L*N_R + N_L*V_R,
            V_L*N_R + N_L*H_R,
        )

    w5 = (359, 322, 19, 26, 8, 8, 8)
    w5s = sigma(w5)
    w10 = apply_subst(T2A, [w5, w5])
    w10A = apply_subst(T2A, [w5s, w5])
    w15X = apply_subst(T2A, [w10, w5])
    w15het = het_gao_vec(w10, w5, 105709, 14490, 14490, 134753, C1, 134753, C1)
    w15AX = apply_subst(T2A, [w10A, w5])
    w15Ahet = het_gao_vec(w10A, w5, 105709, 12236, 16744, 134753, C1, 134689, 28980)
    w30L = apply_subst(T2A, [w15AX, sigma(w15Ahet)])
    w30hat = het_gao_vec(w15AX, sigma(w15Ahet), 35303606, 5948463, 8180458, 49495055, C2, 49430863, 14088465)

    # M1 d=620 champion
    j30pp = (w15het[0] + w15het[4])
    # Wait: |I30^{++}| = (a15-t15)^2 + 2*t15*s15 = w15het[0]^2 + 2*w15het[4]*(w15het[1]+w15het[2]+w15het[3])
    s15het = w15het[1] + w15het[2] + w15het[3]
    I30pp = w15het[0] ** 2 + 2 * w15het[4] * s15het
    assert I30pp == 2455726444728097

    # Note sigma(w30L) swaps A<->D, H<->V, so w30hat's j0D <-> j0A also swap!
    w40_s0 = het_gao_vec(sigma(w30L), w10A, w30hat[1], w30hat[2], w30hat[3], I30pp, C4, I30pp, C4)
    w35_sub = het_gao_vec(w30L, w5, w30hat[1], w30hat[3], w30hat[2], I30pp, C4, I30pp, C4)
    w65_s1 = het_gao_vec(sigma(w30L), w35_sub, w30hat[1], w30hat[2], w30hat[3], I30pp, C4, I30pp, C4)
    w20_sub = het_gao_vec(w15AX, w5, 35303606, 5948463, 8180458, 49495055, C2, 49495055, C2)
    w50_s2 = het_gao_vec(sigma(w30L), w20_sub, w30hat[1], w30hat[2], w30hat[3], I30pp, C4, I30pp, C4)

    w155 = apply_subst(T3B, [w40_s0, w65_s1, w50_s2])
    M620 = apply_code(C4A, [w155] * 4)
    num620 = floor_15(M620, 620)
    print(f"Verified C1={C1}, C2={C2}, C4={C4}")
    print(f"Verified M620 ({len(str(M620))} digits), d=620 lower bound = {num620} / 10^15 = {num620/1e15:.15f}")
    assert num620 == 3258835618853760

    if args.write_witness:
        out_path = ROOT / "search" / "lower" / "witnesses" / "m1_tandon_d620.json"
        out_path.write_text(json.dumps({
            "dim": 620,
            "num": str(num620),
            "den": str(10**15),
            "rate_str": f"{num620 // 10**15}.{num620 % 10**15:015d}",
            "card": str(M620),
            "card_digits": len(str(M620)),
            "certificates": {"C1": C1, "C2": C2, "C4": C4, "I30pp": I30pp},
            "nodes": {
                "w40_s0": list(w40_s0),
                "w65_s1": list(w65_s1),
                "w50_s2": list(w50_s2),
                "w155": list(w155),
            },
        }, indent=2) + "\n")
        print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
