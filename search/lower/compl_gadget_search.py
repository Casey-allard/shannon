#!/usr/bin/env python3
"""
Independent verifier & PartGadget + Gamma6^3 / Gamma6^4 DP optimizer for C7^c gadgets.
Saves verified witness + DAG recipe to search/lower/compl_witnesses/.
"""
import json
import os
import sys
from decimal import Decimal, getcontext
from itertools import product

getcontext().prec = 60
ADJ = {1, 6}


def sep(u, v):
    return any((a - b) % 7 in ADJ for a, b in zip(u, v))


def is_indep(words):
    for i in range(len(words)):
        for j in range(i + 1, len(words)):
            if not sep(words[i], words[j]):
                return False
    return True


def verify_part_gadget(I, P0, P1, O, H, V):
    assert len(set(map(tuple, I))) == len(I) and is_indep(I), "I not indep"
    assert len(set(map(tuple, P0))) == len(P0) and is_indep(P0), "P0 not indep"
    assert len(set(map(tuple, P1))) == len(P1) and is_indep(P1), "P1 not indep"
    assert len(P0) == len(P1), "P0 and P1 size mismatch"
    b = len(P0)
    I_set = set(map(tuple, I))
    S = []
    for p0, p1 in zip(P0, P1):
        t0, t1 = tuple(p0), tuple(p1)
        if t0 in I_set:
            s, q = t0, t1
        elif t1 in I_set:
            s, q = t1, t0
        else:
            raise AssertionError(f"Neither {t0} nor {t1} in I")
        assert not sep(s, q), f"s={s} and q={q} not close"
        for x in I:
            tx = tuple(x)
            if tx != s:
                assert sep(tx, q), f"q={q} not private to s={s}, collides with {tx}"
        S.append(s)
    assert len(set(S)) == b, "Port centers not distinct"

    for name, A in [("O", O), ("H", H), ("V", V)]:
        assert len(set(map(tuple, A))) == len(A) and is_indep(A), f"{name} not indep"
    for x in O:
        for y in H:
            assert sep(x, y), "O and H close"
        for y in V:
            assert sep(x, y), "O and V close"
    for x in H:
        for y in V:
            assert sep(x, y), "H and V close"
    for p in P0:
        for o in O:
            assert sep(p, o), "P0 and O close"
        for v in V:
            assert sep(p, v), "P0 and V close"
    for p in P1:
        for o in O:
            assert sep(p, o), "P1 and O close"
        for h in H:
            assert sep(p, h), "P1 and H close"
    return (len(I), b, len(O) + len(H) + len(V), len(O), len(H), len(V))


def prod_std(p, q):
    a1, b1, c1, d1, h1, v1 = p
    a2, b2, c2, d2, h2, v2 = q
    return (
        (a1 - b1) * (a2 - b2) + b1 * c2 + c1 * b2,
        b1 * d2 + d1 * b2,
        c1 * c2,
        d1 * d2 + (h1 + v1) * (h2 + v2),
        d1 * h2 + h1 * d2,
        d1 * v2 + v1 * d2,
    )


def prod_xupg1(p, q):
    a1, b1, c1, d1, h1, v1 = p
    a2, b2, c2, d2, h2, v2 = q
    return (
        (a1 - b1) * (a2 - b2) + b1 * c2 + c1 * b2,
        b1 * d2 + d1 * b2,
        d1 * c2 + (h1 + v1) * a2,
        d1 * d2 + (h1 + v1) * b2,
        d1 * h2 + h1 * (a2 - b2),
        d1 * v2 + v1 * (a2 - b2),
    )


def prod_xupg2(p, q):
    a1, b1, c1, d1, h1, v1 = p
    a2, b2, c2, d2, h2, v2 = q
    return (
        (a1 - b1) * (a2 - b2) + b1 * c2 + c1 * b2,
        b1 * d2 + d1 * b2,
        c1 * d2 + a1 * (h2 + v2),
        d1 * d2 + b1 * (h2 + v2),
        h1 * d2 + (a1 - b1) * h2,
        v1 * d2 + (a1 - b1) * v2,
    )


def dp_part_gadget(base_prof, base_dim, max_k=80):
    layers = {1: {base_prof: ("base",)}}
    best_rate = Decimal(base_prof[0]) ** (Decimal(1) / Decimal(base_dim))
    best_info = (1, base_dim, base_prof[0], base_prof, best_rate)
    for k in range(2, max_k + 1):
        cand = {}
        for k1 in range(1, k // 2 + 1):
            k2 = k - k1
            for p1 in layers[k1]:
                for p2 in layers[k2]:
                    for op_name, op_fn in [("std", prod_std), ("x1", prod_xupg1), ("x2", prod_xupg2)]:
                        pr = op_fn(p1, p2)
                        if pr not in cand:
                            cand[pr] = (op_name, k1, p1, k2, p2)
        items = list(cand.items())
        if len(items) > 120:
            by_a = sorted(items, key=lambda kv: (kv[0][0], kv[0][2], kv[0][1]), reverse=True)[:40]
            by_c = sorted(items, key=lambda kv: (kv[0][2], kv[0][0], kv[0][1]), reverse=True)[:40]
            by_b = sorted(items, key=lambda kv: (kv[0][1], kv[0][0], kv[0][2]), reverse=True)[:40]
            layers[k] = dict(by_a + by_c + by_b)
        else:
            layers[k] = cand
        for pr in layers[k]:
            dim = k * base_dim
            rate = Decimal(pr[0]) ** (Decimal(1) / Decimal(dim))
            if rate > best_rate:
                best_rate = rate
                best_info = (k, dim, pr[0], pr, rate)
    return best_info, layers


# Gamma6^3 exact MILP via highspy (216 vars)
GAMMA6_EDGES = {(0, 3), (3, 0), (0, 4), (4, 0), (0, 5), (5, 0), (1, 2), (2, 1), (1, 4), (4, 1), (2, 5), (5, 2)}


def gamma6_close(u, v):
    return u == v or (u, v) in GAMMA6_EDGES


def gamma6_weights(p):
    a, b, c, d, h, v = p
    return [a - b, b, b, d, h, v]


def solve_gamma6_pow3(p1, p2, p3):
    import highspy
    w1, w2, w3 = gamma6_weights(p1), gamma6_weights(p2), gamma6_weights(p3)
    triples = list(product(range(6), repeat=3))
    weights = [w1[a] * w2[b] * w3[c] for a, b, c in triples]
    max_w = max(weights) or 1
    h = highspy.Highs()
    h.silent()
    h.setOptionValue("threads", 1)
    h.setOptionValue("time_limit", 2.0)
    vars_ = [h.addBinary(obj=-float(weights[i] * 1000000 // max_w)) for i in range(216)]
    for i in range(216):
        u = triples[i]
        for j in range(i + 1, 216):
            v = triples[j]
            if gamma6_close(u[0], v[0]) and gamma6_close(u[1], v[1]) and gamma6_close(u[2], v[2]):
                h.addConstr(vars_[i] + vars_[j] <= 1)
    h.run()
    sol = h.getSolution().col_value
    chosen = [triples[i] for i in range(216) if sol[i] > 0.5]
    tot = sum(w1[a] * w2[b] * w3[c] for a, b, c in chosen)
    for i in range(len(chosen)):
        for j in range(i + 1, len(chosen)):
            u, v = chosen[i], chosen[j]
            assert not (gamma6_close(u[0], v[0]) and gamma6_close(u[1], v[1]) and gamma6_close(u[2], v[2]))
    return tot, chosen


def reconstruct_dag(layers, target_k, target_prof):
    nodes = {}
    order = []

    def visit(k, prof):
        key = (k, prof)
        if key in nodes:
            return nodes[key]
        info = layers[k][prof]
        if info[0] == "base":
            idx = len(order)
            order.append({"op": "base", "k": k, "prof": prof})
            nodes[key] = idx
            return idx
        op_name, k1, p1, k2, p2 = info
        i1 = visit(k1, p1)
        i2 = visit(k2, p2)
        idx = len(order)
        order.append({"op": op_name, "left": i1, "right": i2, "k": k, "prof": prof})
        nodes[key] = idx
        return idx

    root = visit(target_k, target_prof)
    return order, root


if __name__ == "__main__":
    path = sys.argv[1] if len(sys.argv) > 1 else "/mnt/nvme2tb/shannon_struct_scratch/compl/d5_gadget_max_d.json"
    with open(path) as f:
        data = json.load(f)
    I, P0, P1, X = data["I"], data["P0"], data["P1"], data["X"]
    dim = len(I[0])
    O, H, V = [], [], []
    for x in X:
        in0 = any(not sep(x, p) for p in P0)
        in1 = any(not sep(x, p) for p in P1)
        assert not (in0 and in1)
        if not in0 and not in1:
            O.append(x)
        elif in0:
            H.append(x)
        else:
            V.append(x)
    prof = verify_part_gadget(I, P0, P1, O, H, V)
    print(f"[verified] dim={dim} profile={prof}")
    best_info, layers = dp_part_gadget(prof, dim, max_k=32)
    k, tot_d, N, best_pr, rate = best_info
    print(f"[DP best <=32] k={k} d={tot_d} N={N} rate={rate:.12f}", flush=True)

    # Test symmetric Gamma6^3 pullback at k=1..4!
    best_g3 = (0, 0, Decimal(0), None, None)
    for k1 in range(1, 5):
        for pr in sorted(layers[k1].keys(), key=lambda pr: pr[0], reverse=True)[:2]:
            tot3, chosen3 = solve_gamma6_pow3(pr, pr, pr)
            d3 = 3 * k1 * dim
            r3 = Decimal(tot3) ** (Decimal(1) / Decimal(d3))
            if r3 > best_g3[2]:
                best_g3 = (k1, d3, r3, pr, (tot3, chosen3))
    print(f"[Gamma6^3 best] k1={best_g3[0]} d={best_g3[1]} N={best_g3[4][0]} |S|={len(best_g3[4][1])} rate={best_g3[2]:.12f}")

    # Save best witness!
    os.makedirs("/home/callard/shannon/search/lower/compl_witnesses", exist_ok=True)
    if best_g3[2] >= rate:
        dag, root = reconstruct_dag(layers, best_g3[0], best_g3[3])
        winner = {
            "mode": "gamma6_pow3",
            "base_dim": dim,
            "base_profile": prof,
            "k1": best_g3[0],
            "total_dim": best_g3[1],
            "N": best_g3[4][0],
            "rate_str": str(best_g3[2])[:22],
            "dag": dag,
            "root": root,
            "gamma6_triples": best_g3[4][1],
            "I": I, "P0": P0, "P1": P1, "O": O, "H": H, "V": V,
        }
    else:
        dag, root = reconstruct_dag(layers, k, best_pr)
        winner = {
            "mode": "part_dag",
            "base_dim": dim,
            "base_profile": prof,
            "k": k,
            "total_dim": tot_d,
            "N": N,
            "rate_str": str(rate)[:22],
            "dag": dag,
            "root": root,
            "I": I, "P0": P0, "P1": P1, "O": O, "H": H, "V": V,
        }
    out_path = "/home/callard/shannon/search/lower/compl_witnesses/compl_c7_d5_partgadget.json"
    with open(out_path, "w") as f:
        json.dump(winner, f, indent=2)
    print(f"[saved] {out_path} mode={winner['mode']} d={winner['total_dim']} rate={winner['rate_str']} dag_nodes={len(winner['dag'])}")
