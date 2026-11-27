#!/usr/bin/env python3
"""Track L2 — `AuxPartition` / `PartGadget` (`prodStd` + `prodXupg1` + `prodXupg2`) Witness Generator.

Pure Python 3.12 standard library for deterministic exact witness generation & verification.

Mathematical construction:
  1. Start from the locked M3 5D base gadget `baseHetero5D` on `strongPow C7 5`:
     - I = polakSchrijver367Trie (367 words in C_7^5)
     - ports = basePorts (8 private pairs on unique zero-hit bipartition bip = 1)
     - X = baseX (X_322: 367 words, d = 322, h = 19, v = 26, |X ∩ N[P0] ∩ N[P1]| = 0)
  2. Generalize `AuxCode` to `AuxPartition` (`O, H, V` pairwise non-close with `O` avoiding
     `P0, P1`, `H` avoiding `P1`, and `V` avoiding `P0`), yielding `PartGadget`.
  3. On `prodAlignedCore(g1, g2)`, `prodXupg1` replaces `(H1 ∪ V1) × X2` with
     `H1 × (B2 ∪ P0_2)` and `V1 × (B2 ∪ P1_2)`, breaking the `c_k = 367^k` stagnation wall:
       d_new = d1*d2 + (h1 + v1)*b2
       h_new = d1*h2 + h1*(a2 - b2)
       v_new = d1*v2 + v1*(a2 - b2)
       c_new = d1*c2 + (h1 + v1)*a2.
  4. Constructing optimal `prodStd` powers `p_9` (d=45) and `p_13` (d=65), upgrading
     `u_22 = prodXupg1(p_9, p_13)` (d=110), and squaring via `t_44 = prodStd(u_22, u_22)`
     (11-node shared DAG, d = 220) certifies an exact 113-digit independent set in C_7^220:
       3258822357711717 / 10^15 <= shannonCapacity (SimpleGraph.cycleGraph 7)
     strictly surpassing BPZ v1 (3258805369885465 / 10^15) by +1.699e-5 and our earlier
     d = 225 Gamma_6^4 pullback (3258821451811711 / 10^15) by +9.059e-7 in pure kernel.
"""

import argparse
import hashlib
import json
import math
import pathlib
import re
import sys

sys.set_int_max_str_digits(100000)

# Locked M3 basePorts on bip = 1 (J0 = {0,1,6}, J1 = {2,3,4,5,7})
BASE_PORTS_5D = (
    {"s": [0, 3, 5, 6, 5], "p0": [6, 3, 5, 0, 5], "p1": [0, 3, 5, 6, 5]},
    {"s": [1, 3, 4, 4, 6], "p0": [2, 3, 5, 4, 6], "p1": [1, 3, 4, 4, 6]},
    {"s": [3, 4, 0, 3, 5], "p0": [3, 4, 0, 3, 5], "p1": [2, 4, 6, 3, 5]},
    {"s": [4, 4, 6, 1, 6], "p0": [4, 4, 6, 1, 6], "p1": [5, 4, 6, 0, 6]},
    {"s": [5, 3, 1, 3, 4], "p0": [5, 3, 1, 3, 4], "p1": [5, 3, 2, 3, 5]},
    {"s": [6, 0, 6, 4, 5], "p0": [6, 0, 6, 4, 5], "p1": [6, 1, 6, 5, 5]},
    {"s": [6, 4, 3, 4, 0], "p0": [6, 4, 2, 4, 6], "p1": [6, 4, 3, 4, 0]},
    {"s": [6, 4, 5, 3, 2], "p0": [6, 4, 5, 3, 2], "p1": [6, 5, 5, 3, 1]},
)


def parse_trie_slices(lean_path: pathlib.Path, prefix: str) -> list[list[int]]:
    text = lean_path.read_text(encoding="utf-8")
    tok_re = re.compile(r"Trie7\.node|\.node|Trie7\.leaf|\.leaf|Trie7\.empty|\.empty|\(|\)")
    words: list[list[int]] = []

    def parse_expr(body: str):
        toks = tok_re.findall(body)
        pos = [0]

        def rec():
            if toks[pos[0]] == "(":
                pos[0] += 1
                v = rec()
                if toks[pos[0]] != ")":
                    raise ValueError("Unbalanced paren in Trie7 expression")
                pos[0] += 1
                return v
            t = toks[pos[0]]
            pos[0] += 1
            if t.endswith("empty"):
                return None
            if t.endswith("leaf"):
                return "L"
            if t.endswith("node"):
                return [rec() for _ in range(7)]
            raise ValueError(f"Unexpected token: {t}")

        return rec()

    def collect(node, pref: list[int]):
        if node is None:
            return
        if node == "L":
            words.append(list(pref))
            return
        for c, ch in enumerate(node):
            collect(ch, pref + [c])

    for s in range(7):
        pat = rf"def\s+{re.escape(prefix)}{s}\s*:\s*Trie7\s+4\s*:=\s*(.*?)(?=\n(?:def|theorem|private|/--|/-!|end\b)|\Z)"
        m = re.search(pat, text, re.S)
        if not m:
            raise ValueError(f"Could not find {prefix}{s} in {lean_path}")
        collect(parse_expr(m.group(1)), [s])
    return sorted(words)


def sha256_words(words: list[list[int]]) -> str:
    payload = "".join(" ".join(str(c) for c in w) + "\n" for w in sorted(words))
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def pg_prod_std(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
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


def pg_prod_xupg1(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    a1, b1, c1, d1, h1, v1 = p
    a2, b2, c2, d2, h2, v2 = q
    d_new = d1 * d2 + (h1 + v1) * b2
    h_new = d1 * h2 + h1 * (a2 - b2)
    v_new = d1 * v2 + v1 * (a2 - b2)
    return (
        (a1 - b1) * (a2 - b2) + b1 * c2 + c1 * b2,
        b1 * d2 + d1 * b2,
        d_new + h_new + v_new,
        d_new,
        h_new,
        v_new,
    )


def pg_prod_xupg2(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    a1, b1, c1, d1, h1, v1 = p
    a2, b2, c2, d2, h2, v2 = q
    d_new = d1 * d2 + b1 * (h2 + v2)
    h_new = h1 * d2 + (a1 - b1) * h2
    v_new = v1 * d2 + (a1 - b1) * v2
    return (
        (a1 - b1) * (a2 - b2) + b1 * c2 + c1 * b2,
        b1 * d2 + d1 * b2,
        d_new + h_new + v_new,
        d_new,
        h_new,
        v_new,
    )


def build_winning_partgadget_dag() -> tuple[list[dict], list[tuple[int, ...]]]:
    """Build exact 11-node PartGadget DAG certifying d = 220 (k = 44):
    optimal prodStd powers p_9 (k=9) and p_13 (k=13), upgraded via
    u_22 = prodXupg1(p_9, p_13), and squared via t_44 = prodStd(u_22, u_22)."""
    base = (367, 8, 367, 322, 19, 26)
    best_p: dict[int, tuple[int, ...]] = {1: base}
    best_split: dict[int, tuple[int, int]] = {}
    for k in range(2, 14):
        best = None
        split = (1, k - 1)
        for i in range(1, k // 2 + 1):
            cand = pg_prod_std(best_p[i], best_p[k - i])
            if best is None or cand[0] > best[0]:
                best = cand
                split = (i, k - i)
        assert best is not None
        best_p[k] = best
        best_split[k] = split

    needed: set[int] = set()

    def mark(k: int):
        if k in needed:
            return
        needed.add(k)
        if k > 1:
            l, r = best_split[k]
            mark(l)
            mark(r)

    mark(9)
    mark(13)

    ordered_ks = sorted(needed)
    k_to_node: dict[int, int] = {}
    ops: list[dict] = []
    node_profs: list[tuple[int, ...]] = []
    for k in ordered_ks:
        idx = len(ops)
        k_to_node[k] = idx
        if k == 1:
            ops.append({"op": "base", "idx": 0, "blocks": 1})
        else:
            l, r = best_split[k]
            ops.append({"op": "prodStd", "i": k_to_node[l], "j": k_to_node[r], "blocks": k})
        node_profs.append(best_p[k])

    # Node u22 = prodXupg1(p_9, p_13)
    i9, i13 = k_to_node[9], k_to_node[13]
    u22_idx = len(ops)
    ops.append({"op": "prodXupg1", "i": i9, "j": i13, "blocks": 22})
    node_profs.append(pg_prod_xupg1(node_profs[i9], node_profs[i13]))

    # Final node t44 = prodStd(u_22, u_22)
    ops.append({"op": "prodStd", "i": u22_idx, "j": u22_idx, "blocks": 44})
    node_profs.append(pg_prod_std(node_profs[u22_idx], node_profs[u22_idx]))

    return ops, node_profs


def compute_exact_floor(N: int, dim: int, den: int) -> int:
    rhs = (den ** dim) * N
    lo = 3 * den
    hi = 4 * den
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid ** dim <= rhs:
            lo = mid
        else:
            hi = mid
    assert lo ** dim <= rhs < (lo + 1) ** dim
    return lo


def generate_witness(project_root: pathlib.Path, out_path: pathlib.Path) -> dict:
    I_words = parse_trie_slices(project_root / "ShannonC7" / "SmallPowers.lean", "ps367Slice")
    X_words = parse_trie_slices(project_root / "ShannonC7" / "ValidTuple.lean", "baseXSlice")
    assert len(I_words) == 367 and len(X_words) == 367

    ops, node_profs = build_winning_partgadget_dag()
    final_blocks = ops[-1]["blocks"]
    final_dim = 5 * final_blocks
    N_exact = node_profs[-1][0]
    den = 10 ** 15
    num = compute_exact_floor(N_exact, final_dim, den)

    sha_I = sha256_words(I_words)
    sha_X = sha256_words(X_words)

    recipe_obj = {
        "engine": "PartGadgetDAG",
        "ops": ops,
        "target_node": len(ops) - 1,
        "terminal_pair": {"enabled": False},
    }
    canon_blob = json.dumps(
        {"sha256_I": sha_I, "sha256_X": sha_X, "ports": list(BASE_PORTS_5D), "recipe": recipe_obj},
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    sha_canon = hashlib.sha256(canon_blob).hexdigest()

    witness = {
        "schema_version": "1.0",
        "witness_id": "frontier_c7_d220_partgadget",
        "kind": "coupled_recursion",
        "graph": "C7",
        "base_dim": 5,
        "final_dim": final_dim,
        "N_exact": str(N_exact),
        "c7_lower_num": str(num),
        "c7_lower_den": str(den),
        "sharp_last_digit": True,
        "sha256_canonical": sha_canon,
        "base_gadgets": [
            {
                "gadget_id": "g0",
                "dim": 5,
                "reuse_lean_I": "polakSchrijver367Trie",
                "reuse_lean_ports": "basePorts",
                "reuse_lean_X": "baseX",
                "I": I_words,
                "ports": list(BASE_PORTS_5D),
                "X": X_words,
                "claimed_profile": {"a": 367, "b": 8, "c": 367, "d": 322, "h": 19, "v": 26},
                "sha256_I": sha_I,
                "sha256_X": sha_X,
            }
        ],
        "recipe": recipe_obj,
        "provenance": {
            "track": "L2",
            "tool": "search/lower/track_l2_search.py",
            "seed": 20261126,
            "created_utc": "2026-11-26T19:05:00Z",
        },
    }

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(witness, indent=2) + "\n", encoding="utf-8")
    return witness


def main() -> int:
    parser = argparse.ArgumentParser(description="Track L2 PartGadget (prodXupg1) witness generator.")
    parser.add_argument(
        "--project-dir",
        type=pathlib.Path,
        default=pathlib.Path(__file__).resolve().parents[2],
    )
    parser.add_argument(
        "--out",
        type=pathlib.Path,
        default=pathlib.Path(__file__).resolve().parent / "witnesses" / "frontier_c7_d220_partgadget.json",
    )
    args = parser.parse_args()
    w = generate_witness(args.project_dir, args.out)
    N = int(w["N_exact"])
    num = int(w["c7_lower_num"])
    den = int(w["c7_lower_den"])
    d = w["final_dim"]
    print(f"[Track L2] Wrote {args.out}")
    print(f"  dim={d}, |ops|={len(w['recipe']['ops'])}, N_digits={len(w['N_exact'])}")
    print(f"  c7_lower = {num} / {den} ({num / den:.15f}, exact rate={math.exp(math.log(N)/d):.15f})")
    print(f"  sha256_canonical = {w['sha256_canonical']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
