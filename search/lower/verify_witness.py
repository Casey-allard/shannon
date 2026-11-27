#!/usr/bin/env python3
"""Independent Pure-Python-Stdlib Exact Witness & Lean Certificate Verifier (`verify_witness.py`).

ZERO third-party imports (strictly Python 3.12 stdlib only) and ZERO shared code with
search scripts or `emit_frontier_lean.py`.

Supports:
  - Full exact verification of base 5D codes (`I`, `ports`, `X`, optional `interior_layer`),
    exact C_7^d strong-product independence (including 0 <-> 6 wrap-around), exact port
    privacy/toggle soundness, and exact asymmetric profile counts.
  - Independent big-integer replay of `PartGadgetDAG` (`base`, `flip`, `prod`, `prodAligned`,
    `prodStd`, `prodXupg1`, `prodXupg2`), `Gamma6Pow4Pullback`, `HeteroDAG`, and
    `ValidTuple.SplitTree`.
  - Exact power inequality `num^d <= den^d * N` and last-digit tightness `(num+1)^d > den^d * N`
    with ZERO float64 arithmetic.
  - Independent static hygiene + fail-closed Lean 4 lexing + constant + DAG / node /
    exponent / Gamma6 cross-check of `ShannonC7/FrontierLower.lean` (both paired with
    `--witness` and in standalone `--verify-lean` mode).
  - 75 isolated positive & negative mutation tests (including concrete graph-level verification
    of `prodStd`, `prodXupg1`, and `prodXupg2` on `C_7^1 ⊠ C_7^1`, plus full Lean 4.32.2 lexer,
    fail-closed pure-math policy, Mathematically Closed 7-Gate Positive & Lexical Whitelist,
    R1-R17/M29-M34/C-1/NB-2..NB-4, declaration-uniqueness, lexical scope, native-decide, Gamma6,
    Unicode, ReDoS, DoS, and crash-guard regression tests) inside `TemporaryDirectory`.

CLI:
  python3 -B search/lower/verify_witness.py --witness <path.json> [...]
  python3 -B search/lower/verify_witness.py --witness <path.json> --verify-lean ShannonC7/FrontierLower.lean
  python3 -B search/lower/verify_witness.py --verify-lean ShannonC7/FrontierLower.lean
  python3 -B search/lower/verify_witness.py --self-test

Exit codes:
  0 = all checks passed
  1 = verification or self-test failure
  2 = invalid CLI usage
"""

import argparse
import hashlib
import json
import pathlib
import re
import sys
import tempfile
import time
import unicodedata

sys.set_int_max_str_digits(100000)

# Fail-closed algorithmic-complexity / OOM DoS bounds (45x FrontierLower d=220, 22x Gamma6 d=440)
MAX_VERIFIER_DIM = 10_000
MAX_PROFILE_BITS = 332_193  # ~100,000 decimal digits (matches int_max_str_digits)
MAX_POW_BITS = 1_000_000    # 87x FrontierLower d=220 (11.4k), 43x Gamma6 d=440 (22.9k); <0.2s CPU worst-case
MAX_DAG_OPS = 512           # 46x FrontierLower d=220 (11 ops) & Gamma6 d=440 (11 ops)
MAX_GAMMA6_TERMS = 1_296    # Exact pigeonhole bound |V(Gamma6^4)| = 6^4 = 1296
MAX_BASE_GADGETS = 4
MAX_BASE_DIM = 12
MAX_BASE_WORDS = 512        # 1.4x optimal 5D base code (367 words); bounded with MAX_BASE_PAIRWISE_WORK
MAX_BASE_PAIRWISE_WORK = 2_500_000  # 1.7x real 5D gadget (1,465,610); caps worst-case legal base CPU < 0.35s
MAX_INPUT_BYTES = 16 * 1024 * 1024  # 16 MiB (>180x FrontierLower.lean & witness JSON)


class VerifyError(Exception):
    """Raised when a witness or Lean cross-check invariant is violated."""


def _parse_ascii_nat(raw: str, label: str) -> int:
    if not raw or not (raw.isascii() and raw.isdigit()):
        raise VerifyError(f"{label}: expected ASCII unsigned decimal integer, got {raw!r}")
    if len(raw) > 100000:
        raise VerifyError(f"{label}: integer exceeds 100000-digit limit ({len(raw)} digits)")
    try:
        return int(raw)
    except ValueError as exc:
        raise VerifyError(f"{label}: invalid integer {raw!r}: {exc}") from exc


def _reject_json_constant(const: str):
    raise VerifyError(f"Invalid non-RFC-8259 JSON constant: {const!r}")


def _check_json_depth(obj, max_depth: int = 64) -> None:
    stack: list[tuple[object, int]] = [(obj, 0)]
    while stack:
        cur, depth = stack.pop()
        if depth > max_depth:
            raise VerifyError(f"JSON nesting depth exceeds maximum allowed ({max_depth})")
        if isinstance(cur, dict):
            for v in cur.values():
                if isinstance(v, (dict, list)):
                    stack.append((v, depth + 1))
        elif isinstance(cur, list):
            for v in cur:
                if isinstance(v, (dict, list)):
                    stack.append((v, depth + 1))


def _load_json_strict(text: str, label: str = "JSON"):
    if "\x00" in text:
        raise VerifyError(f"{label}: contains NUL byte")
    try:
        obj = json.loads(text, parse_constant=_reject_json_constant)
    except VerifyError:
        raise
    except (json.JSONDecodeError, ValueError, RecursionError) as exc:
        raise VerifyError(f"{label}: malformed JSON: {exc}") from exc
    _check_json_depth(obj)
    return obj


def _load_json_file_strict(path: pathlib.Path):
    if path.stat().st_size > MAX_INPUT_BYTES:
        raise VerifyError(f"{path}: file size exceeds MAX_INPUT_BYTES ({MAX_INPUT_BYTES})")
    raw = path.read_bytes()
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise VerifyError(f"{path}: invalid UTF-8: {exc}") from exc
    if "\x00" in text:
        raise VerifyError(f"{path}: contains NUL byte")
    return _load_json_strict(text, label=str(path))


def _req_int(val, label: str) -> int:
    if isinstance(val, bool) or not isinstance(val, int):
        raise VerifyError(f"{label}: expected strict int, got {type(val).__name__}")
    return val


def _req_pos_int_or_str(val, label: str) -> int:
    if isinstance(val, str):
        out = _parse_ascii_nat(val, label)
    else:
        out = _req_int(val, label)
    if out <= 0:
        raise VerifyError(f"{label}: must be strictly positive, got {out}")
    return out


def _c7_close_coord(a: int, b: int) -> bool:
    diff = (a - b) % 7
    return diff == 0 or diff == 1 or diff == 6


def _c7_close(u: tuple[int, ...], v: tuple[int, ...]) -> bool:
    if len(u) != len(v):
        raise VerifyError(f"Dimension mismatch in C7^d close check: {len(u)} vs {len(v)}")
    for a, b in zip(u, v):
        if not _c7_close_coord(a, b):
            return False
    return True


def _validate_word(w, dim: int, label: str) -> tuple[int, ...]:
    if not isinstance(w, list) or len(w) != dim:
        raise VerifyError(f"{label}: expected list of length {dim}, got {w!r}")
    coords = []
    for idx, c in enumerate(w):
        ci = _req_int(c, f"{label}[{idx}]")
        if ci < 0 or ci >= 7:
            raise VerifyError(f"{label}[{idx}]: coordinate {ci} out of 0..6")
        coords.append(ci)
    return tuple(coords)


def _validate_indep_set(raw_words, dim: int, label: str) -> list[tuple[int, ...]]:
    if not isinstance(raw_words, list):
        raise VerifyError(f"{label}: expected list of words")
    if len(raw_words) > MAX_BASE_WORDS:
        raise VerifyError(f"{label}: word count {len(raw_words)} exceeds MAX_BASE_WORDS ({MAX_BASE_WORDS})")
    words = [_validate_word(w, dim, f"{label}[{i}]") for i, w in enumerate(raw_words)]
    seen: set[tuple[int, ...]] = set()
    for w in words:
        if w in seen:
            raise VerifyError(f"{label}: duplicate word {w}")
        seen.add(w)
    n = len(words)
    for i in range(n):
        wi = words[i]
        for j in range(i + 1, n):
            if _c7_close(wi, words[j]):
                raise VerifyError(f"{label}: conflict between {wi} and {words[j]}")
    return words


def _close_to_any(w: tuple[int, ...], S: list[tuple[int, ...]]) -> bool:
    for u in S:
        if _c7_close(w, u):
            return True
    return False


def _sha256_sorted_words(words: list[tuple[int, ...]]) -> str:
    payload = "".join(" ".join(str(c) for c in w) + "\n" for w in sorted(words))
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def _verify_ports(
    I_words: list[tuple[int, ...]], raw_ports, dim: int, label: str
) -> tuple[list[tuple[int, ...]], list[tuple[int, ...]], list[tuple[int, ...]]]:
    if not isinstance(raw_ports, list):
        raise VerifyError(f"{label}: expected list of port objects")
    if len(raw_ports) > MAX_BASE_WORDS:
        raise VerifyError(f"{label}: port count {len(raw_ports)} exceeds MAX_BASE_WORDS ({MAX_BASE_WORDS})")
    I_set = set(I_words)
    S_list: list[tuple[int, ...]] = []
    P0_list: list[tuple[int, ...]] = []
    P1_list: list[tuple[int, ...]] = []
    seen_s: set[tuple[int, ...]] = set()
    for idx, entry in enumerate(raw_ports):
        if not isinstance(entry, dict):
            raise VerifyError(f"{label}[{idx}]: expected dict")
        s = _validate_word(entry.get("s"), dim, f"{label}[{idx}].s")
        p0_key = "p0" if "p0" in entry else "q0"
        p1_key = "p1" if "p1" in entry else "q1"
        p0 = _validate_word(entry.get(p0_key), dim, f"{label}[{idx}].{p0_key}")
        p1 = _validate_word(entry.get(p1_key), dim, f"{label}[{idx}].{p1_key}")
        if s in seen_s:
            raise VerifyError(f"{label}[{idx}]: duplicate port center {s}")
        seen_s.add(s)
        if s not in I_set:
            raise VerifyError(f"{label}[{idx}]: port center {s} not in I")
        if s != p0 and s != p1:
            raise VerifyError(f"{label}[{idx}]: self_mem failed ({s} not in {{{p0}, {p1}}})")
        if p0 == p1:
            raise VerifyError(f"{label}[{idx}]: degenerate non-toggle port p0 == p1 == {p0}")
        if not _c7_close(p0, s) or not _c7_close(p1, s):
            raise VerifyError(f"{label}[{idx}]: port endpoints must lie in N[s]")
        hits0 = [u for u in I_words if _c7_close(u, p0)]
        hits1 = [u for u in I_words if _c7_close(u, p1)]
        if hits0 != [s]:
            raise VerifyError(f"{label}[{idx}]: p0={p0} privacy violation in I (hits={hits0})")
        if hits1 != [s]:
            raise VerifyError(f"{label}[{idx}]: p1={p1} privacy violation in I (hits={hits1})")
        S_list.append(s)
        P0_list.append(p0)
        P1_list.append(p1)

    if len(set(P0_list)) != len(P0_list) or len(set(P1_list)) != len(P1_list):
        raise VerifyError(f"{label}: duplicate endpoints in P0 or P1")
    for pname, plist in (("P0", P0_list), ("P1", P1_list)):
        for i in range(len(plist)):
            for j in range(i + 1, len(plist)):
                if _c7_close(plist[i], plist[j]):
                    raise VerifyError(f"{label}: {pname} conflict between {plist[i]} and {plist[j]}")
    return S_list, P0_list, P1_list


def _estimate_base_gadget_work(g: object, gidx: int) -> int:
    """Validate base-gadget container/size bounds and return upper-bound pairwise `_c7_close` work."""
    if not isinstance(g, dict):
        raise VerifyError(f"base_gadgets[{gidx}]: expected dict, got {type(g).__name__}")
    dim = _req_int(g.get("dim"), f"base_gadgets[{gidx}].dim")
    if dim <= 0 or dim > MAX_BASE_DIM:
        raise VerifyError(f"base_gadgets[{gidx}].dim must be in 1..{MAX_BASE_DIM} (MAX_BASE_DIM), got {dim}")
    raw_I = g.get("I")
    if not isinstance(raw_I, list):
        raise VerifyError(f"base_gadgets[{gidx}].I: expected list of words")
    if len(raw_I) > MAX_BASE_WORDS:
        raise VerifyError(f"base_gadgets[{gidx}].I: word count {len(raw_I)} exceeds MAX_BASE_WORDS ({MAX_BASE_WORDS})")
    raw_X = g.get("X")
    if not isinstance(raw_X, list):
        raise VerifyError(f"base_gadgets[{gidx}].X: expected list of words")
    if len(raw_X) > MAX_BASE_WORDS:
        raise VerifyError(f"base_gadgets[{gidx}].X: word count {len(raw_X)} exceeds MAX_BASE_WORDS ({MAX_BASE_WORDS})")
    raw_ports = g.get("ports")
    if not isinstance(raw_ports, list):
        raise VerifyError(f"base_gadgets[{gidx}].ports: expected list of port objects")
    if len(raw_ports) > MAX_BASE_WORDS:
        raise VerifyError(
            f"base_gadgets[{gidx}].ports: port count {len(raw_ports)} exceeds MAX_BASE_WORDS ({MAX_BASE_WORDS})"
        )
    n_Y = 0
    n_Pi = 0
    il = g.get("interior_layer")
    if il is not None:
        if not isinstance(il, dict):
            raise VerifyError(f"base_gadgets[{gidx}].interior_layer: expected dict, got {type(il).__name__}")
        raw_pi = il.get("ports_int")
        if not isinstance(raw_pi, list):
            raise VerifyError(f"base_gadgets[{gidx}].ports_int: expected list of port objects")
        if len(raw_pi) > MAX_BASE_WORDS:
            raise VerifyError(
                f"base_gadgets[{gidx}].ports_int: port count {len(raw_pi)} exceeds MAX_BASE_WORDS ({MAX_BASE_WORDS})"
            )
        raw_Y = il.get("Y")
        if not isinstance(raw_Y, list):
            raise VerifyError(f"base_gadgets[{gidx}].Y: expected list of words")
        if len(raw_Y) > MAX_BASE_WORDS:
            raise VerifyError(
                f"base_gadgets[{gidx}].Y: word count {len(raw_Y)} exceeds MAX_BASE_WORDS ({MAX_BASE_WORDS})"
            )
        n_Y = len(raw_Y)
        n_Pi = len(raw_pi)
    n_I = len(raw_I)
    n_X = len(raw_X)
    n_P = len(raw_ports)
    return dim * (
        n_I * n_I
        + n_X * n_X
        + n_Y * n_Y
        + 4 * n_P * (n_I + n_X + n_Y + n_P)
        + 4 * n_Pi * (n_X + n_Y + n_P + n_Pi)
    )


def _verify_base_gadget(g: dict, gidx: int) -> dict:
    single_work = _estimate_base_gadget_work(g, gidx)
    if single_work > MAX_BASE_PAIRWISE_WORK:
        raise VerifyError(
            f"base_gadgets[{gidx}] pairwise work {single_work} exceeds "
            f"MAX_BASE_PAIRWISE_WORK ({MAX_BASE_PAIRWISE_WORK})"
        )
    dim = _req_int(g.get("dim"), f"base_gadgets[{gidx}].dim")
    I_words = _validate_indep_set(g.get("I"), dim, f"base_gadgets[{gidx}].I")
    X_words = _validate_indep_set(g.get("X"), dim, f"base_gadgets[{gidx}].X")
    S_list, P0_list, P1_list = _verify_ports(I_words, g.get("ports"), dim, f"base_gadgets[{gidx}].ports")

    sha_I = _sha256_sorted_words(I_words)
    sha_X = _sha256_sorted_words(X_words)
    if "sha256_I" in g and sha_I != g["sha256_I"]:
        raise VerifyError(f"base_gadgets[{gidx}].sha256_I digest mismatch")
    if "sha256_X" in g and sha_X != g["sha256_X"]:
        raise VerifyError(f"base_gadgets[{gidx}].sha256_X digest mismatch")

    h_cnt = 0
    v_cnt = 0
    d_cnt = 0
    for x in X_words:
        in0 = _close_to_any(x, P0_list)
        in1 = _close_to_any(x, P1_list)
        if in0 and in1:
            raise VerifyError(f"base_gadgets[{gidx}]: X word {x} hits BOTH N[P0] and N[P1]")
        if in0:
            h_cnt += 1
        elif in1:
            v_cnt += 1
        else:
            d_cnt += 1

    a_cnt = len(I_words)
    b_cnt = len(S_list)
    c_cnt = len(X_words)
    if b_cnt > a_cnt or d_cnt + h_cnt + v_cnt != c_cnt:
        raise VerifyError(f"base_gadgets[{gidx}]: profile invariant violated")

    cp = g.get("claimed_profile")
    if cp is None:
        cp = {}
    elif not isinstance(cp, dict):
        raise VerifyError(f"base_gadgets[{gidx}].claimed_profile: expected dict, got {type(cp).__name__}")
    expected = {"a": a_cnt, "b": b_cnt, "c": c_cnt, "d": d_cnt, "h": h_cnt, "v": v_cnt}
    for k, ev in expected.items():
        if k in cp and _req_int(cp[k], f"claimed_profile.{k}") != ev:
            raise VerifyError(f"base_gadgets[{gidx}]: claimed_profile.{k}={cp[k]} != exact {ev}")

    layered_info = None
    if g.get("interior_layer") is not None:
        il = g["interior_layer"]
        if not isinstance(il, dict):
            raise VerifyError(f"base_gadgets[{gidx}].interior_layer: expected dict, got {type(il).__name__}")
        Sint, Q0, Q1 = _verify_ports(X_words, il.get("ports_int"), dim, f"base_gadgets[{gidx}].ports_int")
        for q in Q0 + Q1:
            if _close_to_any(q, P0_list) or _close_to_any(q, P1_list):
                raise VerifyError(f"base_gadgets[{gidx}]: interior port endpoint {q} hits N[P0] ∪ N[P1]")
        Y_words = _validate_indep_set(il.get("Y"), dim, f"base_gadgets[{gidx}].Y")
        dY = hY = vY = pY = 0
        for y in Y_words:
            q0h = _close_to_any(y, Q0)
            q1h = _close_to_any(y, Q1)
            if q0h and q1h:
                raise VerifyError(f"base_gadgets[{gidx}]: Y word {y} hits N[Q0] ∩ N[Q1]")
            p0h = _close_to_any(y, P0_list)
            p1h = _close_to_any(y, P1_list)
            if p0h and p1h:
                raise VerifyError(f"base_gadgets[{gidx}]: Y word {y} hits N[P0] ∩ N[P1]")
            if p0h:
                hY += 1
            elif p1h:
                vY += 1
            else:
                dY += 1
                if not q0h and not q1h:
                    pY += 1
        layered_info = {"bX": len(Sint), "e": len(Y_words), "dY": dY, "hY": hY, "vY": vY, "pY": pY}
        cl = il.get("claimed_layered_profile")
        if cl is None:
            cl = {}
        elif not isinstance(cl, dict):
            raise VerifyError(
                f"base_gadgets[{gidx}].claimed_layered_profile: expected dict, got {type(cl).__name__}"
            )
        for k, ev in layered_info.items():
            if k in cl and _req_int(cl[k], f"claimed_layered_profile.{k}") != ev:
                raise VerifyError(f"base_gadgets[{gidx}]: claimed_layered_profile.{k}={cl[k]} != exact {ev}")

    return {
        "dim": dim,
        "profile": (a_cnt, b_cnt, c_cnt, d_cnt, h_cnt, v_cnt),
        "layered": layered_info,
        "I": I_words,
        "X": X_words,
        "sha256_I": sha_I,
        "sha256_X": sha_X,
        "ports": list(zip(S_list, P0_list, P1_list)),
    }


def _flip_prof(p: tuple[int, ...]) -> tuple[int, ...]:
    return (p[0], p[1], p[2], p[3], p[5], p[4])


def _prod_crossed_prof(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    a1, b1, c1, d1, h1, v1 = p
    a2, b2, c2, d2, h2, v2 = q
    return (
        (a1 - b1) * (a2 - b2) + b1 * c2 + c1 * b2,
        b1 * d2 + d1 * b2,
        c1 * c2,
        d1 * d2 + (h1 + v1) * (h2 + v2),
        h1 * d2 + d1 * v2,
        v1 * d2 + d1 * h2,
    )


def _prod_std_prof(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
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


def _prod_xupg1_prof(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    a1, b1, c1, d1, h1, v1 = p
    a2, b2, c2, d2, h2, v2 = q
    d_n = d1 * d2 + (h1 + v1) * b2
    h_n = d1 * h2 + h1 * (a2 - b2)
    v_n = d1 * v2 + v1 * (a2 - b2)
    return (
        (a1 - b1) * (a2 - b2) + b1 * c2 + c1 * b2,
        b1 * d2 + d1 * b2,
        d_n + h_n + v_n,
        d_n,
        h_n,
        v_n,
    )


def _prod_xupg2_prof(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    a1, b1, c1, d1, h1, v1 = p
    a2, b2, c2, d2, h2, v2 = q
    d_n = d1 * d2 + b1 * (h2 + v2)
    h_n = h1 * d2 + (a1 - b1) * h2
    v_n = v1 * d2 + (a1 - b1) * v2
    return (
        (a1 - b1) * (a2 - b2) + b1 * c2 + c1 * b2,
        b1 * d2 + d1 * b2,
        d_n + h_n + v_n,
        d_n,
        h_n,
        v_n,
    )


def _gamma6_adj(u: int, v: int) -> bool:
    e = (u, v) if u < v else (v, u)
    return e in ((0, 3), (0, 4), (0, 5), (1, 2), (1, 4), (2, 5))


def _gamma6_close4(x: tuple[int, ...], y: tuple[int, ...]) -> bool:
    return all(a == b or _gamma6_adj(a, b) for a, b in zip(x, y))


def _check_profile_bounds(prof: tuple[int, ...], label: str) -> None:
    if max(x.bit_length() for x in prof) > MAX_PROFILE_BITS:
        raise VerifyError(f"{label}: profile integer exceeds MAX_PROFILE_BITS ({MAX_PROFILE_BITS})")


def _replay_recipe(recipe: dict, base_infos: list[dict]) -> tuple[int, int]:
    engine = recipe.get("engine")
    ops = recipe.get("ops", [])
    if not isinstance(ops, list) or not ops:
        raise VerifyError("recipe.ops must be a non-empty list")
    if len(ops) > MAX_DAG_OPS:
        raise VerifyError(f"recipe.ops length {len(ops)} exceeds MAX_DAG_OPS ({MAX_DAG_OPS})")

    for b_idx, bi in enumerate(base_infos):
        b_dim = bi["dim"]
        if b_dim <= 0 or b_dim > MAX_VERIFIER_DIM:
            raise VerifyError(f"base_infos[{b_idx}].dim={b_dim} exceeds MAX_VERIFIER_DIM ({MAX_VERIFIER_DIM})")
        _check_profile_bounds(bi["profile"], f"base_infos[{b_idx}]")

    profs: list[tuple[int, ...]] = []
    dims: list[int] = []
    for idx, op in enumerate(ops):
        if not isinstance(op, dict):
            raise VerifyError(f"ops[{idx}]: expected dict, got {type(op).__name__}")
        kind = op.get("op")
        if kind == "base":
            bi = _req_int(op.get("idx"), f"ops[{idx}].idx")
            if not (0 <= bi < len(base_infos)):
                raise VerifyError(f"ops[{idx}].idx={bi} out of range")
            new_dim = base_infos[bi]["dim"]
            new_prof = base_infos[bi]["profile"]
        elif kind == "flip":
            i = _req_int(op.get("i"), f"ops[{idx}].i")
            if not (0 <= i < idx):
                raise VerifyError(f"ops[{idx}].i={i} out of range")
            new_dim = dims[i]
            new_prof = _flip_prof(profs[i])
        elif kind in ("prod", "prodStd", "prodAligned", "prodXupg1", "prodXupg2"):
            i = _req_int(op.get("i"), f"ops[{idx}].i")
            j = _req_int(op.get("j"), f"ops[{idx}].j")
            if not (0 <= i < idx and 0 <= j < idx):
                raise VerifyError(f"ops[{idx}] invalid {kind} refs ({i},{j})")
            new_dim = dims[i] + dims[j]
            if new_dim > MAX_VERIFIER_DIM:
                raise VerifyError(f"ops[{idx}] dim={new_dim} exceeds MAX_VERIFIER_DIM ({MAX_VERIFIER_DIM})")
            if kind == "prod":
                new_prof = _prod_crossed_prof(profs[i], profs[j])
            elif kind in ("prodStd", "prodAligned"):
                new_prof = _prod_std_prof(profs[i], profs[j])
            elif kind == "prodXupg1":
                new_prof = _prod_xupg1_prof(profs[i], profs[j])
            else:
                new_prof = _prod_xupg2_prof(profs[i], profs[j])
        else:
            raise VerifyError(f"Unsupported recipe op: {kind!r}")
        if new_dim <= 0 or new_dim > MAX_VERIFIER_DIM:
            raise VerifyError(f"ops[{idx}] dim={new_dim} exceeds MAX_VERIFIER_DIM ({MAX_VERIFIER_DIM})")
        _check_profile_bounds(new_prof, f"ops[{idx}]")
        profs.append(new_prof)
        dims.append(new_dim)

    if engine == "PartGadgetDAG":
        target = _req_int(recipe.get("target_node", len(profs) - 1), "recipe.target_node")
        if not (0 <= target < len(profs)):
            raise VerifyError(f"Invalid target_node {target}")
        return dims[target], profs[target][0]

    if engine == "Gamma6Pow4Pullback":
        g6 = recipe.get("gamma6_pow4")
        if not isinstance(g6, dict):
            raise VerifyError("Missing recipe.gamma6_pow4 object")
        raw_fnodes = g6.get("factor_nodes")
        raw_fflips = g6.get("factor_flips")
        if not isinstance(raw_fnodes, list) or not isinstance(raw_fflips, list):
            raise VerifyError("gamma6_pow4.factor_nodes and factor_flips must be lists")
        fnodes = [_req_int(x, "factor_nodes") for x in raw_fnodes]
        fflips = [_req_int(x, "factor_flips") for x in raw_fflips]
        if len(fnodes) != 4 or len(fflips) != 4:
            raise VerifyError("gamma6_pow4 requires 4 factor_nodes and 4 factor_flips")
        for nidx in fnodes:
            if not (0 <= nidx < len(profs)):
                raise VerifyError(f"Invalid factor_node index {nidx}")
        for fl in fflips:
            if fl not in (0, 1):
                raise VerifyError(f"Invalid factor_flip value {fl}")
        raw_terms = g6.get("terms", [])
        if not isinstance(raw_terms, list) or not raw_terms:
            raise VerifyError("gamma6_pow4.terms must be a non-empty list")
        if len(raw_terms) > MAX_GAMMA6_TERMS:
            raise VerifyError(
                f"gamma6_pow4.terms length {len(raw_terms)} exceeds MAX_GAMMA6_TERMS ({MAX_GAMMA6_TERMS})"
            )
        terms: list[tuple[int, int, int, int]] = []
        seen_t: set[tuple[int, int, int, int]] = set()
        for ti, rt in enumerate(raw_terms):
            if not isinstance(rt, list) or len(rt) != 4:
                raise VerifyError(f"gamma6_pow4.terms[{ti}]: expected 4-tuple")
            t = tuple(_req_int(c, f"terms[{ti}]") for c in rt)
            if any(c < 0 or c >= 6 for c in t):
                raise VerifyError(f"gamma6_pow4.terms[{ti}]: vertex out of 0..5 in {t}")
            if t in seen_t:
                raise VerifyError(f"gamma6_pow4.terms[{ti}]: duplicate tuple {t}")
            seen_t.add(t)
            terms.append(t)  # type: ignore[arg-type]
        for i in range(len(terms)):
            for j in range(i + 1, len(terms)):
                if _gamma6_close4(terms[i], terms[j]):
                    raise VerifyError(f"Gamma6^4 conflict: {terms[i]} vs {terms[j]}")
        fprofs = [_flip_prof(profs[n]) if fl else profs[n] for n, fl in zip(fnodes, fflips)]
        fdims = [dims[n] for n in fnodes]
        total_dim = sum(fdims)
        if total_dim <= 0 or total_dim > MAX_VERIFIER_DIM:
            raise VerifyError(
                f"gamma6_pow4 total dim={total_dim} exceeds MAX_VERIFIER_DIM ({MAX_VERIFIER_DIM})"
            )

        def g6_weights(p: tuple[int, ...]) -> tuple[int, ...]:
            return (p[0] - p[1], p[1], p[1], p[3], p[4], p[5])

        ws = [g6_weights(p) for p in fprofs]
        total_N = sum(ws[0][a] * ws[1][b] * ws[2][c] * ws[3][d] for a, b, c, d in terms)
        if total_N.bit_length() > MAX_PROFILE_BITS:
            raise VerifyError(f"gamma6_pow4 total_N exceeds MAX_PROFILE_BITS ({MAX_PROFILE_BITS})")
        return total_dim, total_N

    if engine in ("HeteroDAG", "ValidTuple.SplitTree"):
        target = _req_int(recipe.get("target_node", len(profs) - 1), "recipe.target_node")
        if not (0 <= target < len(profs)):
            raise VerifyError(f"Invalid target_node {target}")
        return dims[target], profs[target][0]

    raise VerifyError(f"Unsupported recipe.engine: {engine!r}")


def _check_exact_frontier_bounds(
    num: int, den: int, dim: int, card: int, *, require_sharp: bool, enforce_frontier_floor: bool, label: str
) -> None:
    if dim <= 0 or dim > MAX_VERIFIER_DIM:
        raise VerifyError(f"{label}: dimension must be in 1..{MAX_VERIFIER_DIM}, got {dim}")
    if num <= 0 or den <= 0 or card <= 0:
        raise VerifyError(f"{label}: num, den, card must be strictly positive")
    if max(num.bit_length(), den.bit_length(), card.bit_length()) > MAX_PROFILE_BITS:
        raise VerifyError(f"{label}: integer operand exceeds MAX_PROFILE_BITS ({MAX_PROFILE_BITS})")
    pow_bits = dim * max((num + 1).bit_length(), den.bit_length())
    if pow_bits > MAX_POW_BITS:
        raise VerifyError(f"{label}: power operand size ({pow_bits} bits) exceeds MAX_POW_BITS ({MAX_POW_BITS})")
    lhs = num ** dim
    rhs = (den ** dim) * card
    if lhs > rhs:
        raise VerifyError(f"{label}: Exact power inequality FAILED: num^{dim} > den^{dim} * N")
    if require_sharp:
        if (num + 1) ** dim <= rhs:
            raise VerifyError(f"{label}: Last-digit tightness FAILED: (num+1)^{dim} <= den^{dim} * N")
    if enforce_frontier_floor:
        if num * (10 ** 12) < 3258805369885 * den:
            raise VerifyError(f"{label}: Frontier bound below PROJECT.md §4.4 floor 3258805369885/10^12")
        if num * (10 ** 12) >= 3317667207395 * den:
            raise VerifyError(f"{label}: Frontier bound violates Lovasz ceiling 3317667207395/10^12")
        cubic_val = num ** 3 + 7 * (num ** 2) * den - 49 * num * (den ** 2) + 49 * (den ** 3)
        if cubic_val >= 0:
            raise VerifyError(f"{label}: Frontier bound violates exact Lovasz cubic p(x) < 0")


def _compute_canonical_sha256(gadgets: list[dict], base_infos: list[dict], recipe: dict) -> str:
    if len(gadgets) == 1:
        payload = {
            "sha256_I": base_infos[0]["sha256_I"],
            "sha256_X": base_infos[0]["sha256_X"],
            "ports": gadgets[0]["ports"],
            "recipe": recipe,
        }
    else:
        payload = {
            "gadgets": [
                {
                    "sha256_I": bi["sha256_I"],
                    "sha256_X": bi["sha256_X"],
                    "ports": g["ports"],
                }
                for g, bi in zip(gadgets, base_infos)
            ],
            "recipe": recipe,
        }
    blob = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(blob).hexdigest()


def verify_witness_dict(witness: dict, enforce_frontier_floor: bool = True) -> dict:
    if not isinstance(witness, dict):
        raise VerifyError("Witness root must be a JSON object")
    if witness.get("schema_version") != "1.0":
        raise VerifyError(f"Unsupported schema_version: {witness.get('schema_version')!r}")
    if witness.get("graph") != "C7":
        raise VerifyError(f"Unsupported graph: {witness.get('graph')!r}")

    final_dim = _req_int(witness.get("final_dim"), "final_dim")
    if final_dim <= 0 or final_dim > MAX_VERIFIER_DIM:
        raise VerifyError(f"final_dim must be in 1..{MAX_VERIFIER_DIM}, got {final_dim}")
    N_exact = _req_pos_int_or_str(witness.get("N_exact"), "N_exact")
    num = _req_pos_int_or_str(witness.get("c7_lower_num"), "c7_lower_num")
    den = _req_pos_int_or_str(witness.get("c7_lower_den"), "c7_lower_den")

    gadgets = witness.get("base_gadgets")
    if not isinstance(gadgets, list) or not gadgets:
        raise VerifyError("base_gadgets must be a non-empty list")
    if len(gadgets) > MAX_BASE_GADGETS:
        raise VerifyError(f"base_gadgets length {len(gadgets)} exceeds MAX_BASE_GADGETS ({MAX_BASE_GADGETS})")
    total_base_work = 0
    for i, g in enumerate(gadgets):
        total_base_work += _estimate_base_gadget_work(g, i)
        if total_base_work > MAX_BASE_PAIRWISE_WORK:
            raise VerifyError(
                f"cumulative base_gadgets pairwise work {total_base_work} exceeds "
                f"MAX_BASE_PAIRWISE_WORK ({MAX_BASE_PAIRWISE_WORK})"
            )
    base_infos = [_verify_base_gadget(g, i) for i, g in enumerate(gadgets)]

    recipe = witness.get("recipe")
    if not isinstance(recipe, dict):
        raise VerifyError("Missing recipe object")
    replayed_dim, replayed_N = _replay_recipe(recipe, base_infos)
    if replayed_dim != final_dim:
        raise VerifyError(f"Replayed final_dim={replayed_dim} != claimed {final_dim}")
    if replayed_N != N_exact:
        raise VerifyError(f"Replayed N_exact={replayed_N} != claimed {N_exact}")

    if "sha256_canonical" in witness:
        claimed_canon = witness["sha256_canonical"]
        if (
            not isinstance(claimed_canon, str)
            or len(claimed_canon) != 64
            or not all(ch in "0123456789abcdef" for ch in claimed_canon)
        ):
            raise VerifyError(f"sha256_canonical: invalid 64-char lowercase hex digest {claimed_canon!r}")
        recomp_canon = _compute_canonical_sha256(gadgets, base_infos, recipe)
        if recomp_canon != claimed_canon:
            raise VerifyError(f"sha256_canonical digest mismatch: recomputed={recomp_canon} != claimed={claimed_canon}")

    _check_exact_frontier_bounds(
        num,
        den,
        final_dim,
        N_exact,
        require_sharp=(witness.get("sharp_last_digit") is True),
        enforce_frontier_floor=enforce_frontier_floor,
        label="Witness",
    )

    return {
        "witness_id": witness.get("witness_id", "<unnamed>"),
        "final_dim": final_dim,
        "N_exact": N_exact,
        "num": num,
        "den": den,
        "recipe": recipe,
        "base_profiles": [bi["profile"] for bi in base_infos],
        "base_dims": [bi["dim"] for bi in base_infos],
    }


LOCKED_BASE_PART5D_PROFILE = (367, 8, 367, 322, 19, 26)
LOCKED_BASE_PART5D_DIM = 5

# Exact Lean v4.32.2 identifier character classes (Init/Meta/Defs.lean:101-135).
# Explicitly EXCLUDES λ (U+03BB), Π (U+03A0), Σ (U+03A3), × (U+00D7), ÷ (U+00F7),
# and superscript/modifier letters like ª (U+00AA), ² (U+00B2), ᶜ (U+1D9C), ᵀ (U+1D40).
_LEAN_LETTER_LIKE_RANGES = (
    "\u03b1-\u03ba\u03bc-\u03c9"
    "\u0391-\u039f\u03a1-\u03a2\u03a4-\u03a9"
    "\u03ca-\u03fb"
    "\u1f00-\u1ffe"
    "\u2100-\u214f"
    "\U0001d49c-\U0001d59f"
    "\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u00ff"
    "\u0100-\u017f"
)
_LEAN_SUBSCRIPT_RANGES = "\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
_LEAN_ID_START_CHARS = "A-Za-z_" + _LEAN_LETTER_LIKE_RANGES
_LEAN_ID_REST_CHARS = "A-Za-z0-9_'?!" + _LEAN_LETTER_LIKE_RANGES + _LEAN_SUBSCRIPT_RANGES
_LEAN_ID_REST_CLS = f"[{_LEAN_ID_REST_CHARS}]"
_LEAN_ID_REST_AND_DOT_CLS = f"[{_LEAN_ID_REST_CHARS}.]"

_LEAN_IDENT_RE = re.compile(f"[{_LEAN_ID_START_CHARS}][{_LEAN_ID_REST_CHARS}]*")
_ASCII_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'?!]*")
# Exact Lean v4.32.2 ASCII whitespace (`Basic.lean:563-587` after CRLF normalization):
# Strictly excludes `\t`, `\x0b`, `\x0c`, `\u00a0`, `\u2003`, `\u2028`, `\u2029`, `\x85`, `\u3000`.
_LEAN_ASCII_WS_RE = re.compile(r"[ \r\n]+")
# Closed Lexical Whitelist ASCII control/tab/isolated-CR matcher:
# Permits ONLY printable ASCII (0x20..0x7E), LF ('\n'), and CRLF ('\r\n').
_FORBIDDEN_ASCII_CTRL_RE = re.compile(r"[\x00-\x09\x0b\x0c\x0e-\x1f\x7f]|\r(?!\n)")
_BLOCK_COMMENT_STOP_RE = re.compile(r"/-|-/")
_PLAIN_STR_STOP_RE = re.compile(r'[\\"]')
_INTERP_STR_STOP_RE = re.compile(r'[\\"{]')
# Exact Lean v4.32.2 `numberFnAux` / `decimalNumberFn` scientific-literal support (R16),
# intentionally NOT matching `.digits` without `[eE]` so chained tuple projections (`v.2.1`) remain split.
_NUMBER_RE = re.compile(
    r"0[xX][0-9a-fA-F_]+|0[bB][01_]+|0[oO][0-7_]+|"
    r"[0-9][0-9_]*(?:(?:\.(?!\.)(?:[0-9][0-9_]*)?)?[eE][+-]?[0-9][0-9_]*)?"
)
_CHAR_LIT_RE = re.compile(
    r"'(?:[^'\\]|\\(?:[\\\"'rnt]|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}))'",
    re.DOTALL,
)
# Matches any Char literal whose body is NOT an identifier-start char (or is a backslash escape),
# e.g. '"', '}', '{', ' ', '0', '+', '/', '-', '\x22', '\u007d', '\\', '\n'. Checked BEFORE
# `init_q_pre` (`]`/`×`/`⊕`) so tokens like `𝓝[≠]'"'`, `𝓝[≠]'}'`, `(𝓝[≠]' ','"')`, `(𝓝[≠]'0','"')`
# always lex as CHAR while `a[0]'h`, `a[0]'h'`, `a[0]'(h)`, `Nat ×' Nat` remain untouched.
_NON_ID_CHAR_LIT_RE = re.compile(
    rf"'(?:[^'\\{_LEAN_ID_START_CHARS}]|\\(?:[\\\"'rnt]|x[0-9a-fA-F]{{2}}|u[0-9a-fA-F]{{4}}))'",
    re.DOTALL,
)

# Strictly O(N) linear-time namespace qualifier prefix & Lean 4 declaration matchers.
# Segment chars `[^\s.:;()\[\]{},=]` are disjoint from `[ \t]` and `.`, and `_DECL_MOD_PREFIX`
# is bounded `{0,8}` (Lean v4.32.2 `declModifiers` has at most 5 slots), eliminating ReDoS
# while matching Unicode (`Γ₁.`), primed (`Foo'.`), `_root_.`, and guillemet-unwrapped segments.
_QUAL_SEG = r"[^\s.:;()\[\]{},=]+"
_QUAL_PREFIX = rf"(?:{_QUAL_SEG}[ \t]*\.[ \t]*)*"
_DECL_MOD_PREFIX = r"(?:(?:private|protected|public|meta|noncomputable|partial|unsafe|nonrec)\s+){0,8}+"
_DECL_INTRO_KW = (
    r"(?:def|abbrev|theorem|lemma|opaque|constant|instance|structure|"
    r"inductive|coinductive|class\s+inductive|class\s+abbrev|class|alias|axiom)"
)

_LEAN_TOP_KW = (
    r"theorem|lemma|def|abbrev|example|structure|inductive|coinductive|class|instance|"
    r"opaque|constant|variable|universe|mutual|noncomputable|private|protected|public|"
    r"meta|nonrec|partial|unsafe|local|scoped|namespace|end|section|open|export|import|"
    r"set_option|attribute|axiom|alias|include|omit|deriving"
)
_LEAN_TOP_END = rf"(?=\n[ \t]*(?:(?:{_LEAN_TOP_KW})(?!{_LEAN_ID_REST_CLS})|#|@\[)|\Z)"
_LEAN_SAME_LINE_TOP_KW = (
    r"theorem|lemma|def|abbrev|example|structure|inductive|coinductive|class|instance|"
    r"opaque|constant|variable|universe|mutual|noncomputable|private|protected|public|"
    r"meta|nonrec|partial|unsafe|local|scoped|open|export|deriving|namespace|end|section|"
    r"import|set_option|attribute|axiom|alias|include|omit|assert_not_exists|"
    r"assert_not_imported|recommended_spelling|add_decl_doc|unlock_limits|"
    r"deprecated_module|deprecated_syntax|init_quot|docs_to_verso|"
    r"register_error_explanation|register_tactic_tag|tactic_extension|"
    r"with_weak_namespace|initialize|builtin_initialize|gen_injective_theorems"
)
_LEAN_HASH_STOP_CMD = (
    r"#(?:check|check_failure|print|synth|where|version|time|eval|eval!|reduce|exit|"
    r"guard|guard_expr|guard_msgs|guard_hyp|guard_target|guard_panic|"
    r"import_path|check_assertions|check_tactic|check_tactic_failure|check_simp|"
    r"info_trees|grind_lint|with_exporting|dump_async_env_state|"
    r"show_deprecated_modules|discr_tree_key|discr_tree_simp_key)"
)
_LEAN_BODY_END = (
    rf"(?=(?<!{_LEAN_ID_REST_AND_DOT_CLS})(?:{_LEAN_SAME_LINE_TOP_KW})(?!{_LEAN_ID_REST_CLS})"
    rf"|@\[|{_LEAN_HASH_STOP_CMD}(?!{_LEAN_ID_REST_CLS})|\n[ \t]*#|\Z)"
)


def _is_lean_letter_like(ch: str) -> bool:
    v = ord(ch)
    return (
        (0x03B1 <= v <= 0x03C9 and v != 0x03BB)
        or (0x0391 <= v <= 0x03A9 and v != 0x03A0 and v != 0x03A3)
        or (0x03CA <= v <= 0x03FB)
        or (0x1F00 <= v <= 0x1FFE)
        or (0x2100 <= v <= 0x214F)
        or (0x1D49C <= v <= 0x1D59F)
        or (0x00C0 <= v <= 0x00FF and v != 0x00D7 and v != 0x00F7)
        or (0x0100 <= v <= 0x017F)
    )


def _is_lean_subscript_alnum(ch: str) -> bool:
    v = ord(ch)
    return (
        (0x2080 <= v <= 0x2089)
        or (0x2090 <= v <= 0x209C)
        or (0x1D62 <= v <= 0x1D6A)
        or v == 0x2C7C
    )


def _is_lean_id_start(ch: str) -> bool:
    return ("a" <= ch <= "z") or ("A" <= ch <= "Z") or ch == "_" or _is_lean_letter_like(ch)


def _is_lean_id_rest(ch: str) -> bool:
    return (
        ("a" <= ch <= "z")
        or ("A" <= ch <= "Z")
        or ("0" <= ch <= "9")
        or ch in ("_", "'", "!", "?")
        or _is_lean_letter_like(ch)
        or _is_lean_subscript_alnum(ch)
    )


# Fail-Closed Pure-Math Policy Tables (Lean v4.32.2 Zero-Ambiguity Theorem)
_PURE_BUILTIN_INTERPOLATORS = frozenset({"s!", "f!", "println!"})

_FORBIDDEN_PROOF_IDENTS = frozenset(
    {
        "sorry",
        "sorryAx",
        "admit",
        "axiom",
        "unsafe",
        "unsafeCast",
        "lcProof",
        "implemented_by",
        "extern",
        "native_decide",
        "native",
        "DecideConfig",
        "decide!",
        "bv_decide",
        "bv_decide?",
        "bv_decide_cbv",
        "bv_decide_check",
        "bv_check",
        "reduceBool",
        "reduceNat",
        "nativeEqTrue",
        "mkNativeAuxDecl",
        "evalConst",
        "evalConstCheck",
        "ofReduceBool",
        "ofReduceNat",
        "trustCompiler",
        "skipKernelTC",
        "proofAsSorry",
        "byAsSorry",
        "terminalTacticsAsSorry",
        "allowUnsafeReducibility",
        "partial",
        "opaque",
        "csimp",
        "stop",
        "impossible",
        "apply?",
        "exact?",
        "calc?",
        "hint",
        "plausible",
        "sorry_if_sorry",
        "conv?",
        "default_or_ofNonempty",
        "try?",
        "grind",
        "grind?",
        "finish",
        "finish?",
        "compactness",
        "compactness?",
        "closedness",
        "closedness?",
        "useSorry",
        "try_suggestions",
        "suggestions",
        "mstop",
        "msorry",
        "sym",
        "lia",
        "cutsat",
        "grind_order",
        "grind_linarith",
        "grobner",
        "mvcgen",
        "mvcgen'",
        "mvcgen?",
    }
)

_FORBIDDEN_META_ANY_IDENTS = frozenset(
    {
        "interpolatedStr",
        "interpolatedStrFn",
        "interpolatedStrNoAntiquot",
        "interpolatedStrKind",
        "interpolatedStrLitKind",
        "expandInterpolatedStr",
        "term_parser",
        "tactic_parser",
        "command_parser",
        "doElem_parser",
        "syntax_parser",
        "stx_parser",
        "leading_parser",
        "trailing_parser",
        "builtin_term_parser",
        "builtin_tactic_parser",
        "builtin_command_parser",
        "builtin_doElem_parser",
        "builtin_syntax_parser",
        "macro_expander",
        "term_elab",
        "tactic_elab",
        "command_elab",
        "doElem_elab",
        "tactic_extension",
        "modifyEnv",
        "setEnv",
        "addDecl",
        "addAndCompile",
        "registerEnvExtension",
        "registerSimplePersistentEnvExtension",
        "registerPersistentEnvExtension",
        "env_extension",
        "addInstance",
    }
)

# Custom syntax/notation/mixfix, metaprogramming, debug, and non-Init interpolator keywords
# unconditionally rejected in audited pure-math frontier certificate files when not French-quoted.
_FORBIDDEN_META_KEYWORDS = frozenset(
    {
        "syntax",
        "declare_syntax_cat",
        "syntax_cat",
        "macro",
        "macro_rules",
        "elab",
        "elab_rules",
        "binder_predicate",
        "notation",
        "notation3",
        "prefix",
        "infix",
        "infixl",
        "infixr",
        "postfix",
        "register_parser_alias",
        "local_notation",
        "scoped_notation",
        "by_elab",
        "by_elabq",
        "run_tac",
        "run_tacq",
        "run_cmd",
        "run_elab",
        "run_meta",
        "initialize",
        "builtin_initialize",
        "prelude",
        "dbg_trace",
        "idbg",
        "m!",
        "v!",
        "throwError",
        "throwErrorAt",
        "throwErrorWithNestedTraces",
        "throwNamedError",
        "throwNamedErrorAt",
        "logNamedError",
        "logNamedErrorAt",
        "logNamedWarning",
        "logNamedWarningAt",
        "logInfo",
        "logInfoAt",
        "logWarning",
        "logWarningAt",
        "logError",
        "logErrorAt",
        "reportIssue!",
        "reportDbgIssue!",
        "reportEMatchIssue!",
        "trace_goal",
        "aesop_trace",
        "aesop_trace!",
        "simproc",
        "dsimproc",
        "cbv_simproc",
        "builtin_simproc",
        "builtin_dsimproc",
        "builtin_cbv_simproc",
        "simproc_decl",
        "dsimproc_decl",
        "cbv_simproc_decl",
        "builtin_simproc_decl",
        "builtin_dsimproc_decl",
        "builtin_cbv_simproc_decl",
        "simproc_pattern",
        "builtin_simproc_pattern",
        "cbv_simproc_pattern",
        "builtin_cbv_simproc_pattern",
        "grind_propagator",
        "builtin_grind_propagator",
        "declare_simp_like_tactic",
        "unif_hint",
        "register_try?_tactic",
        "register_tactic_tag",
        "include",
        "omit",
        "with_weak_namespace",
        "sleep",
        "default_instance",
        "to_additive",
        "to_dual",
        "mk_iff",
        "mk_iff_of_inductive_prop",
        "simps",
        "reassoc",
        "elementwise",
        "module",
        "include_str",
    }
)

_FORBIDDEN_HASH_COMMANDS = frozenset(
    {
        "eval",
        "eval!",
        "reduce",
        "exit",
        "guard",
        "guard_expr",
        "guard_msgs",
        "guard_hyp",
        "guard_target",
        "guard_panic",
    }
)
_FORBIDDEN_CERT_MODS = frozenset({"private", "protected", "meta", "nonrec", "partial", "unsafe"})
_FORBIDDEN_SHADOW_DECLS = (
    # Imported ShannonC7 symbols & namespaces
    "ShannonC7",
    "shannonCapacity",
    "shannonSet",
    "cycleGraph",
    "strongPowPi",
    "strongPow",
    "strongProd",
    "StrongPowV",
    "strongPowAddEquiv",
    "strongPowCongr",
    "strongPow_indepNum_eq_pi",
    "iso_indepNum_eq",
    "c7IsoCycleGraph",
    "indepNum",
    "C7",
    "baseHetero5D",
    "baseHetero5D_asymProfile",
    "le_shannonCapacity_of_nat_pow_pi",
    "le_shannonCapacity_of_nat_pow",
    "le_shannonCapacity_cycleGraph7_of_nat_pow",
    "le_rpow_of_nat_pow",
    "nat_pow_le_of_ble",
    "AsymProfile",
    "HeteroGadget",
    "PortCore",
    "AuxCode",
    "ValidTuple",
    "LayeredTuple",
    "HeteroDAG",
    "Profile",
    "PortSystem",
    "div_lt_div_iff₀",
    # Core / Mathlib types, typeclasses, & literals used in frontier signatures
    "SimpleGraph",
    "Real",
    "Nat",
    "Int",
    "Rat",
    "ℕ",
    "ℝ",
    "ℤ",
    "ℚ",
    "ℂ",
    "ℙ",
    "Fin",
    "Fintype",
    "Finset",
    "Set",
    "List",
    "Array",
    "Bool",
    "Prop",
    "Type",
    "Sort",
    "True",
    "False",
    "Eq",
    "HEq",
    "And",
    "Or",
    "Not",
    "Iff",
    "Exists",
    "LE",
    "LT",
    "GE",
    "GT",
    "HDiv",
    "HPow",
    "HMul",
    "HAdd",
    "HSub",
    "Div",
    "Pow",
    "Mul",
    "Add",
    "Sub",
    "NatCast",
    "IntCast",
    "OfNat",
    "Decidable",
    "DecidableEq",
    "DecidableRel",
    "Nonempty",
    "Inhabited",
    "Subsingleton",
    "Unit",
    "PUnit",
    "Empty",
    "PEmpty",
    "Prod",
    "Sum",
    "Option",
    "true",
    "false",
)

# Mathematically Closed 7-Gate Positive-Whitelist Tables (Lean v4.32.2 + Mathlib/ShannonC7).
# Empirically closed against live Lean v4.32.2 `Lean.Parser.parserExtension` (231 command
# leading tokens, 0 token-less command parsers, 1 trailing token `in`) + exact inventory of
# `ShannonC7/FrontierLower.lean` and BOTH `emit_frontier_lean.py` branches (`PartGadgetDAG`
# & `Gamma6Pow4Pullback`).
_ALLOWED_IMPORT_MODULES = frozenset(
    {
        "ShannonC7.Defs",
        "ShannonC7.Fekete",
        "ShannonC7.CycleC7",
        "ShannonC7.TrieVerifier",
        "ShannonC7.Decimal",
        "ShannonC7.SmallPowers",
        "ShannonC7.ValidTuple",
        "ShannonC7.HeteroLayered",
    }
)
_ALLOWED_NAMESPACE_STACKS = frozenset(
    {
        ("ShannonC7",),
        ("ShannonC7", "PartGadget"),
    }
)
_ALLOWED_DECL_MODIFIERS = frozenset({"noncomputable"})
_ALLOWED_DECL_INTROS = frozenset({"structure", "abbrev", "def", "theorem"})
_ALLOWED_COL0_COMMAND_HEADS = (
    frozenset({"import", "set_option", "namespace", "end", "variable"})
    | _ALLOWED_DECL_MODIFIERS
    | _ALLOWED_DECL_INTROS
)
_FORBIDDEN_UNLISTED_COMMANDS = frozenset(
    {
        # Typeclass / instance / attribute / scope / export / deriving hijacking (R2, R3, R4, R5, M29)
        "instance",
        "default_instance",
        "attribute",
        "open",
        "export",
        "local",
        "scoped",
        "deriving",
        # Disallowed declaration modifiers, visibility, & module/section headers
        "private",
        "protected",
        "public",
        "meta",
        "nonrec",
        "partial",
        "unsafe",
        "module",
        "prelude",
        "section",
        # Disallowed declaration kinds & mutual/universe/variable variants
        "lemma",
        "example",
        "class",
        "inductive",
        "coinductive",
        "alias",
        "mutual",
        "irreducible_def",
        "axiom",
        "opaque",
        "constant",
        "universe",
        "universes",
        "variable?",
        "variables",
        "include",
        "omit",
        # Metaprogramming, custom syntax, notation, simproc, & propagator commands
        "macro",
        "macro_rules",
        "elab",
        "elab_rules",
        "syntax",
        "declare_syntax_cat",
        "binder_predicate",
        "infix",
        "infixl",
        "infixr",
        "prefix",
        "postfix",
        "notation",
        "notation3",
        "initialize",
        "builtin_initialize",
        "tactic_extension",
        "run_cmd",
        "run_elab",
        "run_meta",
        "simproc",
        "simproc_decl",
        "dsimproc",
        "dsimproc_decl",
        "cbv_simproc",
        "cbv_simproc_decl",
        "builtin_simproc",
        "builtin_simproc_decl",
        "builtin_dsimproc",
        "builtin_dsimproc_decl",
        "builtin_cbv_simproc",
        "builtin_cbv_simproc_decl",
        "grind_propagator",
        "builtin_grind_propagator",
        "declare_simp_like_tactic",
        "unif_hint",
        # Declaration-synthesizing / env-mutating / tactic-registering commands & attributes
        "to_additive",
        "to_additive?",
        "to_additive_do_translate",
        "to_additive_dont_translate",
        "to_additive_ignore_args",
        "to_additive_name_hint",
        "insert_to_additive_translation",
        "to_dual",
        "to_dual?",
        "to_dual_do_translate",
        "to_dual_dont_translate",
        "to_dual_ignore_args",
        "to_dual_name_hint",
        "to_dual_insert_cast",
        "to_dual_insert_cast_fun",
        "mk_iff",
        "mk_iff_of_inductive_prop",
        "simps",
        "simps?",
        "simps!",
        "simps!?",
        "simps?!",
        "initialize_simps_projections",
        "initialize_simps_projections?",
        "reassoc",
        "elementwise",
        "norm_cast_add_elim",
        # All remaining Lean v4.32.2 + Mathlib + Batteries + Aesop registered command heads
        "add_decl_doc",
        "add_aesop_rules",
        "erase_aesop_rules",
        "declare_aesop_rule_sets",
        "assert_not_exists",
        "assert_not_imported",
        "assert_no_sorry",
        "recommended_spelling",
        "deprecated_syntax",
        "deprecated_module",
        "deprecate",
        "docs_to_verso",
        "extend_docs",
        "library_note",
        "init_quot",
        "unlock_limits",
        "unset_option",
        "seal",
        "unseal",
        "sudo",
        "whatsnew",
        "reprove",
        "test_extern",
        "def_wanted",
        "theorem_wanted",
        "instance_wanted",
        "proof_wanted",
        "set_library_suggestions",
        "show_panel_widgets",
        "suppress_compilation",
        "unsuppress_compilation",
        "guard_min_heartbeats",
        "guard_decl",
        "recall",
        "recall?",
        "grind_annotated",
        "grind_pattern",
        "init_grind_norm",
        "register_builtin_option",
        "register_error_explanation",
        "register_grind_attr",
        "register_hint",
        "register_label_attr",
        "register_linter_set",
        "register_option",
        "register_simp_attr",
        "register_sym_dsimp",
        "register_sym_simp",
        "register_sym_simp_attr",
        "register_tactic_tag",
        "register_try?_tactic",
        "register_aesop_check_option",
        "declare_bitwise_int_theorems",
        "declare_bitwise_uint_theorems",
        "declare_command_config_elab",
        "declare_command_config_elab_legacy",
        "declare_config_elab",
        "declare_config_elab_legacy",
        "declare_core_config_elab",
        "declare_eval_bin",
        "declare_eval_bin_bitwise",
        "declare_eval_bin_bool_pred",
        "declare_int_theorems",
        "declare_sint_simprocs",
        "declare_term_config_elab",
        "declare_uint_simprocs",
        "declare_uint_theorems",
        "def_eval_config_item",
        "elab_stx_quot",
        "end_local_scope",
        "with_weak_namespace",
        "compile_def",
        "compile_inductive",
        "gen_injective_theorems",
        "reset_grind_attrs",
        "simproc_pattern",
        "cbv_simproc_pattern",
        "builtin_simproc_pattern",
        "builtin_cbv_simproc_pattern",
    }
)
_OPEN_DELIMS = frozenset({"(", "[", "{", "⟨", "⦃"})
_CLOSE_DELIMS = frozenset({")", "]", "}", "⟩", "⦄"})
# Contiguous expression closing delimiters allowed before `.foo?` projections (NB-2b).
# Explicitly EXCLUDES `}` so tactic-block `by { trivial }.simp?` stays strictly rejected!
_EXPR_CLOSE_DELIMS = frozenset({")", "]", "⟩"})
_DECL_INTRO_KW_SET = frozenset(
    {
        "def",
        "abbrev",
        "theorem",
        "lemma",
        "opaque",
        "constant",
        "instance",
        "structure",
        "inductive",
        "coinductive",
        "class",
        "alias",
        "axiom",
    }
)
_LEAN_SCOPE_NON_NAME_KWS = frozenset(
    {
        "theorem",
        "lemma",
        "def",
        "abbrev",
        "example",
        "structure",
        "inductive",
        "coinductive",
        "class",
        "instance",
        "opaque",
        "constant",
        "variable",
        "universe",
        "mutual",
        "noncomputable",
        "private",
        "protected",
        "public",
        "meta",
        "nonrec",
        "partial",
        "unsafe",
        "local",
        "scoped",
        "namespace",
        "end",
        "section",
        "open",
        "export",
        "import",
        "set_option",
        "attribute",
        "axiom",
        "alias",
        "include",
        "omit",
        "deriving",
    }
)
# Unconditional Lean v4.32.2 TokenTable 2-char quote-suffixed Unicode operators
# (Live 822-token dump: Q_ANY minus `]'`, `''`, `⁻¹'`/`⁻¹'o`, and ident/hash tokens).
# None of these characters is `isIdFirst`, so `Basic.lean:1041` unconditionally lexes `<op>'`
# left-to-right at the first character (closing M34/R12 and fixing the `f ∘' g` benign FP).
_UNCOND_UNICODE_QUOTE_OPS = frozenset({"×", "⊕", "Σ", "∏", "∑", "∘"})
# Exhaustive 21 Unicode-leading non-`#`/non-quote `PUNCT_END_ID` tokens from live Lean v4.32.2
# 822-token `TokenTable` (`Basic.lean:1009, 1041`), grouped by first char, longest-first (R17).
_UNICODE_PUNCT_END_ID_PREFIXES: dict[str, tuple[str, ...]] = {
    "→": ("→*₀o", "→+*o", "→*o", "→+o", "→g", "→o", "→r"),
    "≃": ("≃+*o", "≃*o", "≃+o", "≃g", "≃o", "≃r"),
    "↪": ("↪g", "↪o", "↪r"),
    "∘": ("∘SL", "∘L"),
    "≤": ("≤i",),
    "⊕": ("⊕g",),
    "×": ("×ℂ",),
}
# All 25 unused `PUNCT_END_ID` tokens banned unconditionally in Stage 7B Rule L2 (only `≃g` is
# used in `FrontierLower.lean`, and `≃g` is enforced whitespace-followed!).
_FORBIDDEN_PUNCT_END_ID_TOKENS = frozenset(
    {
        "MOD",
        "PMOD",
        "ZMOD",
        "<i",
        "~r",
        "×ℂ",
        "→*₀o",
        "→+*o",
        "→*o",
        "→+o",
        "→g",
        "→o",
        "→r",
        "↪g",
        "↪o",
        "↪r",
        "∘SL",
        "∘L",
        "≃+*o",
        "≃*o",
        "≃+o",
        "≃o",
        "≃r",
        "≤i",
        "⊕g",
    }
)
# Sole parser-ambiguous contiguous quote prefix (`GetElem` `]'` vs scoped `𝓝[...]`/`ℤ[...]` + Char).
_INIT_CONTIG_QUOTE_PREFIX = frozenset({"]"})
# Non-TokenTable Mathlib fallback quote prefixes checked AFTER `_CHAR_LIT_RE` (so `#'"'` lexes `'"'`).
_MATHLIB_FALLBACK_QUOTE_PREFIX = frozenset({"#", "∃", "⟧", "*", "℘", "ᶠ", "𝓡"})
# Compiled fail-closed string-introducer guards for `]'<id>'` disambiguation (R12-DOUBLE/TRIPLE-PRIME).
_RAW_STR_START_RE = re.compile(r'r#*"')
_INTERP_START_RE = re.compile(rf"(?:s!|f!|println!)(?!{_LEAN_ID_REST_CLS})")


def _is_lexer_qual_dot_or_backtick(
    tokens: list[tuple[str, str, int, int, bool]], sep_idx: int
) -> bool:
    """True iff `tokens[sep_idx]` is a Lean qualifier `.` (leading dot or field projection)
    or single name-literal `` ` `` — used ONLY inside `_lex_lean4_single_pass` to suppress
    `r"..."` raw strings and `s!`/`f!`/`println!` interpolated strings.

    Live Lean v4.32.2 TokenTable proof across all 8 whitelisted ShannonC7.* modules + Lean
    (822 tokens): DOT_END = #[*..., ., .., ..., <..., |>.]. ONLY multi-dot tokens
    (prev == contiguous '.') are non-qualifier dot operators; every other contiguous '.'
    is a field projection or leading-dot identifier (never a raw-string or interp-string introducer).
    """
    if sep_idx < 0 or tokens[sep_idx][0] != "PUNCT":
        return False
    sym = tokens[sep_idx][1]
    if sym == ".":
        if sep_idx == 0:
            return True
        prev = tokens[sep_idx - 1]
        return not (prev[0] == "PUNCT" and prev[1] == "." and prev[3] == tokens[sep_idx][2])
    if sym == "`":
        if sep_idx == 0:
            return True
        prev = tokens[sep_idx - 1]
        return not (prev[0] == "PUNCT" and prev[1] == "`" and prev[3] == tokens[sep_idx][2])
    return False


def _has_ident_dot_or_backtick_prev(
    tokens: list[tuple[str, str, int, int, bool]], idx: int
) -> bool:
    """True iff `tokens[idx]` is immediately preceded (contiguously) by `IDENT.` or single `` ` ``.
    NEVER returns True for a leading/tactic-focusing dot `.` after whitespace, `{`, `;`, etc."""
    if idx <= 0:
        return False
    sep = tokens[idx - 1]
    if sep[0] != "PUNCT" or sep[3] != tokens[idx][2]:
        return False
    sym = sep[1]
    if sym == ".":
        return (
            idx >= 2
            and tokens[idx - 2][0] == "IDENT"
            and tokens[idx - 2][3] == sep[2]
        )
    if sym == "`":
        if idx == 1:
            return True
        prev = tokens[idx - 2]
        return not (prev[0] == "PUNCT" and prev[1] == "`" and prev[3] == sep[2])
    return False


def _has_qproj_dot_or_backtick_prev(
    tokens: list[tuple[str, str, int, int, bool]], idx: int
) -> bool:
    """True iff `tokens[idx]` is contiguously preceded by `<expr_atom>.`
    (IDENT, NUMBER, STRING, CHAR, or non-brace closing expr delimiter `)`/`]`/`⟩` + contiguous `.`)
    or single `` ` ``. Used ONLY in Stage 7A Pass A for `?`-suffixed field projections
    like `([1, 2, 3]).getElem? 0` and `(l ++ l).find? ...` (NB-2b).
    NEVER matches tactic focusing `.` (`by .simp?`, `by { trivial }; .simp?`, `by { trivial }.simp?`),
    and NEVER overrides Stage 3 `_FORBIDDEN_PROOF_IDENTS` (`try?`, `exact?`, `grind?`, etc.).
    """
    if _has_ident_dot_or_backtick_prev(tokens, idx):
        return True
    if idx < 2:
        return False
    sep = tokens[idx - 1]
    if sep[0] != "PUNCT" or sep[1] != "." or sep[3] != tokens[idx][2]:
        return False
    prev = tokens[idx - 2]
    if prev[3] != sep[2]:
        return False
    return (
        prev[0] in ("NUMBER", "STRING", "CHAR")
        or (prev[0] == "PUNCT" and prev[1] in _EXPR_CLOSE_DELIMS)
    )


# Token 5-tuple layout: (kind, text, start, end, is_french_quoted)
# kind in ("IDENT", "STRING", "CHAR", "NUMBER", "PUNCT")
def _lex_lean4_single_pass(src: str) -> tuple[list[tuple[str, str, int, int, bool]], str]:
    """Strict single-pass O(N) zero-recursion Lean v4.32.2 lexer & sanitizer.

    Matches installed Lean v4.32.2 `Lean/Parser/Basic.lean` & `Init/Meta/Defs.lean`:
      - Line comments (`-- ...`) and nested block comments (`/- ... -/`, `/-- ... -/`, `/-! ... -/`),
        matching `Basic.lean:578-586` (`pos + 3` after normal `/-`, whitespace skip after `/--` & `/-!`).
      - Exact 2-state O(N) raw string DFA (`r"..."`, `r#"..."#`, ...), suppressed ONLY after qualifier `.` or single `` ` ``.
      - Unambiguous O(1) Init interpolated strings (`s!`, `f!`, `println!` unqualified & non-French-quoted)
        with explicit heap stack `interp_brace_stack` (zero Python recursion).
      - Plain strings (`"..."`) with backslash escapes; every string emits `' "" '` / `' ""\n'`.
      - Exact 5-step `'` / `Char`-literal rule (`''`, `Init` `]`/`×`/`⊕`+' with O(1) `𝓝[...]`/`ℤ[...]` & even-quote guards, `_CHAR_LIT_RE`, Mathlib fallback, fail-closed).
      - French-quoted identifiers (`«...»`) unwrapped to `" " + inner + " "` iff `inner` is a full Lean identifier,
        else `" __LEAN_GUIL__ "` (closing space/symbol-guillemet namespace spoofing).
    """
    if "\x00" in src:
        raise VerifyError("NUL byte in Lean source")
    n = len(src)
    tokens: list[tuple[str, str, int, int, bool]] = []
    clean_chunks: list[str] = []
    interp_brace_stack: list[int] = []
    lbracket_stack: list[int] = []
    last_rbrack_open_idx = -1
    pos = 0

    tok_append = tokens.append
    clean_append = clean_chunks.append
    ws_match = _LEAN_ASCII_WS_RE.match
    ascii_id_match = _ASCII_IDENT_RE.match
    uni_id_match = _LEAN_IDENT_RE.match
    num_match = _NUMBER_RE.match
    char_match = _CHAR_LIT_RE.match
    non_id_char_match = _NON_ID_CHAR_LIT_RE.match
    comm_search = _BLOCK_COMMENT_STOP_RE.search
    plain_str_search = _PLAIN_STR_STOP_RE.search
    interp_str_search = _INTERP_STR_STOP_RE.search
    pure_interps = _PURE_BUILTIN_INTERPOLATORS
    uncond_q_ops = _UNCOND_UNICODE_QUOTE_OPS
    uni_punct_end_id = _UNICODE_PUNCT_END_ID_PREFIXES
    math_q_pre = _MATHLIB_FALLBACK_QUOTE_PREFIX
    raw_str_start_match = _RAW_STR_START_RE.match
    interp_start_match = _INTERP_START_RE.match

    def finish_comment_block(p: int) -> tuple[int, bool]:
        start_p = p
        depth = 1
        while depth > 0:
            m = comm_search(src, p)
            if m is None:
                raise VerifyError("Unclosed Lean block comment (`/-`) at EOF")
            if m.group(0) == "/-":
                depth += 1
            else:
                depth -= 1
            p = m.end()
        return p, ("\n" in src[start_p:p])

    def skip_lean_ws_after_doc_opener(p: int) -> tuple[int, bool]:
        saw_nl = False
        while p < n:
            mw = ws_match(src, p)
            if mw is not None:
                if "\n" in mw.group(0):
                    saw_nl = True
                p = mw.end()
                continue
            c = src[p]
            if c == "-" and p + 1 < n and src[p + 1] == "-":
                nl = src.find("\n", p + 2)
                if nl == -1:
                    return n, saw_nl
                saw_nl = True
                p = nl + 1
            elif c == "/" and p + 1 < n and src[p + 1] == "-":
                if p + 2 >= n:
                    raise VerifyError("Unclosed Lean block comment (`/-`) at EOF")
                c2 = src[p + 2]
                if c2 == "-" or c2 == "!":
                    break
                if c2 == "\n":
                    saw_nl = True
                p, inner_nl = finish_comment_block(p + 3)
                if inner_nl:
                    saw_nl = True
            else:
                break
        return p, saw_nl

    def scan_interp_body(p: int) -> int:
        chunk_start = p
        while True:
            m = interp_str_search(src, p)
            if m is None:
                raise VerifyError("Unclosed Lean interpolated string at EOF")
            hit = m.group(0)
            mpos = m.start()
            if hit == "\\":
                if mpos + 1 >= n:
                    raise VerifyError("Unclosed Lean interpolated string (trailing backslash) at EOF")
                p = mpos + 2
                continue
            if "\n" in src[chunk_start:mpos]:
                clean_append("\n")
            if hit == '"':
                tok_append(("STRING", '"' + src[chunk_start : mpos + 1], chunk_start, mpos + 1, False))
                clean_append(' "" ')
                return mpos + 1
            tok_append(("PUNCT", "{", mpos, mpos + 1, False))
            clean_append(" { ")
            interp_brace_stack.append(1)
            return mpos + 1

    while pos < n:
        ch = src[pos]
        oc = ord(ch)

        if oc == 32 or oc == 10 or oc == 13:
            mw = ws_match(src, pos)
            if mw is not None:
                clean_append(mw.group(0))
                pos = mw.end()
                continue

        if (97 <= oc <= 122) or (65 <= oc <= 90) or oc == 95:
            if oc == 114:  # 'r' raw-string check (suppressed ONLY after qualifier `.` or single `` ` ``)
                is_dotted_or_name = (
                    bool(tokens)
                    and tokens[-1][3] == pos
                    and _is_lexer_qual_dot_or_backtick(tokens, len(tokens) - 1)
                )
                if not is_dotted_or_name:
                    k = 0
                    while pos + 1 + k < n and src[pos + 1 + k] == "#":
                        k += 1
                    if pos + 1 + k < n and src[pos + 1 + k] == '"':
                        start_r = pos
                        p = pos + 2 + k
                        while True:
                            q = src.find('"', p)
                            if q == -1:
                                raise VerifyError("Unclosed Lean raw string literal at EOF")
                            h = q + 1
                            end_h = min(n, h + k)
                            while h < end_h and src[h] == "#":
                                h += 1
                            if h - (q + 1) == k:
                                pos = h
                                break
                            p = h
                        raw_lit = src[start_r:pos]
                        tok_append(("STRING", raw_lit, start_r, pos, False))
                        clean_append(' ""\n' if "\n" in raw_lit else ' "" ')
                        continue
            ma = ascii_id_match(src, pos)
            end_i = ma.end()
            if end_i < n and ord(src[end_i]) >= 128:
                mu = uni_id_match(src, pos)
                end_i = mu.end()
            ident = src[pos:end_i]
            tok_append(("IDENT", ident, pos, end_i, False))
            clean_append(ident)
            pos = end_i
            continue

        if 48 <= oc <= 57:
            mn = num_match(src, pos)
            end_n = mn.end()
            num_txt = src[pos:end_n]
            tok_append(("NUMBER", num_txt, pos, end_n, False))
            clean_append(num_txt + " " if (end_n < n and _is_lean_id_start(src[end_n])) else num_txt)
            pos = end_n
            continue

        if oc == 34:  # '"'
            is_interp = (
                bool(tokens)
                and tokens[-1][0] == "IDENT"
                and not tokens[-1][4]
                and tokens[-1][1] in pure_interps
                and (
                    len(tokens) < 2
                    or not (
                        tokens[-2][3] == tokens[-1][2]
                        and _is_lexer_qual_dot_or_backtick(tokens, len(tokens) - 2)
                    )
                )
            )
            if is_interp:
                pos = scan_interp_body(pos + 1)
                continue
            start_s = pos
            p = pos + 1
            while True:
                m = plain_str_search(src, p)
                if m is None:
                    raise VerifyError("Unclosed Lean string literal at EOF")
                if m.group(0) == "\\":
                    if m.start() + 1 >= n:
                        raise VerifyError("Unclosed Lean string literal (trailing backslash) at EOF")
                    p = m.start() + 2
                    continue
                pos = m.start() + 1
                break
            raw_lit = src[start_s:pos]
            tok_append(("STRING", raw_lit, start_s, pos, False))
            clean_append(' ""\n' if "\n" in raw_lit else ' "" ')
            continue

        if oc == 45 and pos + 1 < n and src[pos + 1] == "-":  # '--'
            nl = src.find("\n", pos + 2)
            pos = n if nl == -1 else nl
            continue

        if oc == 47 and pos + 1 < n and src[pos + 1] == "/":  # '//' (END_SLASH subtype token, R15)
            tok_append(("PUNCT", "//", pos, pos + 2, False))
            clean_append("//")
            pos += 2
            continue

        if oc == 47 and pos + 1 < n and src[pos + 1] == "\\":  # '/\' (conjunction token, NB-4)
            tok_append(("PUNCT", "/\\", pos, pos + 2, False))
            clean_append("/\\")
            pos += 2
            continue

        if oc == 47 and pos + 1 < n and src[pos + 1] == "-":  # '/-', '/--', '/-!'
            if pos + 2 >= n:
                raise VerifyError("Unclosed Lean block comment (`/-`) at EOF")
            c2 = src[pos + 2]
            if c2 == "-" or c2 == "!":
                p2, ws_nl = skip_lean_ws_after_doc_opener(pos + 3)
                pos, body_nl = finish_comment_block(p2)
                saw_nl = ws_nl or body_nl
            else:
                saw_nl = c2 == "\n"
                pos, body_nl = finish_comment_block(pos + 3)
                saw_nl = saw_nl or body_nl
            clean_append("\n" if saw_nl else " ")
            continue

        if interp_brace_stack:
            if oc == 123:  # '{'
                interp_brace_stack[-1] += 1
                tok_append(("PUNCT", "{", pos, pos + 1, False))
                clean_append("{")
                pos += 1
                continue
            if oc == 125:  # '}'
                if interp_brace_stack[-1] > 1:
                    interp_brace_stack[-1] -= 1
                    tok_append(("PUNCT", "}", pos, pos + 1, False))
                    clean_append("}")
                    pos += 1
                    continue
                interp_brace_stack.pop()
                tok_append(("PUNCT", "}", pos, pos + 1, False))
                clean_append(" } ")
                pos = scan_interp_body(pos + 1)
                continue

        if oc == 39:  # "'"
            is_rbrack_prev = (
                pos > 0
                and src[pos - 1] == "]"
                and bool(tokens)
                and tokens[-1][0] == "PUNCT"
                and tokens[-1][1] == "]"
                and tokens[-1][3] == pos
            )
            is_non_getelem_rbrack = (
                is_rbrack_prev
                and last_rbrack_open_idx > 0
                and tokens[last_rbrack_open_idx - 1][0] == "IDENT"
                and tokens[last_rbrack_open_idx - 1][1] in ("𝓝", "ℤ")
                and tokens[last_rbrack_open_idx - 1][3] == tokens[last_rbrack_open_idx][2]
            )
            if is_rbrack_prev and is_non_getelem_rbrack:
                # Layer-1 defense-in-depth for locally rebound `let 𝓝 := #[...]` / `let ℤ := #[...]`
                # (R12-NHDS / R12-Z): NEVER permit `]''` or `]' '` / `]'\n'` / `]'('` followed by
                # quote/escape/brace/ident while preserving `𝓝[≠]'"'`, `𝓝[≠]'}'`, `(𝓝[≠]' ','"')`.
                if pos + 1 < n and src[pos + 1] == "'":
                    raise VerifyError("Ambiguous double-quote immediately after `]` (`]''`)")
                md_ng = non_id_char_match(src, pos)
                if (
                    md_ng is not None
                    and md_ng.group(0) in ("' '", "'\n'", "'\r'", "'('")
                    and md_ng.end() < n
                    and (
                        src[md_ng.end()] in ('"', "'", "\\", "{", "}")
                        or _is_lean_id_start(src[md_ng.end()])
                    )
                ):
                    raise VerifyError("Ambiguous Char-like literal immediately after `]` (`]'...`)")
                mc_ng = char_match(src, pos)
                if mc_ng is not None:
                    q_end_ng = mc_ng.end()
                    k_q_ng = 0
                    while q_end_ng + k_q_ng < n and src[q_end_ng + k_q_ng] == "'":
                        k_q_ng += 1
                    after_q_ng = q_end_ng + k_q_ng
                    if (
                        k_q_ng % 2 == 1
                        and after_q_ng < n
                        and src[after_q_ng] in (" ", "\n", "\r", "(")
                    ):
                        md_ng2 = non_id_char_match(src, after_q_ng - 1)
                        if (
                            md_ng2 is not None
                            and md_ng2.end() < n
                            and src[md_ng2.end()] in ('"', "'", "\\", "{", "}")
                        ):
                            raise VerifyError("Ambiguous Char-like literal immediately after `]` (`]'...`)")

            if is_rbrack_prev and not is_non_getelem_rbrack:
                # Fail-closed guard for `GetElem` `]'` vs `''`/`CHAR` ambiguity (R12a/b/d/e/f):
                # Never steal the `'` of `]'` into `PUNCT "''"` or a fake non-id `CHAR` literal.
                if pos + 1 < n and src[pos + 1] == "'":
                    raise VerifyError("Ambiguous double-quote immediately after `]` (`]''`)")
                if non_id_char_match(src, pos) is not None:
                    raise VerifyError("Ambiguous Char-like literal immediately after `]` (`]'...`)")
                mc_q = char_match(src, pos)
                lex_as_char = False
                if mc_q is not None:
                    # Strictly O(N): each `'` is scanned at most twice across the entire input.
                    q_end = mc_q.end()
                    k_quotes = 0
                    while q_end + k_quotes < n and src[q_end + k_quotes] == "'":
                        k_quotes += 1
                    after_q = q_end + k_quotes
                    # R12-PRIME: when `k_quotes` is odd (e.g. `a[0]'h''\n'"'`, `a[0]'h'' '"'`,
                    # `a[0]'h''('"')`), emit `PUNCT "'"` so `h''` stays an IDENT (zero desync!).
                    # R12-DOUBLE/TRIPLE-PRIME: when `k_quotes` is even and followed by raw/interp
                    # string introducer (`a[0]'h'r"\""`, `a[0]'h's! "{"`), fail closed!
                    if k_quotes % 2 == 0 and after_q < n:
                        if (
                            raw_str_start_match(src, after_q) is not None
                            or interp_start_match(src, after_q) is not None
                        ):
                            raise VerifyError("Ambiguous string introducer after `]'<id>'` sequence")
                        if _is_lean_id_start(src[after_q]) or src[after_q] in ('"', "«", "#", "(", "{"):
                            lex_as_char = True
                if lex_as_char:
                    lit = mc_q.group(0)
                    end_c = mc_q.end()
                    tok_append(("CHAR", lit, pos, end_c, False))
                    clean_append(" ' '\n" if "\n" in lit else " ' ' ")
                    pos = end_c
                    continue
                tok_append(("PUNCT", "'", pos, pos + 1, False))
                clean_append("'")
                pos += 1
                continue

            if pos + 1 < n and src[pos + 1] == "'":
                tok_append(("PUNCT", "''", pos, pos + 2, False))
                clean_append("''")
                pos += 2
                continue
            md = non_id_char_match(src, pos)
            if md is not None:
                lit = md.group(0)
                end_c = md.end()
                tok_append(("CHAR", lit, pos, end_c, False))
                clean_append(" ' '\n" if "\n" in lit else " ' ' ")
                pos = end_c
                continue
            mc = char_match(src, pos)
            if mc is not None:
                lit = mc.group(0)
                end_c = mc.end()
                tok_append(("CHAR", lit, pos, end_c, False))
                clean_append(" ' '\n" if "\n" in lit else " ' ' ")
                pos = end_c
                continue
            if pos > 0 and src[pos - 1] in math_q_pre:
                tok_append(("PUNCT", "'", pos, pos + 1, False))
                clean_append("'")
                pos += 1
                continue
            raise VerifyError("Unclosed or malformed Lean Char literal")

        if oc == 60:  # '<': greedily lex '<...<'/'<...' (NB-4), '<<<'/'<=<'/'<-' (R15), '<i' (R17)
            if src.startswith("<...<", pos):
                tok_append(("PUNCT", "<...<", pos, pos + 5, False))
                clean_append("<...<")
                pos += 5
                continue
            if src.startswith("<...", pos):
                tok_append(("PUNCT", "<...", pos, pos + 4, False))
                clean_append("<...")
                pos += 4
                continue
            if pos + 2 < n and src[pos : pos + 3] in ("<<<", "<=<"):
                tk3 = src[pos : pos + 3]
                tok_append(("PUNCT", tk3, pos, pos + 3, False))
                clean_append(tk3)
                pos += 3
                continue
            if pos + 1 < n and src[pos + 1] == "-":
                tok_append(("PUNCT", "<-", pos, pos + 2, False))
                clean_append("<-")
                pos += 2
                continue
            if pos + 1 < n and src[pos + 1] == "i":
                tok_append(("PUNCT", "<i", pos, pos + 2, False))
                clean_append("<i" if (pos + 2 < n and src[pos + 2] in (" ", "\n", "\r")) else "<i ")
                pos += 2
                continue

        if oc == 92 and pos + 1 < n and src[pos + 1] == "/":  # '\/' (END_SLASH disjunction token, R15)
            tok_append(("PUNCT", "\\/", pos, pos + 2, False))
            clean_append("\\/")
            pos += 2
            continue

        if oc == 61:  # '=': greedily lex '=<<' (NB-4) and '=>'
            if pos + 2 < n and src[pos + 1] == "<" and src[pos + 2] == "<":
                tok_append(("PUNCT", "=<<", pos, pos + 3, False))
                clean_append("=<<")
                pos += 3
                continue
            if pos + 1 < n and src[pos + 1] == ">":
                tok_append(("PUNCT", "=>", pos, pos + 2, False))
                clean_append("=>")
                pos += 2
                continue

        if oc == 94 and pos + 1 < n and src[pos + 1] == "<":  # '^<' (NB-4)
            tok_append(("PUNCT", "^<", pos, pos + 2, False))
            clean_append("^<")
            pos += 2
            continue

        if oc == 42 and src.startswith("*...<", pos):  # '*...<' (NB-4)
            tok_append(("PUNCT", "*...<", pos, pos + 5, False))
            clean_append("*...<")
            pos += 5
            continue

        if oc == 46 and src.startswith("...<", pos):  # '...<' (NB-4)
            tok_append(("PUNCT", "...<", pos, pos + 4, False))
            clean_append("...<")
            pos += 4
            continue

        if oc == 126 and pos + 1 < n and src[pos + 1] == "r":  # '~r' (R17)
            tok_append(("PUNCT", "~r", pos, pos + 2, False))
            clean_append("~r" if (pos + 2 < n and src[pos + 2] in (" ", "\n", "\r")) else "~r ")
            pos += 2
            continue

        if oc >= 128:
            if oc == 0x00AB:  # '«'
                end_g = src.find("»", pos + 1)
                if end_g == -1:
                    raise VerifyError("Unclosed Lean escaped identifier (`«...»`) at EOF")
                inner = src[pos + 1 : end_g]
                if "\n" in inner or "\r" in inner:
                    raise VerifyError("Newline inside Lean escaped identifier (`«...»`)")
                tok_append(("IDENT", inner, pos, end_g + 1, True))
                mu_in = uni_id_match(inner, 0) if inner else None
                if mu_in is not None and mu_in.end() == len(inner):
                    clean_append(" " + inner + " ")
                else:
                    clean_append(" __LEAN_GUIL__ ")
                pos = end_g + 1
                continue
            if ch in uncond_q_ops and pos + 1 < n and src[pos + 1] == "'":
                op_txt = ch + "'"
                tok_append(("PUNCT", op_txt, pos, pos + 2, False))
                clean_append(op_txt)
                pos += 2
                continue
            if oc == 0x207B and pos + 2 < n and src[pos + 1] == "¹" and src[pos + 2] == "'":
                if pos + 3 < n and src[pos + 3] == "o":
                    tok_append(("PUNCT", "⁻¹'o", pos, pos + 4, False))
                    clean_append("⁻¹'o")
                    pos += 4
                else:
                    tok_append(("PUNCT", "⁻¹'", pos, pos + 3, False))
                    clean_append("⁻¹'")
                    pos += 3
                continue
            u_ops = uni_punct_end_id.get(ch)
            if u_ops is not None:
                matched_uop = None
                for uop in u_ops:
                    if src.startswith(uop, pos):
                        matched_uop = uop
                        break
                if matched_uop is not None:
                    u_len = len(matched_uop)
                    tok_append(("PUNCT", matched_uop, pos, pos + u_len, False))
                    clean_append(
                        matched_uop
                        if (pos + u_len < n and src[pos + u_len] in (" ", "\n", "\r"))
                        else matched_uop + " "
                    )
                    pos += u_len
                    continue
            mu = uni_id_match(src, pos)
            if mu is not None:
                end_i = mu.end()
                ident = src[pos:end_i]
                tok_append(("IDENT", ident, pos, end_i, False))
                clean_append(ident)
                pos = end_i
                continue

        if oc == 91:  # '[': preserve bracket stack & greedily split `[PMOD`/`[ZMOD`/`[MOD` (R17)
            lbracket_stack.append(len(tokens))
            tok_append(("PUNCT", "[", pos, pos + 1, False))
            if src[pos : pos + 5] in ("[PMOD", "[ZMOD"):
                kw_part = src[pos + 1 : pos + 5]
                tok_append(("PUNCT", kw_part, pos + 1, pos + 5, False))
                clean_append("[" + kw_part + " ")
                pos += 5
                continue
            if src[pos : pos + 4] == "[MOD":
                tok_append(("PUNCT", "MOD", pos + 1, pos + 4, False))
                clean_append("[MOD ")
                pos += 4
                continue
            clean_append("[")
            pos += 1
            continue
        if oc == 93:  # ']'
            last_rbrack_open_idx = lbracket_stack.pop() if lbracket_stack else -1
        tok_append(("PUNCT", ch, pos, pos + 1, False))
        clean_append(ch)
        pos += 1

    if interp_brace_stack:
        raise VerifyError("Unclosed `{...}` interpolation in Lean interpolated string at EOF")
    return tokens, "".join(clean_chunks)


def _strip_lean_comments_and_strings(src: str) -> str:
    """Backward-compatible helper returning sanitized live Lean code."""
    return _lex_lean4_single_pass(src)[1]


def _check_lean_hygiene(
    tokens: list[tuple[str, str, int, int, bool]], lean_path: pathlib.Path | str
) -> None:
    """Enforce Fail-Closed Pure-Math Policy directly on exact Lean v4.32.2 tokens (O(N))."""
    n_tok = len(tokens)
    forb_proof = _FORBIDDEN_PROOF_IDENTS
    forb_meta_any = _FORBIDDEN_META_ANY_IDENTS
    forb_meta_kw = _FORBIDDEN_META_KEYWORDS
    forb_hash = _FORBIDDEN_HASH_COMMANDS

    for idx, tok in enumerate(tokens):
        kind, word, t_start, t_end, is_fq = tok
        if kind == "PUNCT" and word == "∎":
            raise VerifyError(f"{lean_path}: forbidden proof/kernel token '∎' found in live code")
        if kind != "IDENT":
            continue
        if word in forb_proof:
            raise VerifyError(f"{lean_path}: forbidden proof/kernel token {word!r} found in live code")
        if word in forb_meta_any:
            raise VerifyError(f"{lean_path}: forbidden meta/parser token {word!r} found in live code")
        if not is_fq:
            if word in forb_meta_kw:
                raise VerifyError(f"{lean_path}: forbidden metaprogramming/syntax token {word!r} found in live code")
            if (
                word == "eval"
                and idx + 1 < n_tok
                and tokens[idx + 1][0] == "PUNCT"
                and tokens[idx + 1][1] == "%"
                and tokens[idx + 1][2] == t_end
                and not _has_ident_dot_or_backtick_prev(tokens, idx)
            ):
                raise VerifyError(f"{lean_path}: forbidden unsafe `eval%` elaborator found in live code")
            if (
                word == "trace"
                and idx + 1 < n_tok
                and tokens[idx + 1][0] == "PUNCT"
                and tokens[idx + 1][1] == "["
                and tokens[idx + 1][2] == t_end
            ):
                raise VerifyError(
                    f"{lean_path}: forbidden `trace[...]` metaprogramming construct found in live code"
                )
            if word == "decide" and idx + 1 < n_tok:
                nxt = tokens[idx + 1]
                if nxt[0] == "PUNCT" and nxt[1] in ("+", "-", "{"):
                    raise VerifyError(
                        f"{lean_path}: forbidden configured `decide {nxt[1]}...` tactic "
                        f"(only bare pure-kernel `decide` allowed)"
                    )
                if (
                    nxt[0] == "PUNCT"
                    and nxt[1] == "("
                    and idx + 4 < n_tok
                    and tokens[idx + 2][0] == "IDENT"
                    and tokens[idx + 3][0] == "PUNCT"
                    and tokens[idx + 3][1] == ":"
                    and tokens[idx + 4][0] == "PUNCT"
                    and tokens[idx + 4][1] == "="
                    and tokens[idx + 3][3] == tokens[idx + 4][2]
                ):
                    raise VerifyError(
                        f"{lean_path}: forbidden configured `decide ({tokens[idx + 2][1]} := ...)` tactic"
                    )
            if (
                word in forb_hash
                and idx > 0
                and tokens[idx - 1][0] == "PUNCT"
                and tokens[idx - 1][1] == "#"
                and tokens[idx - 1][3] == t_start
            ):
                raise VerifyError(f"{lean_path}: forbidden command `#{word}` found in live code")
            if word == "import":
                unqual = not _has_ident_dot_or_backtick_prev(tokens, idx)
                if unqual:
                    mod_idx = idx + 1
                    if (
                        mod_idx < n_tok
                        and tokens[mod_idx][0] == "IDENT"
                        and not tokens[mod_idx][4]
                        and tokens[mod_idx][1] == "all"
                    ):
                        mod_idx += 1
                    if mod_idx < n_tok and tokens[mod_idx][0] == "IDENT" and tokens[mod_idx][1] == "Mathlib":
                        has_dot_cont = (
                            mod_idx + 1 < n_tok
                            and tokens[mod_idx + 1][0] == "PUNCT"
                            and tokens[mod_idx + 1][1] == "."
                            and tokens[mod_idx + 1][2] == tokens[mod_idx][3]
                        )
                        if not has_dot_cont:
                            raise VerifyError(f"{lean_path}: forbidden wholesale `import Mathlib`")


def _build_line_starts(src: str) -> list[int]:
    starts = [0]
    pos = 0
    while True:
        nl = src.find("\n", pos)
        if nl == -1:
            break
        starts.append(nl + 1)
        pos = nl + 1
    return starts


def _read_dotted_ident_checked(
    tokens: list[tuple[str, str, int, int, bool]], idx: int
) -> tuple[list[str], bool, int]:
    """Read contiguous dotted ident; returns `(segments, any_french_quoted, next_idx)`."""
    n_tok = len(tokens)
    if idx >= n_tok or tokens[idx][0] != "IDENT":
        return [], False, idx
    segs = [tokens[idx][1]]
    any_fq = bool(tokens[idx][4])
    cur = idx + 1
    while (
        cur + 1 < n_tok
        and tokens[cur][0] == "PUNCT"
        and tokens[cur][1] == "."
        and tokens[cur][2] == tokens[cur - 1][3]
        and tokens[cur + 1][0] == "IDENT"
        and tokens[cur + 1][2] == tokens[cur][3]
    ):
        segs.append(tokens[cur + 1][1])
        if tokens[cur + 1][4]:
            any_fq = True
        cur += 2
    return segs, any_fq, cur


def _check_lean_positive_whitelist(
    src: str,
    tokens: list[tuple[str, str, int, int, bool]],
    lean_path: pathlib.Path | str,
) -> None:
    """Enforce Mathematically Closed 7-Gate Positive Whitelist directly on Lean v4.32.2 tokens (O(N)).

    Runs unconditionally as Stage 7 (after Stage 6 `_check_lean_decl_scopes`) so defense-in-depth
    Stages 3-6 remain unmasked while `verify_lean_file` is 100% mathematically fail-closed:
      - Gate 1: Header-only `import` strictly in `_ALLOWED_IMPORT_MODULES` (col 0, depth 0, 1/line).
      - Gate 2: Scoped `set_option ... in` ONLY at col 0 depth 0 for `linter.unusedFintypeInType false`
                or `exponentiation.threshold <1..10_000_000>` before a whitelisted decl/set_option.
      - Gate 3: Total unconditional ban on `@[...]` attributes at ALL depths & columns.
      - Gate 4: Total unconditional ban on contiguous `#<ident>` (except pure `s!`/`f!`/`println!`).
      - Gate 5: Exact balanced `namespace`/`end` stacks in `{("ShannonC7",), ("ShannonC7", "PartGadget")}`
                (NO `section`!), `variable` ONLY inside `ShannonC7.PartGadget`.
      - Gate 6A: Global rejection of ALL non-whitelisted Lean v4.32.2 command/modifier/synthesizer keywords.
      - Gate 6B: True positive col-0/depth-0 grammar over exact 10-keyword `_ALLOWED_COL0_COMMAND_HEADS`,
                `noncomputable` ONLY immediately before `def`, zero indented/chained commands, exact delimiter balance.
    """
    n_tok = len(tokens)
    line_starts = _build_line_starts(src)
    n_lines = len(line_starts)
    pure_interps = _PURE_BUILTIN_INTERPOLATORS
    forb_cmds = _FORBIDDEN_UNLISTED_COMMANDS
    open_d = _OPEN_DELIMS
    close_d = _CLOSE_DELIMS

    # Pass A (strict O(N) via monotone line pointer):
    # Compute (line, col, depth) + enforce Gate 3 (@[), Gate 4 (#<ident>),
    # Gate 6A (_FORBIDDEN_UNLISTED_COMMANDS), and non-col0/non-depth0 `set_option` EVERYWHERE.
    depths: list[int] = [0] * n_tok
    lns: list[int] = [0] * n_tok
    cols: list[int] = [0] * n_tok
    cur_depth = 0
    cur_li = 0

    for idx, tok in enumerate(tokens):
        kind, word, ts, te, is_fq = tok
        while cur_li + 1 < n_lines and line_starts[cur_li + 1] <= ts:
            cur_li += 1
        ln = cur_li + 1
        col = ts - line_starts[cur_li]
        lns[idx] = ln
        cols[idx] = col
        depths[idx] = cur_depth

        if kind == "PUNCT":
            if word in open_d:
                cur_depth += 1
            elif word in close_d:
                cur_depth -= 1
                if cur_depth < 0:
                    raise VerifyError(f"{lean_path}:{ln}: unmatched closing delimiter `{word}`")
            if (
                word == "@"
                and idx + 1 < n_tok
                and tokens[idx + 1][0] == "PUNCT"
                and tokens[idx + 1][1] == "["
            ):
                raise VerifyError(
                    f"{lean_path}:{ln}: forbidden attribute syntax `@[...]` "
                    f"(0 attributes permitted in pure-math frontier certificates)"
                )
        elif kind == "IDENT" and not is_fq:
            if (
                idx > 0
                and tokens[idx - 1][0] == "PUNCT"
                and tokens[idx - 1][1] == "#"
                and tokens[idx - 1][3] == ts
                and word not in pure_interps
            ):
                raise VerifyError(f"{lean_path}:{ln}: forbidden `#`-command `#{word}` found in live code")
            if word in forb_cmds and not _has_ident_dot_or_backtick_prev(tokens, idx):
                raise VerifyError(
                    f"{lean_path}:{ln}: forbidden non-whitelisted Lean command/modifier `{word}`"
                )
            if (
                word == "set_option"
                and not _has_ident_dot_or_backtick_prev(tokens, idx)
                and (col != 0 or depths[idx] != 0)
            ):
                raise VerifyError(
                    f"{lean_path}:{ln}: `set_option` only permitted at column 0 depth 0 "
                    f"(got col={col}, depth={depths[idx]})"
                )
            if (word.endswith("?") or word.endswith("?!")) and not _has_qproj_dot_or_backtick_prev(tokens, idx):
                is_decl_name_pos = (
                    idx > 0
                    and tokens[idx - 1][0] == "IDENT"
                    and not tokens[idx - 1][4]
                    and tokens[idx - 1][1] in _ALLOWED_DECL_INTROS
                )
                if not is_decl_name_pos:
                    raise VerifyError(
                        f"{lean_path}:{ln}: forbidden interactive `?`-suggestion tactic/identifier `{word}`"
                    )

    if cur_depth != 0:
        raise VerifyError(f"{lean_path}: unclosed delimiter(s) at EOF (depth={cur_depth})")

    # Pass B (strict O(N)):
    # Enforce Gate 1 (header-only closed imports), Gate 2 (exact scoped `set_option ... in`),
    # Gate 5 (closed `namespace`/`variable`/`end` stacks, NO `section`), and Gate 6B
    # (exact 10-keyword col-0/depth-0 grammar + no indented/same-line chaining).
    header_done = False
    ns_stack: list[str] = []
    allowed_inline_cmd_idx: set[int] = set()
    require_col0_at_idx: set[int] = {0} if n_tok > 0 else set()
    allowed_col0 = _ALLOWED_COL0_COMMAND_HEADS
    allowed_intros = _ALLOWED_DECL_INTROS
    allowed_set_opt_targets = _ALLOWED_DECL_MODIFIERS | allowed_intros | {"set_option"}

    idx = 0
    while idx < n_tok:
        kind, word, ts, te, is_fq = tokens[idx]
        ln, col, depth = lns[idx], cols[idx], depths[idx]

        if idx in require_col0_at_idx and col != 0:
            raise VerifyError(
                f"{lean_path}:{ln}: indented or same-line token `{word}` (col={col}) "
                f"not allowed after header/scope command"
            )

        # Gate 1: Closed Header-Only `import` Whitelist
        if kind == "IDENT" and not is_fq and word == "import" and not _has_ident_dot_or_backtick_prev(tokens, idx):
            mod_idx = idx + 1
            saw_all = False
            if (
                mod_idx < n_tok
                and tokens[mod_idx][0] == "IDENT"
                and not tokens[mod_idx][4]
                and tokens[mod_idx][1] == "all"
            ):
                saw_all = True
                mod_idx += 1
            segs, any_fq, next_idx = _read_dotted_ident_checked(tokens, mod_idx)
            mod_name = ".".join(segs) if segs else "<missing>"
            if mod_name == "Mathlib":
                raise VerifyError(f"{lean_path}:{ln}: forbidden wholesale `import Mathlib`")
            if header_done or col != 0 or depth != 0:
                raise VerifyError(
                    f"{lean_path}:{ln}: forbidden `import {mod_name}` outside column-0 module header"
                )
            if saw_all:
                raise VerifyError(f"{lean_path}:{ln}: forbidden `import all {mod_name}`")
            if any_fq or not segs:
                raise VerifyError(f"{lean_path}:{ln}: malformed or French-quoted `import {mod_name}`")
            if mod_name not in _ALLOWED_IMPORT_MODULES:
                raise VerifyError(
                    f"{lean_path}:{ln}: forbidden non-whitelisted `import {mod_name}` "
                    f"(allowed: {sorted(_ALLOWED_IMPORT_MODULES)})"
                )
            if next_idx < n_tok and lns[next_idx] == ln:
                raise VerifyError(
                    f"{lean_path}:{ln}: unexpected trailing token `{tokens[next_idx][1]}` on `import` line"
                )
            if next_idx < n_tok:
                require_col0_at_idx.add(next_idx)
            idx = next_idx
            continue

        header_done = True

        # Gate 2: Closed Scoped `set_option ... in` Whitelist
        if kind == "IDENT" and not is_fq and word == "set_option" and not _has_ident_dot_or_backtick_prev(tokens, idx):
            key_segs, key_fq, after_key = _read_dotted_ident_checked(tokens, idx + 1)
            opt_key = ".".join(key_segs) if key_segs else "<missing>"
            if key_fq or not key_segs or after_key >= n_tok:
                raise VerifyError(f"{lean_path}:{ln}: malformed `set_option {opt_key}`")
            val_kind, val_word, _, _, val_fq = tokens[after_key]
            ok_opt = (
                opt_key == "linter.unusedFintypeInType"
                and val_kind == "IDENT"
                and not val_fq
                and val_word == "false"
            ) or (
                opt_key == "exponentiation.threshold"
                and val_kind == "NUMBER"
                and len(val_word) <= 8
                and val_word.isascii()
                and val_word.isdigit()
                and val_word == str(int(val_word))
                and 1 <= int(val_word) <= 10_000_000
            )
            if not ok_opt:
                raise VerifyError(
                    f"{lean_path}:{ln}: forbidden non-whitelisted `set_option {opt_key} {val_word}`"
                )
            in_idx = after_key + 1
            if (
                in_idx >= n_tok
                or tokens[in_idx][0] != "IDENT"
                or tokens[in_idx][4]
                or tokens[in_idx][1] != "in"
            ):
                raise VerifyError(
                    f"{lean_path}:{ln}: unscoped `set_option {opt_key}` not allowed (must be scoped with `in`)"
                )
            target_idx = in_idx + 1
            if target_idx >= n_tok:
                raise VerifyError(f"{lean_path}:{ln}: dangling `set_option ... in` at EOF")
            if lns[target_idx] == ln:
                allowed_inline_cmd_idx.add(target_idx)
            else:
                require_col0_at_idx.add(target_idx)
            tk_k, tk_w, _, _, tk_fq = tokens[target_idx]
            if tk_k != "IDENT" or tk_fq or tk_w not in allowed_set_opt_targets:
                raise VerifyError(
                    f"{lean_path}:{ln}: `set_option ... in` must precede a whitelisted declaration, got `{tk_w}`"
                )
            idx = target_idx
            continue

        # Gate 6B: True Positive Top-Level Command & Modifier Grammar (EXACT 10 keywords)
        is_top_cmd_site = (col == 0 and depth == 0) or (idx in allowed_inline_cmd_idx)

        if is_top_cmd_site:
            if kind != "IDENT" or is_fq or word not in allowed_col0:
                raise VerifyError(
                    f"{lean_path}:{ln}: forbidden non-whitelisted top-level command `{word}` "
                    f"(allowed: {sorted(allowed_col0)})"
                )

            if word == "namespace":
                segs, any_fq, next_idx = _read_dotted_ident_checked(tokens, idx + 1)
                if not segs or any_fq:
                    raise VerifyError(f"{lean_path}:{ln}: malformed or French-quoted `namespace`")
                ns_stack.extend(segs)
                cur_ns = tuple(ns_stack)
                if cur_ns not in _ALLOWED_NAMESPACE_STACKS:
                    raise VerifyError(
                        f"{lean_path}:{ln}: forbidden non-whitelisted namespace "
                        f"`{'.'.join(cur_ns)}` (allowed: `ShannonC7`, `ShannonC7.PartGadget`)"
                    )
                if next_idx < n_tok and lns[next_idx] == ln:
                    raise VerifyError(
                        f"{lean_path}:{ln}: unexpected trailing token `{tokens[next_idx][1]}` on `namespace` line"
                    )
                if next_idx < n_tok:
                    require_col0_at_idx.add(next_idx)
                idx = next_idx
                continue

            if word == "end":
                next_idx = idx + 1
                if next_idx >= n_tok or lns[next_idx] != ln:
                    raise VerifyError(
                        f"{lean_path}:{ln}: anonymous `end` not permitted (must name open namespace {ns_stack})"
                    )
                segs, any_fq, next_idx = _read_dotted_ident_checked(tokens, next_idx)
                if not segs or any_fq or len(ns_stack) < len(segs) or ns_stack[-len(segs) :] != segs:
                    raise VerifyError(
                        f"{lean_path}:{ln}: mismatched `end {'.'.join(segs)}` for namespace stack {ns_stack}"
                    )
                del ns_stack[-len(segs) :]
                if next_idx < n_tok and lns[next_idx] == ln:
                    raise VerifyError(
                        f"{lean_path}:{ln}: unexpected trailing token `{tokens[next_idx][1]}` on `end` line"
                    )
                if next_idx < n_tok:
                    require_col0_at_idx.add(next_idx)
                idx = next_idx
                continue

            if word == "variable":
                cur_ns = tuple(ns_stack)
                if cur_ns != ("ShannonC7", "PartGadget"):
                    ns_s = ".".join(cur_ns) if cur_ns else "<root>"
                    raise VerifyError(
                        f"{lean_path}:{ln}: `variable` only permitted inside closed sub-namespace "
                        f"`ShannonC7.PartGadget` (current namespace: `{ns_s}`)"
                    )
                if idx + 1 >= n_tok or tokens[idx + 1][0] != "PUNCT" or tokens[idx + 1][1] not in ("(", "{", "[", "⦃"):
                    raise VerifyError(f"{lean_path}:{ln}: malformed `variable` binder list")
                j = idx + 1
                b_depth = 0
                while j < n_tok:
                    jk, jw, _, _, jfq = tokens[j]
                    if b_depth == 0:
                        if j > idx + 1 and cols[j] == 0:
                            break
                        if jk == "IDENT" and not jfq and jw == "in":
                            raise VerifyError(f"{lean_path}:{ln}: `variable ... in` combinator not permitted")
                        if jk == "PUNCT" and jw in ("(", "{", "[", "⦃"):
                            b_depth += 1
                        else:
                            raise VerifyError(f"{lean_path}:{lns[j]}: unexpected token `{jw}` in `variable` command")
                    else:
                        if (
                            jk == "IDENT"
                            and not jfq
                            and jw in allowed_col0
                            and not _has_ident_dot_or_backtick_prev(tokens, j)
                        ):
                            raise VerifyError(
                                f"{lean_path}:{lns[j]}: command/modifier `{jw}` not allowed inside `variable` binder"
                            )
                        if jk == "PUNCT" and jw in open_d:
                            b_depth += 1
                        elif jk == "PUNCT" and jw in close_d:
                            b_depth -= 1
                    j += 1
                idx = j
                continue

            if word == "noncomputable":
                cur = idx + 1
                if cur >= n_tok or tokens[cur][0] != "IDENT" or tokens[cur][4] or tokens[cur][1] != "def":
                    got = tokens[cur][1] if cur < n_tok else "<EOF>"
                    raise VerifyError(
                        f"{lean_path}:{ln}: `noncomputable` modifier must immediately precede `def`, got `{got}`"
                    )
                if lns[cur] != ln and cols[cur] != 0:
                    raise VerifyError(
                        f"{lean_path}:{lns[cur]}: indented `def` after `noncomputable` not allowed"
                    )
                allowed_inline_cmd_idx.add(cur)
                idx = cur
                continue

            if word in allowed_intros:
                segs, any_fq, _ = _read_dotted_ident_checked(tokens, idx + 1)
                if not segs:
                    raise VerifyError(f"{lean_path}:{ln}: `{word}` must be followed by a declaration identifier")
                if segs[0] == "_root_":
                    raise VerifyError(
                        f"{lean_path}:{ln}: forbidden `_root_`-qualified declaration `{'.'.join(segs)}`"
                    )
                if any_fq:
                    raise VerifyError(
                        f"{lean_path}:{ln}: forbidden French-quoted declaration name `{'.'.join(segs)}`"
                    )
                if not ns_stack:
                    raise VerifyError(
                        f"{lean_path}:{ln}: forbidden root-level `{word}` declaration outside whitelisted namespace "
                        f"(must lie inside `ShannonC7` or `ShannonC7.PartGadget`)"
                    )
                idx += 1
                continue

        else:
            if (
                kind == "IDENT"
                and not is_fq
                and word in allowed_col0
                and not _has_ident_dot_or_backtick_prev(tokens, idx)
            ):
                raise VerifyError(
                    f"{lean_path}:{ln}: top-level command/modifier `{word}` not allowed indented or chained "
                    f"(col={col}, depth={depth})"
                )

        idx += 1

    if ns_stack:
        raise VerifyError(f"{lean_path}: unclosed namespace scope(s) at EOF: {ns_stack}")


def _check_lean_lexical_whitelist(
    src: str,
    tokens: list[tuple[str, str, int, int, bool]],
    lean_path: pathlib.Path | str,
) -> None:
    r"""Enforce Mathematically Closed Lexical Whitelist inside `verify_lean_file` (O(N)).

    Runs unconditionally as Stage 7B (immediately after Stage 7A `_check_lean_positive_whitelist`
    and before Stage 8 big-int bounds — Pure Placement B, preserving 0% masking of Stage 2-7A
    defense-in-depth checks while strictly closing the entire lexical attack surface).

    Empirically verified 0 false positives across locked `ShannonC7/FrontierLower.lean`
    (`01507bbe...`), CRLF copies, and BOTH branches of locked `emit_frontier_lean.py`
    (`145c43b1...`: `PartGadgetDAG` & `Gamma6Pow4Pullback`, all 1,600 AST string constants):
      - Rule L1: ZERO ASCII control chars (<0x20 except LF / CRLF), ZERO tabs ('\t'), ZERO
        isolated CR ('\r' not followed by '\n'), ZERO DEL/C1 controls (0x7F..0x9F), ZERO
        non-ASCII whitespace, ZERO Unicode Cf/Cc/Cs/Zl/Zp/Zs chars, ZERO French guillemets («/»).
      - Rule L2: ZERO `STRING` tokens, ZERO `CHAR` tokens, ZERO `is_french_quoted` tokens,
        ZERO quote-containing `PUNCT` tokens (`''`, `]'`, `×'`, `⊕'`, `∘'`, `⁻¹'`, `Σ'`, etc.).
      - Rule L3: Independent raw-source O(N) closed scanner enforcing:
          * ZERO plain `/- ... -/` block comments,
          * ONLY strictly flat, col-0, depth-0, EOL-terminated `/-- ... -/` and `/-! ... -/`
            doc comments whose immediate opener char is ASCII space/LF/CR and whose body
            (including the `-` of closing `-/` to catch `/-- --/` & `/-- /-/`) contains ZERO
            `/-`, ZERO `--`, ZERO `"`, and ZERO `'`,
          * ZERO `"` outside plain `--` comments,
          * ZERO `'` outside Lean `IDENT` continuations (`_is_lean_id_start` + `_is_lean_id_rest`)
            and plain `--` comments,
          * ZERO comment-ambiguous `END_DASH`/`END_SLASH` sequences (`<--`, `\/-`, `//-`).
    """
    # Rule L1a: Forbidden ASCII control chars, tabs, & isolated CR
    m_ctrl = _FORBIDDEN_ASCII_CTRL_RE.search(src)
    if m_ctrl is not None:
        off = m_ctrl.start()
        ln = src.count("\n", 0, off) + 1
        ch = m_ctrl.group(0)
        raise VerifyError(
            f"{lean_path}:{ln}: forbidden ASCII control/tab/isolated-CR character U+{ord(ch):04X}"
        )

    # Rule L1b: Forbidden non-ASCII whitespace, C1 controls, Cf/Cc/Cs/Zl/Zp/Zs, & guillemets
    for ch in sorted(set(src), key=ord):
        oc = ord(ch)
        if oc < 128:
            continue
        if ch in ("«", "»"):
            ln = src.count("\n", 0, src.index(ch)) + 1
            raise VerifyError(f"{lean_path}:{ln}: forbidden French guillemet `{ch}`")
        if (
            ch.isspace()
            or (0x7F <= oc <= 0x9F)
            or unicodedata.category(ch) in ("Cf", "Cc", "Cs", "Zl", "Zp", "Zs")
        ):
            ln = src.count("\n", 0, src.index(ch)) + 1
            raise VerifyError(
                f"{lean_path}:{ln}: forbidden non-ASCII whitespace/control/format character U+{oc:04X}"
            )

    # Rule L2: Token-level closed lexical whitelist (incl. R16 pure-decimal NUMBER & R17 PUNCT_END_ID)
    line_starts = _build_line_starts(src)
    n_lines = len(line_starts)
    n_toks = len(tokens)
    n_src = len(src)
    forb_punct_end_id = _FORBIDDEN_PUNCT_END_ID_TOKENS
    cur_li = 0
    for tok_idx, (kind, word, ts, te, is_fq) in enumerate(tokens):
        while cur_li + 1 < n_lines and line_starts[cur_li + 1] <= ts:
            cur_li += 1
        ln = cur_li + 1
        if is_fq:
            raise VerifyError(f"{lean_path}:{ln}: forbidden French-quoted identifier `«{word}»`")
        if kind == "STRING":
            raise VerifyError(
                f"{lean_path}:{ln}: forbidden double-quoted string literal in frontier certificate"
            )
        if kind == "CHAR":
            raise VerifyError(f"{lean_path}:{ln}: forbidden Char literal in frontier certificate")
        if kind == "NUMBER":
            if not (word.isascii() and word.isdigit()):
                raise VerifyError(
                    f"{lean_path}:{ln}: forbidden non-decimal/scientific/underscored numeric literal `{word}`"
                )
            if (
                tok_idx + 1 < n_toks
                and tokens[tok_idx + 1][0] == "IDENT"
                and te == tokens[tok_idx + 1][2]
            ):
                raise VerifyError(
                    f"{lean_path}:{ln}: forbidden numeric literal `{word}` contiguously followed by identifier "
                    f"`{tokens[tok_idx + 1][1]}`"
                )
        if kind == "PUNCT":
            if "'" in word:
                raise VerifyError(
                    f"{lean_path}:{ln}: forbidden non-identifier quote punctuation `{word}`"
                )
            if word in forb_punct_end_id:
                raise VerifyError(
                    f"{lean_path}:{ln}: forbidden TokenTable ident-suffix punctuation `{word}`"
                )
            if word == "≃g" and te < n_src and src[te] not in (" ", "\n", "\r"):
                raise VerifyError(
                    f"{lean_path}:{ln}: `≃g` must be immediately followed by ASCII whitespace"
                )

    # Rule L3: Independent raw-source O(N) closed scanner (decoupled from complex string/char lexer)
    n = len(src)
    pos = 0
    cur_depth = 0
    cur_li = 0
    open_d = _OPEN_DELIMS
    close_d = _CLOSE_DELIMS
    ascii_id_match = _ASCII_IDENT_RE.match
    uni_id_match = _LEAN_IDENT_RE.match

    def line_of(p: int) -> int:
        nonlocal cur_li
        while cur_li + 1 < n_lines and line_starts[cur_li + 1] <= p:
            cur_li += 1
        return cur_li + 1

    while pos < n:
        ch = src[pos]
        oc = ord(ch)
        if ch == " " or ch == "\n" or ch == "\r":
            pos += 1
            continue
        # Consume full Lean v4.32.2 identifiers: identifier-continuation `'` is permitted ONLY here!
        if (97 <= oc <= 122) or (65 <= oc <= 90) or oc == 95:
            end_i = ascii_id_match(src, pos).end()
            if end_i < n and ord(src[end_i]) >= 128:
                end_i = uni_id_match(src, pos).end()
            pos = end_i
            continue
        if oc >= 128:
            mu = uni_id_match(src, pos)
            if mu is not None:
                pos = mu.end()
                continue
        # Lean v4.32.2 END_DASH (`<-`) & END_SLASH (`\/`, `//`) collision guards (R15)
        if ch == "<":
            if pos + 2 < n and src[pos : pos + 3] == "<--":
                raise VerifyError(
                    f"{lean_path}:{line_of(pos)}: forbidden comment-ambiguous `<--` sequence"
                )
            if pos + 2 < n and src[pos : pos + 3] in ("<<<", "<=<"):
                pos += 3
                continue
            if pos + 1 < n and src[pos + 1] == "-":
                pos += 2
                continue
            pos += 1
            continue
        if ch == "\\":
            if pos + 2 < n and src[pos : pos + 3] == "\\/-":
                raise VerifyError(
                    f"{lean_path}:{line_of(pos)}: forbidden comment-ambiguous `\\/-` sequence"
                )
            if pos + 1 < n and src[pos + 1] == "/":
                pos += 2
                continue
            pos += 1
            continue
        if ch == "/":
            if pos + 2 < n and src[pos : pos + 3] == "//-":
                raise VerifyError(
                    f"{lean_path}:{line_of(pos)}: forbidden comment-ambiguous `//-` sequence"
                )
            if pos + 1 < n and src[pos + 1] == "/":
                pos += 2
                continue
            if pos + 1 < n and src[pos + 1] == "-":
                ln = line_of(pos)
                col = pos - line_starts[cur_li]
                if pos + 2 >= n or src[pos + 2] not in ("-", "!"):
                    raise VerifyError(
                        f"{lean_path}:{ln}: forbidden plain block comment `/- ... -/` "
                        f"(only flat col-0 `/--` and `/-!` doc comments permitted)"
                    )
                opener = src[pos : pos + 3]
                if col != 0 or cur_depth != 0:
                    raise VerifyError(
                        f"{lean_path}:{ln}: doc comment `{opener}` only permitted at column 0 depth 0 "
                        f"(got col={col}, depth={cur_depth})"
                    )
                if pos + 3 >= n or src[pos + 3] not in (" ", "\n", "\r"):
                    raise VerifyError(
                        f"{lean_path}:{ln}: doc comment `{opener}` must be immediately followed "
                        f"by ASCII space or newline"
                    )
                close_pos = src.find("-/", pos + 3)
                if close_pos == -1:
                    raise VerifyError(f"{lean_path}:{ln}: unclosed doc comment `{opener}` at EOF")
                body = src[pos + 3 : close_pos]
                body_ext = src[pos + 3 : close_pos + 1]
                if "/-" in body_ext:
                    raise VerifyError(
                        f"{lean_path}:{ln}: forbidden nested `/-` inside doc comment `{opener}`"
                    )
                if "--" in body_ext:
                    raise VerifyError(
                        f"{lean_path}:{ln}: forbidden `--` inside doc comment `{opener}`"
                    )
                if '"' in body:
                    raise VerifyError(
                        f"{lean_path}:{ln}: forbidden `\"` inside doc comment `{opener}`"
                    )
                if "'" in body:
                    raise VerifyError(
                        f"{lean_path}:{ln}: forbidden `'` inside doc comment `{opener}`"
                    )
                after = close_pos + 2
                while after < n and src[after] == " ":
                    after += 1
                if after < n and src[after] not in ("\n", "\r"):
                    end_ln = src.count("\n", 0, close_pos) + 1
                    raise VerifyError(
                        f"{lean_path}:{end_ln}: unexpected trailing token on same line after doc comment `-/`"
                    )
                pos = close_pos + 2
                continue
            pos += 1
            continue
        if ch == "-" and pos + 1 < n and src[pos + 1] == "-":
            nl = src.find("\n", pos + 2)
            pos = n if nl == -1 else nl + 1
            continue
        if ch == '"':
            raise VerifyError(
                f"{lean_path}:{line_of(pos)}: forbidden double quote `\"` outside `--` comment"
            )
        if ch == "'":
            raise VerifyError(
                f"{lean_path}:{line_of(pos)}: forbidden non-identifier single quote `'` outside `--` comment"
            )
        if ch in open_d:
            cur_depth += 1
        elif ch in close_d:
            cur_depth -= 1
        pos += 1


# Pre-compiled module-level Lean 4 declaration & extraction regexes (compiled once at import time).
_ALL_DECLS_RE = re.compile(
    rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})({_DECL_MOD_PREFIX})({_DECL_INTRO_KW})"
    rf"(?:(?<=instance)\s*\((?:[^()]|\([^()]*\))*\))?\s+"
    rf"({_QUAL_PREFIX})([{_LEAN_ID_START_CHARS}][{_LEAN_ID_REST_CHARS}]*)(?!{_LEAN_ID_REST_CLS})"
)
_ALIAS_LR_RE = re.compile(
    rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})({_DECL_MOD_PREFIX})(alias)\s*⟨\s*"
    rf"({_QUAL_PREFIX})([{_LEAN_ID_START_CHARS}][{_LEAN_ID_REST_CHARS}]*|_)\s*,\s*"
    rf"({_QUAL_PREFIX})([{_LEAN_ID_START_CHARS}][{_LEAN_ID_REST_CHARS}]*|_)\s*⟩"
)
_DECL_PAT_CACHE: dict[str, re.Pattern[str]] = {}
_IDENT_RE_CACHE: dict[str, re.Pattern[str]] = {}

_RE_BASE_PROFILE = re.compile(
    rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})def\s+frontierBaseProfile\s*:\s*AsymProfile\s*:=\s*\{{([^}}]*)\}}\s*{_LEAN_BODY_END}",
    re.S,
)
_RE_BASE_FIELDS = {
    field: re.compile(rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS}){field}\s*:=\s*([^,\n}}]+)")
    for field in ("a", "b", "c", "d", "h", "v")
}
_RE_BASE_PART5D = re.compile(
    rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})(?:noncomputable\s+)?def\s+basePart5D\s*:\s*"
    rf"PartGadget\s*\(\s*strongPow\s+C7\s+([0-9]+)\s*\)\s*:=\s*"
    rf"PartGadget\.ofHeteroGadget\s+baseHetero5D\s*{_LEAN_BODY_END}",
    re.S,
)
_RE_BASE_PART5D_EQ = re.compile(
    rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})theorem\s+basePart5D_asymProfile_eq\s*:\s*"
    rf"basePart5D\.asymProfile\s*=\s*frontierBaseProfile\s*:=",
    re.S,
)
_RE_FRONTIER_PROF = re.compile(
    rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})def\s+frontierProf([0-9]+)\s*:\s*AsymProfile\s*:=\s*(.*?){_LEAN_BODY_END}",
    re.S,
)
_RE_FRONTIER_PROF_FLIP = re.compile(r"frontierProf([0-9]+)\.flip")
_RE_FRONTIER_PROF_BIN = re.compile(
    r"frontierProf([0-9]+)\.(prodAligned|prodXupg1|prodXupg2)\s+frontierProf([0-9]+)"
)
_RE_FRONTIER_NODE = re.compile(
    rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})(?:noncomputable\s+)?def\s+frontierNode([0-9]+)\s*:\s*"
    rf"PartGadget\s*\(\s*strongPow\s+C7\s+([0-9]+)\s*\)\s*:=\s*(.*?){_LEAN_BODY_END}",
    re.S,
)
_RE_FRONTIER_NODE_BIN = re.compile(
    r"\(\s*frontierNode([0-9]+)\.(prodStd|prodXupg1|prodXupg2)\s+frontierNode([0-9]+)\s*\)"
    r"\.mapIso\s*\(\s*strongPowAddEquiv\s+C7\s+([0-9]+)\s+([0-9]+)\s*\)\.symm"
)
_RE_FRONTIER_NODE_PROFILE = re.compile(
    rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})theorem\s+frontierNode([0-9]+)_profile\s*:\s*"
    rf"frontierNode([0-9]+)\.asymProfile\s*=\s*frontierProf([0-9]+)\s*:=",
    re.S,
)
_RE_NAT_DEFS = {
    nm: re.compile(
        rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})def\s+{nm}\s*:\s*(?:ℕ|Nat)\s*:=\s*(.*?){_LEAN_BODY_END}",
        re.S,
    )
    for nm in ("c7_lower_num", "c7_lower_den", "frontierCard")
}
_RE_G6_TERMS = re.compile(
    rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})def\s+frontierGamma6Terms\s*:\s*List\s+Gamma6Quad\s*:=\s*"
    rf"\[([^\[\]]*)\]\s*{_LEAN_BODY_END}",
    re.S,
)
_RE_G6_TUPLE = re.compile(r"\(\s*([0-9]+)\s*,\s*([0-9]+)\s*,\s*([0-9]+)\s*,\s*([0-9]+)\s*\)")
_RE_TARGET_A_EQ = re.compile(
    rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})theorem\s+frontierTarget_a_eq\s*:\s*"
    rf"frontierProf([0-9]+)\.a\s*=\s*frontierCard\s*:=",
    re.S,
)
_RE_FACTOR_PROF = re.compile(
    rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})def\s+frontierFactorProf([0-9]+)\s*:\s*AsymProfile\s*:=\s*"
    rf"frontierProf([0-9]+)(\.flip)?\s*{_LEAN_BODY_END}",
    re.S,
)
_RE_FACTOR_NODE = re.compile(
    rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})(?:noncomputable\s+)?def\s+frontierFactor([0-9]+)\s*:\s*"
    rf"PartGadget\s*\(\s*strongPow\s+C7\s+([0-9]+)\s*\)\s*:=\s*(.*?){_LEAN_BODY_END}",
    re.S,
)
_RE_FACTOR_PROFILE = re.compile(
    rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})theorem\s+frontierFactor([0-9]+)_profile\s*:\s*"
    rf"frontierFactor([0-9]+)\.asymProfile\s*=\s*frontierFactorProf([0-9]+)\s*:=(.*?){_LEAN_BODY_END}",
    re.S,
)
_RE_G6_INDEP = re.compile(
    rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})theorem\s+frontierGamma6Terms_indep\s*:\s*"
    rf"gamma6QuadListIndepBool\s+frontierGamma6Terms\s*=\s*true\s*:=",
    re.S,
)
_RE_G6_WEIGHT = re.compile(
    rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})theorem\s+frontierGamma6Terms_weight_eq\s*:\s*"
    rf"gamma6QuadListWeight\s+frontierFactorProf0\s+frontierFactorProf1\s+"
    rf"frontierFactorProf2\s+frontierFactorProf3\s+frontierGamma6Terms\s*=\s*frontierCard\s*:=",
    re.S,
)
_RE_CARD_LE_INDEP = re.compile(
    rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})theorem\s+frontierCard_le_indepNum\s*:\s*"
    rf"frontierCard\s*(?:≤|<=)\s*\(\s*strongPowPi\s*\(\s*SimpleGraph\.cycleGraph\s+7\s*\)\s*([0-9]+)\s*\)\.indepNum\s*:="
    rf"(.*?){_LEAN_BODY_END}",
    re.S,
)
_RE_POW_LE = re.compile(
    rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})theorem\s+frontier_pow_le\s*:\s*"
    rf"c7_lower_num\s*\^\s*([0-9]+)\s*(?:≤|<=)\s*c7_lower_den\s*\^\s*([0-9]+)\s*\*\s*frontierCard\s*:=",
    re.S,
)
_RE_DEN_POS = re.compile(
    rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})theorem\s+c7_lower_den_pos\s*:\s*0\s*<\s*c7_lower_den\s*:=",
    re.S,
)
_RE_FRONTIER_THM = re.compile(
    rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})theorem\s+c7_lower_frontier\s*:\s*"
    rf"\(\s*c7_lower_num\s*:\s*ℝ\s*\)\s*/\s*\(\s*c7_lower_den\s*:\s*ℝ\s*\)\s*(?:≤|<=)\s*"
    rf"shannonCapacity\s*\(\s*SimpleGraph\.cycleGraph\s+7\s*\)\s*:=(.*?){_LEAN_BODY_END}",
    re.S,
)
_RE_OPT_COMP_THMS = {
    "c7_lower_gt_bpz_v1": re.compile(
        rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})theorem\s+c7_lower_gt_bpz_v1\s*:\s*"
        rf"\(\s*3258805369885465\s*:\s*ℝ\s*\)\s*/\s*1000000000000000\s*<\s*"
        rf"\(\s*c7_lower_num\s*:\s*ℝ\s*\)\s*/\s*\(\s*c7_lower_den\s*:\s*ℝ\s*\)\s*:=",
        re.S,
    ),
    "c7_lower_gt_bpz_v2": re.compile(
        rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})theorem\s+c7_lower_gt_bpz_v2\s*:\s*"
        rf"\(\s*3258827985920007\s*:\s*ℝ\s*\)\s*/\s*1000000000000000\s*<\s*"
        rf"\(\s*c7_lower_num\s*:\s*ℝ\s*\)\s*/\s*\(\s*c7_lower_den\s*:\s*ℝ\s*\)\s*:=",
        re.S,
    ),
    "c7_lower_gt_tandon": re.compile(
        rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})theorem\s+c7_lower_gt_tandon\s*:\s*"
        rf"\(\s*3258832620353\s*:\s*ℝ\s*\)\s*/\s*1000000000000\s*<\s*"
        rf"\(\s*c7_lower_num\s*:\s*ℝ\s*\)\s*/\s*\(\s*c7_lower_den\s*:\s*ℝ\s*\)\s*:=",
        re.S,
    ),
}


def _index_all_decls(clean: str) -> dict[str, list[tuple[str, str, str, str]]]:
    """Single-pass O(N) index of every Lean 4 declaration in `clean` keyed by leaf identifier."""
    by_leaf: dict[str, list[tuple[str, str, str, str]]] = {}
    for m in _ALL_DECLS_RE.finditer(clean):
        leaf = m.group(4)
        entry = (m.group(1), m.group(2), m.group(3), leaf)
        if leaf in by_leaf:
            by_leaf[leaf].append(entry)
        else:
            by_leaf[leaf] = [entry]
    if "alias" in clean:
        for m in _ALIAS_LR_RE.finditer(clean):
            mods, kw = m.group(1), m.group(2)
            for qual, leaf in ((m.group(3), m.group(4)), (m.group(5), m.group(6))):
                if leaf == "_":
                    continue
                entry = (mods, kw, qual, leaf)
                if leaf in by_leaf:
                    by_leaf[leaf].append(entry)
                else:
                    by_leaf[leaf] = [entry]
    return by_leaf


def _find_decl_matches(
    clean: str,
    name_pat: str,
    decl_index: dict[str, list[tuple[str, str, str, str]]] | None = None,
) -> list[tuple[str, str, str, str]]:
    """Return all `(mods, kw, qual, leaf_name)` declarations matching `name_pat` in live Lean code."""
    if decl_index is not None:
        if name_pat in decl_index:
            return decl_index[name_pat]
        leaf_re = _DECL_PAT_CACHE.get(name_pat)
        if leaf_re is None:
            leaf_re = re.compile(rf"^(?:{name_pat})$")
            _DECL_PAT_CACHE[name_pat] = leaf_re
        out: list[tuple[str, str, str, str]] = []
        for leaf, entries in decl_index.items():
            if leaf_re.match(leaf):
                out.extend(entries)
        return out
    pat = _DECL_PAT_CACHE.get(f"FULL:{name_pat}")
    if pat is None:
        pat = re.compile(
            rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS})({_DECL_MOD_PREFIX})({_DECL_INTRO_KW})"
            rf"(?:(?<=instance)\s*\((?:[^()]|\([^()]*\))*\))?\s+"
            rf"({_QUAL_PREFIX})({name_pat})(?!{_LEAN_ID_REST_CLS})"
        )
        _DECL_PAT_CACHE[f"FULL:{name_pat}"] = pat
    return [(m.group(1), m.group(2), m.group(3), m.group(4)) for m in pat.finditer(clean)]


def _assert_unique_decl(
    clean: str,
    name: str,
    *,
    expected_kw: str,
    allow_noncomputable: bool,
    lean_path: pathlib.Path | str,
    decl_index: dict[str, list[tuple[str, str, str, str]]] | None = None,
) -> None:
    """Enforce that `name` has exactly 1 unqualified public declaration with exact keyword/computability."""
    matches = decl_index.get(name, []) if decl_index is not None else _find_decl_matches(clean, re.escape(name))
    if len(matches) == 0:
        raise VerifyError(f"{lean_path}: missing `{expected_kw} {name}`")
    if len(matches) > 1:
        raise VerifyError(f"{lean_path}: duplicate/shadowed declaration of `{name}` ({len(matches)} found)")
    mods, kw, qual, _ = matches[0]
    if qual:
        raise VerifyError(f"{lean_path}: qualified/shadowed declaration `{qual.strip()}{name}` not allowed")
    if kw != expected_kw:
        raise VerifyError(f"{lean_path}: `{name}` must be `{expected_kw}`, found `{kw}`")
    mod_tokens = set(mods.split())
    if mod_tokens & _FORBIDDEN_CERT_MODS:
        raise VerifyError(f"{lean_path}: forbidden declaration modifier(s) `{mods.strip()}` on `{name}`")
    if not allow_noncomputable and "noncomputable" in mod_tokens:
        raise VerifyError(f"{lean_path}: `{name}` must not be `noncomputable`")


def _validate_indexed_decls(
    clean: str,
    prefix: str,
    suffix: str,
    *,
    expected_kw: str,
    allow_noncomputable: bool,
    lean_path: pathlib.Path | str,
    decl_index: dict[str, list[tuple[str, str, str, str]]] | None = None,
) -> set[int]:
    """Validate all declarations matching `<prefix><nat><suffix>` are unique, public, unqualified, canonical."""
    p_len = len(prefix)
    s_len = len(suffix)
    if decl_index is not None:
        matches: list[tuple[str, str, str, str]] = []
        for leaf, entries in decl_index.items():
            if leaf.startswith(prefix) and (not s_len or leaf.endswith(suffix)):
                mid = leaf[p_len : len(leaf) - s_len if s_len else len(leaf)]
                if mid and mid.isascii() and mid.isdigit():
                    matches.extend(entries)
    else:
        matches = _find_decl_matches(clean, rf"{re.escape(prefix)}[0-9]+{re.escape(suffix)}")
    seen: set[int] = set()
    for mods, kw, qual, leaf in matches:
        raw_idx = leaf[p_len : len(leaf) - s_len if s_len else len(leaf)]
        idx = _parse_ascii_nat(raw_idx, f"{lean_path}: {leaf} index")
        if raw_idx != str(idx):
            raise VerifyError(f"{lean_path}: non-canonical leading-zero index in `{leaf}`")
        if qual:
            raise VerifyError(f"{lean_path}: qualified/shadowed declaration `{qual.strip()}{leaf}` not allowed")
        if kw != expected_kw:
            raise VerifyError(f"{lean_path}: `{leaf}` must be `{expected_kw}`, found `{kw}`")
        mod_tokens = set(mods.split())
        if mod_tokens & _FORBIDDEN_CERT_MODS:
            raise VerifyError(f"{lean_path}: forbidden declaration modifier(s) `{mods.strip()}` on `{leaf}`")
        if not allow_noncomputable and "noncomputable" in mod_tokens:
            raise VerifyError(f"{lean_path}: `{leaf}` must not be `noncomputable`")
        if idx in seen:
            raise VerifyError(f"{lean_path}: duplicate/shadowed declaration of `{leaf}`")
        seen.add(idx)
    return seen


def _assert_absent_decl(
    clean: str,
    name_pat: str,
    label: str,
    lean_path: pathlib.Path | str,
    decl_index: dict[str, list[tuple[str, str, str, str]]] | None = None,
) -> None:
    """Reject stray/cross-branch declarations matching `name_pat`."""
    matches = _find_decl_matches(clean, name_pat, decl_index=decl_index)
    if matches:
        raise VerifyError(f"{lean_path}: unexpected `{label}` declaration(s) ({len(matches)} found)")


def _read_dotted_ident(
    tokens: list[tuple[str, str, int, int, bool]], idx: int
) -> tuple[list[str], int]:
    """Read a contiguous dotted Lean 4 identifier starting at `tokens[idx]`."""
    n_tok = len(tokens)
    if idx >= n_tok or tokens[idx][0] != "IDENT":
        return [], idx
    segs = [tokens[idx][1]]
    cur = idx + 1
    while (
        cur + 1 < n_tok
        and tokens[cur][0] == "PUNCT"
        and tokens[cur][1] == "."
        and tokens[cur][2] == tokens[cur - 1][3]
        and tokens[cur + 1][0] == "IDENT"
        and tokens[cur + 1][2] == tokens[cur][3]
    ):
        segs.append(tokens[cur + 1][1])
        cur += 2
    return segs, cur


def _check_lean_decl_scopes(
    src: str,
    tokens: list[tuple[str, str, int, int, bool]],
    cert_decl_names: set[str],
    computable_decl_names: set[str],
    lean_path: pathlib.Path | str,
) -> None:
    """Single-pass O(N) lexical `namespace`/`section`/`mutual`/`variable`/`end` scope tracker.

    Verifies that every audited certificate declaration in `cert_decl_names` is declared:
      1. Unqualified at exact effective namespace stack `["ShannonC7"]`,
      2. With ZERO active `variable` declarations in any enclosing frame or at top level,
      3. Outside any `mutual` block and outside any `meta section`, and
      4. Outside any `noncomputable section` when the declaration is in `computable_decl_names`.
    """
    n_tok = len(tokens)
    stack: list[dict[str, object]] = []
    top_level_var = False
    checked_cert_decls: set[str] = set()
    decl_intro_kws = _DECL_INTRO_KW_SET
    non_name_kws = _LEAN_SCOPE_NON_NAME_KWS

    def col_of(byte_pos: int) -> int:
        nl = src.rfind("\n", 0, byte_pos)
        return byte_pos if nl == -1 else byte_pos - nl - 1

    def has_scope_name_arg(kw_idx: int, kw_start: int, kw_end: int) -> bool:
        nxt_idx = kw_idx + 1
        if nxt_idx >= n_tok:
            return False
        nxt_kind, nxt_word, nxt_start, _, nxt_fq = tokens[nxt_idx]
        if nxt_kind != "IDENT":
            return False
        if not nxt_fq and nxt_word in non_name_kws:
            return False
        gap = src[kw_end:nxt_start]
        if "\n" not in gap:
            return True
        return col_of(nxt_start) > col_of(kw_start)

    idx = 0
    while idx < n_tok:
        kind, word, t_start, t_end, is_fq = tokens[idx]
        if kind != "IDENT" or is_fq:
            idx += 1
            continue
        if _has_ident_dot_or_backtick_prev(tokens, idx):
            idx += 1
            continue

        if word == "namespace":
            segs, next_idx = _read_dotted_ident(tokens, idx + 1)
            if not segs:
                raise VerifyError(f"{lean_path}: malformed `namespace` command")
            for seg in segs:
                stack.append({"kind": "namespace", "name": seg, "has_var": False, "noncomp": False, "meta": False})
            idx = next_idx
            continue

        if word == "section":
            sec_mods: set[str] = set()
            j = idx - 1
            while (
                j >= 0
                and tokens[j][0] == "IDENT"
                and not tokens[j][4]
                and tokens[j][1] in ("public", "noncomputable", "meta")
            ):
                sec_mods.add(tokens[j][1])
                j -= 1
            is_noncomp = "noncomputable" in sec_mods
            is_meta = "meta" in sec_mods
            if has_scope_name_arg(idx, t_start, t_end):
                segs, next_idx = _read_dotted_ident(tokens, idx + 1)
                for seg in segs:
                    stack.append(
                        {"kind": "section", "name": seg, "has_var": False, "noncomp": is_noncomp, "meta": is_meta}
                    )
                idx = next_idx
            else:
                stack.append(
                    {"kind": "section", "name": None, "has_var": False, "noncomp": is_noncomp, "meta": is_meta}
                )
                idx += 1
            continue

        if word == "mutual":
            stack.append({"kind": "mutual", "name": None, "has_var": False, "noncomp": False, "meta": False})
            idx += 1
            continue

        if word == "variable":
            if stack:
                stack[-1]["has_var"] = True
            else:
                top_level_var = True
            idx += 1
            continue

        if word == "end":
            if has_scope_name_arg(idx, t_start, t_end):
                segs, next_idx = _read_dotted_ident(tokens, idx + 1)
                if len(stack) < len(segs) or [f["name"] for f in stack[-len(segs) :]] != segs:
                    raise VerifyError(
                        f"{lean_path}: mismatched `end {'.'.join(segs)}` for open scope stack "
                        f"{[f['name'] for f in stack]}"
                    )
                del stack[-len(segs) :]
                idx = next_idx
            else:
                if not stack or stack[-1]["name"] is not None:
                    raise VerifyError(
                        f"{lean_path}: anonymous `end` cannot close open scope stack "
                        f"{[f['name'] for f in stack]}"
                    )
                stack.pop()
                idx += 1
            continue

        if word in decl_intro_kws:
            name_idx = idx + 1
            if (
                word == "class"
                and name_idx < n_tok
                and tokens[name_idx][0] == "IDENT"
                and not tokens[name_idx][4]
                and tokens[name_idx][1] in ("inductive", "abbrev")
            ):
                name_idx += 1
            if (
                word == "instance"
                and name_idx < n_tok
                and tokens[name_idx][0] == "PUNCT"
                and tokens[name_idx][1] == "("
            ):
                depth = 1
                name_idx += 1
                while name_idx < n_tok and depth > 0:
                    if tokens[name_idx][0] == "PUNCT":
                        if tokens[name_idx][1] == "(":
                            depth += 1
                        elif tokens[name_idx][1] == ")":
                            depth -= 1
                    name_idx += 1
            declared_segs_list: list[list[str]] = []
            if (
                word == "alias"
                and name_idx < n_tok
                and tokens[name_idx][0] == "PUNCT"
                and tokens[name_idx][1] == "⟨"
            ):
                cur = name_idx + 1
                while cur < n_tok and not (tokens[cur][0] == "PUNCT" and tokens[cur][1] == "⟩"):
                    if tokens[cur][0] == "IDENT":
                        segs_a, cur = _read_dotted_ident(tokens, cur)
                        if segs_a and segs_a != ["_"]:
                            declared_segs_list.append(segs_a)
                    else:
                        cur += 1
            else:
                segs_d, _ = _read_dotted_ident(tokens, name_idx)
                if segs_d:
                    declared_segs_list.append(segs_d)

            for segs_d in declared_segs_list:
                leaf = segs_d[-1]
                if leaf in cert_decl_names:
                    if len(segs_d) > 1:
                        raise VerifyError(
                            f"{lean_path}: qualified certificate declaration `{'.'.join(segs_d)}` not allowed"
                        )
                    ns_path = [f["name"] for f in stack if f["kind"] == "namespace"]
                    if ns_path != ["ShannonC7"]:
                        ns_str = ".".join(str(x) for x in ns_path) if ns_path else "<root>"
                        raise VerifyError(
                            f"{lean_path}: `{leaf}` declared in namespace `{ns_str}` (must be `ShannonC7`)"
                        )
                    if top_level_var or any(bool(f["has_var"]) for f in stack):
                        raise VerifyError(
                            f"{lean_path}: active `variable` declaration in scope at `{leaf}`"
                        )
                    if any(f["kind"] == "mutual" for f in stack):
                        raise VerifyError(f"{lean_path}: `{leaf}` must not be declared inside `mutual` block")
                    if any(bool(f["meta"]) for f in stack):
                        raise VerifyError(f"{lean_path}: `{leaf}` must not be declared inside `meta section`")
                    if leaf in computable_decl_names and any(bool(f["noncomp"]) for f in stack):
                        raise VerifyError(
                            f"{lean_path}: computable `{leaf}` must not be declared inside `noncomputable section`"
                        )
                    checked_cert_decls.add(leaf)

        idx += 1

    missing_scoped = sorted(cert_decl_names - checked_cert_decls)
    if missing_scoped:
        raise VerifyError(f"{lean_path}: scope tracker did not verify certificate declaration(s): {missing_scoped}")


def _has_lean_ident(text: str, ident: str) -> bool:
    """Check whether unqualified `ident` occurs as a standalone Lean 4 identifier in `text`."""
    pat = _IDENT_RE_CACHE.get(ident)
    if pat is None:
        pat = re.compile(rf"(?<!{_LEAN_ID_REST_AND_DOT_CLS}){re.escape(ident)}(?!{_LEAN_ID_REST_CLS})")
        _IDENT_RE_CACHE[ident] = pat
    return pat.search(text) is not None


def _parse_lean_base_profile(
    clean: str,
    lean_path: pathlib.Path,
    decl_index: dict[str, list[tuple[str, str, str, str]]] | None = None,
) -> tuple[int, int, int, int, int, int]:
    """Parse unique `def frontierBaseProfile : AsymProfile := { ... }` directly from live Lean code."""
    _assert_unique_decl(
        clean,
        "frontierBaseProfile",
        expected_kw="def",
        allow_noncomputable=False,
        lean_path=lean_path,
        decl_index=decl_index,
    )
    matches = _RE_BASE_PROFILE.findall(clean)
    if len(matches) != 1:
        raise VerifyError(f"{lean_path}: malformed `def frontierBaseProfile : AsymProfile := {{...}}`")
    body = matches[0]
    vals: list[int] = []
    for field in ("a", "b", "c", "d", "h", "v"):
        f_matches = _RE_BASE_FIELDS[field].findall(body)
        if len(f_matches) != 1:
            raise VerifyError(f"{lean_path}: frontierBaseProfile missing or duplicate field `{field}`")
        raw_v = f_matches[0].strip()
        vals.append(_parse_ascii_nat(raw_v, f"{lean_path}: frontierBaseProfile.{field}"))
    a, b, c, d, h, v = vals
    if a <= 0 or b > a or d + h + v != c:
        raise VerifyError(f"{lean_path}: frontierBaseProfile invariant violated: {(a, b, c, d, h, v)}")

    # Verify unique `basePart5D` binding to `baseHetero5D` and unique profile equality theorem
    _assert_unique_decl(
        clean,
        "basePart5D",
        expected_kw="def",
        allow_noncomputable=True,
        lean_path=lean_path,
        decl_index=decl_index,
    )
    bp_match = _RE_BASE_PART5D.findall(clean)
    if (
        len(bp_match) != 1
        or _parse_ascii_nat(bp_match[0], f"{lean_path}: basePart5D dim") != LOCKED_BASE_PART5D_DIM
    ):
        raise VerifyError(
            f"{lean_path}: `basePart5D` must bind uniquely to `PartGadget.ofHeteroGadget baseHetero5D` at dim 5"
        )
    _assert_unique_decl(
        clean,
        "basePart5D_asymProfile_eq",
        expected_kw="theorem",
        allow_noncomputable=False,
        lean_path=lean_path,
        decl_index=decl_index,
    )
    bp_eq = _RE_BASE_PART5D_EQ.findall(clean)
    if len(bp_eq) != 1:
        raise VerifyError(f"{lean_path}: expected unique `theorem basePart5D_asymProfile_eq`")

    prof = (a, b, c, d, h, v)
    if prof != LOCKED_BASE_PART5D_PROFILE:
        raise VerifyError(
            f"{lean_path}: frontierBaseProfile={prof} != locked basePart5D/baseHetero5D profile {LOCKED_BASE_PART5D_PROFILE}"
        )
    return prof


def _parse_lean_dag_ops(
    clean: str,
    lean_path: pathlib.Path | str = "<lean>",
    decl_index: dict[str, list[tuple[str, str, str, str]]] | None = None,
) -> list[dict]:
    """Independently parse unique `def frontierProf<idx> : AsymProfile := ...` DAG definitions from Lean."""
    seen_decl_ids = _validate_indexed_decls(
        clean,
        "frontierProf",
        "",
        expected_kw="def",
        allow_noncomputable=False,
        lean_path=lean_path,
        decl_index=decl_index,
    )

    if len(seen_decl_ids) > MAX_DAG_OPS:
        raise VerifyError(
            f"{lean_path}: frontierProf DAG op count {len(seen_decl_ids)} exceeds MAX_DAG_OPS ({MAX_DAG_OPS})"
        )

    found: dict[int, dict] = {}
    for m in _RE_FRONTIER_PROF.finditer(clean):
        if len(found) >= MAX_DAG_OPS:
            raise VerifyError(f"{lean_path}: frontierProf DAG op count exceeds MAX_DAG_OPS ({MAX_DAG_OPS})")
        raw_idx = m.group(1)
        idx = _parse_ascii_nat(raw_idx, f"{lean_path}: frontierProf index")
        if raw_idx != str(idx):
            raise VerifyError(f"{lean_path}: non-canonical leading-zero index frontierProf{raw_idx}")
        if idx in found:
            raise VerifyError(f"{lean_path}: duplicate definition of frontierProf{idx}")
        rhs = " ".join(m.group(2).split())
        if rhs == "frontierBaseProfile":
            found[idx] = {"op": "base", "idx": 0}
        elif (mf := _RE_FRONTIER_PROF_FLIP.fullmatch(rhs)):
            ri = _parse_ascii_nat(mf.group(1), f"{lean_path}: frontierProf{idx} flip ref")
            if mf.group(1) != str(ri):
                raise VerifyError(f"{lean_path}: non-canonical ref frontierProf{mf.group(1)} in frontierProf{idx}")
            found[idx] = {"op": "flip", "i": ri}
        elif (mp := _RE_FRONTIER_PROF_BIN.fullmatch(rhs)):
            op_name = "prodStd" if mp.group(2) == "prodAligned" else mp.group(2)
            ri = _parse_ascii_nat(mp.group(1), f"{lean_path}: frontierProf{idx} lhs ref")
            rj = _parse_ascii_nat(mp.group(3), f"{lean_path}: frontierProf{idx} rhs ref")
            if mp.group(1) != str(ri) or mp.group(3) != str(rj):
                raise VerifyError(f"{lean_path}: non-canonical ref in frontierProf{idx}")
            found[idx] = {"op": op_name, "i": ri, "j": rj}
        else:
            raise VerifyError(f"{lean_path}: unrecognized frontierProf{idx} RHS: {rhs!r}")
    if len(found) != len(seen_decl_ids):
        missing = sorted(seen_decl_ids - set(found.keys()))
        raise VerifyError(f"{lean_path}: malformed frontierProf declaration(s): {missing}")
    if not found:
        return []
    expected_keys = list(range(len(found)))
    if sorted(found.keys()) != expected_keys:
        raise VerifyError(f"{lean_path}: non-contiguous frontierProf indices: {sorted(found.keys())}")
    return [found[k] for k in expected_keys]


def _verify_lean_dag_nodes(
    clean: str,
    dag_ops: list[dict],
    base_dim: int,
    lean_path: pathlib.Path,
    decl_index: dict[str, list[tuple[str, str, str, str]]] | None = None,
) -> list[int]:
    """Cross-check every `frontierNode<k>` (operator, operands, strongPow dim) and `frontierNode<k>_profile`."""
    seen_node_ids = _validate_indexed_decls(
        clean,
        "frontierNode",
        "",
        expected_kw="def",
        allow_noncomputable=True,
        lean_path=lean_path,
        decl_index=decl_index,
    )
    seen_prof_ids = _validate_indexed_decls(
        clean,
        "frontierNode",
        "_profile",
        expected_kw="theorem",
        allow_noncomputable=False,
        lean_path=lean_path,
        decl_index=decl_index,
    )

    found_nodes: dict[int, tuple[int, str]] = {}
    for m in _RE_FRONTIER_NODE.finditer(clean):
        raw_idx = m.group(1)
        idx = _parse_ascii_nat(raw_idx, f"{lean_path}: frontierNode index")
        if raw_idx != str(idx):
            raise VerifyError(f"{lean_path}: non-canonical leading-zero index frontierNode{raw_idx}")
        if idx in found_nodes:
            raise VerifyError(f"{lean_path}: duplicate definition of frontierNode{idx}")
        dim_decl = _parse_ascii_nat(m.group(2), f"{lean_path}: frontierNode{idx} dim")
        rhs = " ".join(m.group(3).split())
        found_nodes[idx] = (dim_decl, rhs)

    expected_keys = list(range(len(dag_ops)))
    if len(found_nodes) != len(seen_node_ids) or sorted(found_nodes.keys()) != expected_keys:
        raise VerifyError(
            f"{lean_path}: frontierNode definitions {sorted(found_nodes.keys())} do not match "
            f"frontierProf indices {expected_keys}"
        )
    if sorted(seen_prof_ids) != expected_keys:
        raise VerifyError(
            f"{lean_path}: frontierNode<k>_profile theorems {sorted(seen_prof_ids)} do not match "
            f"frontierProf indices {expected_keys}"
        )

    prof_thm_counts: dict[int, int] = {}
    for k1, k2, k3 in _RE_FRONTIER_NODE_PROFILE.findall(clean):
        if k1 == k2 == k3:
            ik = _parse_ascii_nat(k1, f"{lean_path}: frontierNode{k1}_profile index")
            if k1 == str(ik):
                prof_thm_counts[ik] = prof_thm_counts.get(ik, 0) + 1

    if base_dim <= 0 or base_dim > MAX_VERIFIER_DIM:
        raise VerifyError(f"{lean_path}: base_dim={base_dim} exceeds MAX_VERIFIER_DIM ({MAX_VERIFIER_DIM})")
    dims: list[int] = []
    for k, op in enumerate(dag_ops):
        dim_decl, rhs = found_nodes[k]
        kind = op["op"]
        if kind == "base":
            exp_dim = base_dim
            if rhs != "basePart5D":
                raise VerifyError(f"{lean_path}: frontierNode{k} RHS {rhs!r} != 'basePart5D'")
        elif kind == "flip":
            i = op["i"]
            if not (0 <= i < k):
                raise VerifyError(f"{lean_path}: frontierNode{k} invalid flip ref {i}")
            exp_dim = dims[i]
            if rhs != f"frontierNode{i}.flip":
                raise VerifyError(f"{lean_path}: frontierNode{k} RHS {rhs!r} != 'frontierNode{i}.flip'")
        elif kind in ("prodStd", "prodXupg1", "prodXupg2"):
            i, j = op["i"], op["j"]
            if not (0 <= i < k and 0 <= j < k):
                raise VerifyError(f"{lean_path}: frontierNode{k} invalid {kind} refs ({i}, {j})")
            di, dj = dims[i], dims[j]
            exp_dim = di + dj
            if exp_dim > MAX_VERIFIER_DIM:
                raise VerifyError(
                    f"{lean_path}: frontierNode{k} dim={exp_dim} exceeds MAX_VERIFIER_DIM ({MAX_VERIFIER_DIM})"
                )
            mp = _RE_FRONTIER_NODE_BIN.fullmatch(rhs)
            if not mp:
                raise VerifyError(f"{lean_path}: unrecognized frontierNode{k} RHS: {rhs!r}")
            ni = _parse_ascii_nat(mp.group(1), f"{lean_path}: frontierNode{k} lhs ref")
            node_op = mp.group(2)
            nj = _parse_ascii_nat(mp.group(3), f"{lean_path}: frontierNode{k} rhs ref")
            r_di = _parse_ascii_nat(mp.group(4), f"{lean_path}: frontierNode{k} lhs dim")
            r_dj = _parse_ascii_nat(mp.group(5), f"{lean_path}: frontierNode{k} rhs dim")
            if node_op != kind or ni != i or nj != j or r_di != di or r_dj != dj:
                raise VerifyError(
                    f"{lean_path}: frontierNode{k} mismatch: got {node_op}(node{ni}, node{nj}) dims=({r_di},{r_dj}), "
                    f"expected {kind}(node{i}, node{j}) dims=({di},{dj})"
                )
        else:
            raise VerifyError(f"{lean_path}: unsupported DAG op {kind!r} at node {k}")

        if dim_decl != exp_dim:
            raise VerifyError(f"{lean_path}: frontierNode{k} declared dim={dim_decl} != expected {exp_dim}")
        dims.append(exp_dim)

        if prof_thm_counts.get(k, 0) != 1:
            raise VerifyError(f"{lean_path}: expected unique `theorem frontierNode{k}_profile`")
    return dims


def verify_lean_file(
    lean_path: pathlib.Path, witness_summary: dict | None = None, enforce_frontier_floor: bool = True
) -> dict:
    if lean_path.stat().st_size > MAX_INPUT_BYTES:
        raise VerifyError(f"{lean_path}: file size exceeds MAX_INPUT_BYTES ({MAX_INPUT_BYTES})")
    raw = lean_path.read_bytes()
    try:
        src = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise VerifyError(f"{lean_path}: invalid UTF-8: {exc}") from exc
    if "\x00" in src:
        raise VerifyError(f"{lean_path}: contains NUL byte")

    try:
        tokens, clean = _lex_lean4_single_pass(src)
    except RecursionError as exc:
        raise VerifyError(f"{lean_path}: excessive nesting depth in Lean syntax") from exc
    _check_lean_hygiene(tokens, lean_path)
    decl_index = _index_all_decls(clean)
    for imp_nm in _FORBIDDEN_SHADOW_DECLS:
        if imp_nm in decl_index:
            raise VerifyError(
                f"{lean_path}: forbidden local redeclaration/shadowing of imported symbol `{imp_nm}`"
            )

    def extract_nat_def(name: str) -> int:
        _assert_unique_decl(
            clean,
            name,
            expected_kw="def",
            allow_noncomputable=False,
            lean_path=lean_path,
            decl_index=decl_index,
        )
        matches = _RE_NAT_DEFS[name].findall(clean)
        if len(matches) != 1:
            raise VerifyError(f"{lean_path}: expected unique `def {name} : ℕ := <nat>`, found {len(matches)}")
        rhs = matches[0].strip()
        val = _parse_ascii_nat(rhs, f"{lean_path}: `{name}` RHS")
        if val <= 0:
            raise VerifyError(f"{lean_path}: `{name}` must be strictly positive, got {val}")
        return val

    l_num = extract_nat_def("c7_lower_num")
    l_den = extract_nat_def("c7_lower_den")
    l_card = extract_nat_def("frontierCard")

    dag_ops = _parse_lean_dag_ops(clean, lean_path, decl_index=decl_index)

    # Optional Gamma6^4 terms parsing (require unique public unqualified def if present)
    parsed_terms: list[tuple[int, int, int, int]] | None = None
    g6_decls = decl_index.get("frontierGamma6Terms", [])
    if len(g6_decls) > 1:
        raise VerifyError(f"{lean_path}: duplicate/shadowed `frontierGamma6Terms` declarations ({len(g6_decls)})")
    if len(g6_decls) == 1:
        g6_mods, g6_kw, g6_qual, _ = g6_decls[0]
        if g6_qual:
            raise VerifyError(f"{lean_path}: qualified/shadowed `frontierGamma6Terms` not allowed")
        if g6_kw != "def":
            raise VerifyError(f"{lean_path}: `frontierGamma6Terms` must be `def`, found `{g6_kw}`")
        g6_mod_toks = set(g6_mods.split())
        if (g6_mod_toks & _FORBIDDEN_CERT_MODS) or "noncomputable" in g6_mod_toks:
            raise VerifyError(f"{lean_path}: forbidden modifier `{g6_mods.strip()}` on `frontierGamma6Terms`")
        g6_matches = _RE_G6_TERMS.findall(clean)
        if len(g6_matches) != 1:
            raise VerifyError(f"{lean_path}: malformed `frontierGamma6Terms` definition")
        raw_items = [it.strip() for it in re.split(r"\)\s*,", g6_matches[0].strip()) if it.strip()]
        if len(raw_items) > MAX_GAMMA6_TERMS:
            raise VerifyError(
                f"{lean_path}: frontierGamma6Terms count {len(raw_items)} exceeds MAX_GAMMA6_TERMS ({MAX_GAMMA6_TERMS})"
            )
        parsed_terms = []
        for idx_it, it in enumerate(raw_items):
            if idx_it + 1 < len(raw_items) and not it.endswith(")"):
                it = it + ")"
            mt = _RE_G6_TUPLE.fullmatch(it)
            if not mt:
                raise VerifyError(f"{lean_path}: malformed tuple in frontierGamma6Terms: {it!r}")
            parsed_terms.append(
                (
                    _parse_ascii_nat(mt.group(1), f"{lean_path}: frontierGamma6Terms[{idx_it}][0]"),
                    _parse_ascii_nat(mt.group(2), f"{lean_path}: frontierGamma6Terms[{idx_it}][1]"),
                    _parse_ascii_nat(mt.group(3), f"{lean_path}: frontierGamma6Terms[{idx_it}][2]"),
                    _parse_ascii_nat(mt.group(4), f"{lean_path}: frontierGamma6Terms[{idx_it}][3]"),
                )
            )
        if not parsed_terms:
            raise VerifyError(f"{lean_path}: parsed 0 tuples from frontierGamma6Terms")
        if len(set(parsed_terms)) != len(parsed_terms):
            raise VerifyError(f"{lean_path}: duplicate tuple in frontierGamma6Terms")
        for t in parsed_terms:
            if any(c < 0 or c >= 6 for c in t):
                raise VerifyError(f"{lean_path}: out-of-range Gamma6 vertex in {t}")
        for i in range(len(parsed_terms)):
            for j in range(i + 1, len(parsed_terms)):
                if _gamma6_close4(parsed_terms[i], parsed_terms[j]):
                    raise VerifyError(
                        f"{lean_path}: Gamma6^4 conflict in Lean file: {parsed_terms[i]} vs {parsed_terms[j]}"
                    )

    # Reject empty / spoof Lean files lacking a real PartGadget DAG construction
    if not dag_ops:
        raise VerifyError(
            f"{lean_path}: missing `frontierProf<k>` DAG definitions (refusing spoof/empty Lean certificate)"
        )

    base_prof = _parse_lean_base_profile(clean, lean_path, decl_index=decl_index)
    node_dims = _verify_lean_dag_nodes(clean, dag_ops, LOCKED_BASE_PART5D_DIM, lean_path, decl_index=decl_index)
    base_infos_parsed = [{"dim": LOCKED_BASE_PART5D_DIM, "profile": base_prof}]

    tgt_node: int | None = None
    lean_fnodes: list[int] | None = None
    lean_fflips: list[int] | None = None

    if parsed_terms is None:
        _assert_absent_decl(clean, r"frontierFactorProf[0-9]+", "frontierFactorProf<k>", lean_path, decl_index)
        _assert_absent_decl(clean, r"frontierFactor[0-9]+", "frontierFactor<k>", lean_path, decl_index)
        _assert_absent_decl(clean, r"frontierFactor[0-9]+_profile", "frontierFactor<k>_profile", lean_path, decl_index)
        _assert_absent_decl(clean, "frontierGamma6Terms_indep", "frontierGamma6Terms_indep", lean_path, decl_index)
        _assert_absent_decl(
            clean, "frontierGamma6Terms_weight_eq", "frontierGamma6Terms_weight_eq", lean_path, decl_index
        )

        _assert_unique_decl(
            clean,
            "frontierTarget_a_eq",
            expected_kw="theorem",
            allow_noncomputable=False,
            lean_path=lean_path,
            decl_index=decl_index,
        )
        tgt_matches = _RE_TARGET_A_EQ.findall(clean)
        if len(tgt_matches) != 1:
            raise VerifyError(
                f"{lean_path}: missing or malformed `theorem frontierTarget_a_eq : frontierProf<k>.a = frontierCard`"
            )
        tgt_node = _parse_ascii_nat(tgt_matches[0], f"{lean_path}: frontierTarget_a_eq target")
        if tgt_matches[0] != str(tgt_node):
            raise VerifyError(
                f"{lean_path}: non-canonical ref frontierProf{tgt_matches[0]} in frontierTarget_a_eq"
            )
        replayed_dim, replayed_lean_card = _replay_recipe(
            {"engine": "PartGadgetDAG", "ops": dag_ops, "target_node": tgt_node}, base_infos_parsed
        )
    else:
        _assert_absent_decl(clean, "frontierTarget_a_eq", "frontierTarget_a_eq", lean_path, decl_index)
        fp_ids = _validate_indexed_decls(
            clean,
            "frontierFactorProf",
            "",
            expected_kw="def",
            allow_noncomputable=False,
            lean_path=lean_path,
            decl_index=decl_index,
        )
        fn_ids = _validate_indexed_decls(
            clean,
            "frontierFactor",
            "",
            expected_kw="def",
            allow_noncomputable=True,
            lean_path=lean_path,
            decl_index=decl_index,
        )
        fprof_thm_ids = _validate_indexed_decls(
            clean,
            "frontierFactor",
            "_profile",
            expected_kw="theorem",
            allow_noncomputable=False,
            lean_path=lean_path,
            decl_index=decl_index,
        )
        if sorted(fp_ids) != [0, 1, 2, 3]:
            raise VerifyError(f"{lean_path}: expected frontierFactorProf0..3, found {sorted(fp_ids)}")
        if sorted(fn_ids) != [0, 1, 2, 3]:
            raise VerifyError(f"{lean_path}: expected frontierFactor0..3, found {sorted(fn_ids)}")
        if sorted(fprof_thm_ids) != [0, 1, 2, 3]:
            raise VerifyError(f"{lean_path}: expected frontierFactor0..3_profile, found {sorted(fprof_thm_ids)}")

        fp_parsed: dict[int, list[tuple[int, int]]] = {}
        for raw_fi, raw_nidx, flip_s in _RE_FACTOR_PROF.findall(clean):
            fi = _parse_ascii_nat(raw_fi, f"{lean_path}: frontierFactorProf index")
            if raw_fi != str(fi):
                continue
            nidx = _parse_ascii_nat(raw_nidx, f"{lean_path}: frontierFactorProf{fi} node")
            if raw_nidx != str(nidx):
                raise VerifyError(
                    f"{lean_path}: non-canonical ref frontierProf{raw_nidx} in frontierFactorProf{fi}"
                )
            fp_parsed.setdefault(fi, []).append((nidx, 1 if flip_s == ".flip" else 0))

        fn_parsed: dict[int, list[tuple[int, str]]] = {}
        for raw_fi, raw_dim, raw_rhs in _RE_FACTOR_NODE.findall(clean):
            fi = _parse_ascii_nat(raw_fi, f"{lean_path}: frontierFactor index")
            if raw_fi != str(fi):
                continue
            dim_v = _parse_ascii_nat(raw_dim, f"{lean_path}: frontierFactor{fi} dim")
            fn_parsed.setdefault(fi, []).append((dim_v, raw_rhs.strip()))

        fprof_thm_parsed: dict[int, list[str]] = {}
        for fi1, fi2, fi3, body in _RE_FACTOR_PROFILE.findall(clean):
            if fi1 == fi2 == fi3:
                fi = _parse_ascii_nat(fi1, f"{lean_path}: frontierFactor{fi1}_profile index")
                if fi1 == str(fi):
                    fprof_thm_parsed.setdefault(fi, []).append(body)

        lean_fnodes = []
        lean_fflips = []
        for fi in range(4):
            fp_list = fp_parsed.get(fi, [])
            if len(fp_list) != 1:
                raise VerifyError(f"{lean_path}: malformed `frontierFactorProf{fi}`")
            nidx, fl = fp_list[0]
            if not (0 <= nidx < len(dag_ops)):
                raise VerifyError(f"{lean_path}: frontierFactorProf{fi} references invalid node {nidx}")
            exp_rhs = f"frontierNode{nidx}.flip" if fl else f"frontierNode{nidx}"
            fn_list = fn_parsed.get(fi, [])
            if len(fn_list) != 1 or fn_list[0][0] != node_dims[nidx] or fn_list[0][1] != exp_rhs:
                raise VerifyError(f"{lean_path}: frontierFactor{fi} mismatch against frontierFactorProf{fi}")
            fthm_list = fprof_thm_parsed.get(fi, [])
            if len(fthm_list) != 1 or not _has_lean_ident(fthm_list[0], f"frontierNode{nidx}_profile"):
                raise VerifyError(
                    f"{lean_path}: malformed or unbound `theorem frontierFactor{fi}_profile` "
                    f"(must reference frontierNode{nidx}_profile)"
                )
            lean_fnodes.append(nidx)
            lean_fflips.append(fl)

        _assert_unique_decl(
            clean,
            "frontierGamma6Terms_indep",
            expected_kw="theorem",
            allow_noncomputable=False,
            lean_path=lean_path,
            decl_index=decl_index,
        )
        _assert_unique_decl(
            clean,
            "frontierGamma6Terms_weight_eq",
            expected_kw="theorem",
            allow_noncomputable=False,
            lean_path=lean_path,
            decl_index=decl_index,
        )
        g6_indep = _RE_G6_INDEP.findall(clean)
        g6_wt = _RE_G6_WEIGHT.findall(clean)
        if len(g6_indep) != 1 or len(g6_wt) != 1:
            raise VerifyError(f"{lean_path}: missing unique Gamma6 indep/weight theorems")
        replayed_dim, replayed_lean_card = _replay_recipe(
            {
                "engine": "Gamma6Pow4Pullback",
                "ops": dag_ops,
                "gamma6_pow4": {
                    "factor_nodes": lean_fnodes,
                    "factor_flips": lean_fflips,
                    "terms": [list(t) for t in parsed_terms],
                },
            },
            base_infos_parsed,
        )

    if replayed_lean_card != l_card:
        raise VerifyError(f"{lean_path}: replayed Lean DAG card={replayed_lean_card} != frontierCard={l_card}")

    # Verify theorem signatures bind exact replayed dimension & public contract
    _assert_unique_decl(
        clean,
        "frontierCard_le_indepNum",
        expected_kw="theorem",
        allow_noncomputable=False,
        lean_path=lean_path,
        decl_index=decl_index,
    )
    indep_m = _RE_CARD_LE_INDEP.findall(clean)
    if len(indep_m) != 1:
        raise VerifyError(f"{lean_path}: malformed `theorem frontierCard_le_indepNum` signature")
    indep_dim = _parse_ascii_nat(indep_m[0][0], f"{lean_path}: frontierCard_le_indepNum dim")
    indep_body = indep_m[0][1]
    if indep_dim != replayed_dim:
        raise VerifyError(
            f"{lean_path}: frontierCard_le_indepNum dim={indep_dim} != replayed DAG dim={replayed_dim}"
        )
    if tgt_node is not None:
        req_idents = (
            f"frontierNode{tgt_node}",
            f"frontierNode{tgt_node}_profile",
            "frontierTarget_a_eq",
        )
        missing_refs = [ident for ident in req_idents if not _has_lean_ident(indep_body, ident)]
        if missing_refs:
            raise VerifyError(
                f"{lean_path}: frontierCard_le_indepNum body missing reference(s) {missing_refs}"
            )
    else:
        req_g6_idents = (
            "gamma6Pow4_card_le_cycleGraph7_indepNum",
            "frontierGamma6Terms",
            "frontierGamma6Terms_indep",
            "frontierGamma6Terms_weight_eq",
            *(f"frontierFactor{fi}" for fi in range(4)),
            *(f"frontierFactor{fi}_profile" for fi in range(4)),
        )
        missing_refs = [ident for ident in req_g6_idents if not _has_lean_ident(indep_body, ident)]
        if missing_refs:
            raise VerifyError(
                f"{lean_path}: Gamma6 frontierCard_le_indepNum body missing reference(s) {missing_refs}"
            )

    _assert_unique_decl(
        clean,
        "frontier_pow_le",
        expected_kw="theorem",
        allow_noncomputable=False,
        lean_path=lean_path,
        decl_index=decl_index,
    )
    pow_m = _RE_POW_LE.findall(clean)
    if len(pow_m) != 1:
        raise VerifyError(f"{lean_path}: malformed `theorem frontier_pow_le` signature")
    exp_l = _parse_ascii_nat(pow_m[0][0], f"{lean_path}: frontier_pow_le lhs exponent")
    exp_r = _parse_ascii_nat(pow_m[0][1], f"{lean_path}: frontier_pow_le rhs exponent")
    if exp_l != replayed_dim or exp_r != replayed_dim:
        raise VerifyError(
            f"{lean_path}: frontier_pow_le exponents ({exp_l}, {exp_r}) != replayed DAG dim={replayed_dim}"
        )

    _assert_unique_decl(
        clean,
        "c7_lower_den_pos",
        expected_kw="theorem",
        allow_noncomputable=False,
        lean_path=lean_path,
        decl_index=decl_index,
    )
    den_pos_m = _RE_DEN_POS.findall(clean)
    if len(den_pos_m) != 1:
        raise VerifyError(f"{lean_path}: expected unique `theorem c7_lower_den_pos : 0 < c7_lower_den`")

    _assert_unique_decl(
        clean,
        "c7_lower_frontier",
        expected_kw="theorem",
        allow_noncomputable=False,
        lean_path=lean_path,
        decl_index=decl_index,
    )
    front_m = _RE_FRONTIER_THM.findall(clean)
    if len(front_m) != 1:
        raise VerifyError(f"{lean_path}: expected unique `theorem c7_lower_frontier` matching public contract")
    frontier_body = front_m[0]
    req_frontier_idents = (
        "le_shannonCapacity_of_nat_pow_pi",
        "c7_lower_den_pos",
        "frontierCard_le_indepNum",
        "frontier_pow_le",
    )
    missing_frontier_refs = [ident for ident in req_frontier_idents if not _has_lean_ident(frontier_body, ident)]
    if missing_frontier_refs:
        raise VerifyError(
            f"{lean_path}: c7_lower_frontier body missing reference(s) {missing_frontier_refs}"
        )

    cert_decl_names: set[str] = {
        "frontierBaseProfile",
        "basePart5D",
        "basePart5D_asymProfile_eq",
        "frontierCard",
        "frontierCard_le_indepNum",
        "c7_lower_num",
        "c7_lower_den",
        "c7_lower_den_pos",
        "frontier_pow_le",
        "c7_lower_frontier",
    }
    computable_decl_names: set[str] = {
        "frontierBaseProfile",
        "frontierCard",
        "c7_lower_num",
        "c7_lower_den",
    }
    for k in range(len(dag_ops)):
        cert_decl_names.add(f"frontierProf{k}")
        cert_decl_names.add(f"frontierNode{k}")
        cert_decl_names.add(f"frontierNode{k}_profile")
        computable_decl_names.add(f"frontierProf{k}")
    if parsed_terms is None:
        cert_decl_names.add("frontierTarget_a_eq")
    else:
        cert_decl_names.add("frontierGamma6Terms")
        cert_decl_names.add("frontierGamma6Terms_indep")
        cert_decl_names.add("frontierGamma6Terms_weight_eq")
        computable_decl_names.add("frontierGamma6Terms")
        for fi in range(4):
            cert_decl_names.add(f"frontierFactorProf{fi}")
            cert_decl_names.add(f"frontierFactor{fi}")
            cert_decl_names.add(f"frontierFactor{fi}_profile")
            computable_decl_names.add(f"frontierFactorProf{fi}")

    for opt_thm in ("c7_lower_gt_bpz_v1", "c7_lower_gt_bpz_v2", "c7_lower_gt_tandon"):
        if opt_thm in decl_index:
            _assert_unique_decl(
                clean,
                opt_thm,
                expected_kw="theorem",
                allow_noncomputable=False,
                lean_path=lean_path,
                decl_index=decl_index,
            )
            if len(_RE_OPT_COMP_THMS[opt_thm].findall(clean)) != 1:
                raise VerifyError(f"{lean_path}: malformed `{opt_thm}` signature")
            cert_decl_names.add(opt_thm)

    _check_lean_decl_scopes(src, tokens, cert_decl_names, computable_decl_names, lean_path)
    _check_lean_positive_whitelist(src, tokens, lean_path)
    _check_lean_lexical_whitelist(src, tokens, lean_path)

    # Enforce exact mathematical bounds even in standalone `--verify-lean` mode
    _check_exact_frontier_bounds(
        l_num,
        l_den,
        replayed_dim,
        l_card,
        require_sharp=True,
        enforce_frontier_floor=enforce_frontier_floor,
        label=f"Lean {lean_path}",
    )

    if witness_summary is not None:
        if "base_profiles" in witness_summary and witness_summary["base_profiles"]:
            if base_prof != witness_summary["base_profiles"][0]:
                raise VerifyError(
                    f"Lean frontierBaseProfile={base_prof} != witness base profile {witness_summary['base_profiles'][0]}"
                )
        if "base_dims" in witness_summary and witness_summary["base_dims"]:
            if LOCKED_BASE_PART5D_DIM != witness_summary["base_dims"][0]:
                raise VerifyError(
                    f"Lean basePart5D dim={LOCKED_BASE_PART5D_DIM} != witness base dim {witness_summary['base_dims'][0]}"
                )
        if "final_dim" in witness_summary and replayed_dim != witness_summary["final_dim"]:
            raise VerifyError(f"Lean dim={replayed_dim} != witness final_dim={witness_summary['final_dim']}")
        if l_num != witness_summary["num"]:
            raise VerifyError(f"Lean c7_lower_num={l_num} != witness {witness_summary['num']}")
        if l_den != witness_summary["den"]:
            raise VerifyError(f"Lean c7_lower_den={l_den} != witness {witness_summary['den']}")
        if l_card != witness_summary["N_exact"]:
            raise VerifyError(f"Lean frontierCard={l_card} != witness {witness_summary['N_exact']}")
        w_recipe = witness_summary["recipe"]
        w_engine = w_recipe.get("engine")
        if w_engine not in ("PartGadgetDAG", "Gamma6Pow4Pullback"):
            raise VerifyError(f"Unsupported witness engine for Lean cross-check: {w_engine!r}")
        w_ops_norm = [
            (
                {"op": "base", "idx": op["idx"]}
                if op["op"] == "base"
                else {"op": "flip", "i": op["i"]}
                if op["op"] == "flip"
                else {"op": "prodStd" if op["op"] == "prodAligned" else op["op"], "i": op["i"], "j": op["j"]}
            )
            for op in w_recipe["ops"]
        ]
        if dag_ops != w_ops_norm:
            raise VerifyError(f"Lean DAG ops ({len(dag_ops)}) != witness ops ({len(w_ops_norm)})")
        if w_engine == "PartGadgetDAG":
            if parsed_terms is not None:
                raise VerifyError("Witness uses PartGadgetDAG but Lean file defines frontierGamma6Terms")
            w_tgt = w_recipe.get("target_node", len(w_ops_norm) - 1)
            if tgt_node != w_tgt:
                raise VerifyError(f"Lean target node {tgt_node} != witness target_node {w_tgt}")
        else:
            if parsed_terms is None:
                raise VerifyError("Witness uses Gamma6Pow4Pullback but Lean file has no frontierGamma6Terms")
            w_terms = [tuple(t) for t in w_recipe["gamma6_pow4"]["terms"]]
            if parsed_terms != w_terms:
                raise VerifyError(f"Lean frontierGamma6Terms ({len(parsed_terms)}) != witness terms ({len(w_terms)})")
            if lean_fnodes != w_recipe["gamma6_pow4"]["factor_nodes"]:
                raise VerifyError("Lean frontierFactor nodes != witness factor_nodes")
            if lean_fflips != w_recipe["gamma6_pow4"]["factor_flips"]:
                raise VerifyError("Lean frontierFactor flips != witness factor_flips")

    return {
        "num": l_num,
        "den": l_den,
        "card": l_card,
        "dim": replayed_dim,
        "n_ops": len(dag_ops),
        "n_terms": len(parsed_terms) if parsed_terms else 0,
    }


def _make_mini_c7_1_witness() -> dict:
    I = [[0], [2], [5]]
    X = [[0], [5]]
    return {
        "schema_version": "1.0",
        "witness_id": "selftest_c7_1",
        "kind": "hetero_dag",
        "graph": "C7",
        "base_dim": 1,
        "final_dim": 1,
        "N_exact": "3",
        "c7_lower_num": "3",
        "c7_lower_den": "1",
        "sharp_last_digit": True,
        "base_gadgets": [
            {
                "gadget_id": "mini0",
                "dim": 1,
                "I": I,
                "ports": [{"s": [2], "p0": [2], "p1": [3]}],
                "X": X,
                "claimed_profile": {"a": 3, "b": 1, "c": 2, "d": 2, "h": 0, "v": 0},
                "sha256_I": _sha256_sorted_words([tuple(w) for w in I]),
                "sha256_X": _sha256_sorted_words([tuple(w) for w in X]),
            }
        ],
        "recipe": {"engine": "HeteroDAG", "ops": [{"op": "base", "idx": 0}]},
    }


def _concrete_verify_partgadget_products_on_c7() -> None:
    r"""Explicit graph-level verification of prodStd, prodXupg1, prodXupg2 on concrete C_7^1 x C_7^1!
    Take g1 = g2 on C_7^1: I = {0, 2, 5}, S = {2}, P0 = {2}, P1 = {3}, B = {0, 5}.
    Pick X = {1, 4, 6}: 1 vs 4 (dist 3 ok), 4 vs 6 (dist 2 ok), 1 vs 6 (dist 2 ok)!
    1 in N[2] \ N[3] -> H={1}; 4 in N[3] \ N[2] -> V={4}; 6 outside both -> O={6}!
    Exact profile: a=3, b=1, c=3, d=1, h=1, v=1 (ALL THREE O, H, V NON-EMPTY!!)."""
    B = [(0,), (5,)]
    S = [(2,)]
    P0 = [(2,)]
    P1 = [(3,)]
    O = [(6,)]
    H = [(1,)]
    V = [(4,)]
    prof = (3, 1, 3, 1, 1, 1)

    def cart(A, B_):
        return [a + b for a in A for b in B_]

    def check_indep2(pts, name):
        if len(set(pts)) != len(pts):
            raise VerifyError(f"concrete {name}: duplicate vertex")
        for i in range(len(pts)):
            for j in range(i + 1, len(pts)):
                if _c7_close(pts[i], pts[j]):
                    raise VerifyError(f"concrete {name}: conflict {pts[i]} vs {pts[j]}")

    def check_not_close2(A, B_, name):
        for x in A:
            for y in B_:
                if _c7_close(x, y):
                    raise VerifyError(f"concrete {name}: close {x} vs {y}")

    # Common aligned core in C_7^2:
    I_new = cart(B, B) + cart(S, O) + cart(P0, V) + cart(P1, H) + cart(O, S) + cart(H, P0) + cart(V, P1)
    S_new = cart(S, O) + cart(O, S)
    P0_new = cart(P0, O) + cart(O, P0)
    P1_new = cart(P1, O) + cart(O, P1)
    check_indep2(I_new, "I_new")
    check_indep2(P0_new, "P0_new")
    check_indep2(P1_new, "P1_new")
    if len(I_new) != 10 or len(S_new) != 2:
        raise VerifyError(f"Unexpected I_new/S_new card: {len(I_new)}, {len(S_new)}")

    # Verify all 3 operators concretely on C_7^2:
    cases = [
        ("prodStd", _prod_std_prof(prof, prof),
         cart(O, O) + cart(H, H) + cart(H, V) + cart(V, H) + cart(V, V),
         cart(H, O) + cart(O, H),
         cart(V, O) + cart(O, V)),
        ("prodXupg1", _prod_xupg1_prof(prof, prof),
         cart(O, O) + cart(H, P0) + cart(V, P1),
         cart(O, H) + cart(H, B),
         cart(O, V) + cart(V, B)),
        ("prodXupg2", _prod_xupg2_prof(prof, prof),
         cart(O, O) + cart(P0, H) + cart(P1, V),
         cart(H, O) + cart(B, H),
         cart(V, O) + cart(B, V)),
    ]
    for name, exp_p, On, Hn, Vn in cases:
        check_indep2(On, f"{name}.O")
        check_indep2(Hn, f"{name}.H")
        check_indep2(Vn, f"{name}.V")
        check_not_close2(On, Hn, f"{name}.O-H")
        check_not_close2(On, Vn, f"{name}.O-V")
        check_not_close2(Hn, Vn, f"{name}.H-V")
        check_not_close2(P0_new, On, f"{name}.P0-O")
        check_not_close2(P1_new, On, f"{name}.P1-O")
        check_not_close2(P1_new, Hn, f"{name}.P1-H")
        check_not_close2(P0_new, Vn, f"{name}.P0-V")
        got_p = (len(I_new), len(S_new), len(On) + len(Hn) + len(Vn), len(On), len(Hn), len(Vn))
        if got_p != exp_p:
            raise VerifyError(f"concrete {name}: got profile {got_p} != expected {exp_p}")


def _make_valid_d220_mock_lean() -> str:
    """Self-contained valid d=220 Lean fixture satisfying all standalone `--verify-lean` checks."""
    return (
        "/-- Mock frontier certificate fixture (d = 220). -/\n"
        "namespace ShannonC7\n\n"
        "def frontierBaseProfile : AsymProfile :=\n"
        "  { a := 367, b := 8, c := 367, d := 322, h := 19, v := 26,\n"
        "    hba := by decide, hdhv := by decide }\n\n"
        "noncomputable def basePart5D : PartGadget (strongPow C7 5) :=\n"
        "  PartGadget.ofHeteroGadget baseHetero5D\n\n"
        "theorem basePart5D_asymProfile_eq : basePart5D.asymProfile = frontierBaseProfile := by\n"
        "  rfl\n\n"
        "def frontierProf0 : AsymProfile := frontierBaseProfile\n"
        "noncomputable def frontierNode0 : PartGadget (strongPow C7 5) := basePart5D\n"
        "theorem frontierNode0_profile : frontierNode0.asymProfile = frontierProf0 := basePart5D_asymProfile_eq\n\n"
        "def frontierProf1 : AsymProfile := frontierProf0.prodAligned frontierProf0\n"
        "noncomputable def frontierNode1 : PartGadget (strongPow C7 10) :=\n"
        "  (frontierNode0.prodStd frontierNode0).mapIso (strongPowAddEquiv C7 5 5).symm\n"
        "theorem frontierNode1_profile : frontierNode1.asymProfile = frontierProf1 := rfl\n\n"
        "def frontierProf2 : AsymProfile := frontierProf0.prodAligned frontierProf1\n"
        "noncomputable def frontierNode2 : PartGadget (strongPow C7 15) :=\n"
        "  (frontierNode0.prodStd frontierNode1).mapIso (strongPowAddEquiv C7 5 10).symm\n"
        "theorem frontierNode2_profile : frontierNode2.asymProfile = frontierProf2 := rfl\n\n"
        "def frontierProf3 : AsymProfile := frontierProf1.prodAligned frontierProf1\n"
        "noncomputable def frontierNode3 : PartGadget (strongPow C7 20) :=\n"
        "  (frontierNode1.prodStd frontierNode1).mapIso (strongPowAddEquiv C7 10 10).symm\n"
        "theorem frontierNode3_profile : frontierNode3.asymProfile = frontierProf3 := rfl\n\n"
        "def frontierProf4 : AsymProfile := frontierProf1.prodAligned frontierProf2\n"
        "noncomputable def frontierNode4 : PartGadget (strongPow C7 25) :=\n"
        "  (frontierNode1.prodStd frontierNode2).mapIso (strongPowAddEquiv C7 10 15).symm\n"
        "theorem frontierNode4_profile : frontierNode4.asymProfile = frontierProf4 := rfl\n\n"
        "def frontierProf5 : AsymProfile := frontierProf2.prodAligned frontierProf2\n"
        "noncomputable def frontierNode5 : PartGadget (strongPow C7 30) :=\n"
        "  (frontierNode2.prodStd frontierNode2).mapIso (strongPowAddEquiv C7 15 15).symm\n"
        "theorem frontierNode5_profile : frontierNode5.asymProfile = frontierProf5 := rfl\n\n"
        "def frontierProf6 : AsymProfile := frontierProf2.prodAligned frontierProf3\n"
        "noncomputable def frontierNode6 : PartGadget (strongPow C7 35) :=\n"
        "  (frontierNode2.prodStd frontierNode3).mapIso (strongPowAddEquiv C7 15 20).symm\n"
        "theorem frontierNode6_profile : frontierNode6.asymProfile = frontierProf6 := rfl\n\n"
        "def frontierProf7 : AsymProfile := frontierProf3.prodAligned frontierProf4\n"
        "noncomputable def frontierNode7 : PartGadget (strongPow C7 45) :=\n"
        "  (frontierNode3.prodStd frontierNode4).mapIso (strongPowAddEquiv C7 20 25).symm\n"
        "theorem frontierNode7_profile : frontierNode7.asymProfile = frontierProf7 := rfl\n\n"
        "def frontierProf8 : AsymProfile := frontierProf5.prodAligned frontierProf6\n"
        "noncomputable def frontierNode8 : PartGadget (strongPow C7 65) :=\n"
        "  (frontierNode5.prodStd frontierNode6).mapIso (strongPowAddEquiv C7 30 35).symm\n"
        "theorem frontierNode8_profile : frontierNode8.asymProfile = frontierProf8 := rfl\n\n"
        "def frontierProf9 : AsymProfile := frontierProf7.prodXupg1 frontierProf8\n"
        "noncomputable def frontierNode9 : PartGadget (strongPow C7 110) :=\n"
        "  (frontierNode7.prodXupg1 frontierNode8).mapIso (strongPowAddEquiv C7 45 65).symm\n"
        "theorem frontierNode9_profile : frontierNode9.asymProfile = frontierProf9 := rfl\n\n"
        "def frontierProf10 : AsymProfile := frontierProf9.prodAligned frontierProf9\n"
        "noncomputable def frontierNode10 : PartGadget (strongPow C7 220) :=\n"
        "  (frontierNode9.prodStd frontierNode9).mapIso (strongPowAddEquiv C7 110 110).symm\n"
        "theorem frontierNode10_profile : frontierNode10.asymProfile = frontierProf10 := rfl\n\n"
        "def frontierCard : ℕ := 74705260449010907031291311728445696992339746673817850928852859227950431526005228577975175899699338829613565617217\n"
        "theorem frontierTarget_a_eq : frontierProf10.a = frontierCard := rfl\n\n"
        "theorem frontierCard_le_indepNum :\n"
        "    frontierCard ≤ (strongPowPi (SimpleGraph.cycleGraph 7) 220).indepNum := by\n"
        "  have h1 := frontierNode10.card_le_indepNum\n"
        "  rw [frontierNode10_profile, frontierTarget_a_eq] at h1\n"
        "  exact h1\n\n"
        "def c7_lower_num : ℕ := 3258822357711717\n"
        "def c7_lower_den : ℕ := 1000000000000000\n"
        "theorem c7_lower_den_pos : 0 < c7_lower_den := by decide\n"
        "theorem frontier_pow_le :\n"
        "    c7_lower_num ^ 220 ≤ c7_lower_den ^ 220 * frontierCard :=\n"
        "  nat_pow_le_of_ble rfl\n"
        "theorem c7_lower_frontier :\n"
        "    (c7_lower_num : ℝ) / (c7_lower_den : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7) :=\n"
        "  le_shannonCapacity_of_nat_pow_pi (by decide) c7_lower_den_pos frontierCard_le_indepNum frontier_pow_le\n\n"
        "end ShannonC7\n"
    )


def _make_valid_g6_mock_lean() -> str:
    """Self-contained valid d=20 Gamma6Pow4Pullback Lean fixture (2 DAG ops, 5 terms, flips=[0,1,0,1])."""
    return (
        "namespace ShannonC7\n\n"
        "def frontierBaseProfile : AsymProfile :=\n"
        "  { a := 367, b := 8, c := 367, d := 322, h := 19, v := 26,\n"
        "    hba := by decide, hdhv := by decide }\n\n"
        "noncomputable def basePart5D : PartGadget (strongPow C7 5) :=\n"
        "  PartGadget.ofHeteroGadget baseHetero5D\n\n"
        "theorem basePart5D_asymProfile_eq : basePart5D.asymProfile = frontierBaseProfile := by\n"
        "  rfl\n\n"
        "def frontierProf0 : AsymProfile := frontierBaseProfile\n"
        "noncomputable def frontierNode0 : PartGadget (strongPow C7 5) := basePart5D\n"
        "theorem frontierNode0_profile : frontierNode0.asymProfile = frontierProf0 := basePart5D_asymProfile_eq\n\n"
        "def frontierProf1 : AsymProfile := frontierProf0.prodAligned frontierProf0\n"
        "noncomputable def frontierNode1 : PartGadget (strongPow C7 10) :=\n"
        "  (frontierNode0.prodStd frontierNode0).mapIso (strongPowAddEquiv C7 5 5).symm\n"
        "theorem frontierNode1_profile : frontierNode1.asymProfile = frontierProf1 := rfl\n\n"
        "def frontierFactorProf0 : AsymProfile := frontierProf0\n"
        "noncomputable def frontierFactor0 : PartGadget (strongPow C7 5) := frontierNode0\n"
        "theorem frontierFactor0_profile : frontierFactor0.asymProfile = frontierFactorProf0 :=\n"
        "  frontierNode0_profile\n\n"
        "def frontierFactorProf1 : AsymProfile := frontierProf0.flip\n"
        "noncomputable def frontierFactor1 : PartGadget (strongPow C7 5) := frontierNode0.flip\n"
        "theorem frontierFactor1_profile : frontierFactor1.asymProfile = frontierFactorProf1 := by\n"
        "  rw [frontierFactor1, PartGadget.flip_asymProfile, frontierNode0_profile]; rfl\n\n"
        "def frontierFactorProf2 : AsymProfile := frontierProf0\n"
        "noncomputable def frontierFactor2 : PartGadget (strongPow C7 5) := frontierNode0\n"
        "theorem frontierFactor2_profile : frontierFactor2.asymProfile = frontierFactorProf2 :=\n"
        "  frontierNode0_profile\n\n"
        "def frontierFactorProf3 : AsymProfile := frontierProf0.flip\n"
        "noncomputable def frontierFactor3 : PartGadget (strongPow C7 5) := frontierNode0.flip\n"
        "theorem frontierFactor3_profile : frontierFactor3.asymProfile = frontierFactorProf3 := by\n"
        "  rw [frontierFactor3, PartGadget.flip_asymProfile, frontierNode0_profile]; rfl\n\n"
        "def frontierGamma6Terms : List Gamma6Quad := [\n"
        "  (0, 0, 0, 0),\n"
        "  (1, 3, 3, 3),\n"
        "  (2, 1, 5, 3),\n"
        "  (3, 2, 1, 5),\n"
        "  (4, 5, 2, 1)\n"
        "]\n\n"
        "theorem frontierGamma6Terms_indep : gamma6QuadListIndepBool frontierGamma6Terms = true := rfl\n\n"
        "def frontierCard : ℕ := 16878352609\n\n"
        "theorem frontierGamma6Terms_weight_eq :\n"
        "    gamma6QuadListWeight frontierFactorProf0 frontierFactorProf1\n"
        "      frontierFactorProf2 frontierFactorProf3 frontierGamma6Terms = frontierCard := rfl\n\n"
        "theorem frontierCard_le_indepNum :\n"
        "    frontierCard ≤ (strongPowPi (SimpleGraph.cycleGraph 7) 20).indepNum := by\n"
        "  have h := gamma6Pow4_card_le_cycleGraph7_indepNum\n"
        "    frontierFactor0 frontierFactor1 frontierFactor2 frontierFactor3\n"
        "    frontierGamma6Terms frontierGamma6Terms_indep\n"
        "  rw [frontierFactor0_profile, frontierFactor1_profile,\n"
        "    frontierFactor2_profile, frontierFactor3_profile,\n"
        "    frontierGamma6Terms_weight_eq] at h\n"
        "  exact h\n\n"
        "def c7_lower_num : ℕ := 3246134443218\n"
        "def c7_lower_den : ℕ := 1000000000000\n"
        "theorem c7_lower_den_pos : 0 < c7_lower_den := by decide\n"
        "theorem frontier_pow_le :\n"
        "    c7_lower_num ^ 20 ≤ c7_lower_den ^ 20 * frontierCard :=\n"
        "  nat_pow_le_of_ble rfl\n"
        "theorem c7_lower_frontier :\n"
        "    (c7_lower_num : ℝ) / (c7_lower_den : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7) :=\n"
        "  le_shannonCapacity_of_nat_pow_pi (by decide) c7_lower_den_pos frontierCard_le_indepNum frontier_pow_le\n\n"
        "end ShannonC7\n"
    )


def run_self_test() -> int:
    """Execute 75 isolated positive & negative mutation tests strictly inside TemporaryDirectory() (plus read-only check on FrontierLower.lean)."""
    tests: list[tuple[str, bool, callable]] = []

    def expect_pass(name, fn):
        tests.append((name, True, fn))

    def expect_fail(name, fn):
        tests.append((name, False, fn))

    def expect_fail_all(name, cases: list[tuple[str, callable]]):
        def runner():
            for label, subfn in cases:
                try:
                    subfn()
                except VerifyError:
                    continue
                raise RuntimeError(f"sub-case {label!r} unexpectedly PASSED")
            raise VerifyError(f"all {len(cases)} sub-cases rejected")

        tests.append((name, False, runner))

    def expect_fail_all_msg(name, cases: list[tuple[str, callable, str]]):
        def runner():
            for label, subfn, req_substr in cases:
                try:
                    subfn()
                except VerifyError as exc:
                    if req_substr and req_substr not in str(exc):
                        raise RuntimeError(
                            f"sub-case {label!r} failed with unexpected message {str(exc)!r} "
                            f"(expected substring {req_substr!r})"
                        )
                    continue
                raise RuntimeError(f"sub-case {label!r} unexpectedly PASSED")
            raise VerifyError(f"all {len(cases)} sub-cases rejected with verified reasons")

        tests.append((name, False, runner))

    with tempfile.TemporaryDirectory(prefix="verify_witness_st_") as tmpdir:
        tmp = pathlib.Path(tmpdir)
        valid_lean_src = _make_valid_d220_mock_lean()
        valid_d220_ops = [
            {"op": "base", "idx": 0},
            {"op": "prodStd", "i": 0, "j": 0},
            {"op": "prodStd", "i": 0, "j": 1},
            {"op": "prodStd", "i": 1, "j": 1},
            {"op": "prodStd", "i": 1, "j": 2},
            {"op": "prodStd", "i": 2, "j": 2},
            {"op": "prodStd", "i": 2, "j": 3},
            {"op": "prodStd", "i": 3, "j": 4},
            {"op": "prodStd", "i": 5, "j": 6},
            {"op": "prodXupg1", "i": 7, "j": 8},
            {"op": "prodStd", "i": 9, "j": 9},
        ]

        # ST-01: Positive control (1D HeteroDAG)
        def st01():
            w = _make_mini_c7_1_witness()
            p = tmp / "good.json"
            p.write_text(json.dumps(w), encoding="utf-8")
            verify_witness_dict(json.loads(p.read_text(encoding="utf-8")), enforce_frontier_floor=False)

        expect_pass("ST-01 positive 1D HeteroDAG control", st01)

        # ST-02: Positive control (1D LayeredTuple)
        def st02():
            I = [[0], [2], [5]]
            X = [[5]]
            Y = [[0]]
            w = {
                "schema_version": "1.0",
                "witness_id": "selftest_layered",
                "kind": "layered_tuple",
                "graph": "C7",
                "base_dim": 1,
                "final_dim": 1,
                "N_exact": "3",
                "c7_lower_num": "3",
                "c7_lower_den": "1",
                "sharp_last_digit": True,
                "base_gadgets": [
                    {
                        "gadget_id": "l0",
                        "dim": 1,
                        "I": I,
                        "ports": [{"s": [2], "p0": [2], "p1": [3]}],
                        "X": X,
                        "interior_layer": {
                            "ports_int": [{"s": [5], "q0": [5], "q1": [6]}],
                            "Y": Y,
                            "claimed_layered_profile": {"bX": 1, "e": 1, "dY": 1, "hY": 0, "vY": 0, "pY": 0},
                        },
                        "claimed_profile": {"a": 3, "b": 1, "c": 1, "d": 1, "h": 0, "v": 0},
                    }
                ],
                "recipe": {"engine": "HeteroDAG", "ops": [{"op": "base", "idx": 0}]},
            }
            verify_witness_dict(w, enforce_frontier_floor=False)

        expect_pass("ST-02 positive 1D LayeredTuple control", st02)

        # ST-03: Positive concrete graph-level independence check of prodStd, prodXupg1, prodXupg2 on C_7^2
        expect_pass(
            "ST-03 positive concrete C7^2 graph-level verification of prodStd/prodXupg1/prodXupg2",
            _concrete_verify_partgadget_products_on_c7,
        )

        # ST-04: Positive PartGadgetDAG multi-op replay (base + prodStd + prodXupg1 + prodXupg2 + flip)
        def st04():
            w = _make_mini_c7_1_witness()
            w["base_gadgets"][0]["X"] = [[1], [4], [6]]
            w["base_gadgets"][0]["claimed_profile"] = {"a": 3, "b": 1, "c": 3, "d": 1, "h": 1, "v": 1}
            w["base_gadgets"][0].pop("sha256_X", None)
            w["final_dim"] = 4
            w["N_exact"] = "100"
            w["c7_lower_num"] = "316"
            w["c7_lower_den"] = "100"
            w["recipe"] = {
                "engine": "PartGadgetDAG",
                "ops": [
                    {"op": "base", "idx": 0},
                    {"op": "prodXupg1", "i": 0, "j": 0},
                    {"op": "flip", "i": 1},
                    {"op": "prodXupg2", "i": 1, "j": 2},
                ],
                "target_node": 3,
            }
            verify_witness_dict(w, enforce_frontier_floor=False)

        expect_pass("ST-04 positive PartGadgetDAG multi-op replay (xupg1 + flip + xupg2)", st04)

        # ST-05: Negative — cyclic 0 <-> 6 wrap-around conflict in I
        def st05():
            w = _make_mini_c7_1_witness()
            w["base_gadgets"][0]["I"] = [[0], [2], [6]]
            w["base_gadgets"][0].pop("sha256_I", None)
            verify_witness_dict(w, enforce_frontier_floor=False)

        expect_fail("ST-05 negative 0<->6 cyclic wrap-around conflict", st05)

        # ST-06: Negative — duplicate word in I
        def st06():
            w = _make_mini_c7_1_witness()
            w["base_gadgets"][0]["I"] = [[0], [2], [2]]
            w["base_gadgets"][0].pop("sha256_I", None)
            verify_witness_dict(w, enforce_frontier_floor=False)

        expect_fail("ST-06 negative duplicate word in I", st06)

        # ST-07: Negative — out-of-range coordinate 7
        def st07():
            w = _make_mini_c7_1_witness()
            w["base_gadgets"][0]["I"] = [[0], [2], [7]]
            w["base_gadgets"][0].pop("sha256_I", None)
            verify_witness_dict(w, enforce_frontier_floor=False)

        expect_fail("ST-07 negative out-of-range coordinate 7", st07)

        # ST-08: Negative — broken port privacy
        def st08():
            w = _make_mini_c7_1_witness()
            w["base_gadgets"][0]["ports"] = [{"s": [2], "p0": [2], "p1": [1]}]
            verify_witness_dict(w, enforce_frontier_floor=False)

        expect_fail("ST-08 negative broken port privacy", st08)

        # ST-09: Negative — degenerate non-toggle port
        def st09():
            w = _make_mini_c7_1_witness()
            w["base_gadgets"][0]["ports"] = [{"s": [2], "p0": [2], "p1": [2]}]
            verify_witness_dict(w, enforce_frontier_floor=False)

        expect_fail("ST-09 negative degenerate non-toggle port", st09)

        # ST-10: Negative — X word lands in N[P0] ∩ N[P1]
        def st10():
            w = _make_mini_c7_1_witness()
            w["base_gadgets"][0]["X"] = [[0], [3]]
            w["base_gadgets"][0].pop("sha256_X", None)
            verify_witness_dict(w, enforce_frontier_floor=False)

        expect_fail("ST-10 negative X hits N[P0] ∩ N[P1]", st10)

        # ST-11: Negative — interior port endpoint hits N[P1]
        def st11():
            w = _make_mini_c7_1_witness()
            w["base_gadgets"][0]["X"] = [[5]]
            w["base_gadgets"][0].pop("sha256_X", None)
            w["base_gadgets"][0]["claimed_profile"] = {"a": 3, "b": 1, "c": 1, "d": 1, "h": 0, "v": 0}
            w["base_gadgets"][0]["interior_layer"] = {
                "ports_int": [{"s": [5], "q0": [5], "q1": [4]}],
                "Y": [[0]],
            }
            verify_witness_dict(w, enforce_frontier_floor=False)

        expect_fail("ST-11 negative interior port hits outer N[P1]", st11)

        # ST-12: Negative — rounded-up +1 ULP numerator
        def st12():
            w = _make_mini_c7_1_witness()
            w["c7_lower_num"] = "31"
            w["c7_lower_den"] = "10"
            verify_witness_dict(w, enforce_frontier_floor=False)

        expect_fail("ST-12 negative rounded-up +1 ULP numerator", st12)

        # ST-13: Negative — mismatched N_exact vs replay
        def st13():
            w = _make_mini_c7_1_witness()
            w["N_exact"] = "4"
            verify_witness_dict(w, enforce_frontier_floor=False)

        expect_fail("ST-13 negative mismatched N_exact vs replay", st13)

        # ST-14: Negative — Lean c7_lower_num mismatch vs witness summary
        def st14():
            mock_lean = tmp / "MockFrontier.lean"
            mock_lean.write_text(valid_lean_src, encoding="utf-8")
            fake_summary = {
                "num": 3258822357711716,
                "den": 1000000000000000,
                "final_dim": 220,
                "N_exact": 74705260449010907031291311728445696992339746673817850928852859227950431526005228577975175899699338829613565617217,
                "recipe": {"engine": "PartGadgetDAG", "ops": valid_d220_ops, "target_node": 10},
            }
            verify_lean_file(mock_lean, fake_summary)

        expect_fail("ST-14 negative Lean c7_lower_num mismatch", st14)

        # ST-15: Negative — Lean DAG op mismatch vs witness summary
        def st15():
            mock_lean = tmp / "MockDagMismatch.lean"
            mock_lean.write_text(valid_lean_src, encoding="utf-8")
            alt_ops = [dict(op) for op in valid_d220_ops]
            alt_ops[9] = {"op": "prodXupg2", "i": 7, "j": 8}
            fake_summary = {
                "num": 3258822357711717,
                "den": 1000000000000000,
                "final_dim": 220,
                "N_exact": 74705260449010907031291311728445696992339746673817850928852859227950431526005228577975175899699338829613565617217,
                "recipe": {"engine": "PartGadgetDAG", "ops": alt_ops, "target_node": 10},
            }
            verify_lean_file(mock_lean, fake_summary)

        expect_fail("ST-15 negative Lean DAG op mismatch caught", st15)

        # ST-16: Negative — Lean forbidden token `native_decide` caught
        def st16():
            mock_lean = tmp / "MockCheat.lean"
            mock_lean.write_text(valid_lean_src + "\ntheorem bad : True := by native_decide\n", encoding="utf-8")
            verify_lean_file(mock_lean, None)

        expect_fail("ST-16 negative Lean forbidden native_decide token", st16)

        # ST-17: Positive standalone `--verify-lean` control (valid d=220 pure-math + general-lexer Char/raw/interp/comments)
        def st17():
            mock_lean = tmp / "MockValidStandalone.lean"
            pure_math_extras = (
                "/-! Benign module doc header -/\n"
                "/-- Benign declaration doc comment -/\n"
                "-- benign line comment with \"quotes\" and 'chars'\n"
                "def okPrime (hq₁' a'' : Nat) : Nat := hq₁' + a''\n"
            )
            mock_lean.write_text(
                valid_lean_src.replace("\nend ShannonC7\n", f"\n{pure_math_extras}\nend ShannonC7\n", 1),
                encoding="utf-8",
            )
            res = verify_lean_file(mock_lean, None, enforce_frontier_floor=True)
            if res["dim"] != 220 or res["n_ops"] != 11:
                raise VerifyError(f"Unexpected standalone verify_lean_file result: {res}")
            # General-lexer parity control (strings, chars, raw/interp, nested comments)
            gen_lex_benign = (
                "/- -/ /---/ /-!-/\n"
                "def okPrime (hq₁' a'' : Nat) : Nat := hq₁' + a''\n"
                "def okQuoteChar : Char := '\"'\n"
                "def okEscChar : Char := '\\''\n"
                "def okHexChar : Char := '\\x22'\n"
                "def okUniChar : Char := '\\u0022'\n"
                "def okRaw : String := r#\"\\\"#\n"
                "def okPlain : String := \"sorry is benign inside non-interpolated plain string\"\n"
                "def okInterp : String := s!\"value={1 + 2} literal=\\{sorry}\"\n"
            )
            toks_g, _ = _lex_lean4_single_pass(gen_lex_benign)
            _check_lean_hygiene(toks_g, "<st17_gen_lex>")

        expect_pass("ST-17 positive standalone --verify-lean d=220 baseline + general-lexer Char/raw/interp/comments", st17)

        # ST-18: Negative (M11a) — interpolated string s!"{(sorry : String)}" smuggling
        def st18():
            p = tmp / "M11a.lean"
            p.write_text(valid_lean_src + '\ndef evil : String := s!"{(sorry : String)}"\n', encoding="utf-8")
            verify_lean_file(p, None)

        expect_fail('ST-18 negative (M11a) s!"{(sorry : String)}" interpolated smuggling', st18)

        # ST-19: Negative (M11b) — interpolated string s!"{by native_decide}" smuggling
        def st19():
            p = tmp / "M11b.lean"
            p.write_text(valid_lean_src + '\ndef evil : String := s!"{by native_decide}"\n', encoding="utf-8")
            verify_lean_file(p, None)

        expect_fail('ST-19 negative (M11b) s!"{by native_decide}" interpolated smuggling', st19)

        # ST-20: Negative (M21) — f!"{sorry}", m!"{sorry}", nested s!"{s!"{sorry}"}", comment-gap, char-in-interp, dbg_trace, throwErrorAt
        def _mk_lean_check(fname: str, snippet: str):
            def _fn():
                p = tmp / fname
                p.write_text(valid_lean_src + "\n" + snippet + "\n", encoding="utf-8")
                verify_lean_file(p, None)
            return _fn

        expect_fail_all(
            "ST-20 negative (M21) f!/m!/nested/comment-gap/char-in-interp/dbg_trace/throwErrorAt smuggling",
            [
                ("f!", _mk_lean_check("m21_f.lean", 'def e1 := f!"{sorry}"')),
                ("m!", _mk_lean_check("m21_m.lean", 'def e2 := m!"{axiom}"')),
                ("nested_s!", _mk_lean_check("m21_nest.lean", 'def e3 := s!"{s!"{sorry}"}"')),
                ("comment_gap", _mk_lean_check("m21_gap.lean", 'def e4 := s! /- gap -/ "{sorry}"')),
                ("char_rbrace_in_interp", _mk_lean_check("m21_chr.lean", "def e5 := s!\"{let c := '}'; sorry}\"")),
                ("str_rbrace_in_interp", _mk_lean_check("m21_str.lean", 'def e6 := s!"{let s := "}"; sorry}"')),
                ("escaped_bslash_interp", _mk_lean_check("m21_bs.lean", 'def e7 := s!"\\\\{sorry}"')),
                ("dbg_trace", _mk_lean_check("m21_dbg.lean", 'def e8 := dbg_trace "{sorry}"; 0')),
                ("throwErrorAt", _mk_lean_check("m21_err.lean", 'def e9 := throwErrorAt ref "{native_decide}"')),
            ],
        )

        # ST-21: Negative (M11c) — Char literal '"', raw string r#"\"#, and guillemet «"» quote-desync smuggling
        expect_fail_all(
            "ST-21 negative (M11c) Char '\"' + raw r#\"\\\"# + guillemet «\"» quote-desync smuggling",
            [
                (
                    "char_dquote",
                    _mk_lean_check(
                        "m11c_char.lean",
                        "def q1 : Char := '\"'\ntheorem evil_char_smuggle : False := sorry\ndef q2 : Char := '\"'",
                    ),
                ),
                (
                    "raw_bslash",
                    _mk_lean_check(
                        "m11c_raw.lean",
                        'def r1 : String := r#"\\"#\ntheorem evil_raw_smuggle : False := sorry\ndef r2 : String := r#""#',
                    ),
                ),
                (
                    "guillemet_dquote",
                    _mk_lean_check(
                        "m11c_guil.lean",
                        'def «"» : Nat := 0\ntheorem evil_guil_smuggle : False := sorry\ndef «"2» : Nat := 0',
                    ),
                ),
            ],
        )

        # ST-22: Negative (M11d, M20) — unclosed comments (/-, /-/, /--/, /-!/), unclosed strings, raw strings, interp, Char
        expect_fail_all(
            "ST-22 negative (M11d/M20) unclosed block comments, strings, raw strings, interp, and Char",
            [
                ("unclosed_bcomm", _mk_lean_check("m11d_1.lean", "/- unclosed sorry")),
                ("slash_dash_slash", _mk_lean_check("m11d_2.lean", "/-/")),
                ("doc_slash_dash_dash_slash", _mk_lean_check("m11d_3.lean", "/--/")),
                ("moddoc_slash_dash_bang_slash", _mk_lean_check("m11d_4.lean", "/-!/")),
                ("nested_unclosed", _mk_lean_check("m11d_5.lean", "/- /- -/")),
                ("unclosed_str", _mk_lean_check("m20_1.lean", 'def s := "unclosed')),
                ("unclosed_raw", _mk_lean_check("m20_2.lean", 'def s := r#"unclosed"')),
                ("unclosed_interp", _mk_lean_check("m20_3.lean", 'def s := s!"{1 + 2')),
                ("unclosed_char", _mk_lean_check("m20_4.lean", "def c := 'a")),
                ("unclosed_guil", _mk_lean_check("m20_5.lean", "def «unclosed := 0")),
            ],
        )

        # ST-23: Negative (M01b) — standalone --verify-lean +1 ULP numerator
        def st23():
            p = tmp / "M01b.lean"
            p.write_text(
                valid_lean_src.replace("3258822357711717", "3258822357711718"),
                encoding="utf-8",
            )
            verify_lean_file(p, None)

        expect_fail("ST-23 negative (M01b) standalone --verify-lean +1 ULP numerator", st23)

        # ST-24: Negative (M23) — standalone --verify-lean 3-line spoof file
        def st24():
            p = tmp / "M23.lean"
            p.write_text(
                "def c7_lower_num : ℕ := 99999999999999999\n"
                "def c7_lower_den : ℕ := 1\n"
                "def frontierCard : ℕ := 1\n",
                encoding="utf-8",
            )
            verify_lean_file(p, None)

        expect_fail("ST-24 negative (M23) standalone --verify-lean 3-line spoof file", st24)

        # ST-25: Negative (M13) — tampered frontierBaseProfile (a := 368)
        def st25():
            p = tmp / "M13.lean"
            p.write_text(
                valid_lean_src.replace("a := 367,", "a := 368,"),
                encoding="utf-8",
            )
            verify_lean_file(p, None)

        expect_fail("ST-25 negative (M13) tampered frontierBaseProfile (a := 368)", st25)

        # ST-26: Negative (M14) — tampered frontier_pow_le exponent (220 -> 1) & frontierCard_le_indepNum dim
        expect_fail_all(
            "ST-26 negative (M14) tampered frontier_pow_le exponent & frontierCard_le_indepNum dim",
            [
                (
                    "pow_exp_both",
                    lambda: (
                        (tmp / "M14a.lean").write_text(
                            valid_lean_src.replace(
                                "c7_lower_num ^ 220 ≤ c7_lower_den ^ 220 * frontierCard",
                                "c7_lower_num ^ 1 ≤ c7_lower_den ^ 1 * frontierCard",
                            ),
                            encoding="utf-8",
                        ),
                        verify_lean_file(tmp / "M14a.lean", None),
                    ),
                ),
                (
                    "pow_exp_rhs",
                    lambda: (
                        (tmp / "M14b.lean").write_text(
                            valid_lean_src.replace(
                                "c7_lower_num ^ 220 ≤ c7_lower_den ^ 220 * frontierCard",
                                "c7_lower_num ^ 220 ≤ c7_lower_den ^ 221 * frontierCard",
                            ),
                            encoding="utf-8",
                        ),
                        verify_lean_file(tmp / "M14b.lean", None),
                    ),
                ),
                (
                    "indep_dim",
                    lambda: (
                        (tmp / "M14c.lean").write_text(
                            valid_lean_src.replace(
                                "(strongPowPi (SimpleGraph.cycleGraph 7) 220).indepNum",
                                "(strongPowPi (SimpleGraph.cycleGraph 7) 5).indepNum",
                            ),
                            encoding="utf-8",
                        ),
                        verify_lean_file(tmp / "M14c.lean", None),
                    ),
                ),
            ],
        )

        # ST-27: Negative (M17, M22) — duplicate def c7_lower_num and duplicate def frontierProf10
        expect_fail_all(
            "ST-27 negative (M17/M22) duplicate def c7_lower_num & duplicate def frontierProf10",
            [
                ("dup_num", _mk_lean_check("M17.lean", "def c7_lower_num : ℕ := 1")),
                (
                    "dup_prof10",
                    _mk_lean_check("M22.lean", "def frontierProf10 : AsymProfile := frontierBaseProfile"),
                ),
                (
                    "dup_node10",
                    _mk_lean_check(
                        "M22b.lean",
                        "noncomputable def frontierNode10 : PartGadget (strongPow C7 5) := basePart5D",
                    ),
                ),
            ],
        )

        # ST-28: Negative (M15) — tampered sha256_canonical in witness JSON
        def st28():
            w = _make_mini_c7_1_witness()
            w["sha256_canonical"] = "0" * 64
            verify_witness_dict(w, enforce_frontier_floor=False)

        expect_fail("ST-28 negative (M15) tampered sha256_canonical digest", st28)

        # ST-29: Negative (M16) — tampered frontierNode9 (prodXupg1 -> prodStd) while frontierProf9 unchanged
        def st29():
            p = tmp / "M16.lean"
            p.write_text(
                valid_lean_src.replace(
                    "(frontierNode7.prodXupg1 frontierNode8)",
                    "(frontierNode7.prodStd frontierNode8)",
                ),
                encoding="utf-8",
            )
            verify_lean_file(p, None)

        expect_fail("ST-29 negative (M16) tampered frontierNode9 (prodXupg1 -> prodStd)", st29)

        # ST-30: Defense-in-depth — Unicode digit '²', non-dict claimed_profile, and HeteroDAG target_node
        def st30():
            # Positive check: HeteroDAG honors recipe.target_node cleanly
            w_ok = _make_mini_c7_1_witness()
            w_ok["recipe"] = {
                "engine": "HeteroDAG",
                "ops": [{"op": "base", "idx": 0}, {"op": "prodAligned", "i": 0, "j": 0}],
                "target_node": 0,
            }
            verify_witness_dict(w_ok, enforce_frontier_floor=False)

            # Negative sub-cases must raise VerifyError (not ValueError/TypeError!)
            for label, mut in (
                ("unicode_digit", lambda w: w.__setitem__("N_exact", "²")),
                ("nondict_cp", lambda w: w["base_gadgets"][0].__setitem__("claimed_profile", [1, 2])),
                ("bad_target", lambda w: w["recipe"].__setitem__("target_node", 99)),
            ):
                w = _make_mini_c7_1_witness()
                mut(w)
                try:
                    verify_witness_dict(w, enforce_frontier_floor=False)
                except VerifyError:
                    continue
                raise RuntimeError(f"sub-case {label!r} did not raise VerifyError")

        expect_pass("ST-30 positive/negative defense-in-depth (Unicode digits, dict guards, HeteroDAG target_node)", st30)

        def _mk_lean_mut(fname: str, src_text: str, summary: dict | None = None, floor: bool = True):
            def _fn():
                p = tmp / fname
                p.write_text(src_text, encoding="utf-8")
                verify_lean_file(p, summary, enforce_frontier_floor=floor)
            return _fn

        # ST-31: Negative (M24/B-1) — Unicode non-isIdRest suffix forbidden-token smuggling
        expect_fail_all_msg(
            "ST-31 negative (M24) Unicode non-isIdRest suffix forbidden-token smuggling",
            [
                ("sorry_compl", _mk_lean_check("st31_1.lean", "def e1 : SimpleGraph (Fin 7) := sorryᶜ"), "sorry"),
                ("sorry_transp", _mk_lean_check("st31_2.lean", "def e2 := sorryᵀ"), "sorry"),
                ("sorry_lambda", _mk_lean_check("st31_3.lean", "def e3 := sorryλx => x"), "sorry"),
                ("sorry_sup2", _mk_lean_check("st31_4.lean", "def e4 := sorry²"), "sorry"),
                ("sorry_inv", _mk_lean_check("st31_5.lean", "def e5 := sorry⁻¹"), "sorry"),
                ("axiom_compl", _mk_lean_check("st31_6.lean", "def e6 := axiomᶜ"), "axiom"),
                ("native_decide_compl", _mk_lean_check("st31_7.lean", "def e7 := native_decideᶜ"), "native_decide"),
                ("sorry_pi", _mk_lean_check("st31_8.lean", "def e8 := sorryΠ"), "sorry"),
                ("sorry_sigma", _mk_lean_check("st31_9.lean", "def e9 := sorryΣ"), "sorry"),
            ],
        )

        # ST-32: Negative (B-1/B06a) — Non-ident Unicode char + `'"'` Char-literal quote-desync smuggling
        expect_fail_all_msg(
            "ST-32 negative (B-1/B06a) non-ident Unicode char + '\"' Char-literal quote-desync smuggling",
            [
                (
                    "ord_fem_char",
                    _mk_lean_check("st32_1.lean", "def q1 := ª'\"'\ntheorem evil : False := sorry\ndef q2 := '\"'"),
                    "sorry",
                ),
                (
                    "sup2_char",
                    _mk_lean_check("st32_2.lean", "def q1 := x²'\"'\ntheorem evil : False := sorry\ndef q2 := '\"'"),
                    "sorry",
                ),
                (
                    "sigma_char_unclosed",
                    _mk_lean_check("st32_3.lean", "def q1 := Σ'\"'\ntheorem evil : False := sorry\ndef q2 := '\"'"),
                    "Unclosed",
                ),
                (
                    "sigma_dblq_char",
                    _mk_lean_check("st32_3b.lean", "def q1 := Σ''\"'\ntheorem evil : False := sorry\ndef q2 := '\"'"),
                    "sorry",
                ),
                (
                    "sigma_sp_char",
                    _mk_lean_check("st32_3c.lean", "def q1 := Σ' '\"'\ntheorem evil : False := sorry\ndef q2 := '\"'"),
                    "sorry",
                ),
                (
                    "pi_char",
                    _mk_lean_check("st32_4.lean", "def q1 := Π'\"'\ntheorem evil : False := sorry\ndef q2 := '\"'"),
                    "sorry",
                ),
                (
                    "lambda_char",
                    _mk_lean_check("st32_5.lean", "def q1 := λ'\"'\ntheorem evil : False := sorry\ndef q2 := '\"'"),
                    "sorry",
                ),
                (
                    "hash_char",
                    _mk_lean_check("st32_6.lean", "def q1 := #'\"'\ntheorem evil : False := sorry\ndef q2 := '\"'"),
                    "sorry",
                ),
                (
                    "poc_V01",
                    _mk_lean_check(
                        "st32_v01.lean",
                        'local prefix:max "ª" => id\ndef q1 := ª\'"\'\ntheorem evil : False := sorry\ndef q2 := \'"\'',
                    ),
                    "prefix",
                ),
                (
                    "poc_V02",
                    _mk_lean_check(
                        "st32_v02.lean",
                        'local infixl:65 "²" => fun _ y => y\ndef q1 := x²\'"\'\ntheorem evil : False := sorry\ndef q2 := \'"\'',
                    ),
                    "infixl",
                ),
                (
                    "poc_B06a",
                    _mk_lean_check(
                        "st32_b06a.lean",
                        'prefix:max "Σ" => id\ndef q1 := Σ\'\'"\'\ntheorem evil : False := sorry\ndef q2 := \'"\'',
                    ),
                    "prefix",
                ),
            ],
        )

        # ST-33: Positive — Valid Lean 4.32.2 Unicode math identifiers & underscore-joined benign names
        def st33():
            extras = (
                "def α₁ : Nat := 1\n"
                "def Γ₆ : Nat := 2\n"
                "def sorry_helper : Nat := 3\n"
                "def my_axiom_bound : Nat := 4\n"
                "def partial_sum : Nat := 5\n"
                "def hq₁' : Nat := 6\n"
                "def hB'card : Nat := 7\n"
                "def find? : Nat := 8\n"
                "def compute_degree! : Nat := 9\n"
                "def xᵥ : Nat := 10\n"
                "def xⱼ : Nat := 11\n"
                "def ℕ_helper : Nat := 12\n"
            )
            p = tmp / "st33_unicode_ok.lean"
            p.write_text(
                valid_lean_src.replace("\nend ShannonC7\n", f"\n{extras}\nend ShannonC7\n", 1),
                encoding="utf-8",
            )
            verify_lean_file(p, None)

        expect_pass("ST-33 positive valid Lean 4.32.2 Unicode math identifiers & underscore benign names", st33)

        # ST-34: Negative (B-2/B01..B05/X1..X3) — Fail-Closed Pure-Math Policy: Meta/Trace/Error/Interpolator APIs
        long_ref = "id (" * 60 + "ref" + ")" * 60
        st34_cases: list[tuple[str, callable, str]] = []
        for idx_api, api_name in enumerate(
            (
                "throwNamedError",
                "throwNamedErrorAt",
                "logNamedError",
                "logNamedErrorAt",
                "logNamedWarning",
                "logNamedWarningAt",
            )
        ):
            st34_cases.append(
                (
                    f"{api_name}_interp",
                    _mk_lean_check(
                        f"st34_na_{idx_api}.lean",
                        f'def e := {api_name} lean.unknownIdentifier "{{(sorry : String)}}"',
                    ),
                    api_name,
                )
            )
            st34_cases.append(
                (
                    f"{api_name}_plain",
                    _mk_lean_check(f"st34_np_{idx_api}.lean", f'def e := {api_name} lean.id "msg"'),
                    api_name,
                )
            )
        st34_cases.extend(
            [
                ("trace_goal", _mk_lean_check("st34_tg.lean", 'def e := trace_goal[grind] "{(sorry : String)}"'), "trace_goal"),
                ("trace_br", _mk_lean_check("st34_tr1.lean", 'def e := trace[cls] "{(sorry : String)}"'), "trace["),
                (
                    "trace_long300",
                    _mk_lean_check("st34_tr2.lean", 'def e := trace[' + ("a" * 300) + '] "{(sorry : String)}"'),
                    "trace[",
                ),
                ("macro_trace_br", _mk_lean_check("st34_tr3.lean", 'def e := Macro.trace[cls] "{sorry}"'), "trace["),
                (
                    "X3_trace_array",
                    _mk_lean_check(
                        "st34_x3.lean",
                        'def trace : Array (String → String) := #[id]\ndef x := trace[0] "{"\ntheorem cheat : False := sorry\ndef y := "}"',
                    ),
                    "trace[",
                ),
                ("dbg_trace_plain", _mk_lean_check("st34_dbg.lean", 'def e := dbg_trace "plain"; 0'), "dbg_trace"),
                ("idbg", _mk_lean_check("st34_idbg.lean", "def e := idbg 0"), "idbg"),
                ("throwError_plain", _mk_lean_check("st34_te.lean", 'def e := throwError "plain"'), "throwError"),
                (
                    "throwErrorAt_long300",
                    _mk_lean_check("st34_tea1.lean", f'def e := throwErrorAt ({long_ref}) "{{(sorry : String)}}"'),
                    "throwErrorAt",
                ),
                (
                    "throwErrorAt_semi",
                    _mk_lean_check("st34_tea2.lean", 'def e := throwErrorAt (let x := tk; x) "{(sorry : String)}"'),
                    "throwErrorAt",
                ),
                (
                    "X1_m_bang",
                    _mk_lean_check(
                        "st34_x1.lean",
                        'def m! (s : String) := s\ndef x := m!"{"\ntheorem cheat : False := sorry\ndef y := "}"',
                    ),
                    "m!",
                ),
                (
                    "X2_v_bang",
                    _mk_lean_check(
                        "st34_x2.lean",
                        'def v! (s : String) := s\ndef x := v!"{"\ntheorem cheat : False := sorry\ndef y := "}"',
                    ),
                    "v!",
                ),
                ("reportIssue!", _mk_lean_check("st34_ri1.lean", 'def e := reportIssue! "x"'), "reportIssue!"),
                ("reportDbgIssue!", _mk_lean_check("st34_ri2.lean", 'def e := reportDbgIssue! "x"'), "reportDbgIssue!"),
                (
                    "reportEMatchIssue!",
                    _mk_lean_check("st34_ri3.lean", 'def e := reportEMatchIssue! "x"'),
                    "reportEMatchIssue!",
                ),
                ("aesop_trace", _mk_lean_check("st34_at1.lean", 'def e := aesop_trace[x] "y"'), "aesop_trace"),
                ("aesop_trace!", _mk_lean_check("st34_at2.lean", 'def e := aesop_trace![x] "y"'), "aesop_trace!"),
                (
                    "B03_logInfoAt_plain",
                    _mk_lean_check("st34_b03a.lean", 'def e := logInfoAt (let x := tk; x) "{by native_decide}"'),
                    "logInfoAt",
                ),
                (
                    "B03_logInfoAt_m",
                    _mk_lean_check("st34_b03b.lean", 'def e := logInfoAt (let x := tk; x) m!"{by native_decide}"'),
                    "logInfoAt",
                ),
                (
                    "B03_logInfoAt_s",
                    _mk_lean_check("st34_b03c.lean", 'def e := logInfoAt (let x := tk; x) s!"{by native_decide}"'),
                    "logInfoAt",
                ),
                ("logInfo", _mk_lean_check("st34_li.lean", 'def e := logInfo "x"'), "logInfo"),
                ("logWarning", _mk_lean_check("st34_lw.lean", 'def e := logWarning "x"'), "logWarning"),
                ("logWarningAt", _mk_lean_check("st34_lwa.lean", 'def e := logWarningAt tk "x"'), "logWarningAt"),
                ("logError", _mk_lean_check("st34_le.lean", 'def e := logError "x"'), "logError"),
                ("logErrorAt", _mk_lean_check("st34_lea.lean", 'def e := logErrorAt tk "x"'), "logErrorAt"),
                (
                    "throwErrorWithNestedTraces",
                    _mk_lean_check("st34_twn.lean", 'def e := throwErrorWithNestedTraces "x"'),
                    "throwErrorWithNestedTraces",
                ),
            ]
        )
        expect_fail_all_msg(
            "ST-34 negative (B-2/B01..B05/X1..X3) fail-closed Meta/Trace/Error/Interpolator APIs",
            st34_cases,
        )

        # ST-35: Negative (B07a-b/policy/stealth) — Metaprogramming, custom syntax, notation, prelude, env, stealth options, #eval/#reduce
        st35_specs: list[tuple[str, str, str]] = [
            ("macro", 'macro "myMac" : term => `(0)', "macro"),
            ("macro_rules", "macro_rules | `(0) => `(0)", "macro_rules"),
            ("elab", 'elab "myElab" : term => pure default', "elab"),
            ("elab_rules", "elab_rules | `(0) => pure default", "elab_rules"),
            ("syntax", 'syntax "mySyn" : term', "syntax"),
            ("declare_syntax_cat", "declare_syntax_cat mycat", "declare_syntax_cat"),
            ("syntax_cat", "def x := syntax_cat", "syntax_cat"),
            ("binder_predicate", "binder_predicate x \" ∈' \" y:term => `($x = $y)", "binder_predicate"),
            ("notation3", 'notation3 "myN3" => 0', "notation3"),
            ("infix", 'infix:65 " ⊕₀ " => Nat.add', "infix"),
            ("infixl", 'infixl:65 " ⊕₁ " => Nat.add', "infixl"),
            ("infixr", 'infixr:65 " ⊕₂ " => Nat.add', "infixr"),
            ("prefix", 'prefix:max "¬₀" => id', "prefix"),
            ("postfix", 'postfix:max "‼" => id', "postfix"),
            ("notation", 'notation "myNot" => 0', "notation"),
            ("by_elab", "def e := by_elab pure default", "by_elab"),
            ("run_tac", "def e := run_tac pure ()", "run_tac"),
            ("run_cmd", "run_cmd pure ()", "run_cmd"),
            ("run_elab", "run_elab pure ()", "run_elab"),
            ("run_meta", "run_meta pure ()", "run_meta"),
            ("initialize", "initialize myInit : Nat := pure 0", "initialize"),
            ("builtin_initialize", "builtin_initialize myBI : Nat := pure 0", "builtin_initialize"),
            ("prelude", "prelude\nimport Init.Prelude", "prelude"),
            ("interpolatedStr", "def e := interpolatedStr", "interpolatedStr"),
            ("fq_interpolatedStr", "def e := «interpolatedStr»", "interpolatedStr"),
            ("expandInterpolatedStr", "def e := expandInterpolatedStr", "expandInterpolatedStr"),
            ("register_parser_alias", "def e := register_parser_alias", "register_parser_alias"),
            ("term_parser", "@[term_parser] def myP := 0", "term_parser"),
            ("modifyEnv", "def e := modifyEnv", "modifyEnv"),
            ("setEnv", "def e := setEnv", "setEnv"),
            ("addDecl", "def e := addDecl", "addDecl"),
            ("addAndCompile", "def e := addAndCompile", "addAndCompile"),
            (
                "B07a_infixl_lt_dash_dash",
                'infixl:65 "<--" => fun (a b : Nat) => a + b\ndef e := 1 <-- (sorry : Nat)',
                "infixl",
            ),
            (
                "B07b_infixl_lt_slash_dash",
                'infixl:65 "</-" => fun (a b : Nat) => a + b\ninfixl:65 "-/>" => fun (a b : Nat) => a + b\ndef e := (1 </- 2) + (sorry : Nat) + (1 -/> 2)',
                "infixl",
            ),
            ("opaque", "opaque auxOp : Nat := 0", "opaque"),
            ("partial", "partial def auxP (n : Nat) : Nat := auxP n", "partial"),
            ("csimp", "@[csimp] theorem auxC : True := trivial", "csimp"),
            ("proofAsSorry", "set_option debug.proofAsSorry true", "proofAsSorry"),
            ("byAsSorry", "set_option debug.byAsSorry true", "byAsSorry"),
            ("terminalTacticsAsSorry", "set_option debug.terminalTacticsAsSorry true", "terminalTacticsAsSorry"),
            ("skipKernelTC", "set_option debug.skipKernelTC true", "skipKernelTC"),
            ("allowUnsafeReducibility", "set_option allowUnsafeReducibility true", "allowUnsafeReducibility"),
            ("hash_eval", "#eval 1", "#eval"),
            ("hash_eval_bang", "#eval! 1", "#eval!"),
            ("hash_reduce", "#reduce 1", "#reduce"),
            ("import_Mathlib", "import Mathlib", "import Mathlib"),
            ("import_fq_Mathlib", "import «Mathlib»", "import Mathlib"),
            ("import_all_Mathlib", "import all Mathlib", "import Mathlib"),
        ]
        expect_fail_all_msg(
            "ST-35 negative (B07a-b/policy/stealth) forbidden meta/syntax/notation/stealth-option/#eval/import Mathlib",
            [
                (lbl, _mk_lean_check(f"st35_{i}.lean", code), req)
                for i, (lbl, code, req) in enumerate(st35_specs)
            ],
        )

        # ST-36: Negative (Traps #1 & #2, dotted-r, focusing dot, newline-char, deep-nesting C-5)
        expect_fail_all_msg(
            "ST-36 negative (Traps #1-#2/dotted-r/focus-dot/nl-char/C-5) zero-import lexer desync & deep nesting",
            [
                (
                    "trap1_plain_brace",
                    _mk_lean_check(
                        "st36_1.lean",
                        'def x : String := "{"\ntheorem cheat : False := sorry\ndef y : String := "}"',
                    ),
                    "sorry",
                ),
                (
                    "non_interp_fq_s",
                    _mk_lean_check(
                        "st36_2.lean",
                        'def x := «s!» "{"\ntheorem cheat : False := sorry\ndef y := "}"',
                    ),
                    "sorry",
                ),
                (
                    "non_interp_backtick_s",
                    _mk_lean_check(
                        "st36_3.lean",
                        'def x := f `s! "{"\ntheorem cheat : False := sorry\ndef y := "}"',
                    ),
                    "sorry",
                ),
                (
                    "non_interp_dot_s",
                    _mk_lean_check(
                        "st36_4.lean",
                        'def x := Foo.s! "{"\ntheorem cheat : False := sorry\ndef y := "}"',
                    ),
                    "sorry",
                ),
                (
                    "non_interp_foo_bang",
                    _mk_lean_check(
                        "st36_5.lean",
                        'def x := foo!"{"\ntheorem cheat : False := sorry\ndef y := "}"',
                    ),
                    "sorry",
                ),
                (
                    "non_interp_after_empty_s",
                    _mk_lean_check(
                        "st36_6.lean",
                        'def x := f s!"" "{"\ntheorem cheat : False := sorry\ndef y := "}"',
                    ),
                    "sorry",
                ),
                (
                    "trap2_gt_line_comment",
                    _mk_lean_check(
                        "st36_7.lean",
                        'def x : Prop := 1>--"\n2\ntheorem cheat : False := sorry\ndef y : Prop := 1>--"\n2',
                    ),
                    "sorry",
                ),
                (
                    "trap2_lt_block_comment",
                    _mk_lean_check(
                        "st36_8.lean",
                        'def x : Prop := 1</- " -/2\ntheorem cheat : False := sorry\ndef y : Prop := 1</- " -/2',
                    ),
                    "sorry",
                ),
                (
                    "trap2_ident_line_comment",
                    _mk_lean_check(
                        "st36_9.lean",
                        'def a : Nat := 1\ndef x : Nat := a-- "\ntheorem cheat : False := sorry\ndef y : Nat := a-- "',
                    ),
                    "sorry",
                ),
                (
                    "trap2_ident_block_comment",
                    _mk_lean_check(
                        "st36_10.lean",
                        'def a : Nat := 1\ndef x : Nat := a/- " -/\ntheorem cheat : False := sorry\ndef y : Nat := a/- " -/',
                    ),
                    "sorry",
                ),
                (
                    "bracket_quote_sorry",
                    _mk_lean_check("st36_11.lean", "def e (a : List Nat) := a[0]'(sorry)"),
                    "sorry",
                ),
                (
                    "dotted_r_desync",
                    _mk_lean_check(
                        "st36_12.lean",
                        'def r1 := Foo.r"\\""\ntheorem evil : False := sorry\ndef r2 := "\\""',
                    ),
                    "sorry",
                ),
                (
                    "backtick_r_desync",
                    _mk_lean_check(
                        "st36_13.lean",
                        'def r1 := f `r"\\""\ntheorem evil : False := sorry\ndef r2 := "\\""',
                    ),
                    "sorry",
                ),
                (
                    "dotted_r_hash_desync",
                    _mk_lean_check(
                        "st36_14.lean",
                        'def r1 := Foo.r#"\\""\ntheorem evil : False := sorry\ndef r2 := "\\""',
                    ),
                    "sorry",
                ),
                (
                    "focusing_dot_s_interp",
                    _mk_lean_check("st36_15.lean", 'theorem t : True := by\n  . s!"{sorry}"'),
                    "sorry",
                ),
                (
                    "literal_newline_char_desync",
                    _mk_lean_check(
                        "st36_16.lean",
                        "def q1 := '\n''\"'\ntheorem evil : False := sorry\ndef q2 := '\"'",
                    ),
                    "sorry",
                ),
                (
                    "deep_interp_1200_sorry",
                    _mk_lean_check("st36_17.lean", "def d1 := " + ('s!"{' * 1200) + "sorry" + ('}"' * 1200)),
                    "sorry",
                ),
                (
                    "deep_interp_1200_unclosed",
                    _mk_lean_check("st36_18.lean", "def d2 := " + ('s!"{' * 1200) + "1"),
                    "Unclosed",
                ),
                (
                    "unclosed_nested_brace",
                    _mk_lean_check("st36_19.lean", 'def u1 := s!"{1 + {2}"'),
                    "Unclosed",
                ),
                (
                    "unclosed_println_interp",
                    _mk_lean_check("st36_20.lean", 'def u2 := println!"{1'),
                    "Unclosed",
                ),
            ],
        )

        # ST-37: Positive (B10a-d/C15) — Benign pure-math edge cases & general-lexer non-interpolating controls
        def st37():
            pure_math_benign = (
                "def ok_trace_id (A : Nat) := Matrix.trace A + trace A\n"
                "/-- doc sorry -/\n"
                "/-! moddoc sorry -/\n"
                "def ok_adj1 := 1--sorry\n"
                "def ok_adj3 := a--sorry\n"
                "def ok_dot_eval (t : Nat) := t.eval\n"
            )
            p = tmp / "st37_benign.lean"
            p.write_text(
                valid_lean_src.replace("\nend ShannonC7\n", f"\n{pure_math_benign}\nend ShannonC7\n", 1),
                encoding="utf-8",
            )
            verify_lean_file(p, None)

            gen_lex_benign = (
                "def ok_b10a (a : List Nat) (h h' : 0 < a.length) : Nat := a[0]'h + a[0]'(h) + a[0]'h'\n"
                "def ok_b10b1 : Type := Nat ×' Nat\n"
                "def ok_b10b2 : Type := Nat ⊕' Nat\n"
                "def ok_b10b3 (x : Nat) := #' x\n"
                "def ok_b10b4 (f : Nat → Nat) (s : Set Nat) := f ⁻¹' s\n"
                "def ok_b10b5 := Σ' x : Nat, Fin x\n"
                "def ok_b10b6 (f : {x : Nat} → Nat → Nat) (g : Nat → Nat) := f ∘' g\n"
                "def ok_b10c (f : Nat → Nat) (s : Set Nat) := f '' s\n"
                'def ok_b10d (trace : Nat) : String := let _ := trace\n  "hello {not interp"\n'
                'def ok_c15 (a b : String) := a ++ b\ndef ok_c15_use := ok_c15 s!"" "{sorry}"\n'
                'def ok_p1 := println! r"{"\n'
                'def ok_p2 := println! ("{ sorry }")\n'
                'def ok_p3 := «s!» "{ sorry }"\n'
                'def ok_p4 := f `s! "{ sorry }"\n'
                'def ok_p5 := Foo.s! "{ sorry }"\n'
                'def ok_p6 := myplain!"{ sorry }"\n'
                'def ok_p7 := «dbg_trace» "{ sorry }"\n'
                "/- outer /- sorry -/ outer -/\n"
                "/-- -- -/\n-/\n"
                "/-/- -/\n"
                "/-/-/\n"
                "def ok_adj2 := 1/-sorry-/ + 2\n"
                "def ok_adj4 := a/-sorry-/ + 2\n"
            )
            toks_g, _ = _lex_lean4_single_pass(gen_lex_benign)
            _check_lean_hygiene(toks_g, "<st37_gen_lex>")

        expect_pass("ST-37 positive (B10a-d/C15) benign pure-math edge cases & general-lexer non-interpolating controls", st37)

        # ST-38: Positive + Negative (B10e/NB-3) — `_LEAN_BODY_END` trailing boundaries & Closed Whitelist reconciliation
        def st38():
            anchor = "def c7_lower_num : ℕ := 3258822357711717"
            # Part 1: ALL whitelisted trailing commands MUST terminate `c7_lower_num` cleanly AND pass verify_lean_file
            pos_trails = (
                ("def", "def auxDef : Nat := 1"),
                ("noncomp_def", "noncomputable def auxNoncomp : Nat := 1"),
                ("theorem", "theorem auxThm : True := trivial"),
                ("abbrev", "abbrev AuxAbbrev := Nat"),
                ("structure", "structure AuxS where\n  x : Nat"),
                ("set_option_exp", "set_option exponentiation.threshold 4096 in\ntheorem auxOpt : True := trivial"),
                (
                    "set_option_linter",
                    "set_option linter.unusedFintypeInType false in\nstructure AuxS2 where\n  y : Nat",
                ),
                ("ns_partgadget_var", "namespace PartGadget\nvariable (n : Nat)\nend PartGadget"),
                ("end_reopen_ns", "end ShannonC7\nnamespace ShannonC7"),
            )
            for lbl, trail in pos_trails:
                p = tmp / f"st38_pos_{lbl}.lean"
                p.write_text(valid_lean_src.replace(anchor, f"{anchor}\n{trail}", 1), encoding="utf-8")
                verify_lean_file(p, None)

            # Part 2: Non-whitelisted trailing commands MUST still terminate `_RE_NAT_DEFS` cleanly
            # at `"3258822357711717"` (defense-in-depth) AND be rejected by Stage 7 Closed Positive Whitelist
            banned_trails = (
                ("example", "example : True := trivial"),
                ("inductive", "inductive AuxI\n  | mk"),
                ("class", "class AuxC (α : Type) where\n  val : α"),
                ("instance", "instance : Inhabited Unit := ⟨()⟩"),
                ("section_variable", "section\nvariable (n : Nat)\nend"),
                ("nonrec_def", "nonrec def auxNonrec : Nat := 1"),
                ("universe", "universe u"),
                ("attr_simp", "@[simp] theorem auxSimp1 : True := trivial"),
                ("attr_simp_space", "@[ simp ] theorem auxSimp2 : True := trivial"),
                ("hash_check", "#check c7_lower_num"),
                ("trailing_var_shannon", "variable (n : Nat)"),
            )
            for lbl, trail in banned_trails:
                mut_src = (
                    valid_lean_src.replace("\nend ShannonC7\n", f"\n{trail}\nend ShannonC7\n", 1)
                    if lbl == "trailing_var_shannon"
                    else valid_lean_src.replace(anchor, f"{anchor}\n{trail}", 1)
                )
                _, clean_m = _lex_lean4_single_pass(mut_src)
                nat_m = _RE_NAT_DEFS["c7_lower_num"].findall(clean_m)
                if len(nat_m) != 1 or nat_m[0].strip() != "3258822357711717":
                    raise RuntimeError(f"ST-38 Part 2 boundary check failed on {lbl!r}: got {nat_m!r}")
                p = tmp / f"st38_banned_{lbl}.lean"
                p.write_text(mut_src, encoding="utf-8")
                try:
                    verify_lean_file(p, None)
                except VerifyError:
                    continue
                raise RuntimeError(f"ST-38 banned trailing command {lbl!r} unexpectedly PASSED")

            # Part 3: Negative multiline continuation & keyword-prefix collisions MUST fail on Stage 5 nat RHS
            neg_trails = (
                ("cont_plus1", "  + 1\ntheorem auxCont : True := trivial"),
                ("kw_prefix_theorem", "theorem_not_kw"),
                ("kw_prefix_def", "def_not_kw"),
            )
            for lbl, trail in neg_trails:
                p = tmp / f"st38_neg_{lbl}.lean"
                p.write_text(valid_lean_src.replace(anchor, f"{anchor}\n{trail}", 1), encoding="utf-8")
                try:
                    verify_lean_file(p, None)
                except VerifyError as exc:
                    if "expected ASCII unsigned decimal integer" not in str(exc):
                        raise RuntimeError(f"ST-38 negative {lbl!r} masked by unexpected error: {exc}")
                    continue
                raise RuntimeError(f"ST-38 negative sub-case {lbl!r} unexpectedly PASSED")

        expect_pass("ST-38 positive/negative (B10e/NB-3) _LEAN_BODY_END boundaries & Closed Whitelist reconciliation", st38)

        # ST-39: Positive (B-4) — Strict O(N) lexer throughput & zero-RecursionError stress guard
        def st39():
            s1 = "def many_strs : List String := [" + ", ".join(['s!""'] * 1000 + ['"a"'] * 1000) + "]\n"
            t0 = time.process_time()
            toks1, _ = _lex_lean4_single_pass(s1)
            _check_lean_hygiene(toks1, "<st39_many_strs>")
            dt1 = time.process_time() - t0
            if dt1 >= 0.25:
                raise RuntimeError(f"ST-39 2000-string O(N) guard exceeded 0.25s CPU: {dt1:.3f}s")
            p1 = tmp / "st39_many_strs.lean"
            p1.write_text(valid_lean_src.replace("\nend ShannonC7\n", f"\n{s1}\nend ShannonC7\n", 1), encoding="utf-8")
            t0 = time.process_time()
            try:
                verify_lean_file(p1, None)
                raise RuntimeError("ST-39 2000-string file unexpectedly passed Closed Lexical Whitelist")
            except VerifyError as exc:
                if "string literal" not in str(exc):
                    raise RuntimeError(f"ST-39 2000-string unexpected rejection: {exc}")
            dt1_v = time.process_time() - t0
            if dt1_v >= 0.25:
                raise RuntimeError(f"ST-39 2000-string verify_lean_file O(N) guard exceeded 0.25s CPU: {dt1_v:.3f}s")

            raw_decoy = "r" + ("#" * 500) + '"' + (('"' + ("#" * 499)) * 20) + '"' + ("#" * 500)
            s2 = f"def raw_decoy : String := {raw_decoy}\n"
            t0 = time.process_time()
            toks2, _ = _lex_lean4_single_pass(s2)
            _check_lean_hygiene(toks2, "<st39_raw_dfa>")
            dt2 = time.process_time() - t0
            if dt2 >= 0.10:
                raise RuntimeError(f"ST-39 raw-string DFA guard exceeded 0.10s CPU: {dt2:.3f}s")
            p2 = tmp / "st39_raw_dfa.lean"
            p2.write_text(valid_lean_src.replace("\nend ShannonC7\n", f"\n{s2}\nend ShannonC7\n", 1), encoding="utf-8")
            t0 = time.process_time()
            try:
                verify_lean_file(p2, None)
                raise RuntimeError("ST-39 raw-string DFA file unexpectedly passed Closed Lexical Whitelist")
            except VerifyError as exc:
                if "string literal" not in str(exc):
                    raise RuntimeError(f"ST-39 raw-string DFA unexpected rejection: {exc}")
            dt2_v = time.process_time() - t0
            if dt2_v >= 0.10:
                raise RuntimeError(f"ST-39 raw-string verify_lean_file DFA guard exceeded 0.10s CPU: {dt2_v:.3f}s")

            s3 = "def deep_ok := " + ('s!"{' * 2000) + "1" + ('}"' * 2000) + "\n"
            t0 = time.process_time()
            toks3, _ = _lex_lean4_single_pass(s3)
            _check_lean_hygiene(toks3, "<st39_deep_ok>")
            dt3 = time.process_time() - t0
            if dt3 >= 0.25:
                raise RuntimeError(f"ST-39 2000-deep interp guard exceeded 0.25s CPU: {dt3:.3f}s")
            p3 = tmp / "st39_deep_ok.lean"
            p3.write_text(valid_lean_src.replace("\nend ShannonC7\n", f"\n{s3}\nend ShannonC7\n", 1), encoding="utf-8")
            t0 = time.process_time()
            try:
                verify_lean_file(p3, None)
                raise RuntimeError("ST-39 2000-deep interp file unexpectedly passed Closed Lexical Whitelist")
            except VerifyError as exc:
                if "string literal" not in str(exc):
                    raise RuntimeError(f"ST-39 2000-deep interp unexpected rejection: {exc}")
            dt3_v = time.process_time() - t0
            if dt3_v >= 0.25:
                raise RuntimeError(f"ST-39 2000-deep verify_lean_file O(N) guard exceeded 0.25s CPU: {dt3_v:.3f}s")

            # Pure-math 2000-element List Nat passing full verify_lean_file in O(N)
            p4 = tmp / "st39_many_nats.lean"
            s4 = "def many_nats : List Nat := [" + ", ".join(str(i) for i in range(2000)) + "]\n"
            p4.write_text(valid_lean_src.replace("\nend ShannonC7\n", f"\n{s4}\nend ShannonC7\n", 1), encoding="utf-8")
            t0 = time.process_time()
            verify_lean_file(p4, None)
            dt4 = time.process_time() - t0
            if dt4 >= 0.25:
                raise RuntimeError(f"ST-39 2000-nat pure-math O(N) guard exceeded 0.25s CPU: {dt4:.3f}s")

        expect_pass("ST-39 positive (B-4) strict O(N) lexer throughput & 2000-deep zero-RecursionError guard", st39)

        # ST-40: Positive — ReDoS-free `_QUAL_PREFIX` linear-time guard
        def st40():
            p = tmp / "st40_redos.lean"
            redos_defs = (
                "def "
                + ("a." * 2000)
                + "not_target : Nat := 0\ndef "
                + ("a . " * 2000)
                + "not_target2 : Nat := 0\n"
            )
            p.write_text(
                valid_lean_src.replace("\nend ShannonC7\n", f"\n{redos_defs}\nend ShannonC7\n", 1),
                encoding="utf-8",
            )
            t0 = time.process_time()
            verify_lean_file(p, None)
            dt = time.process_time() - t0
            if dt >= 0.10:
                raise RuntimeError(f"ST-40 ReDoS _QUAL_PREFIX guard exceeded 0.10s CPU: {dt:.3f}s")

        expect_pass("ST-40 positive ReDoS-free _QUAL_PREFIX linear-time guard", st40)

        # ST-41: Negative (B-3/B08a-e) — Qualified, guillemet, space/symbol-guillemet, primed, & Unicode def shadowing
        expect_fail_all(
            "ST-41 negative (B-3/B08a-e) qualified/guillemet/primed/Unicode def shadowing",
            [
                ("qual_guil_leaf", _mk_lean_check("st41_1.lean", "def ShannonC7.«c7_lower_num» : ℕ := 1")),
                ("guil_qual_plain_leaf", _mk_lean_check("st41_2.lean", "def «ShannonC7».c7_lower_num : ℕ := 1")),
                ("guil_both", _mk_lean_check("st41_3.lean", "def «ShannonC7».«c7_lower_num» : ℕ := 1")),
                ("space_guil_qual", _mk_lean_check("st41_4.lean", "def «A B».c7_lower_num : ℕ := 1")),
                ("colon_guil_qual", _mk_lean_check("st41_5.lean", "def «:».c7_lower_num : ℕ := 1")),
                ("primed_qual", _mk_lean_check("st41_6.lean", "def Foo'.c7_lower_num : ℕ := 1")),
                ("unicode_qual", _mk_lean_check("st41_7.lean", "def Γ₁.c7_lower_num : ℕ := 1")),
                (
                    "qual_guil_prof10",
                    _mk_lean_check("st41_8.lean", "def ShannonC7.«frontierProf10» : AsymProfile := frontierBaseProfile"),
                ),
                (
                    "qual_guil_node10",
                    _mk_lean_check(
                        "st41_9.lean",
                        "noncomputable def ShannonC7.«frontierNode10» : PartGadget (strongPow C7 5) := basePart5D",
                    ),
                ),
                ("abbrev_num", _mk_lean_check("st41_10.lean", "abbrev c7_lower_num : ℕ := 1")),
                ("opaque_num", _mk_lean_check("st41_11.lean", "opaque c7_lower_num : ℕ := 1")),
                ("qual_base_prof", _mk_lean_check("st41_12.lean", "def Foo.frontierBaseProfile : AsymProfile := frontierBaseProfile")),
                (
                    "qual_base_part",
                    _mk_lean_check("st41_13.lean", "noncomputable def Foo.basePart5D : PartGadget (strongPow C7 5) := basePart5D"),
                ),
            ],
        )

        # ST-42: Negative (B-3/B09a-d) — Qualified theorem shadowing & in-place visibility/computability/keyword replacement
        expect_fail_all(
            "ST-42 negative (B-3/B09a-d) qualified theorem shadowing & in-place modifier/keyword replacement",
            [
                ("qual_frontier", _mk_lean_check("st42_1.lean", "theorem ShannonC7.c7_lower_frontier : True := trivial")),
                ("qual_pow_le", _mk_lean_check("st42_2.lean", "theorem ShannonC7.frontier_pow_le : True := trivial")),
                ("qual_indepNum", _mk_lean_check("st42_3.lean", "theorem ShannonC7.frontierCard_le_indepNum : True := trivial")),
                ("qual_target_a", _mk_lean_check("st42_4.lean", "theorem ShannonC7.frontierTarget_a_eq : True := trivial")),
                ("qual_den_pos", _mk_lean_check("st42_5.lean", "theorem ShannonC7.c7_lower_den_pos : True := trivial")),
                ("qual_basePart_eq", _mk_lean_check("st42_6.lean", "theorem ShannonC7.basePart5D_asymProfile_eq : True := trivial")),
                ("qual_node0_prof", _mk_lean_check("st42_7.lean", "theorem ShannonC7.frontierNode0_profile : True := trivial")),
                ("dup_lemma_frontier", _mk_lean_check("st42_8.lean", "lemma c7_lower_frontier : True := trivial")),
                (
                    "inplace_lemma_frontier",
                    _mk_lean_mut(
                        "st42_9.lean",
                        valid_lean_src.replace("theorem c7_lower_frontier", "lemma c7_lower_frontier", 1),
                    ),
                ),
                (
                    "inplace_lemma_basePart_eq",
                    _mk_lean_mut(
                        "st42_10.lean",
                        valid_lean_src.replace("theorem basePart5D_asymProfile_eq", "lemma basePart5D_asymProfile_eq", 1),
                    ),
                ),
                (
                    "inplace_private_num",
                    _mk_lean_mut(
                        "st42_11.lean",
                        valid_lean_src.replace("def c7_lower_num", "private def c7_lower_num", 1),
                    ),
                ),
                (
                    "inplace_noncomp_num",
                    _mk_lean_mut(
                        "st42_12.lean",
                        valid_lean_src.replace("def c7_lower_num", "noncomputable def c7_lower_num", 1),
                    ),
                ),
                (
                    "inplace_protected_frontier",
                    _mk_lean_mut(
                        "st42_13.lean",
                        valid_lean_src.replace("theorem c7_lower_frontier", "protected theorem c7_lower_frontier", 1),
                    ),
                ),
                (
                    "inplace_private_frontier",
                    _mk_lean_mut(
                        "st42_14.lean",
                        valid_lean_src.replace("theorem c7_lower_frontier", "private theorem c7_lower_frontier", 1),
                    ),
                ),
                (
                    "inplace_private_prof0",
                    _mk_lean_mut(
                        "st42_15.lean",
                        valid_lean_src.replace("def frontierProf0", "private def frontierProf0", 1),
                    ),
                ),
                (
                    "inplace_private_node0",
                    _mk_lean_mut(
                        "st42_16.lean",
                        valid_lean_src.replace("noncomputable def frontierNode0", "private noncomputable def frontierNode0", 1),
                    ),
                ),
            ],
        )

        # ST-43: Negative (NB-1/D03) — frontierCard_le_indepNum word-boundary & cross-branch stray-decl tampering
        expect_fail_all(
            "ST-43 negative (NB-1/D03) frontierCard_le_indepNum word-boundary & cross-branch stray-decl tampering",
            [
                (
                    "D03_node0_spoof",
                    _mk_lean_mut(
                        "st43_1.lean",
                        valid_lean_src.replace("frontierNode10.card_le_indepNum", "frontierNode0.card_le_indepNum", 1),
                    ),
                ),
                (
                    "D03_node1_prefix",
                    _mk_lean_mut(
                        "st43_2.lean",
                        valid_lean_src.replace("frontierNode10.card_le_indepNum", "frontierNode1.card_le_indepNum", 1),
                    ),
                ),
                (
                    "D03_qual_ref_spoof",
                    _mk_lean_mut(
                        "st43_3.lean",
                        valid_lean_src.replace(
                            "frontierNode10.card_le_indepNum", "Foo.frontierNode10.card_le_indepNum", 1
                        ),
                    ),
                ),
                (
                    "missing_target_a_eq_ref",
                    _mk_lean_mut(
                        "st43_4.lean",
                        valid_lean_src.replace(
                            "rw [frontierNode10_profile, frontierTarget_a_eq]", "rw [frontierNode10_profile]", 1
                        ),
                    ),
                ),
                (
                    "stray_g6_decl",
                    _mk_lean_check("st43_5.lean", "def frontierFactorProf0 : AsymProfile := frontierProf0"),
                ),
            ],
        )

        valid_g6_lean = _make_valid_g6_mock_lean()
        valid_g6_summary = {
            "num": 3246134443218,
            "den": 1000000000000,
            "final_dim": 20,
            "N_exact": 16878352609,
            "recipe": {
                "engine": "Gamma6Pow4Pullback",
                "ops": [{"op": "base", "idx": 0}, {"op": "prodStd", "i": 0, "j": 0}],
                "gamma6_pow4": {
                    "factor_nodes": [0, 0, 0, 0],
                    "factor_flips": [0, 1, 0, 1],
                    "terms": [[0, 0, 0, 0], [1, 3, 3, 3], [2, 1, 5, 3], [3, 2, 1, 5], [4, 5, 2, 1]],
                },
            },
        }

        # ST-44: Positive (NB-4) — Gamma6Pow4Pullback standalone & paired verification (d=20, 5 terms, 2 DAG ops)
        def st44():
            p = tmp / "st44_g6_valid.lean"
            p.write_text(valid_g6_lean, encoding="utf-8")
            r_std = verify_lean_file(p, None, enforce_frontier_floor=False)
            if r_std["dim"] != 20 or r_std["n_ops"] != 2 or r_std["n_terms"] != 5:
                raise VerifyError(f"Unexpected standalone Gamma6 result: {r_std}")
            r_pair = verify_lean_file(p, valid_g6_summary, enforce_frontier_floor=False)
            if r_pair["dim"] != 20 or r_pair["n_ops"] != 2 or r_pair["n_terms"] != 5:
                raise VerifyError(f"Unexpected paired Gamma6 result: {r_pair}")

        expect_pass("ST-44 positive (NB-4) Gamma6Pow4Pullback standalone & paired verification (d=20)", st44)

        # ST-45: Negative (NB-4/Unchallenged #4) — Gamma6Pow4Pullback exhaustive negative mutation suite
        alt_g6_summary = json.loads(json.dumps(valid_g6_summary))
        alt_g6_summary["recipe"]["ops"][1] = {"op": "prodXupg1", "i": 0, "j": 0}
        expect_fail_all(
            "ST-45 negative (NB-4/Unchallenged #4) Gamma6Pow4Pullback paired DAG ops, factors, terms, & body mutations",
            [
                ("paired_dag_op_tamper", _mk_lean_mut("st45_1.lean", valid_g6_lean, alt_g6_summary, False)),
                (
                    "g6_terms_trailing_append",
                    _mk_lean_mut(
                        "st45_2.lean",
                        valid_g6_lean.replace("  (4, 5, 2, 1)\n]", "  (4, 5, 2, 1)\n] ++ [(0, 0, 0, 0)]", 1),
                        None,
                        False,
                    ),
                ),
                (
                    "g6_terms_qual_dup",
                    _mk_lean_mut(
                        "st45_3.lean",
                        valid_g6_lean + "\ndef ShannonC7.frontierGamma6Terms : List Gamma6Quad := []\n",
                        None,
                        False,
                    ),
                ),
                (
                    "g6_indep_qual_dup",
                    _mk_lean_mut(
                        "st45_4a.lean",
                        valid_g6_lean + "\ntheorem ShannonC7.frontierGamma6Terms_indep : True := trivial\n",
                        None,
                        False,
                    ),
                ),
                (
                    "g6_weight_qual_dup",
                    _mk_lean_mut(
                        "st45_4b.lean",
                        valid_g6_lean + "\ntheorem ShannonC7.frontierGamma6Terms_weight_eq : True := trivial\n",
                        None,
                        False,
                    ),
                ),
                (
                    "g6_missing_factor0_profile",
                    _mk_lean_mut(
                        "st45_5.lean",
                        valid_g6_lean.replace(
                            "theorem frontierFactor0_profile : frontierFactor0.asymProfile = frontierFactorProf0 :=\n  frontierNode0_profile\n",
                            "",
                            1,
                        ),
                        None,
                        False,
                    ),
                ),
                (
                    "g6_dup_factor0_profile",
                    _mk_lean_mut(
                        "st45_6.lean",
                        valid_g6_lean + "\ntheorem ShannonC7.frontierFactor0_profile : True := trivial\n",
                        None,
                        False,
                    ),
                ),
                (
                    "g6_tampered_factor0_profile_body",
                    _mk_lean_mut(
                        "st45_7.lean",
                        valid_g6_lean.replace(
                            "theorem frontierFactor0_profile : frontierFactor0.asymProfile = frontierFactorProf0 :=\n  frontierNode0_profile",
                            "theorem frontierFactor0_profile : frontierFactor0.asymProfile = frontierFactorProf0 :=\n  frontierNode1_profile",
                            1,
                        ),
                        None,
                        False,
                    ),
                ),
                (
                    "g6_factor0_multiline_cont",
                    _mk_lean_mut(
                        "st45_8.lean",
                        valid_g6_lean.replace(
                            "noncomputable def frontierFactor0 : PartGadget (strongPow C7 5) := frontierNode0",
                            "noncomputable def frontierFactor0 : PartGadget (strongPow C7 5) := frontierNode0\n  |> id",
                            1,
                        ),
                        None,
                        False,
                    ),
                ),
                (
                    "g6_factorProf0_multiline_cont",
                    _mk_lean_mut(
                        "st45_9.lean",
                        valid_g6_lean.replace(
                            "def frontierFactorProf0 : AsymProfile := frontierProf0",
                            "def frontierFactorProf0 : AsymProfile := frontierProf0\n  |> id",
                            1,
                        ),
                        None,
                        False,
                    ),
                ),
                (
                    "g6_body_drop_indep",
                    _mk_lean_mut(
                        "st45_10a.lean",
                        valid_g6_lean.replace(
                            "    frontierGamma6Terms frontierGamma6Terms_indep", "    frontierGamma6Terms rfl", 1
                        ),
                        None,
                        False,
                    ),
                ),
                (
                    "g6_body_drop_f3_prof",
                    _mk_lean_mut(
                        "st45_10b.lean",
                        valid_g6_lean.replace("frontierFactor3_profile,", "", 1),
                        None,
                        False,
                    ),
                ),
                (
                    "g6_body_drop_pullback_thm",
                    _mk_lean_mut(
                        "st45_10c.lean",
                        valid_g6_lean.replace("gamma6Pow4_card_le_cycleGraph7_indepNum", "fakePullbackThm", 1),
                        None,
                        False,
                    ),
                ),
                (
                    "g6_stray_part_target",
                    _mk_lean_mut(
                        "st45_11.lean",
                        valid_g6_lean + "\ntheorem frontierTarget_a_eq : frontierProf0.a = frontierCard := rfl\n",
                        None,
                        False,
                    ),
                ),
            ],
        )

        # ST-46: Negative — Non-ASCII Unicode digits rejected across ALL Lean numeric & index regexes
        expect_fail_all(
            "ST-46 negative non-ASCII Unicode digits rejected across all Lean numeric & index regexes",
            [
                ("num_arabic", _mk_lean_mut("st46_1.lean", valid_lean_src.replace("3258822357711717", "325882235771171٥", 1))),
                ("den_arabic", _mk_lean_mut("st46_2.lean", valid_lean_src.replace("1000000000000000", "100000000000000٠", 1))),
                ("base_a_arabic", _mk_lean_mut("st46_3.lean", valid_lean_src.replace("a := 367,", "a := 36٧,", 1))),
                ("prof_idx_arabic", _mk_lean_mut("st46_4.lean", valid_lean_src.replace("def frontierProf1 ", "def frontierProf١ ", 1))),
                ("node_dim_arabic", _mk_lean_mut("st46_5.lean", valid_lean_src.replace("strongPow C7 10", "strongPow C7 ١٠", 1))),
                ("pow_exp_arabic", _mk_lean_mut("st46_6.lean", valid_lean_src.replace("c7_lower_num ^ 220", "c7_lower_num ^ ٢٢٠", 1))),
                (
                    "g6_tuple_arabic",
                    _mk_lean_mut("st46_7.lean", valid_g6_lean.replace("(0, 0, 0, 0)", "(٠, 0, 0, 0)", 1), None, False),
                ),
            ],
        )

        # ST-47: Negative (B11a-b/NB-2/C-1/C-3/C-4) — Malformed JSON containers, RFC 8259 NaN/Inf, deep nesting, >100k-digit DoS
        def _mk_g6_json_mut(mut_fn):
            def _fn():
                w = _make_mini_c7_1_witness()
                w["recipe"] = {
                    "engine": "Gamma6Pow4Pullback",
                    "ops": [{"op": "base", "idx": 0}],
                    "gamma6_pow4": {
                        "factor_nodes": [0, 0, 0, 0],
                        "factor_flips": [0, 0, 0, 0],
                        "terms": [[0, 0, 0, 0]],
                    },
                }
                mut_fn(w)
                verify_witness_dict(w, enforce_frontier_floor=False)
            return _fn

        def _st47_oversized_json_str():
            w = _make_mini_c7_1_witness()
            w["N_exact"] = "9" * 100001
            verify_witness_dict(w, enforce_frontier_floor=False)

        expect_fail_all(
            "ST-47 negative (B11a-b/C-1/C-3/C-4) malformed JSON containers, NaN/Inf, deep nesting, & >100k-digit DoS",
            [
                ("fnodes_null", _mk_g6_json_mut(lambda w: w["recipe"]["gamma6_pow4"].__setitem__("factor_nodes", None))),
                ("fnodes_int", _mk_g6_json_mut(lambda w: w["recipe"]["gamma6_pow4"].__setitem__("factor_nodes", 42))),
                ("fflips_null", _mk_g6_json_mut(lambda w: w["recipe"]["gamma6_pow4"].__setitem__("factor_flips", None))),
                ("fflips_str", _mk_g6_json_mut(lambda w: w["recipe"]["gamma6_pow4"].__setitem__("factor_flips", "0101"))),
                ("fflips_int", _mk_g6_json_mut(lambda w: w["recipe"]["gamma6_pow4"].__setitem__("factor_flips", 123))),
                ("oversized_json_str", _st47_oversized_json_str),
                (
                    "oversized_lean_nat",
                    _mk_lean_mut("st47_bignat.lean", valid_lean_src.replace("3258822357711717", "9" * 100001, 1)),
                ),
                ("json_NaN", lambda: _load_json_strict('{"a": NaN}')),
                ("json_Inf", lambda: _load_json_strict('{"a": Infinity}')),
                ("json_NegInf", lambda: _load_json_strict('{"a": -Infinity}')),
                ("json_deep_nest", lambda: _load_json_strict(("[" * 2000) + ("]" * 2000))),
                ("json_deep_nest_10k", lambda: _load_json_strict(("[" * 10000) + ("]" * 10000))),
                ("json_bare_100k_int", lambda: _load_json_strict('{"N_exact": ' + ("9" * 100001) + "}")),
            ],
        )

        # ST-48: Negative (B11c/C-2) — Invalid UTF-8 & NUL-byte crash guards on JSON & Lean file paths
        def _mk_bytes_json(fname: str, payload: bytes):
            def _fn():
                p = tmp / fname
                p.write_bytes(payload)
                _load_json_file_strict(p)
            return _fn

        def _mk_bytes_lean(fname: str, payload: bytes):
            def _fn():
                p = tmp / fname
                p.write_bytes(payload)
                verify_lean_file(p, None)
            return _fn

        expect_fail_all(
            "ST-48 negative (B11c/C-2) invalid UTF-8 & NUL-byte crash guards on JSON & Lean paths",
            [
                ("json_invalid_utf8", _mk_bytes_json("st48_bad_utf8.json", b"\xff\xfe\x00invalid")),
                ("lean_invalid_utf8", _mk_bytes_lean("st48_bad_utf8.lean", b"\xff\xfe")),
                ("json_nul_byte", _mk_bytes_json("st48_nul.json", b'{"a": 1}\x00')),
                ("lean_nul_byte", _mk_bytes_lean("st48_nul.lean", b"def c7_lower_num : Nat := 1\x00\n")),
            ],
        )

        # ST-49: Negative + Positive (C01/C02) — `𝓝[≠]'"'`, `𝓝[≠]'}'`, non-ident Char literals after `]`/`×`/`⊕`, & general-lexer benign controls
        def st49():
            # General-lexer positive benign controls (quote-suffixed operators) must pass cleanly
            gen_ok = (
                "def ok_st49 (a : List Nat) (h h' h'' : 0 < a.length) : Nat :=\n"
                "  a[0]'h + a[0]'h' + a[0]'h'' + a[0]'(h)\n"
                "def ok_st49_t1 : Type := Nat ×' Nat\n"
                "def ok_st49_t2 : Type := Nat ⊕' Nat\n"
            )
            toks_ok, _ = _lex_lean4_single_pass(gen_ok)
            _check_lean_hygiene(toks_ok, "<st49_benign>")
            neg_cases = [
                ("C01_nhds_ne_dquote", "def q := 𝓝[≠]'\"'\ntheorem evil : False := sorry\n-- \""),
                ("C01_nhds_ge_dquote", "def q := 𝓝[≥]'\"'\ntheorem evil : False := sorry\n-- \""),
                ("C02_nhds_rbrace", "def q := s!\"{let _ := 𝓝[≠]'}'; (sorry : String)}\""),
                ("C01_nhds_lbrace", "def q := 𝓝[≠]'{'\ntheorem evil : False := sorry"),
                ("C01_nhds_hex22", "def q := 𝓝[≠]'\\x22'\ntheorem evil : False := sorry\n-- \""),
                ("C01_nhds_uni7d", "def q := s!\"{let _ := 𝓝[≠]'\\u007d'; (sorry : String)}\""),
                ("C01_nhds_bslash", "def q := 𝓝[≠]'\\\\'\ntheorem evil : False := sorry"),
                ("C01_nhds_space_comma", "def q := (𝓝[≠]' ','\"')\ntheorem evil : False := sorry\n-- \""),
                ("C01_nhds_zero_comma", "def q := (𝓝[≠]'0','\"')\ntheorem evil : False := sorry\n-- \""),
                ("C01_nhds_img_dquote", "def q := 𝓝[≠]'a''''\"'\ntheorem evil : False := sorry\n-- \""),
            ]
            for idx_c, (lbl, snippet) in enumerate(neg_cases):
                p_bad = tmp / f"st49_neg_{idx_c}.lean"
                p_bad.write_text(valid_lean_src + "\n" + snippet + "\n", encoding="utf-8")
                try:
                    verify_lean_file(p_bad, None)
                except VerifyError as exc:
                    if "sorry" not in str(exc):
                        raise RuntimeError(f"ST-49 sub-case {lbl!r} failed without exposing sorry: {exc}")
                    continue
                raise RuntimeError(f"ST-49 sub-case {lbl!r} unexpectedly PASSED")

        expect_pass("ST-49 positive/negative (C01/C02) 𝓝[≠] Char-literal desync guards & benign controls", st49)

        # ST-50: Negative (C03a-c) — `#s!"{...}"` & `#f!"{...}"` prefix-operator interpolated smuggling
        expect_fail_all_msg(
            "ST-50 negative (C03a-c) #s! and #f! prefix-operator interpolated smuggling",
            [
                ("C03a_hash_s_sorry", _mk_lean_check("st50_1.lean", 'def e1 := #s!"{(sorry : String)}"'), "sorry"),
                ("C03b_hash_f_sorry", _mk_lean_check("st50_2.lean", 'def e2 := #f!"{(sorry : String)}"'), "sorry"),
                (
                    "C03c_hash_s_native_decide",
                    _mk_lean_check("st50_3.lean", 'def e3 := #s!"{let _ : 1 = 1 := (by native_decide); ""}"'),
                    "native_decide",
                ),
            ],
        )

        # ST-51: Negative (M25) — Native-compiler custom-axiom smuggling (`decide +native`, `decide (config := ...)`, `bv_decide`, `reduceBool`)
        expect_fail_all(
            "ST-51 negative (M25) decide +native, decide (config := ...), bv_decide, & Lean.reduceBool/reduceNat",
            [
                (
                    "decide_plus_native",
                    _mk_lean_mut(
                        "st51_1.lean",
                        valid_lean_src.replace("nat_pow_le_of_ble rfl", "by decide +native", 1),
                    ),
                ),
                (
                    "decide_config_record",
                    _mk_lean_mut(
                        "st51_2.lean",
                        valid_lean_src.replace("by decide", "by decide (config := { native := true })", 1),
                    ),
                ),
                (
                    "decide_config_anon_ctor",
                    _mk_lean_mut(
                        "st51_3.lean",
                        valid_lean_src.replace("by decide", "by decide (config := ⟨false, true, true, false⟩)", 1),
                    ),
                ),
                (
                    "decide_neg_kernel_config",
                    _mk_lean_mut(
                        "st51_4.lean",
                        valid_lean_src.replace("by decide", "by decide -kernel (config := ⟨false, true, true, false⟩)", 1),
                    ),
                ),
                ("bv_decide", _mk_lean_check("st51_5.lean", "theorem t : True := by bv_decide")),
                ("bv_decide_q", _mk_lean_check("st51_6.lean", "theorem t : True := by bv_decide?")),
                ("bv_check", _mk_lean_check("st51_7.lean", 'theorem t : True := by bv_check "a.lrat"')),
                ("reduceBool", _mk_lean_check("st51_8.lean", "def rb : Bool := Lean.reduceBool true")),
                ("reduceNat", _mk_lean_check("st51_9.lean", "def rn : Nat := Lean.reduceNat 0")),
                ("nativeEqTrue", _mk_lean_check("st51_10.lean", "def neq := Lean.Meta.nativeEqTrue")),
                ("DecideConfig", _mk_lean_check("st51_11.lean", "def cfg : DecideConfig := ⟨false, true, true, false⟩")),
                ("decide_bang", _mk_lean_check("st51_12.lean", "theorem t : True := by decide!")),
            ],
        )

        # ST-52: Negative + Linear-Time ReDoS (B-1/B-2/M26/C05a-d/C08/C09) — `declModifiers`, `coinductive`, `alias`, `noncomputable section`
        def st52():
            # B-2 linear-time ReDoS check on 5,000 repeated `private ` tokens
            t0 = time.process_time()
            _index_all_decls(("private " * 5000) + "foo")
            dt = time.process_time() - t0
            if dt >= 0.10:
                raise RuntimeError(f"ST-52 B-2 ReDoS guard exceeded 0.10s CPU: {dt:.3f}s")

            neg_muts = [
                (
                    "C05a_private_nonrec_num",
                    valid_lean_src.replace("def c7_lower_num", "private nonrec def c7_lower_num", 1),
                ),
                (
                    "C05b_protected_nonrec_frontier",
                    valid_lean_src.replace("theorem c7_lower_frontier", "protected nonrec theorem c7_lower_frontier", 1),
                ),
                (
                    "C05c_noncomp_nonrec_num",
                    valid_lean_src.replace("def c7_lower_num", "noncomputable nonrec def c7_lower_num", 1),
                ),
                (
                    "C05d_private_meta_num",
                    valid_lean_src.replace("def c7_lower_num", "private meta def c7_lower_num", 1),
                ),
                (
                    "M26_private_nonrec_frontier",
                    valid_lean_src.replace("theorem c7_lower_frontier", "private nonrec theorem c7_lower_frontier", 1),
                ),
                (
                    "C09_coinductive_dup_num",
                    valid_lean_src + "\ncoinductive Foo.c7_lower_num : Prop where\n  | mk : Foo.c7_lower_num\n",
                ),
                (
                    "C08_alias_dup_num",
                    valid_lean_src + "\nnamespace Shadow\ndef fake_n : ℕ := 999\nalias c7_lower_num := fake_n\nend Shadow\n",
                ),
                (
                    "C08_alias_lr_dup_frontier",
                    valid_lean_src + "\nnamespace Shadow\nalias ⟨c7_lower_frontier, _⟩ := Iff.rfl\nend Shadow\n",
                ),
                (
                    "noncomputable_section_num",
                    valid_lean_src.replace(
                        "def c7_lower_num : ℕ := 3258822357711717",
                        "noncomputable section\ndef c7_lower_num : ℕ := 3258822357711717\nend",
                        1,
                    ),
                ),
                (
                    "meta_section_frontier",
                    valid_lean_src.replace(
                        "theorem c7_lower_frontier :",
                        "meta section\ntheorem c7_lower_frontier :",
                        1,
                    ).replace("\nend ShannonC7\n", "\nend\nend ShannonC7\n", 1),
                ),
            ]
            for idx_m, (lbl, txt) in enumerate(neg_muts):
                p = tmp / f"st52_{idx_m}.lean"
                p.write_text(txt, encoding="utf-8")
                try:
                    verify_lean_file(p, None)
                except VerifyError:
                    continue
                raise RuntimeError(f"ST-52 sub-case {lbl!r} unexpectedly PASSED")

        expect_pass(
            "ST-52 positive/negative (B-1/B-2/M26/C05/C08/C09) declModifiers, coinductive, alias, noncomp section, & ReDoS",
            st52,
        )

        # ST-53: Negative (C04a/C04b/M27) — `variable`/`include`/typeclass vacuous forgery & `c7_lower_frontier` proof-body tampering
        expect_fail_all(
            "ST-53 negative (C04a/C04b/M27) variable/include/typeclass forgery & c7_lower_frontier body tampering",
            [
                (
                    "C04a_M27_var_include_false",
                    _mk_lean_mut(
                        "st53_1.lean",
                        valid_lean_src.replace(
                            "theorem c7_lower_frontier :\n"
                            "    (c7_lower_num : ℝ) / (c7_lower_den : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7) :=\n"
                            "  le_shannonCapacity_of_nat_pow_pi (by decide) c7_lower_den_pos frontierCard_le_indepNum frontier_pow_le",
                            "section\nvariable (h : False)\ninclude h\ntheorem c7_lower_frontier :\n"
                            "    (c7_lower_num : ℝ) / (c7_lower_den : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7) :=\n"
                            "  False.elim h\nend",
                            1,
                        ),
                    ),
                ),
                (
                    "C04b_var_typeclass_no_include",
                    _mk_lean_mut(
                        "st53_2.lean",
                        valid_lean_src.replace(
                            "theorem c7_lower_frontier :",
                            "class Bogus : Prop where f : False\nsection\nvariable [h : Bogus]\ntheorem c7_lower_frontier :",
                            1,
                        ).replace("\nend ShannonC7\n", "\nend\nend ShannonC7\n", 1),
                    ),
                ),
                (
                    "top_level_variable_false",
                    _mk_lean_mut(
                        "st53_3.lean",
                        "variable (h : False)\n" + valid_lean_src,
                    ),
                ),
                (
                    "var_in_combinator",
                    _mk_lean_mut(
                        "st53_4.lean",
                        valid_lean_src.replace(
                            "theorem c7_lower_frontier :",
                            "variable (h : False) in\ntheorem c7_lower_frontier :",
                            1,
                        ),
                    ),
                ),
                (
                    "frontier_body_missing_le_shannon",
                    _mk_lean_mut(
                        "st53_5.lean",
                        valid_lean_src.replace(
                            "le_shannonCapacity_of_nat_pow_pi (by decide) c7_lower_den_pos frontierCard_le_indepNum frontier_pow_le",
                            "fake_thm c7_lower_den_pos frontierCard_le_indepNum frontier_pow_le",
                            1,
                        ),
                    ),
                ),
                (
                    "frontier_body_missing_pow_le",
                    _mk_lean_mut(
                        "st53_6.lean",
                        valid_lean_src.replace(
                            "le_shannonCapacity_of_nat_pow_pi (by decide) c7_lower_den_pos frontierCard_le_indepNum frontier_pow_le",
                            "le_shannonCapacity_of_nat_pow_pi (by decide) c7_lower_den_pos frontierCard_le_indepNum rfl",
                            1,
                        ),
                    ),
                ),
            ],
        )

        # ST-54: Negative (C06/C11) — `#exit`, `#guard*`, & Lean v4.32.2 simproc/propagator/meta commands
        st54_specs: list[tuple[str, str, str]] = [
            ("C06_hash_exit", "#exit", "#exit"),
            ("C11_hash_guard", "#guard (1 + 1 == 2)", "#guard"),
            ("C11_hash_guard_expr", "#guard_expr 1 = 1", "#guard_expr"),
            ("C11_hash_guard_msgs", "#guard_msgs in #check 1", "#guard_msgs"),
            ("C11_hash_guard_hyp", "#guard_hyp h : True", "#guard_hyp"),
            ("C11_hash_guard_target", "#guard_target = True", "#guard_target"),
            ("C11_simproc", "simproc mySimp (1 + 1) := fun _ => pure .continue", "simproc"),
            ("C11_dsimproc", "dsimproc myDSimp (1 + 1) := fun _ => pure .continue", "dsimproc"),
            ("C11_cbv_simproc", "cbv_simproc myCbv (1 + 1) := fun _ => pure .continue", "cbv_simproc"),
            ("C11_grind_propagator", "grind_propagator down myProp (Nat.add) := fun _ => pure ()", "grind_propagator"),
            ("C11_declare_simp_like", "declare_simp_like_tactic mySimp", "declare_simp_like_tactic"),
            ("C11_unif_hint", "unif_hint (x : Nat) where |- x =?= x", "unif_hint"),
            ("C11_register_tactic_tag", 'register_tactic_tag myTag "doc"', "register_tactic_tag"),
            ("C11_omit", "omit h", "omit"),
            ("C11_with_weak_namespace", "with_weak_namespace Foo def x := 1", "with_weak_namespace"),
        ]
        expect_fail_all_msg(
            "ST-54 negative (C06/C11) #exit, #guard*, & Lean v4.32.2 simproc/propagator/meta commands",
            [
                (lbl, _mk_lean_check(f"st54_{i}.lean", code), req)
                for i, (lbl, code, req) in enumerate(st54_specs)
            ],
        )

        # ST-55: Negative (C07a-d/NB-1) — Same-line & `nonrec` body absorption on PartGadget & Gamma6 + leading-zero ref
        expect_fail_all(
            "ST-55 negative (C07a-d/NB-1) same-line & nonrec body absorption + Gamma6 leading-zero ref",
            [
                (
                    "C07a_same_line_def_part",
                    _mk_lean_mut(
                        "st55_1.lean",
                        valid_lean_src.replace(
                            "  have h1 := frontierNode10.card_le_indepNum\n"
                            "  rw [frontierNode10_profile, frontierTarget_a_eq] at h1\n"
                            "  exact h1",
                            "  exact fake_proof def decoy := (frontierNode10, frontierNode10_profile, frontierTarget_a_eq)",
                            1,
                        ),
                    ),
                ),
                (
                    "C07a_paren_no_space_def_part",
                    _mk_lean_mut(
                        "st55_2.lean",
                        valid_lean_src.replace(
                            "  have h1 := frontierNode10.card_le_indepNum\n"
                            "  rw [frontierNode10_profile, frontierTarget_a_eq] at h1\n"
                            "  exact h1",
                            "  exact (fake_proof)def decoy := (frontierNode10, frontierNode10_profile, frontierTarget_a_eq)",
                            1,
                        ),
                    ),
                ),
                (
                    "C07b_next_line_nonrec_part",
                    _mk_lean_mut(
                        "st55_3.lean",
                        valid_lean_src.replace(
                            "  have h1 := frontierNode10.card_le_indepNum\n"
                            "  rw [frontierNode10_profile, frontierTarget_a_eq] at h1\n"
                            "  exact h1",
                            "  exact fake_proof\nnonrec def decoy := (frontierNode10, frontierNode10_profile, frontierTarget_a_eq)",
                            1,
                        ),
                    ),
                ),
                (
                    "C07_same_line_hash_check",
                    _mk_lean_mut(
                        "st55_4.lean",
                        valid_lean_src.replace(
                            "  have h1 := frontierNode10.card_le_indepNum\n"
                            "  rw [frontierNode10_profile, frontierTarget_a_eq] at h1\n"
                            "  exact h1",
                            "  exact fake_proof #check (frontierNode10, frontierNode10_profile, frontierTarget_a_eq)",
                            1,
                        ),
                    ),
                ),
                (
                    "C07c_same_line_def_g6",
                    _mk_lean_mut(
                        "st55_5.lean",
                        valid_g6_lean.replace(
                            "theorem frontierFactor0_profile : frontierFactor0.asymProfile = frontierFactorProf0 :=\n  frontierNode0_profile",
                            "theorem frontierFactor0_profile : frontierFactor0.asymProfile = frontierFactorProf0 := rfl def decoy := frontierNode0_profile",
                            1,
                        ),
                        None,
                        False,
                    ),
                ),
                (
                    "C07d_next_line_nonrec_g6",
                    _mk_lean_mut(
                        "st55_6.lean",
                        valid_g6_lean.replace(
                            "theorem frontierFactor0_profile : frontierFactor0.asymProfile = frontierFactorProf0 :=\n  frontierNode0_profile",
                            "theorem frontierFactor0_profile : frontierFactor0.asymProfile = frontierFactorProf0 := rfl\nnonrec def decoy := frontierNode0_profile",
                            1,
                        ),
                        None,
                        False,
                    ),
                ),
                (
                    "NB1_g6_leading_zero_ref",
                    _mk_lean_mut(
                        "st55_7.lean",
                        valid_g6_lean.replace(
                            "def frontierFactorProf0 : AsymProfile := frontierProf0",
                            "def frontierFactorProf0 : AsymProfile := frontierProf00",
                            1,
                        ),
                        None,
                        False,
                    ),
                ),
            ],
        )

        # ST-56: Negative (C10) — Namespace tampering (`namespace Bogus`, nested `ShannonC7.Extra`, root namespace, `mutual`)
        expect_fail_all(
            "ST-56 negative (C10) namespace tampering (Bogus, nested ShannonC7.Extra, root namespace, mutual)",
            [
                (
                    "C10_namespace_bogus",
                    _mk_lean_mut(
                        "st56_1.lean",
                        valid_lean_src.replace("namespace ShannonC7", "namespace Bogus").replace(
                            "end ShannonC7", "end Bogus"
                        ),
                    ),
                ),
                (
                    "C10_nested_extra_around_frontier",
                    _mk_lean_mut(
                        "st56_2.lean",
                        valid_lean_src.replace(
                            "theorem c7_lower_frontier :",
                            "namespace Extra\ntheorem c7_lower_frontier :",
                            1,
                        ).replace("\nend ShannonC7\n", "\nend Extra\nend ShannonC7\n", 1),
                    ),
                ),
                (
                    "C10_no_namespace_at_all",
                    _mk_lean_mut(
                        "st56_3.lean",
                        valid_lean_src.replace("namespace ShannonC7\n\n", "").replace("\nend ShannonC7\n", "\n"),
                    ),
                ),
                (
                    "C10_mutual_around_num",
                    _mk_lean_mut(
                        "st56_4.lean",
                        valid_lean_src.replace(
                            "def c7_lower_num : ℕ := 3258822357711717",
                            "mutual\ndef c7_lower_num : ℕ := 3258822357711717\nend",
                            1,
                        ),
                    ),
                ),
                (
                    "shadow_imported_cycleGraph",
                    _mk_lean_mut(
                        "st56_5.lean",
                        valid_lean_src.replace(
                            "namespace ShannonC7\n",
                            "namespace ShannonC7\ndef SimpleGraph.cycleGraph (n : ℕ) : SimpleGraph Unit := ⊥\n",
                            1,
                        ),
                    ),
                ),
                (
                    "shadow_imported_le_shannon",
                    _mk_lean_mut(
                        "st56_6.lean",
                        valid_lean_src.replace(
                            "namespace ShannonC7\n",
                            "namespace ShannonC7\ntheorem le_shannonCapacity_of_nat_pow_pi : True := trivial\n",
                            1,
                        ),
                    ),
                ),
            ],
        )

        # ST-57: Positive + Negative (R1/NB-3) — `𝓝[≠]'a'''...` dual lexer desync guards, general-lexer benign `a[0]'h*`, & O(N) primes
        def st57():
            gen_ok = (
                "def ok_st57_idx (a : List Nat) (b : List Nat) (h h' h'' h''' h'''' : 0 < a.length) : Nat :=\n"
                "  a[0]'h + a[0]'h' + a[0]'h'' + a[0]'h''' + a[0]'h'''' + a[0]'(h) + (a[0]'h''') + a[b[0]]'h'\n"
                "def ok_st57_list (a : List Nat) (h''' : 0 < a.length) : List Nat := [a[0]'h''']\n"
                "def ok_st57_prod : Type := Nat ×' Nat\n"
                "def ok_st57_sum : Type := Nat ⊕' Nat\n"
                "def ok_st57_img (f : Nat → Nat) (s : Set Nat) := f '' s\n"
                "def ok_st57_trace_str : String :=\n"
                "  let trace := 1\n"
                "  let _ := trace\n"
                '  "hello {not interp"\n'
            )
            toks_ok, _ = _lex_lean4_single_pass(gen_ok)
            _check_lean_hygiene(toks_ok, "<st57_benign>")

            # Strict O(N) benchmark on `a[0]'h` + 10,000 primes (both general lexer & verify_lean_file Stage 7B rejection)
            perf_snippet = "def ok_st57_many_q := a[0]'h" + ("'" * 10000) + "\n"
            t0 = time.process_time()
            toks_p, _ = _lex_lean4_single_pass(perf_snippet)
            _check_lean_hygiene(toks_p, "<st57_perf>")
            dt = time.process_time() - t0
            if dt >= 0.05:
                raise RuntimeError(f"ST-57 O(N) 10,000-prime general-lexer guard exceeded 0.05s CPU: {dt:.4f}s")
            p_perf = tmp / "st57_perf.lean"
            p_perf.write_text(
                valid_lean_src.replace("\nend ShannonC7\n", f"\n{perf_snippet}\nend ShannonC7\n", 1),
                encoding="utf-8",
            )
            t0 = time.process_time()
            try:
                verify_lean_file(p_perf, None)
                raise RuntimeError("ST-57 10,000-prime `a[0]'h...` unexpectedly passed Closed Lexical Whitelist")
            except VerifyError as exc:
                if "quote punctuation" not in str(exc):
                    raise RuntimeError(f"ST-57 10,000-prime unexpected rejection: {exc}")
            dt_v = time.process_time() - t0
            if dt_v >= 0.05:
                raise RuntimeError(f"ST-57 O(N) 10,000-prime verify_lean_file guard exceeded 0.05s CPU: {dt_v:.4f}s")

            r1_neg_cases = [
                ("R1a_nhds_ne_img_sorry", "def q := 𝓝[≠]'a'''sorry", "sorry"),
                ("R1b_nhds_ne_img_s_interp", 'def q := 𝓝[≠]\'a\'\'\'s!"{(sorry : String)}"', "sorry"),
                (
                    "R1c_nhds_ne_img_s_native",
                    'def q := 𝓝[≠]\'a\'\'\'s!"{let _ : 1 = 1 := (by native_decide); ""}"',
                    "native_decide",
                ),
                ("R1e_nhds_ne_img_f_interp", 'def q := 𝓝[≠]\'a\'\'\'f!"{(sorry : String)}"', "sorry"),
                ("R1d_nhds_ne_img_raw_str", 'def q := 𝓝[≠]\'a\'\'\'r"\\"\ntheorem evil : False := sorry\n-- "', "sorry"),
                (
                    "R1f_nhds_ne_img_raw_hash",
                    'def q := 𝓝[≠]\'a\'\'\'r#"\\"#\ntheorem evil : False := sorry\n-- "#',
                    "sorry",
                ),
                ("R1g_nhds_ne_img_paren", "def q := 𝓝[≠]'a'''(sorry)", "sorry"),
                ("R1h_nhds_ne_img_fq_sorry", "def q := 𝓝[≠]'a'''«sorry»", "sorry"),
                ("R1i_nhds_ne_img_hash_s", 'def q := 𝓝[≠]\'a\'\'\'#s!"{(sorry : String)}"', "sorry"),
                ("R1j_nhds_ge_img_sorry", "def q := 𝓝[≥]'a'''sorry", "sorry"),
                ("R1j_nhds_le_img_sorry", "def q := 𝓝[≤]'a'''sorry", "sorry"),
                ("R1j_nhds_gt_img_sorry", "def q := 𝓝[>]'a'''sorry", "sorry"),
                ("R1j_nhds_lt_img_sorry", "def q := 𝓝[<]'a'''sorry", "sorry"),
                ("R1k_nhds_top_img_sorry", "def q := 𝓝[(⊤ : Set Char)]'a'''sorry", "sorry"),
                ("R1k_nhds_nested_brack", "def q := 𝓝[a[0]]'a'''sorry", "sorry"),
                ("R1k_nhds_top_fq_sorry", "def q := 𝓝[(⊤ : Set Char)]'a'''«sorry»", "sorry"),
                (
                    "R1k_nhds_top_raw_str",
                    'def q := 𝓝[(⊤ : Set Char)]\'a\'\'\'r"\\"\ntheorem evil : False := sorry\n-- "',
                    "sorry",
                ),
                ("R1l_nhds_direct_sorry", "def q := 𝓝[≠]'a'sorry", "sorry"),
                ("R1l_poly_rx_sorry", "def q := R[X]'a'sorry", "sorry"),
                ("R1l_prod_quote_unclosed", "def q := Nat ×'\"'\ntheorem evil : False := sorry\ndef q2 := '\"'", "Unclosed"),
                ("R1l_prod_dblq_sorry", "def q := Nat ×''a'sorry", "sorry"),
                ("R1l_prod_sp_sorry", "def q := Nat ×' 'a'sorry", "sorry"),
            ]
            for idx_c, (lbl, snippet, req) in enumerate(r1_neg_cases):
                p_bad = tmp / f"st57_neg_{idx_c}.lean"
                p_bad.write_text(valid_lean_src + "\n" + snippet + "\n", encoding="utf-8")
                try:
                    verify_lean_file(p_bad, None)
                except VerifyError as exc:
                    if req not in str(exc):
                        raise RuntimeError(f"ST-57 sub-case {lbl!r} masked: got {str(exc)!r}, expected {req!r}")
                    continue
                raise RuntimeError(f"ST-57 sub-case {lbl!r} unexpectedly PASSED")

        expect_pass("ST-57 positive/negative (R1/NB-3) 𝓝[≠]'a'''... dual lexer desync guards & benign a[0]'h*", st57)

        # ST-58: Negative + ReDoS (R2/M29/R5) — Typeclass instance hijacking & named `instance (priority := high)`
        def st58():
            # Strict O(N) ReDoS checks on `optNamedPrio` in `_ALL_DECLS_RE`
            t0 = time.process_time()
            _index_all_decls(("instance (priority := high) " * 2000) + "foo")
            dt1 = time.process_time() - t0
            if dt1 >= 0.05:
                raise RuntimeError(f"ST-58 ReDoS optNamedPrio guard exceeded 0.05s CPU: {dt1:.4f}s")
            t0 = time.process_time()
            _index_all_decls("instance " + ("(" * 5000))
            dt2 = time.process_time() - t0
            if dt2 >= 0.05:
                raise RuntimeError(f"ST-58 ReDoS unclosed-paren guard exceeded 0.05s CPU: {dt2:.4f}s")

            orig_frontier = (
                "theorem c7_lower_frontier :\n"
                "    (c7_lower_num : ℝ) / (c7_lower_den : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7) :=\n"
                "  le_shannonCapacity_of_nat_pow_pi (by decide) c7_lower_den_pos frontierCard_le_indepNum frontier_pow_le"
            )
            forged_frontier = (
                "theorem c7_lower_frontier :\n"
                "    (c7_lower_num : ℝ) / (c7_lower_den : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7) := by\n"
                "  have _ := @le_shannonCapacity_of_nat_pow_pi (Fin 7)\n"
                "  have _ := c7_lower_den_pos\n"
                "  have _ := frontierCard_le_indepNum\n"
                "  have _ := frontier_pow_le\n"
                "  exact trivial"
            )
            st58_cases = [
                (
                    "R2a_M29a_local_inst_LE_Real",
                    valid_lean_src.replace(
                        orig_frontier,
                        "local instance (priority := high) : LE ℝ where le _ _ := True\n" + forged_frontier,
                        1,
                    ),
                    "local",
                ),
                (
                    "R2b_M29b_attribute_local_inst",
                    valid_lean_src.replace(
                        orig_frontier,
                        "def _bogusLEReal : LE ℝ := ⟨fun _ _ => True⟩\n"
                        "attribute [local instance 99999] _bogusLEReal\n"
                        + forged_frontier,
                        1,
                    ),
                    "attribute",
                ),
                (
                    "R2b_M29c_attr_on_def_local_inst",
                    valid_lean_src.replace(
                        orig_frontier,
                        "@[local instance 99999, reducible] def _bogusLEReal : LE ℝ := ⟨fun _ _ => True⟩\n"
                        + forged_frontier,
                        1,
                    ),
                    "@[",
                ),
                (
                    "R2_default_instance",
                    valid_lean_src.replace(
                        "\nend ShannonC7\n",
                        "\n@[default_instance] def _bogusDefInst : LE ℝ := ⟨fun _ _ => True⟩\nend ShannonC7\n",
                        1,
                    ),
                    "default_instance",
                ),
                (
                    "R5a_named_inst_prio_num",
                    valid_lean_src.replace(
                        "\nend ShannonC7\n",
                        "\ninstance (priority := high) c7_lower_num : Inhabited ℕ := ⟨999⟩\nend ShannonC7\n",
                        1,
                    ),
                    "duplicate/shadowed declaration of `c7_lower_num`",
                ),
                (
                    "R5b_named_inst_prio_shannon",
                    valid_lean_src.replace(
                        "\nend ShannonC7\n",
                        "\ninstance (priority := high) shannonCapacity : Inhabited ℕ := ⟨999⟩\nend ShannonC7\n",
                        1,
                    ),
                    "shannonCapacity",
                ),
                (
                    "R2c_local_inst_HDiv",
                    valid_lean_src.replace(
                        "\nend ShannonC7\n",
                        "\nlocal instance (priority := high) : HDiv ℝ ℝ ℝ where hDiv _ _ := 0\nend ShannonC7\n",
                        1,
                    ),
                    "local",
                ),
                (
                    "R2f_local_inst_OfNat7",
                    valid_lean_src.replace(
                        "\nend ShannonC7\n",
                        "\nlocal instance (priority := high) : OfNat ℕ 7 where ofNat := 100\nend ShannonC7\n",
                        1,
                    ),
                    "local",
                ),
                (
                    "R2d_local_inst_NatCast",
                    valid_lean_src.replace(
                        "\nend ShannonC7\n",
                        "\nlocal instance (priority := high) : NatCast ℝ where natCast _ := 0\nend ShannonC7\n",
                        1,
                    ),
                    "local",
                ),
                (
                    "R2e_M29d_local_inst_LE_Nat",
                    valid_lean_src.replace(
                        "\nend ShannonC7\n",
                        "\nlocal instance (priority := high) : LE ℕ where le _ _ := True\nend ShannonC7\n",
                        1,
                    ),
                    "local",
                ),
                (
                    "R2_scoped_inst_LE_Real",
                    valid_lean_src.replace(
                        "\nend ShannonC7\n",
                        "\nscoped instance : LE ℝ where le _ _ := True\nend ShannonC7\n",
                        1,
                    ),
                    "scoped",
                ),
                (
                    "R2_bare_instance",
                    valid_lean_src.replace(
                        "\nend ShannonC7\n",
                        "\ninstance : Inhabited Unit := ⟨()⟩\nend ShannonC7\n",
                        1,
                    ),
                    "instance",
                ),
            ]
            for idx_c, (lbl, txt, req) in enumerate(st58_cases):
                p = tmp / f"st58_{idx_c}.lean"
                p.write_text(txt, encoding="utf-8")
                try:
                    verify_lean_file(p, None)
                except VerifyError as exc:
                    if req not in str(exc):
                        raise RuntimeError(f"ST-58 sub-case {lbl!r} masked: got {str(exc)!r}, expected {req!r}")
                    continue
                raise RuntimeError(f"ST-58 sub-case {lbl!r} unexpectedly PASSED")

        expect_pass("ST-58 negative+ReDoS (R2/M29/R5) typeclass instance hijacking & named optNamedPrio", st58)

        # ST-59: Negative (R3/NB-1) — Same-line `open`/`export`/`local`/`scoped`/`assert_not_*`/`#import_path` body boundaries
        orig_card_body = (
            "  have h1 := frontierNode10.card_le_indepNum\n"
            "  rw [frontierNode10_profile, frontierTarget_a_eq] at h1\n"
            "  exact h1"
        )
        orig_front_body = (
            "  le_shannonCapacity_of_nat_pow_pi (by decide) c7_lower_den_pos frontierCard_le_indepNum frontier_pow_le"
        )
        orig_g6_f0 = "theorem frontierFactor0_profile : frontierFactor0.asymProfile = frontierFactorProf0 :=\n  frontierNode0_profile"
        expect_fail_all_msg(
            "ST-59 negative (R3/NB-1) same-line open/export/local/scoped/assert_not_*/#import_path body boundaries",
            [
                (
                    "R3b_frontier_same_line_open",
                    _mk_lean_mut(
                        "st59_1.lean",
                        valid_lean_src.replace(
                            orig_front_body,
                            "  trivial open ShannonC7 (le_shannonCapacity_of_nat_pow_pi c7_lower_den_pos frontierCard_le_indepNum frontier_pow_le)",
                            1,
                        ),
                    ),
                    "c7_lower_frontier body missing reference(s)",
                ),
                (
                    "R3b_frontier_same_line_export",
                    _mk_lean_mut(
                        "st59_2.lean",
                        valid_lean_src.replace(
                            orig_front_body,
                            "  trivial export ShannonC7 (le_shannonCapacity_of_nat_pow_pi c7_lower_den_pos frontierCard_le_indepNum frontier_pow_le)",
                            1,
                        ),
                    ),
                    "c7_lower_frontier body missing reference(s)",
                ),
                (
                    "R3a_card_le_same_line_open",
                    _mk_lean_mut(
                        "st59_3.lean",
                        valid_lean_src.replace(
                            orig_card_body,
                            "  exact trivial open ShannonC7 (frontierNode10 frontierNode10_profile frontierTarget_a_eq)",
                            1,
                        ),
                    ),
                    "frontierCard_le_indepNum body missing reference(s)",
                ),
                (
                    "R3a_card_le_same_line_export",
                    _mk_lean_mut(
                        "st59_4.lean",
                        valid_lean_src.replace(
                            orig_card_body,
                            "  exact trivial export ShannonC7 (frontierNode10 frontierNode10_profile frontierTarget_a_eq)",
                            1,
                        ),
                    ),
                    "frontierCard_le_indepNum body missing reference(s)",
                ),
                (
                    "R3_card_le_same_line_local",
                    _mk_lean_mut(
                        "st59_5.lean",
                        valid_lean_src.replace(
                            orig_card_body,
                            "  exact trivial local def decoy := (frontierNode10, frontierNode10_profile, frontierTarget_a_eq)",
                            1,
                        ),
                    ),
                    "frontierCard_le_indepNum body missing reference(s)",
                ),
                (
                    "R3_card_le_same_line_scoped",
                    _mk_lean_mut(
                        "st59_6.lean",
                        valid_lean_src.replace(
                            orig_card_body,
                            "  exact trivial scoped def decoy := (frontierNode10, frontierNode10_profile, frontierTarget_a_eq)",
                            1,
                        ),
                    ),
                    "frontierCard_le_indepNum body missing reference(s)",
                ),
                (
                    "R3c_g6_factor0_same_line_open",
                    _mk_lean_mut(
                        "st59_7.lean",
                        valid_g6_lean.replace(
                            orig_g6_f0,
                            "theorem frontierFactor0_profile : frontierFactor0.asymProfile = frontierFactorProf0 := rfl open ShannonC7 (frontierNode0_profile)",
                            1,
                        ),
                        None,
                        False,
                    ),
                    "malformed or unbound",
                ),
                (
                    "R3c_g6_factor0_same_line_export",
                    _mk_lean_mut(
                        "st59_8.lean",
                        valid_g6_lean.replace(
                            orig_g6_f0,
                            "theorem frontierFactor0_profile : frontierFactor0.asymProfile = frontierFactorProf0 := rfl export ShannonC7 (frontierNode0_profile)",
                            1,
                        ),
                        None,
                        False,
                    ),
                    "malformed or unbound",
                ),
                (
                    "NB1_same_line_assert_not_exists",
                    _mk_lean_mut(
                        "st59_9.lean",
                        valid_lean_src.replace(
                            orig_card_body,
                            "  exact trivial assert_not_exists frontierNode10 frontierNode10_profile frontierTarget_a_eq",
                            1,
                        ),
                    ),
                    "frontierCard_le_indepNum body missing reference(s)",
                ),
                (
                    "NB1_same_line_assert_not_imported",
                    _mk_lean_mut(
                        "st59_10.lean",
                        valid_lean_src.replace(
                            orig_card_body,
                            "  exact trivial assert_not_imported frontierNode10 frontierNode10_profile frontierTarget_a_eq",
                            1,
                        ),
                    ),
                    "frontierCard_le_indepNum body missing reference(s)",
                ),
                (
                    "NB1_same_line_hash_import_path",
                    _mk_lean_mut(
                        "st59_11.lean",
                        valid_lean_src.replace(
                            orig_card_body,
                            "  exact trivial #import_path frontierNode10 frontierNode10_profile frontierTarget_a_eq",
                            1,
                        ),
                    ),
                    "frontierCard_le_indepNum body missing reference(s)",
                ),
            ],
        )

        # ST-60: Negative (R4) — Declaration-synthesizing attributes, `structure`+`export`, & `SimpleGraph`/`Real` shadowing
        def _mk_in_ns(fname: str, payload: str):
            return _mk_lean_mut(fname, valid_lean_src.replace("\nend ShannonC7\n", f"\n{payload}\nend ShannonC7\n", 1))

        expect_fail_all_msg(
            "ST-60 negative (R4) decl-synthesizing attributes, structure+export, & SimpleGraph/Real shadowing",
            [
                (
                    "R4a_full_ns_to_additive_cycleGraph",
                    _mk_in_ns(
                        "st60_1.lean",
                        "namespace SimpleGraph\n@[to_additive cycleGraph] def myMulBogusGraph (_ : ℕ) : _root_.SimpleGraph (Fin (2 * 2)) := ⊥\nend SimpleGraph",
                    ),
                    "to_additive",
                ),
                (
                    "R4a_bare_to_additive_cycleGraph",
                    _mk_in_ns("st60_2.lean", "@[to_additive cycleGraph] def myMulBogusGraph (_ : ℕ) : Nat := 0"),
                    "to_additive",
                ),
                (
                    "R4_to_dual",
                    _mk_in_ns("st60_3.lean", "@[to_dual c7_lower_num] def myDualSrc : ℕ := 0"),
                    "to_dual",
                ),
                (
                    "R4c_mk_iff_inductive",
                    _mk_in_ns("st60_4.lean", "@[mk_iff c7_lower_num] inductive DummyInd : Prop where | mk : DummyInd"),
                    "mk_iff",
                ),
                (
                    "R4c_mk_iff_def",
                    _mk_in_ns("st60_5.lean", "@[mk_iff c7_lower_num] def dummyMkIff : Prop := True"),
                    "mk_iff",
                ),
                (
                    "R4_simps",
                    _mk_in_ns("st60_6.lean", "@[simps] structure AuxSimps where x : ℕ"),
                    "simps",
                ),
                (
                    "R4d_struct_export",
                    _mk_in_ns("st60_7.lean", "structure AuxExpS where\n  c7_lower_num : ℕ\nexport AuxExpS (c7_lower_num)"),
                    "export",
                ),
                (
                    "R4_ns_SimpleGraph",
                    _mk_in_ns("st60_8.lean", "namespace SimpleGraph\ndef auxSg : ℕ := 0\nend SimpleGraph"),
                    "SimpleGraph",
                ),
                (
                    "R4_def_SimpleGraph",
                    _mk_in_ns("st60_9.lean", "def SimpleGraph := Unit"),
                    "SimpleGraph",
                ),
                (
                    "R4_def_Real",
                    _mk_in_ns("st60_10.lean", "def Real := Unit"),
                    "Real",
                ),
            ],
        )

        # ST-61: Positive + Negative — Mathematically Closed 7-Gate Positive Whitelist across all 7 dimensions
        def st61():
            # Positive Control A: Synthetic Gamma6Pow4Pullback d=20 with ALL whitelisted constructs
            g6_full = (
                "import ShannonC7.ValidTuple\n"
                "import ShannonC7.HeteroLayered\n"
                "import ShannonC7.Decimal\n\n"
                + valid_g6_lean.replace(
                    "namespace ShannonC7\n\n",
                    "namespace ShannonC7\n\n"
                    "set_option linter.unusedFintypeInType false in\n"
                    "structure AuxOk where\n"
                    "  x : ℕ\n\n"
                    "abbrev AuxOkAlias := AuxOk\n\n"
                    "namespace PartGadget\n"
                    "variable {α : Type*}\n"
                    "end PartGadget\n\n",
                    1,
                ).replace(
                    "theorem frontier_pow_le :",
                    "set_option exponentiation.threshold 4096 in\ntheorem frontier_pow_le :",
                    1,
                )
            )
            p_g6_ok = tmp / "st61_g6_ok.lean"
            p_g6_ok.write_text(g6_full, encoding="utf-8")
            res_g6 = verify_lean_file(p_g6_ok, valid_g6_summary, enforce_frontier_floor=False)
            if res_g6["dim"] != 20 or res_g6["n_ops"] != 2 or res_g6["n_terms"] != 5:
                raise RuntimeError(f"ST-61 Gamma6 positive control mismatch: {res_g6}")

            # Positive Control B: Real ShannonC7/FrontierLower.lean (read-only)
            real_frontier = pathlib.Path(__file__).resolve().parents[2] / "ShannonC7" / "FrontierLower.lean"
            if real_frontier.is_file():
                res_real = verify_lean_file(real_frontier, None, enforce_frontier_floor=True)
                if (
                    res_real["num"] != 3258822357711717
                    or res_real["den"] != 1000000000000000
                    or res_real["dim"] != 220
                    or res_real["n_ops"] != 11
                    or res_real["n_terms"] != 0
                ):
                    raise RuntimeError(f"ST-61 real FrontierLower.lean mismatch: {res_real}")

            # Negative Matrix: 68 sub-cases spanning all 7 Closed Positive Whitelist dimensions
            def in_ns(snippet: str) -> str:
                return valid_lean_src.replace("\nend ShannonC7\n", f"\n{snippet}\nend ShannonC7\n", 1)

            def at_root(snippet: str) -> str:
                return valid_lean_src + "\n" + snippet + "\n"

            wl_neg_cases: list[tuple[str, str]] = [
                # Dim 1: Unlisted / misplaced top-level commands (31 cases)
                ("cmd_col0_unknown", at_root("bogus_future_cmd foo")),
                ("cmd_line1_indented_unknown", "  bogus_line1_cmd foo\n" + valid_lean_src),
                ("decl_root_prefix", in_ns("def _root_.Int.s! (_ : ℤ) (a : String) : String := a")),
                ("decl_fq_name", in_ns("def ZDay.«s!» (a : String) : String := a")),
                ("cmd_indented_local", in_ns("  local def indentedLocal : Nat := 0")),
                ("cmd_indented_unknown", at_root("  bogus_indented_cmd bar")),
                ("cmd_indented_def", in_ns("  def indentedDef : Nat := 0")),
                ("cmd_same_line_chained_def", in_ns("def chainA : Nat := 1 def chainB : Nat := 2")),
                (
                    "cmd_same_line_after_end",
                    valid_lean_src.replace("end ShannonC7", "end ShannonC7 bogus_future_cmd foo", 1),
                ),
                (
                    "cmd_same_line_after_opt_in",
                    in_ns("set_option exponentiation.threshold 4096 in bogus_future_cmd foo"),
                ),
                (
                    "cmd_same_line_open_after_end",
                    valid_lean_src.replace("end ShannonC7", "end ShannonC7 open ShannonC7", 1),
                ),
                ("cmd_deriving_top", in_ns("deriving instance Repr for AsymProfile")),
                ("cmd_deriving_struct", in_ns("structure AuxDeriv where\n  x : Nat\nderiving Repr")),
                ("cmd_module", "module\n" + valid_lean_src),
                ("cmd_prelude", "prelude\n" + valid_lean_src),
                ("cmd_class", in_ns("class AuxClass (α : Type) where\n  v : α")),
                ("cmd_inductive", in_ns("inductive AuxInd\n  | mk")),
                ("cmd_universe", in_ns("universe u")),
                ("cmd_example", in_ns("example : True := trivial")),
                ("cmd_open", in_ns("open ShannonC7")),
                ("cmd_section", in_ns("section AuxSec\nend AuxSec")),
                ("cmd_variable_in_shannon", in_ns("variable (x : Nat)")),
                ("cmd_lemma", in_ns("lemma auxLemma : True := trivial")),
                ("cmd_irreducible_def", in_ns("irreducible_def auxIrred : Nat := 1")),
                ("cmd_sudo", in_ns("sudo def auxSudo : Nat := 1")),
                ("cmd_add_decl_doc", in_ns('/-- doc -/\nadd_decl_doc c7_lower_num')),
                ("cmd_compile_def_pct", in_ns("compile_def% c7_lower_num")),
                ("cmd_prange_open", in_ns("def p := *...open")),
                ("cmd_prange_set_option", in_ns('def p := ""...set_option')),
                (
                    "cmd_where_local_inst",
                    in_ns("def auxWhere : Nat := 1 where\n  @[local instance] inst : LE Nat := ⟨fun _ _ => True⟩"),
                ),
                ("cmd_noncomp_theorem", in_ns("noncomputable theorem auxNcThm : True := trivial")),
                # Dim 2: Unlisted modifiers on non-cert helper decls (7 cases)
                ("mod_public", in_ns("public def auxPub : Nat := 1")),
                ("mod_private", in_ns("private def auxPriv : Nat := 1")),
                ("mod_protected", in_ns("protected def auxProt : Nat := 1")),
                ("mod_nonrec", in_ns("nonrec def auxNonrec : Nat := 1")),
                ("mod_meta", in_ns("meta def auxMeta : Nat := 1")),
                ("mod_partial", in_ns("partial def auxPart (n : Nat) : Nat := auxPart n")),
                ("mod_unsafe", in_ns("unsafe def auxUnsafe : Nat := 1")),
                # Dim 3: Unlisted @[...] attributes (7 cases)
                ("attr_custom", in_ns("@[custom_attr] def auxCustom : Nat := 1")),
                ("attr_reducible", in_ns("@[reducible] def auxRed : Nat := 1")),
                ("attr_simp", in_ns("@[simp] theorem auxSimp : True := trivial")),
                ("attr_simp_ws", in_ns("@[ simp ] theorem auxSimpWs : True := trivial")),
                ("attr_extern", in_ns('@[extern "foo"] def auxExt : Nat := 1')),
                ("attr_implemented_by", in_ns("@[implemented_by bar] def auxImpl : Nat := 1")),
                ("attr_csimp", in_ns("@[csimp] theorem auxCsimp : True := trivial")),
                # Dim 4: Unlisted import modules & import forms (7 cases)
                ("imp_lean_elab", "import Lean.Elab\n" + valid_lean_src),
                ("imp_std_bv", "import Std.Tactic.BVDecide\n" + valid_lean_src),
                ("imp_mathlib_topo", "import Mathlib.Topology.Basic\n" + valid_lean_src),
                ("imp_init", "import Init\n" + valid_lean_src),
                ("imp_all_shannon", "import all ShannonC7.ValidTuple\n" + valid_lean_src),
                ("imp_private_shannon", "import private ShannonC7.ValidTuple\n" + valid_lean_src),
                ("imp_midfile_shannon", in_ns("import ShannonC7.ValidTuple")),
                # Dim 5: Unlisted or inline set_option (6 cases)
                ("opt_pp_all", in_ns("set_option pp.all true")),
                ("opt_maxHeartbeats", in_ns("set_option maxHeartbeats 0")),
                ("opt_linter_unusedVars", in_ns("set_option linter.unusedVariables false in\ndef auxOpt : Nat := 1")),
                ("opt_autoImplicit", in_ns("set_option autoImplicit true in\ndef auxAuto : Nat := 1")),
                ("opt_inline_term", in_ns("def auxInlineOpt : Nat := set_option exponentiation.threshold 4096 in 1")),
                ("opt_unscoped_allowed_key", in_ns("set_option exponentiation.threshold 4096")),
                # Dim 6: Unlisted #cmd hash commands (5 cases)
                ("hash_check", in_ns("#check Nat")),
                ("hash_print", in_ns("#print Nat")),
                ("hash_import_path", in_ns("#import_path ShannonC7.ValidTuple")),
                ("hash_synth", in_ns("#synth LE Nat")),
                ("hash_where", in_ns("#where")),
                # Dim 7: Unlisted namespace names (5 cases)
                ("ns_foo", in_ns("namespace Foo\ndef auxFoo : Nat := 1\nend Foo")),
                ("ns_simplegraph", in_ns("namespace SimpleGraph\ndef auxSg : Nat := 1\nend SimpleGraph")),
                ("ns_real", in_ns("namespace Real\ndef auxReal : Nat := 1\nend Real")),
                ("ns_shannon_evil", in_ns("namespace ShannonC7.Evil\ndef auxEvil : Nat := 1\nend ShannonC7.Evil")),
                ("ns_partgadget_at_root", at_root("namespace PartGadget\ndef auxPg : Nat := 1\nend PartGadget")),
            ]
            for idx_w, (lbl, txt) in enumerate(wl_neg_cases):
                p_bad = tmp / f"st61_neg_{idx_w}.lean"
                p_bad.write_text(txt, encoding="utf-8")
                try:
                    verify_lean_file(p_bad, None)
                except VerifyError:
                    continue
                raise RuntimeError(f"ST-61 Closed Whitelist sub-case {lbl!r} unexpectedly PASSED")

        expect_pass(
            "ST-61 positive/negative Mathematically Closed 7-Gate Positive Whitelist (real FrontierLower, Gamma6 d=20, 68 neg)",
            st61,
        )

        # ST-62: Positive + Negative (R6) — Core `Init` PRange `*...`/`...`/`<...` dot-contiguity & field-projection `.s!`
        def st62():
            gen_ok = (
                'def ok_r6_1 := Foo.r"\\""\n'
                'def ok_r6_2 := Foo.r#"\\""\n'
                'def ok_r6_3 := f `r"\\""\n'
                'def ok_r6_4 := Foo.s! "{ sorry }"\n'
                'def ok_r6_5 := f `s! "{ sorry }"\n'
                'def ok_r6_6 := (mkS).s! "{ sorry }"\n'
            )
            toks_ok, _ = _lex_lean4_single_pass(gen_ok)
            _check_lean_hygiene(toks_ok, "<st62_benign>")

            r6_neg_cases = [
                ("R6a_star_dots_s_sorry", 'def p := *...s!"{(sorry : String)}"', "sorry"),
                ("R6b_star_dots_raw_sorry", 'def p := *...r"\\"\ndef q : False := sorry\n-- "', "sorry"),
                (
                    "R6c_star_dots_s_native",
                    'def p := *...s!"{let _ : 1 = 1 := (by native_decide); ""}"',
                    "native_decide",
                ),
                ("R6d_str_dots_s_sorry", 'def p := ""...s!"{(sorry : String)}"', "sorry"),
                ("R6d_str_dots_raw_sorry", 'def p := ""...r"\\"\ndef q : False := sorry\n-- "', "sorry"),
                ("R6e_lt_dots_s_sorry", 'def p := ""<...s!"{(sorry : String)}"', "sorry"),
                ("R6f_star_dots_f_sorry", 'def p := *...f!"{(sorry : String)}"', "sorry"),
                ("R6_dbl_dot_raw_sorry", 'def p := a..r"\\"\ndef q : False := sorry\n-- "', "sorry"),
                ("R6_dbl_backtick_raw_sorry", 'def p := ``r"\\"\ndef q : False := sorry\n-- "', "sorry"),
                (
                    "R6_paren_field_dot_s_brace",
                    'def t5 := (mkS).s! "{"\ntheorem evil : False := sorry\ndef t6 := "}"',
                    "sorry",
                ),
                (
                    "R6_brack_field_dot_s_brace",
                    'def t5 := [mkS][0].s! "{"\ntheorem evil : False := sorry\ndef t6 := "}"',
                    "sorry",
                ),
                (
                    "R6_cdot_field_dot_s_brace",
                    'def t5 := (·.s! "{")\ntheorem evil : False := sorry\ndef t6 := "}"',
                    "sorry",
                ),
                # C-1: All 9 operator/pipe-dot live-compiling exploits
                (
                    "C1_coloneq_dot_s_sorry",
                    'def z1 :=.s! "{"\ntheorem evil : False := sorry\ndef z2 := "}"',
                    "sorry",
                ),
                (
                    "C1_coloneq_dot_s_native",
                    'def z1 :=.s! "{"\ntheorem evil : 1 = 1 := by native_decide\ndef z2 := "}"',
                    "native_decide",
                ),
                (
                    "C1_fatarrow_dot_s_sorry",
                    'def z1 := fun _ =>.s! "{"\ntheorem evil : False := sorry\ndef z2 := "}"',
                    "sorry",
                ),
                (
                    "C1_pipe_dot_s_sorry",
                    'def z1 := mkZ |>.s! "{"\ntheorem evil : False := sorry\ndef z2 := "}"',
                    "sorry",
                ),
                (
                    "C1_slash_dot_s_sorry",
                    'def z1 := 1/.s! "{"\ntheorem evil : False := sorry\ndef z2 := "}"',
                    "sorry",
                ),
                (
                    "C1_plus_dot_s_sorry",
                    'def z1 := 1+.s! "{"\ntheorem evil : False := sorry\ndef z2 := "}"',
                    "sorry",
                ),
                (
                    "C1_mul_dot_s_sorry",
                    'def z1 := 1*.s! "{"\ntheorem evil : False := sorry\ndef z2 := "}"',
                    "sorry",
                ),
                (
                    "C1_coloneq_dot_f_sorry",
                    'def z1 :=.f! "{"\ntheorem evil : False := sorry\ndef z2 := "}"',
                    "sorry",
                ),
                (
                    "C1_coloneq_dot_println_sorry",
                    'def z1 :=.println! "{"\ntheorem evil : False := sorry\ndef z2 := "}"',
                    "sorry",
                ),
                # M30a-d: All 4 postfix/Unicode field-projection exploits
                (
                    "M30a_abs_dot_s_local_inst",
                    'def z1 : String := |(1 : ℤ)|.s! "{"\nlocal instance (priority := high) _forgedLE : LE ℝ := ⟨fun _ _ => True⟩\n-- " } "',
                    "local",
                ),
                (
                    "M30b_compl_dot_s_sorry",
                    'def z1 : String := C7ᶜ.s! "{"\ntheorem evil : False := sorry\n-- " } "',
                    "sorry",
                ),
                (
                    "M30c_norm_dot_f_native",
                    'def z1 : String := ‖x‖.f! "{"\ntheorem evil : 1 = 1 := by native_decide\n-- " } "',
                    "native_decide",
                ),
                (
                    "M30d_inv_dot_println_axiom",
                    'def z1 : String := (1 : ℝ)⁻¹.println! "{"\naxiom bogus : False\n-- " } "',
                    "axiom",
                ),
            ]
            for idx_c, (lbl, snippet, req) in enumerate(r6_neg_cases):
                p_bad = tmp / f"st62_neg_{idx_c}.lean"
                p_bad.write_text(valid_lean_src + "\n" + snippet + "\n", encoding="utf-8")
                try:
                    verify_lean_file(p_bad, None)
                except VerifyError as exc:
                    if req not in str(exc):
                        raise RuntimeError(f"ST-62 sub-case {lbl!r} masked: got {str(exc)!r}, expected {req!r}")
                    continue
                raise RuntimeError(f"ST-62 sub-case {lbl!r} unexpectedly PASSED")

        expect_pass("ST-62 positive/negative (R6/C-1/M30) PRange dot-contiguity & operator/postfix .s!/.f!/.println! guards", st62)

        # ST-63: Negative (R7 + R8) — `sorry`-injecting tactics & pure `abbrev`/`structure`/`theorem` contract gaps
        expect_fail_all_msg(
            "ST-63 negative (R7+R8) sorry-injecting tactics & pure abbrev/structure/optional-theorem contract gaps",
            [
                ("R7_stop", _mk_lean_check("st63_1.lean", "theorem cheat : False := by stop exact trivial"), "stop"),
                (
                    "R7_impossible",
                    _mk_lean_check("st63_2.lean", "theorem cheat : False := by impossible by exact id"),
                    "impossible",
                ),
                ("R7_apply_q", _mk_lean_check("st63_3.lean", "theorem cheat : 5 ≤ 1 := by apply?"), "apply?"),
                ("R7_exact_q", _mk_lean_check("st63_4.lean", "theorem cheat : True := by exact? +all"), "exact?"),
                ("R7_calc_q", _mk_lean_check("st63_5.lean", "theorem cheat : (5 : ℕ) ≤ 1 := by calc?"), "calc?"),
                ("R7_hint", _mk_lean_check("st63_6.lean", "theorem cheat : False := by hint"), "hint"),
                (
                    "R7_plausible",
                    _mk_lean_check("st63_7.lean", "theorem cheat : False := by plausible"),
                    "plausible",
                ),
                (
                    "R7_sorry_if_sorry",
                    _mk_lean_check("st63_8.lean", "theorem cheat : False := by sorry_if_sorry"),
                    "sorry_if_sorry",
                ),
                ("R7_conv_q", _mk_lean_check("st63_9.lean", "theorem cheat : 1 = 1 := by conv?"), "conv?"),
                (
                    "R7_default_or_ofNonempty",
                    _mk_lean_check("st63_10.lean", "def cheat : False := default_or_ofNonempty%"),
                    "default_or_ofNonempty",
                ),
                ("R7_sleep", _mk_lean_check("st63_11.lean", "theorem dos : True := by sleep 1000"), "sleep"),
                ("R8_abbrev_Nat", _mk_in_ns("st63_12.lean", "abbrev Nat := ℝ"), "Nat"),
                (
                    "R8_structure_SimpleGraph",
                    _mk_in_ns("st63_13.lean", "structure SimpleGraph where\n  x : ℕ"),
                    "SimpleGraph",
                ),
                (
                    "R8_malformed_bpz_v1",
                    _mk_in_ns("st63_14.lean", "theorem c7_lower_gt_bpz_v1 : True := trivial"),
                    "malformed `c7_lower_gt_bpz_v1` signature",
                ),
                (
                    "R8_malformed_bpz_v2",
                    _mk_in_ns("st63_15.lean", "theorem c7_lower_gt_bpz_v2 : True := trivial"),
                    "malformed `c7_lower_gt_bpz_v2` signature",
                ),
                (
                    "R8_malformed_tandon",
                    _mk_in_ns("st63_16.lean", "theorem c7_lower_gt_tandon : True := trivial"),
                    "malformed `c7_lower_gt_tandon` signature",
                ),
            ],
        )

        # ST-64: Positive + Negative (R9/M32) — `∎` U+220E, `try?`, `grind`/`sym`/`lia`/`grobner`/`mvcgen'`/`compactness`/`closedness`, `eval%`, & bare `?`-suggestion tactics
        def st64():
            p_ok = tmp / "st64_benign.lean"
            st64_extras = (
                "def ok_q_proj1 (l : List Nat) := l.getElem? 0\n"
                "def ok_q_proj2 (m : List Nat) := m.find? (· == 0)\n"
                "def ok_eval_proj1 (t : Nat) := t.eval\n"
                "def ok_eval_proj2 (t : Nat) := t.eval % 2\n"
            )
            p_ok.write_text(
                valid_lean_src.replace("\nend ShannonC7\n", f"\n{st64_extras}\nend ShannonC7\n", 1),
                encoding="utf-8",
            )
            verify_lean_file(p_ok, None)

            r9_neg_cases = [
                ("R9a_qed_term", "theorem cheat : False := ∎", "∎"),
                ("R9b_qed_tactic", "theorem cheat : False := by ∎", "∎"),
                ("R9c_try_q", "theorem cheat : False := by try?", "try?"),
                ("R9e_grind_q", "theorem cheat : False := by grind?", "grind?"),
                ("R9g_grind_finish_q", "theorem cheat : False := by grind => finish?", "grind"),
                ("R9h_grind_plus_trace", "theorem cheat : False := by grind +trace", "grind"),
                (
                    "R9i_grind_config_trace",
                    "theorem cheat : False := by grind (config := { trace := true })",
                    "grind",
                ),
                ("R9j_grind_finish_trace", "theorem cheat : False := by grind => finish +trace", "grind"),
                ("R9o_grind_trace_only", "theorem cheat : False := by grind +trace only", "grind"),
                ("R9k_compactness_q", "theorem cheat : False := by compactness?", "compactness?"),
                ("R9l_closedness_q", "theorem cheat : False := by closedness?", "closedness?"),
                ("R9m_compactness_trace", "theorem cheat : False := by compactness +trace", "compactness"),
                ("R9n_closedness_trace", "theorem cheat : False := by closedness +trace", "closedness"),
                ("R9_useSorry", "def cfg := { useSorry := true }", "useSorry"),
                ("R9_eval_pct", "def x : Nat := eval% (2 ^ 10)", "eval%"),
                ("R9_sym_trace_finish", "theorem cheat : False := by sym +trace => finish", "sym"),
                ("R9_lia_trace", "theorem cheat : False := by lia +trace", "lia"),
                ("R9_cutsat_trace", "theorem cheat : False := by cutsat +trace", "cutsat"),
                ("R9_grind_order_trace", "theorem cheat : False := by grind_order +trace", "grind_order"),
                ("R9_grind_linarith_trace", "theorem cheat : False := by grind_linarith +trace", "grind_linarith"),
                ("R9_grobner_trace", "theorem cheat : False := by grobner +trace", "grobner"),
                ("R9_mvcgen_prime", "theorem cheat : False := by mvcgen' with finish +trace", "mvcgen'"),
                ("R9_by_elabq", "def x : Nat := by_elabq pure default", "by_elabq"),
                ("R9_run_tacq", "theorem t : True := by run_tacq g => pure ()", "run_tacq"),
                ("R9_bare_simp_q", "theorem t : True := by simp?", "simp?"),
                ("R9_bare_by_q", "theorem t : True := by? trivial", "by?"),
                ("R9_bare_linarith_qbang", "theorem t : True := by linarith?!", "linarith?!"),
                ("M32_mstop", "theorem t : True := by mstop", "mstop"),
                ("M32_msorry", "theorem t : True := by msorry", "msorry"),
                ("M32_try_suggestions", "theorem t : True := by try_suggestions", "try_suggestions"),
                ("M32_suggestions", "theorem t : True := by suggestions", "suggestions"),
            ]
            for idx_c, (lbl, snippet, req) in enumerate(r9_neg_cases):
                p_bad = tmp / f"st64_neg_{idx_c}.lean"
                p_bad.write_text(valid_lean_src + "\n" + snippet + "\n", encoding="utf-8")
                try:
                    verify_lean_file(p_bad, None)
                except VerifyError as exc:
                    if req not in str(exc):
                        raise RuntimeError(f"ST-64 sub-case {lbl!r} masked: got {str(exc)!r}, expected {req!r}")
                    continue
                raise RuntimeError(f"ST-64 sub-case {lbl!r} unexpectedly PASSED")

        expect_pass(
            "ST-64 positive/negative (R9/M32) ∎, try?, grind/sym/lia/grobner/mvcgen'/compactness/closedness, eval%, & ?-tactics",
            st64,
        )

        # ST-65: Positive + Negative (R10/M31 + M33) — Tactic focusing-dot `.open`/`.set_option`/`.sorry` & Unicode `«ℕ»`/`«ℝ»`/`«ℤ»`/`«ℚ»` shadowing
        def st65():
            p_ok = tmp / "st65_benign.lean"
            st65_extras = (
                "def ok_st65_1 (x : Nat) := x.open\n"
                "def ok_st65_2 (Foo : Nat) := Foo.set_option\n"
                "def ok_st65_3 := `open\n"
                "def ok_st65_4 (t : Nat) := t.eval\n"
            )
            p_ok.write_text(
                valid_lean_src.replace("\nend ShannonC7\n", f"\n{st65_extras}\nend ShannonC7\n", 1),
                encoding="utf-8",
            )
            verify_lean_file(p_ok, None)

            st65_neg_cases = [
                ("R10a_dot_open", "theorem t : True := by\n  .open Nat in trivial", "open"),
                (
                    "R10b_dot_setopt",
                    "theorem t : True := by\n  .set_option maxHeartbeats 100000 in trivial",
                    "set_option",
                ),
                ("R10c_brace_dot_open", "theorem t : True := by {.open Nat in trivial}", "open"),
                (
                    "R10d_semi_dot_setopt",
                    "theorem t : True := by\n  skip; .set_option pp.all true in trivial",
                    "set_option",
                ),
                ("M31_semi_contig_dot_open", "theorem t : True := by skip;.open Classical in trivial", "open"),
                (
                    "M31_semi_contig_dot_setopt",
                    "theorem t : True := by skip;.set_option maxHeartbeats 100000 in trivial",
                    "set_option",
                ),
                ("R10_dot_sorry", "theorem t : False := by\n  .sorry", "sorry"),
                ("R10_dot_native_decide", "theorem t : 1 = 1 := by\n  .native_decide", "native_decide"),
                ("R10_dot_decide_native", "theorem t : 1 = 1 := by\n  .decide +native", "decide +"),
                ("R10_dot_stop", "theorem t : False := by\n  .stop", "stop"),
                ("M33_abbrev_fq_N", "abbrev «ℕ» := ℤ", "ℕ"),
                ("M33_abbrev_fq_R", "abbrev «ℝ» := ℤ", "ℝ"),
                ("M33_abbrev_fq_Z", "abbrev «ℤ» := Nat", "ℤ"),
                ("M33_abbrev_fq_Q", "abbrev «ℚ» := Nat", "ℚ"),
                ("M33_abbrev_fq_C", "abbrev «ℂ» := Nat", "ℂ"),
                ("M33_abbrev_fq_P", "abbrev «ℙ» := Nat", "ℙ"),
            ]
            for idx_c, (lbl, snippet, req) in enumerate(st65_neg_cases):
                p_bad = tmp / f"st65_neg_{idx_c}.lean"
                txt = valid_lean_src.replace("\nend ShannonC7\n", f"\n{snippet}\nend ShannonC7\n", 1)
                p_bad.write_text(txt, encoding="utf-8")
                try:
                    verify_lean_file(p_bad, None)
                except VerifyError as exc:
                    if req not in str(exc):
                        raise RuntimeError(f"ST-65 sub-case {lbl!r} masked: got {str(exc)!r}, expected {req!r}")
                    continue
                raise RuntimeError(f"ST-65 sub-case {lbl!r} unexpectedly PASSED")

        expect_pass(
            "ST-65 positive/negative (R10/M31+M33) tactic focusing-dot .open/.set_option/.sorry & «ℕ»/«ℝ»/«ℤ»/«ℚ» shadowing",
            st65,
        )

        # ST-66: Negative (R11a-b) — Exponential DAG/power algorithmic-complexity DoS bounds (< 0.25s CPU each)
        def st66():
            # R11a-1: k=20 JSON witness (dim = 2^20 = 1,048,576)
            ops_k20 = [{"op": "base", "idx": 0}] + [{"op": "prodStd", "i": k, "j": k} for k in range(20)]
            w_r11a = {
                "schema_version": "1.0",
                "witness_id": "r11a_dos",
                "graph": "C7",
                "final_dim": 1 << 20,
                "N_exact": "1",
                "c7_lower_num": "1",
                "c7_lower_den": "1",
                "sharp_last_digit": False,
                "base_gadgets": [
                    {
                        "dim": 1,
                        "I": [[0]],
                        "ports": [],
                        "X": [],
                        "claimed_profile": {"a": 1, "b": 0, "c": 0, "d": 0, "h": 0, "v": 0},
                    }
                ],
                "recipe": {"engine": "PartGadgetDAG", "ops": ops_k20, "target_node": 20},
            }
            t0 = time.process_time()
            try:
                verify_witness_dict(w_r11a, enforce_frontier_floor=False)
                raise RuntimeError("ST-66 R11a k=20 JSON unexpectedly PASSED")
            except VerifyError as exc:
                dt = time.process_time() - t0
                if "10000" not in str(exc):
                    raise RuntimeError(f"ST-66 R11a unexpected error: {exc}")
                if dt >= 0.25:
                    raise RuntimeError(f"ST-66 R11a exceeded 0.25s CPU: {dt:.4f}s")

            # R11a-2: k=20 JSON with spoofed final_dim=1 (forces _replay_recipe guard)
            w_r11a_spoof = dict(w_r11a)
            w_r11a_spoof["final_dim"] = 1
            t0 = time.process_time()
            try:
                verify_witness_dict(w_r11a_spoof, enforce_frontier_floor=False)
                raise RuntimeError("ST-66 R11a spoofed final_dim unexpectedly PASSED")
            except VerifyError as exc:
                dt = time.process_time() - t0
                if "MAX_VERIFIER_DIM" not in str(exc):
                    raise RuntimeError(f"ST-66 R11a spoof unexpected error: {exc}")
                if dt >= 0.25:
                    raise RuntimeError(f"ST-66 R11a spoof exceeded 0.25s CPU: {dt:.4f}s")

            # R11a-3: Direct MAX_POW_BITS guard before num**dim
            t0 = time.process_time()
            try:
                _check_exact_frontier_bounds(
                    10 ** 1000, 10 ** 1000, 5000, 1, require_sharp=False, enforce_frontier_floor=False, label="R11_pow"
                )
                raise RuntimeError("ST-66 R11_pow unexpectedly PASSED")
            except VerifyError as exc:
                dt = time.process_time() - t0
                if "MAX_POW_BITS" not in str(exc):
                    raise RuntimeError(f"ST-66 R11_pow unexpected error: {exc}")
                if dt >= 0.10:
                    raise RuntimeError(f"ST-66 R11_pow exceeded 0.10s CPU: {dt:.4f}s")

            # R11b: k=20 Lean file (dim = 5 * 2^20 = 5,242,880)
            lines_r11b = [
                "namespace ShannonC7",
                "def frontierBaseProfile : AsymProfile := { a := 367, b := 8, c := 367, d := 322, h := 19, v := 26, hba := by decide, hdhv := by decide }",
                "noncomputable def basePart5D : PartGadget (strongPow C7 5) := PartGadget.ofHeteroGadget baseHetero5D",
                "theorem basePart5D_asymProfile_eq : basePart5D.asymProfile = frontierBaseProfile := by rfl",
                "def frontierProf0 : AsymProfile := frontierBaseProfile",
                "noncomputable def frontierNode0 : PartGadget (strongPow C7 5) := basePart5D",
                "theorem frontierNode0_profile : frontierNode0.asymProfile = frontierProf0 := basePart5D_asymProfile_eq",
            ]
            d_cur = 5
            for k in range(1, 21):
                lines_r11b.append(f"def frontierProf{k} : AsymProfile := frontierProf{k - 1}.prodAligned frontierProf{k - 1}")
                lines_r11b.append(
                    f"noncomputable def frontierNode{k} : PartGadget (strongPow C7 {d_cur * 2}) := "
                    f"(frontierNode{k - 1}.prodStd frontierNode{k - 1}).mapIso (strongPowAddEquiv C7 {d_cur} {d_cur}).symm"
                )
                lines_r11b.append(f"theorem frontierNode{k}_profile : frontierNode{k}.asymProfile = frontierProf{k} := rfl")
                d_cur *= 2
            lines_r11b.extend(
                [
                    "def frontierCard : ℕ := 1",
                    "theorem frontierTarget_a_eq : frontierProf20.a = frontierCard := rfl",
                    f"theorem frontierCard_le_indepNum : frontierCard ≤ (strongPowPi (SimpleGraph.cycleGraph 7) {d_cur}).indepNum := by",
                    "  have h1 := frontierNode20.card_le_indepNum",
                    "  rw [frontierNode20_profile, frontierTarget_a_eq] at h1",
                    "  exact h1",
                    "def c7_lower_num : ℕ := 3",
                    "def c7_lower_den : ℕ := 1",
                    "theorem c7_lower_den_pos : 0 < c7_lower_den := by decide",
                    f"theorem frontier_pow_le : c7_lower_num ^ {d_cur} ≤ c7_lower_den ^ {d_cur} * frontierCard := nat_pow_le_of_ble rfl",
                    "theorem c7_lower_frontier : (c7_lower_num : ℝ) / (c7_lower_den : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7) :=",
                    "  le_shannonCapacity_of_nat_pow_pi (by decide) c7_lower_den_pos frontierCard_le_indepNum frontier_pow_le",
                    "end ShannonC7",
                ]
            )
            p_r11b = tmp / "st66_r11b.lean"
            p_r11b.write_text("\n".join(lines_r11b) + "\n", encoding="utf-8")
            t0 = time.process_time()
            try:
                verify_lean_file(p_r11b, None, enforce_frontier_floor=False)
                raise RuntimeError("ST-66 R11b k=20 Lean unexpectedly PASSED")
            except VerifyError as exc:
                dt = time.process_time() - t0
                if "MAX_VERIFIER_DIM" not in str(exc):
                    raise RuntimeError(f"ST-66 R11b unexpected error: {exc}")
                if dt >= 0.25:
                    raise RuntimeError(f"ST-66 R11b exceeded 0.25s CPU: {dt:.4f}s")

        expect_pass(
            "ST-66 negative (R11a-b) exponential DAG/power DoS bounds rejected in <0.25s CPU",
            st66,
        )

        # ST-67: Positive + Negative — Closed Lexical Whitelist & `NB-2a` root-level decl rejections on purely benign code
        def st67():
            def in_ns(snippet: str) -> str:
                return valid_lean_src.replace("\nend ShannonC7\n", f"\n{snippet}\nend ShannonC7\n", 1)

            # Positive control: flat col-0 doc comments + plain `--` comment + CRLF + primed identifiers
            pos_src = in_ns(
                "/-! Benign flat module header -/\n"
                "/-- Benign flat decl doc comment -/\n"
                "-- plain comment allowing \"quotes\" and 'chars'\n"
                "def ok_st67_primes (hq₁' a'' : Nat) : Nat := hq₁' + a''"
            ).replace("\n", "\r\n")
            p_pos = tmp / "st67_pos_crlf.lean"
            p_pos.write_bytes(pos_src.encode("utf-8"))
            verify_lean_file(p_pos, None)

            # Negative matrix: ALL purely benign code (zero `sorry`!) rejected by Stage 7B / 7A / 1
            st67_neg_cases: list[tuple[str, str, str]] = [
                # Strings (STRING / ")
                ("plain_str", in_ns('def ok_s : String := "hello"'), "string literal"),
                ("raw_str", in_ns('def ok_r : String := r"hello"'), "string literal"),
                ("raw_hash_str", in_ns('def ok_rh : String := r#"hello"#'), "string literal"),
                ("interp_s", in_ns('def ok_si : String := s!"val={1}"'), "string literal"),
                ("interp_f", in_ns('def ok_fi : String := f!"val={1}"'), "string literal"),
                ("interp_println", in_ns('def ok_pi := println!"hi"'), "string literal"),
                # Chars & non-identifier quote punctuation (CHAR / PUNCT with ')
                ("char_a", in_ns("def ok_c : Char := 'a'"), "Char literal"),
                ("char_dquote", in_ns("def ok_cq : Char := '\"'"), "Char literal"),
                ("num_char_dquote", in_ns("def ok_nc := 0'\"'"), "Char literal"),
                ("bang_char_a", in_ns("def ok_bc := !'a'"), "Char literal"),
                ("dbl_quote_img", in_ns("def ok_img (f : Nat → Nat) (s : Set Nat) := f '' s"), "quote punctuation"),
                ("pprod_quote", in_ns("def ok_pp : Type := Nat ×' Nat"), "quote punctuation"),
                ("psum_quote", in_ns("def ok_ps : Type := Nat ⊕' Nat"), "quote punctuation"),
                ("dcomp_quote", in_ns("def ok_dc (f : {x : Nat} → Nat → Nat) (g : Nat → Nat) := f ∘' g"), "quote punctuation"),
                ("preimage_quote", in_ns("def ok_pre (f : Nat → Nat) (s : Set Nat) := f ⁻¹' s"), "quote punctuation"),
                ("psigma_quote", in_ns("def ok_sig := Σ' x : Nat, Fin x"), "quote punctuation"),
                ("rbrack_quote", in_ns("def ok_idx (a : List Nat) (h : 0 < a.length) := a[0]'h"), "quote punctuation"),
                ("num_dbl_quote", in_ns("def ok_nq := 0''"), "quote punctuation"),
                # French guillemets («/»)
                ("guil_decl", in_ns("def «foo» : Nat := 1"), "French-quoted"),
                ("guil_expr", in_ns("def ok_g : Nat := «foo»"), "French guillemet"),
                # Disallowed block / doc comments
                ("plain_block_comm", in_ns("/- benign block comment -/"), "plain block comment"),
                ("nested_block_comm", in_ns("/- outer /- inner -/ outer -/"), "plain block comment"),
                ("nested_in_doc", in_ns("/-- outer /- inner -/ outer -/"), "nested"),
                ("nested_in_moddoc", in_ns("/-! outer /- inner -/ outer -/"), "nested"),
                ("doc_inner_dashdash", in_ns("/-- -- -/\n-/"), "--"),
                ("moddoc_inner_dashdash", in_ns("/-! -- -/\n-/"), "--"),
                ("doc_boundary_dashdash_slash", in_ns("/-- --/\n-/"), "--"),
                ("doc_boundary_slashdash_slash", in_ns("/-- /-/\n-/\n-/"), "nested"),
                ("doc_with_dquote", in_ns('/-- has "quote" -/'), '"'),
                ("doc_with_squote", in_ns("/-- has 'prime' -/"), "'"),
                ("non_col0_doc", in_ns("  /-- indented doc -/"), "column 0"),
                ("non_depth0_doc", in_ns("def ok_d : Nat := (\n/-- inside parens -/\n1)"), "depth 0"),
                ("trailing_after_doc", in_ns("def ok_trail : Nat :=\n/-! ok -/ 1"), "trailing token"),
                ("malformed_doc_dash", in_ns("/---/"), "ASCII space or newline"),
                ("malformed_moddoc_dash", in_ns("/-!-/"), "ASCII space or newline"),
                ("malformed_doc_nodelim", in_ns("/--doc -/"), "ASCII space or newline"),
                # Non-ASCII whitespace & control characters
                ("tab_code", in_ns("def ok_tab : Nat := 1\t"), "U+0009"),
                ("bare_cr_code", in_ns("def ok_cr : Nat := 1\r "), "U+000D"),
                ("vt_code", in_ns("def ok_vt : Nat := 1\x0b"), "U+000B"),
                ("ff_code", in_ns("def ok_ff : Nat := 1\x0c"), "U+000C"),
                ("nbsp_code", in_ns("def ok_nbsp : Nat := 1\u00a0"), "U+00A0"),
                ("nbsp_doc", in_ns("/--\u00a0benign -/"), "U+00A0"),
                ("emspace_code", in_ns("def ok_em : Nat := 1\u2003"), "U+2003"),
                ("zwsp_code", in_ns("def ok_zwsp : Nat := 1\u200b"), "U+200B"),
                ("bom_comment", in_ns("def ok_bom : Nat := 1 -- \ufeff"), "U+FEFF"),
                ("rlo_code", in_ns("def ok_rlo : Nat := 1\u202e"), "U+202E"),
                ("nul_code", in_ns("def ok_nul : Nat := 1\x00"), "NUL"),
                # Root-level declarations outside namespace ShannonC7 (NB-2a)
                ("root_def", valid_lean_src + "\ndef rootFoo : Nat := 1\n", "root-level"),
                ("root_theorem_before", "theorem Char.toProp : True := trivial\n" + valid_lean_src, "root-level"),
                ("root_abbrev", valid_lean_src + "\nabbrev RootAbbrev := Nat\n", "root-level"),
                ("root_structure", valid_lean_src + "\nstructure RootS where\n  x : Nat\n", "root-level"),
                ("root_noncomp_def", valid_lean_src + "\nnoncomputable def rootNc : Nat := 1\n", "root-level"),
                (
                    "root_setopt_thm",
                    valid_lean_src + "\nset_option exponentiation.threshold 4096 in\ntheorem rootOpt : True := trivial\n",
                    "root-level",
                ),
            ]
            for idx_c, (lbl, txt, req) in enumerate(st67_neg_cases):
                p_bad = tmp / f"st67_neg_{idx_c}.lean"
                p_bad.write_bytes(txt.encode("utf-8"))
                try:
                    verify_lean_file(p_bad, None)
                except VerifyError as exc:
                    if req not in str(exc):
                        raise RuntimeError(f"ST-67 sub-case {lbl!r} masked: got {str(exc)!r}, expected {req!r}")
                    continue
                raise RuntimeError(f"ST-67 sub-case {lbl!r} unexpectedly PASSED")

        expect_pass(
            "ST-67 positive/negative Closed Lexical Whitelist & NB-2a root-level decl rejections on purely benign code",
            st67,
        )

        # ST-68: Positive + Negative (R12/M34/R12-PRIME/R12-DOUBLE/TRIPLE-PRIME) — Dual Defense-in-Depth lexer quote-op & `]` fixes + benign `f ∘' g`
        def st68():
            # Positive general-lexer parity control (zero FPs including `f ∘' g` and `⁻¹'o`)
            gen_ok = (
                "def ok_dcomp (f : {x : Nat} → Nat → Nat) (g : Nat → Nat) := f ∘' g\n"
                "def ok_pprod : Type := Nat ×' Nat\n"
                "def ok_psum : Type := Nat ⊕' Nat\n"
                "def ok_pre (f : Nat → Nat) (s : Set Nat) := f ⁻¹' s\n"
                "def ok_preo (f : Nat → Nat) (s : Set Nat) := f ⁻¹'o s\n"
                "def ok_sig := Σ' x : Nat, Fin x\n"
                "def ok_tprod := ∏'[x], f x\n"
                "def ok_tsum := ∑'[x], f x\n"
                "def ok_idx (a b : List Nat) (h h' h'' h''' h'''' : 0 < a.length) : Nat :=\n"
                "  a[0]'h + a[0]'h' + a[0]'h'' + a[0]'h''' + a[0]'h'''' + a[0]'(h) + a[b[0]'h]'h'\n"
                "def ok_img (f : Nat → Nat) (s : Set Nat) := f '' s\n"
                "def ok_hash (x : Nat) := #' x\n"
            )
            toks_ok, _ = _lex_lean4_single_pass(gen_ok)
            _check_lean_hygiene(toks_ok, "<st68_gen_lex>")

            # Negative Dual Defense-in-Depth matrix through verify_lean_file (Stage 2 Ambiguous or Stage 3 sorry / Stage 7A local — ZERO masking!)
            st68_neg_cases = [
                # R12 `]` fail-closed Stage 2 guards
                (
                    "R12a_rbrack_dblq_local",
                    "def d := (#[42])[0]''\"'.toProp\nlocal instance (priority := high) _forgedLE : LE ℝ := ⟨fun _ _ => True⟩\n-- \"",
                    "Ambiguous",
                ),
                (
                    "R12a_rbrack_dblq_sorry",
                    "def d := (#[42])[0]''\"'.toProp\ntheorem evil : False := sorry\n-- \"",
                    "Ambiguous",
                ),
                (
                    "R12d_rbrack_sp_sorry",
                    "def d := (#[42])[0]' '\"'.toProp\ntheorem evil : False := sorry\n-- \"",
                    "Ambiguous",
                ),
                (
                    "R12e_rbrack_nl_sorry",
                    "def d := (#[42])[0]'\n'\"'.toProp\ntheorem evil : False := sorry\n-- \"",
                    "Ambiguous",
                ),
                (
                    "R12f_rbrack_paren_sorry",
                    "def d := (#[42])[0]'('\"'.toProp)\ntheorem evil : False := sorry\n-- \"",
                    "Ambiguous",
                ),
                # R12-DOUBLE-PRIME & R12-TRIPLE-PRIME fail-closed Stage 2 guards
                (
                    "R12dp_hr_raw",
                    'def d := a[0]\'h\'r"\\""\ntheorem evil : False := sorry\n-- "',
                    "Ambiguous",
                ),
                (
                    "R12tp_hs_interp",
                    'def d := a[0]\'h\'s! "{"\ntheorem evil : False := sorry\n-- "}"',
                    "Ambiguous",
                ),
                # R12-PRIME (`h''` even trailing primes) exposing exact Stage 3 `sorry`
                (
                    "R12p_h2_nl_sorry",
                    "def d := a[0]'h''\n'\"'.toNat\ntheorem evil : False := sorry\n-- \"",
                    "sorry",
                ),
                (
                    "R12p_h2_sp_sorry",
                    "def d := a[0]'h'' '\"'.toNat\ntheorem evil : False := sorry\n-- \"",
                    "sorry",
                ),
                (
                    "R12p_h2_paren_sorry",
                    "def d := a[0]'h''('\"'.toNat)\ntheorem evil : False := sorry\n-- \"",
                    "sorry",
                ),
                # M34 / R12 greedy Unicode quote-suffixed operators exposing exact Stage 3 `sorry` / Stage 7A `local`
                (
                    "M34a_pprod_sp_local",
                    "def d : Type := Nat ×' '\"' = 'a'\nlocal instance (priority := high) _forgedLE : LE ℝ := ⟨fun _ _ => True⟩\n-- \"",
                    "local",
                ),
                (
                    "M34f_pprod_nosp_local",
                    "def d : Type := Nat ×''\"' = 'a'\nlocal instance (priority := high) _forgedLE : LE ℝ := ⟨fun _ _ => True⟩\n-- \"",
                    "local",
                ),
                (
                    "M34e_pprod_nl_sorry",
                    "def d : Type := Nat ×'\n'\"' = 'a'\ntheorem evil : False := sorry\n-- \"",
                    "sorry",
                ),
                (
                    "M34b_psum_sp_sorry",
                    "def d : Type := Nat ⊕' '\"' = 'a'\ntheorem evil : False := sorry\n-- \"",
                    "sorry",
                ),
                (
                    "M34g_psum_nosp_sorry",
                    "def d : Type := Nat ⊕''\"' = 'a'\ntheorem evil : False := sorry\n-- \"",
                    "sorry",
                ),
                (
                    "M34_dcomp_nosp_sorry",
                    "def d := f ∘''\"'\ntheorem evil : False := sorry\n-- \"",
                    "sorry",
                ),
                (
                    "M34_dcomp_sp_sorry",
                    "def d := f ∘' '\"'\ntheorem evil : False := sorry\n-- \"",
                    "sorry",
                ),
                (
                    "R12l_preimg_nosp_sorry",
                    "def d := (id : Nat → Nat) ⁻¹''\"'\ntheorem evil : False := sorry\n-- \"",
                    "sorry",
                ),
                (
                    "R12m_preimg_sp_sorry",
                    "def d := (id : Nat → Nat) ⁻¹' '\"'\ntheorem evil : False := sorry\n-- \"",
                    "sorry",
                ),
                (
                    "R12n_preimg_paren_sorry",
                    "def d := (id : Nat → Nat) ⁻¹'('\"')\ntheorem evil : False := sorry\n-- \"",
                    "sorry",
                ),
                (
                    "R12_preimg_o_sorry",
                    "def d := f ⁻¹'osorry",
                    "sorry",
                ),
                (
                    "R12_psigma_nosp_sorry",
                    "def d := Σ''\"'\ntheorem evil : False := sorry\n-- \"",
                    "sorry",
                ),
                (
                    "R12_tprod_nosp_sorry",
                    "def d := ∏''\"'\ntheorem evil : False := sorry\n-- \"",
                    "sorry",
                ),
                (
                    "R12_tsum_nosp_sorry",
                    "def d := ∑''\"'\ntheorem evil : False := sorry\n-- \"",
                    "sorry",
                ),
            ]
            for idx_c, (lbl, snippet, req) in enumerate(st68_neg_cases):
                p_bad = tmp / f"st68_neg_{idx_c}.lean"
                txt = valid_lean_src.replace("\nend ShannonC7\n", f"\n{snippet}\nend ShannonC7\n", 1)
                p_bad.write_text(txt, encoding="utf-8")
                try:
                    verify_lean_file(p_bad, None)
                except VerifyError as exc:
                    if req not in str(exc):
                        raise RuntimeError(f"ST-68 sub-case {lbl!r} masked: got {str(exc)!r}, expected {req!r}")
                    continue
                raise RuntimeError(f"ST-68 sub-case {lbl!r} unexpectedly PASSED")

        expect_pass(
            "ST-68 positive/negative (R12/M34/R12-PRIME) Dual Defense-in-Depth lexer quote-op & `]` guards + benign `f ∘' g`",
            st68,
        )

        # ST-69: Positive + Negative (R13 + NB-2b) — Dual Defense-in-Depth doc-comment ASCII ws `[ \r\n]+` & delimited `?`-projections
        def st69():
            # Negative R13 matrix (6 variants exposing exact Stage 7A `local` / Stage 3 `sorry` unmasked!)
            r13_neg_cases = [
                (
                    "R13a_doc_nbsp_local",
                    "/--\u00a0-- -/\nlocal instance (priority := high) _forgedLE : LE ℝ := ⟨fun _ _ => True⟩\n-- -/",
                    "local",
                ),
                ("R13a_doc_nbsp_sorry", "/--\u00a0-- -/\ntheorem evil : False := sorry\n-- -/", "sorry"),
                ("R13b_doc_emspace_sorry", "/--\u2003-- -/\ntheorem evil : False := sorry\n-- -/", "sorry"),
                ("R13c_doc_ff_sorry", "/--\x0c-- -/\ntheorem evil : False := sorry\n-- -/", "sorry"),
                ("R13d_moddoc_nbsp_sorry", "/-!\u00a0-- -/\ntheorem evil : False := sorry\n-- -/", "sorry"),
                ("R13e_doc_vt_sorry", "/--\x0b-- -/\ntheorem evil : False := sorry\n-- -/", "sorry"),
            ]
            for idx_c, (lbl, snippet, req) in enumerate(r13_neg_cases):
                p_bad = tmp / f"st69_r13_{idx_c}.lean"
                txt = valid_lean_src.replace("\nend ShannonC7\n", f"\n{snippet}\nend ShannonC7\n", 1)
                p_bad.write_text(txt, encoding="utf-8")
                try:
                    verify_lean_file(p_bad, None)
                except VerifyError as exc:
                    if req not in str(exc):
                        raise RuntimeError(f"ST-69 R13 sub-case {lbl!r} masked: got {str(exc)!r}, expected {req!r}")
                    continue
                raise RuntimeError(f"ST-69 R13 sub-case {lbl!r} unexpectedly PASSED")

            # Positive NB-2b control (delimited `?`-projections pass full verify_lean_file inside namespace ShannonC7)
            nb2b_pos = (
                "def ok_nb2b_paren1 := ([1, 2, 3]).getElem? 0\n"
                "def ok_nb2b_paren2 (l : List Nat) := (l ++ l).find? (· == 0)\n"
                "def ok_nb2b_brack := [1, 2, 3].getElem? 0\n"
                "def ok_nb2b_angle := (⟨1⟩ : S).foo?\n"
                "def ok_nb2b_angle2 := ⟨1⟩.foo?\n"
            )
            p_ok = tmp / "st69_nb2b_pos.lean"
            p_ok.write_text(
                valid_lean_src.replace("\nend ShannonC7\n", f"\n{nb2b_pos}\nend ShannonC7\n", 1),
                encoding="utf-8",
            )
            verify_lean_file(p_ok, None)

            # Negative NB-2b matrix (7 sub-cases strictly rejected unmasked, incl. `}` exclusion!)
            nb2b_neg_cases = [
                ("nb2b_bare_try_q", "theorem t : False := by try?", "try?"),
                ("nb2b_bare_grind_q", "theorem t : False := by grind?", "grind?"),
                ("nb2b_dot_simp_q", "theorem t : True := by .simp?", "simp?"),
                ("nb2b_semi_dot_simp_q", "theorem t : True := by { trivial }; .simp?", "simp?"),
                ("nb2b_brace_dot_simp_q", "theorem t : True := by { trivial }.simp?", "simp?"),
                ("nb2b_brace_dot_try_q", "theorem t : False := by { trivial }.try?", "try?"),
                ("nb2b_paren_try_q", "def bad_nb2b := (1).try?", "try?"),
            ]
            for idx_c, (lbl, snippet, req) in enumerate(nb2b_neg_cases):
                p_bad = tmp / f"st69_nb2b_{idx_c}.lean"
                txt = valid_lean_src.replace("\nend ShannonC7\n", f"\n{snippet}\nend ShannonC7\n", 1)
                p_bad.write_text(txt, encoding="utf-8")
                try:
                    verify_lean_file(p_bad, None)
                except VerifyError as exc:
                    if req not in str(exc):
                        raise RuntimeError(f"ST-69 NB-2b sub-case {lbl!r} masked: got {str(exc)!r}, expected {req!r}")
                    continue
                raise RuntimeError(f"ST-69 NB-2b sub-case {lbl!r} unexpectedly PASSED")

        expect_pass(
            "ST-69 positive/negative (R13+NB-2b) Dual Defense-in-Depth doc-comment ASCII ws & delimited ?-projections",
            st69,
        )

        # ST-70: Negative (R14) — Algorithmic-complexity DoS bounds (`MAX_DAG_OPS`, `MAX_POW_BITS`, `MAX_BASE_*`, `MAX_GAMMA6_TERMS`) < 0.10s CPU
        def st70():
            def check_fast_err(lbl: str, fn, req: str, limit_s: float = 0.10) -> None:
                t0 = time.process_time()
                try:
                    fn()
                except VerifyError as exc:
                    dt = time.process_time() - t0
                    if req not in str(exc):
                        raise RuntimeError(f"ST-70 {lbl} unexpected error: {exc!r} (expected {req!r})")
                    if dt >= limit_s:
                        raise RuntimeError(f"ST-70 {lbl} exceeded {limit_s}s CPU: {dt:.4f}s")
                    return
                raise RuntimeError(f"ST-70 {lbl} unexpectedly PASSED")

            # R14a-1: JSON 5,001 ops (base + 5000 x prodStd(0,0), final_dim=2)
            w_5000 = _make_mini_c7_1_witness()
            w_5000["final_dim"] = 2
            w_5000["recipe"] = {
                "engine": "PartGadgetDAG",
                "ops": [{"op": "base", "idx": 0}] + [{"op": "prodStd", "i": 0, "j": 0}] * 5000,
                "target_node": 5000,
            }
            check_fast_err("R14a_json_5000_ops", lambda: verify_witness_dict(w_5000, enforce_frontier_floor=False), "MAX_DAG_OPS")

            # R14a-2: JSON exact boundary 513 ops (MAX_DAG_OPS + 1)
            w_513 = _make_mini_c7_1_witness()
            w_513["final_dim"] = 2
            w_513["recipe"] = {
                "engine": "PartGadgetDAG",
                "ops": [{"op": "base", "idx": 0}] + [{"op": "prodStd", "i": 0, "j": 0}] * 512,
                "target_node": 512,
            }
            check_fast_err("R14a_json_513_ops", lambda: verify_witness_dict(w_513, enforce_frontier_floor=False), "MAX_DAG_OPS")

            # R14a-3: Lean file with 513 frontierProf<k> decls
            lean_513_lines = [
                "namespace ShannonC7",
                "def c7_lower_num : ℕ := 3",
                "def c7_lower_den : ℕ := 1",
                "def frontierCard : ℕ := 1",
                "def frontierProf0 : AsymProfile := frontierBaseProfile",
            ] + [f"def frontierProf{k} : AsymProfile := frontierProf0.prodAligned frontierProf0" for k in range(1, 513)] + [
                "end ShannonC7"
            ]
            p_513 = tmp / "st70_lean_513.lean"
            p_513.write_text("\n".join(lean_513_lines) + "\n", encoding="utf-8")
            check_fast_err("R14a_lean_513_ops", lambda: verify_lean_file(p_513, None, enforce_frontier_floor=False), "MAX_DAG_OPS")

            # R14b-1 & R14b-2: MAX_POW_BITS = 1_000_000 (5M bits & 1.01M boundary)
            check_fast_err(
                "R14b_pow_5M_bits",
                lambda: _check_exact_frontier_bounds(
                    (1 << 499) + 1, 1 << 499, 10_000, 1, require_sharp=False, enforce_frontier_floor=False, label="R14b"
                ),
                "MAX_POW_BITS",
            )
            check_fast_err(
                "R14b_pow_1M_edge",
                lambda: _check_exact_frontier_bounds(
                    (1 << 100) + 1, 1 << 100, 10_000, 1, require_sharp=False, enforce_frontier_floor=False, label="R14b_edge"
                ),
                "MAX_POW_BITS",
            )

            # R14c-1: MAX_BASE_WORDS = 512 (513-word base gadget)
            w_bw = _make_mini_c7_1_witness()
            w_bw["base_gadgets"][0]["I"] = [[0]] * (MAX_BASE_WORDS + 1)
            check_fast_err("R14c_base_words", lambda: verify_witness_dict(w_bw, enforce_frontier_floor=False), "MAX_BASE_WORDS")

            # R14c-2: MAX_BASE_DIM = 12 (dim-13 base gadget)
            w_bd = _make_mini_c7_1_witness()
            w_bd["base_gadgets"][0]["dim"] = MAX_BASE_DIM + 1
            check_fast_err("R14c_base_dim", lambda: verify_witness_dict(w_bd, enforce_frontier_floor=False), "MAX_BASE_DIM")

            # R14c-3: MAX_BASE_GADGETS = 4 (5 base gadgets)
            w_bg = _make_mini_c7_1_witness()
            w_bg["base_gadgets"] = [dict(w_bg["base_gadgets"][0]) for _ in range(MAX_BASE_GADGETS + 1)]
            check_fast_err("R14c_base_gadgets", lambda: verify_witness_dict(w_bg, enforce_frontier_floor=False), "MAX_BASE_GADGETS")

            # R14d-1: MAX_GAMMA6_TERMS = 1_296 (JSON 1,297 terms)
            w_g6 = _make_mini_c7_1_witness()
            w_g6["final_dim"] = 4
            w_g6["recipe"] = {
                "engine": "Gamma6Pow4Pullback",
                "ops": [{"op": "base", "idx": 0}],
                "gamma6_pow4": {
                    "factor_nodes": [0, 0, 0, 0],
                    "factor_flips": [0, 0, 0, 0],
                    "terms": [[0, 0, 0, 0]] * (MAX_GAMMA6_TERMS + 1),
                },
            }
            check_fast_err("R14d_gamma6_json_1297", lambda: verify_witness_dict(w_g6, enforce_frontier_floor=False), "MAX_GAMMA6_TERMS")

            # R14d-2: MAX_GAMMA6_TERMS = 1_296 (Lean 1,297 terms)
            g6_1297_txt = valid_g6_lean.replace(
                "def frontierGamma6Terms : List Gamma6Quad := [\n"
                "  (0, 0, 0, 0),\n"
                "  (1, 3, 3, 3),\n"
                "  (2, 1, 5, 3),\n"
                "  (3, 2, 1, 5),\n"
                "  (4, 5, 2, 1)\n"
                "]",
                "def frontierGamma6Terms : List Gamma6Quad := [\n" + ",\n".join(["  (0, 0, 0, 0)"] * (MAX_GAMMA6_TERMS + 1)) + "\n]",
                1,
            )
            p_g6_1297 = tmp / "st70_g6_1297.lean"
            p_g6_1297.write_text(g6_1297_txt, encoding="utf-8")
            check_fast_err(
                "R14d_gamma6_lean_1297",
                lambda: verify_lean_file(p_g6_1297, None, enforce_frontier_floor=False),
                "MAX_GAMMA6_TERMS",
            )

        expect_pass(
            "ST-70 negative (R14) DoS bounds (MAX_DAG_OPS/MAX_POW_BITS/MAX_BASE_*/MAX_GAMMA6_TERMS) rejected <0.10s CPU",
            st70,
        )

        # ST-71: Negative (R15) — `END_DASH`/`END_SLASH` comment-opener collision closure (`<--`, `\/-`, `//-`)
        def st71():
            # Layer 1 (Dual Defense-in-Depth lexer): exposes exact Stage 3 `sorry` unmasked!
            r15_l1_cases = [
                ("R15a_lt_dashdash_sorry", "def c1 : Id Int := do let x <--(sorry : Int); pure x", "sorry"),
                ("R15b_disj_dash_sorry", "def c2 : Prop := False \\/- (sorry : Int) = -1\n-- -/", "sorry"),
                ("R15c_subtype_dash_sorry", "def c3 := { x : Int //- (sorry : Int) = 0 }\n-- -/", "sorry"),
            ]
            for idx_c, (lbl, snippet, req) in enumerate(r15_l1_cases):
                p_bad = tmp / f"st71_l1_{idx_c}.lean"
                txt = valid_lean_src.replace("\nend ShannonC7\n", f"\n{snippet}\nend ShannonC7\n", 1)
                p_bad.write_text(txt, encoding="utf-8")
                try:
                    verify_lean_file(p_bad, None)
                except VerifyError as exc:
                    if req not in str(exc):
                        raise RuntimeError(f"ST-71 L1 sub-case {lbl!r} masked: got {str(exc)!r}, expected {req!r}")
                    continue
                raise RuntimeError(f"ST-71 L1 sub-case {lbl!r} unexpectedly PASSED")

            # Layer 2 (Closed Lexical Whitelist Stage 7B): rejects purely benign `<--`, `\/-`, `//-` (zero `sorry`)!
            r15_l2_cases = [
                ("R15a_benign", "def b1 : Id Int := do let x <--(1 : Int); pure x", "<--"),
                ("R15b_benign", "def b2 : Prop := False \\/- (1 : Int) = -1", "\\/-"),
                ("R15c_benign", "def b3 := { x : Int //- (1 : Int) = 0 }", "//-"),
            ]
            for idx_c, (lbl, snippet, req) in enumerate(r15_l2_cases):
                p_bad = tmp / f"st71_l2_{idx_c}.lean"
                txt = valid_lean_src.replace("\nend ShannonC7\n", f"\n{snippet}\nend ShannonC7\n", 1)
                p_bad.write_text(txt, encoding="utf-8")
                try:
                    verify_lean_file(p_bad, None)
                except VerifyError as exc:
                    if req not in str(exc) or "comment-ambiguous" not in str(exc):
                        raise RuntimeError(f"ST-71 L2 sub-case {lbl!r} masked: got {str(exc)!r}, expected {req!r}")
                    continue
                raise RuntimeError(f"ST-71 L2 sub-case {lbl!r} unexpectedly PASSED")

        expect_pass(
            "ST-71 negative (R15) END_DASH/END_SLASH comment-opener collision closure (<--, \\/-, //-) Layer 1 & Layer 2",
            st71,
        )

        # ST-72: Positive + Negative (R16) — Scientific-literal token-split closure preserving `v.2.1` tuple projections
        def st72():
            # Positive: chained tuple projections (`v.2.1`, `v.2.2`, `v.1.2`) pass full verify_lean_file!
            pos_proj = (
                "def _ok_proj1 (v : (Nat × Nat) × (Nat × Nat)) : Nat := v.2.1 + v.2.2 + v.1.2\n"
            )
            p_ok = tmp / "st72_pos_proj.lean"
            p_ok.write_text(
                valid_lean_src.replace("\nend ShannonC7\n", f"\n{pos_proj}end ShannonC7\n", 1),
                encoding="utf-8",
            )
            verify_lean_file(p_ok, None)

            # Negative Layer 1 (unmasked Stage 3 / Stage 7A rejections — zero masking by Stage 7B!):
            r16_l1_cases = [
                (
                    "R16_1e0_instance",
                    "def _h : Float := 1e0instance (priority := 2000) _bad : LE ℝ := ⟨fun _ _ => True⟩",
                    "instance",
                ),
                (
                    "R16_1E0_instance",
                    "def _h : Float := 1E0instance (priority := 2000) _bad : LE ℝ := ⟨fun _ _ => True⟩",
                    "instance",
                ),
                ("R16_1e0_axiom", "def _h : Float := 1e0axiom _bad : False", "axiom"),
                ("R16_1_0e0_axiom", "def _h : Float := 1.0e0axiom _bad : False", "axiom"),
                ("R16_1_dote0_axiom", "def _h : Float := 1.e0axiom _bad : False", "axiom"),
                ("R16_1_0_e0_def", "def _h : Float := 1_0e0def _bad : Nat := 1", "top-level command/modifier `def`"),
                ("R16_1e_plus_0_open", "def _h : Float := 1e+0open Classical", "open"),
                ("R16_1e_minus_0_setopt", "def _h : Float := 1e-0set_option pp.all true", "set_option"),
                (
                    "R16_0e0_local",
                    "def _h : Float := 0e0local instance _bad : LE ℝ := ⟨fun _ _ => True⟩",
                    "local",
                ),
                (
                    "R16_1_0_instance",
                    "def _h : Float := 1.0instance (priority := 2000) _bad : LE ℝ := ⟨fun _ _ => True⟩",
                    "instance",
                ),
            ]
            for idx_c, (lbl, snippet, req) in enumerate(r16_l1_cases):
                p_bad = tmp / f"st72_l1_{idx_c}.lean"
                txt = valid_lean_src.replace("\nend ShannonC7\n", f"\n{snippet}\nend ShannonC7\n", 1)
                p_bad.write_text(txt, encoding="utf-8")
                try:
                    verify_lean_file(p_bad, None)
                except VerifyError as exc:
                    if req not in str(exc):
                        raise RuntimeError(f"ST-72 L1 sub-case {lbl!r} masked: got {str(exc)!r}, expected {req!r}")
                    continue
                raise RuntimeError(f"ST-72 L1 sub-case {lbl!r} unexpectedly PASSED")

            # Negative Layer 2 (purely benign Stage 7B Rule L2 rejections — zero forbidden commands!):
            r16_l2_cases = [
                ("R16_benign_1e0", "def _b : Float := 1e0", "non-decimal/scientific/underscored"),
                ("R16_benign_0x10", "def _b : Nat := 0x10", "non-decimal/scientific/underscored"),
                ("R16_benign_0b10", "def _b : Nat := 0b10", "non-decimal/scientific/underscored"),
                ("R16_benign_0o7", "def _b : Nat := 0o7", "non-decimal/scientific/underscored"),
                ("R16_benign_1_000", "def _b : Nat := 1_000", "non-decimal/scientific/underscored"),
                ("R16_benign_1foo", "def _b := 1foo", "contiguously followed by identifier"),
                ("R16_benign_1e_0", "def _b := 1e_0", "contiguously followed by identifier"),
                ("R16_benign_1_0foo", "def _b := 1.0foo", "contiguously followed by identifier"),
            ]
            for idx_c, (lbl, snippet, req) in enumerate(r16_l2_cases):
                p_bad = tmp / f"st72_l2_{idx_c}.lean"
                txt = valid_lean_src.replace("\nend ShannonC7\n", f"\n{snippet}\nend ShannonC7\n", 1)
                p_bad.write_text(txt, encoding="utf-8")
                try:
                    verify_lean_file(p_bad, None)
                except VerifyError as exc:
                    if req not in str(exc):
                        raise RuntimeError(f"ST-72 L2 sub-case {lbl!r} masked: got {str(exc)!r}, expected {req!r}")
                    continue
                raise RuntimeError(f"ST-72 L2 sub-case {lbl!r} unexpectedly PASSED")

        expect_pass(
            "ST-72 positive/negative (R16) scientific-literal token-split closure & benign v.2.1 tuple projections",
            st72,
        )

        # ST-73: Positive + Negative (R17) — Exhaustive 26-token TokenTable PUNCT_END_ID closure preserving `G ≃g H`
        def st73():
            # Positive: whitespace-followed `G ≃g H` passes full verify_lean_file!
            pos_isog = "def _ok_isog : Type := C7 ≃g C7\n"
            p_ok = tmp / "st73_pos_isog.lean"
            p_ok.write_text(
                valid_lean_src.replace("\nend ShannonC7\n", f"\n{pos_isog}end ShannonC7\n", 1),
                encoding="utf-8",
            )
            verify_lean_file(p_ok, None)

            # Negative Layer 1 (all PUNCT_END_ID families + #checksorry/#evalsorry hitting Stage 3 / Stage 7A unmasked!):
            r17_l1_cases = [
                ("R17_MOD_sorry", "def _t : Prop := 0 ≡ 0 [MODsorry]", "sorry"),
                ("R17_ZMOD_sorry", "def _t : Prop := (0 : Int) ≡ 0 [ZMODsorry]", "sorry"),
                ("R17_PMOD_sorry", "def _t : Prop := 0 ≡ 0 [PMODsorry]", "sorry"),
                ("R17_MOD_by_elab", "def _t : Prop := 0 ≡ 0 [MODby_elab pure (Lean.mkNatLit 1)]", "by_elab"),
                ("R17_MOD_eval_pct", "def _t : Prop := 0 ≡ 0 [MODeval% (1 : Nat)]", "eval%"),
                ("R17_isog_by_elab", "def _t : Prop := Nonempty (C7 ≃gby_elab pure (Lean.mkConst `ShannonC7.C7))", "by_elab"),
                ("R17_isog_sorry", "def _t : Prop := Nonempty (C7 ≃gsorry)", "sorry"),
                ("R17_lti_sorry", "def _t (x : Nat) := x <isorry", "sorry"),
                ("R17_tilder_sorry", "def _t (x : Nat) := x ~rsorry", "sorry"),
                ("R17_arrowo_sorry", "def _t := Nat →osorry", "sorry"),
                ("R17_arrowstar0o_sorry", "def _t := Nat →*₀osorry", "sorry"),
                ("R17_hookg_sorry", "def _t := Nat ↪gsorry", "sorry"),
                ("R17_compL_sorry", "def _t (f : Nat) := f ∘Lsorry", "sorry"),
                ("R17_compSL_sorry", "def _t (f : Nat) := f ∘SLsorry", "sorry"),
                ("R17_lei_sorry", "def _t (x : Nat) := x ≤isorry", "sorry"),
                ("R17_oplusg_sorry", "def _t (A : Type) := A ⊕gsorry", "sorry"),
                ("R17_timesC_sorry", "def _t (A : Type) := A ×ℂsorry", "sorry"),
                ("R17_hash_checksorry", "#checksorry", "#checksorry"),
                ("R17_hash_evalsorry", "#evalsorry", "#evalsorry"),
            ]
            for idx_c, (lbl, snippet, req) in enumerate(r17_l1_cases):
                p_bad = tmp / f"st73_l1_{idx_c}.lean"
                txt = valid_lean_src.replace("\nend ShannonC7\n", f"\n{snippet}\nend ShannonC7\n", 1)
                p_bad.write_text(txt, encoding="utf-8")
                try:
                    verify_lean_file(p_bad, None)
                except VerifyError as exc:
                    if req not in str(exc):
                        raise RuntimeError(f"ST-73 L1 sub-case {lbl!r} masked: got {str(exc)!r}, expected {req!r}")
                    continue
                raise RuntimeError(f"ST-73 L1 sub-case {lbl!r} unexpectedly PASSED")

            # Negative Layer 2 (purely benign Stage 7B Rule L2 rejections across unused tokens + contiguous `≃gfoo`!):
            r17_l2_cases = [
                ("R17_benign_MOD", "def _b : Prop := 0 ≡ 0 [MOD 1]", "TokenTable ident-suffix punctuation `MOD`"),
                ("R17_benign_ZMOD", "def _b : Prop := (0 : Int) ≡ 0 [ZMOD 1]", "TokenTable ident-suffix punctuation `ZMOD`"),
                ("R17_benign_PMOD", "def _b : Prop := 0 ≡ 0 [PMOD 1]", "TokenTable ident-suffix punctuation `PMOD`"),
                ("R17_benign_lti", "def _b (x y : Nat) := x <i y", "TokenTable ident-suffix punctuation `<i`"),
                ("R17_benign_tilder", "def _b (x y : Nat) := x ~r y", "TokenTable ident-suffix punctuation `~r`"),
                ("R17_benign_isog_contig", "def _b := C7 ≃gfoo", "`≃g` must be immediately followed by ASCII whitespace"),
                ("R17_benign_arrowo", "def _b := Nat →o Nat", "TokenTable ident-suffix punctuation `→o`"),
            ]
            for idx_c, (lbl, snippet, req) in enumerate(r17_l2_cases):
                p_bad = tmp / f"st73_l2_{idx_c}.lean"
                txt = valid_lean_src.replace("\nend ShannonC7\n", f"\n{snippet}\nend ShannonC7\n", 1)
                p_bad.write_text(txt, encoding="utf-8")
                try:
                    verify_lean_file(p_bad, None)
                except VerifyError as exc:
                    if req not in str(exc):
                        raise RuntimeError(f"ST-73 L2 sub-case {lbl!r} masked: got {str(exc)!r}, expected {req!r}")
                    continue
                raise RuntimeError(f"ST-73 L2 sub-case {lbl!r} unexpectedly PASSED")

        expect_pass(
            "ST-73 positive/negative (R17) 26-token TokenTable PUNCT_END_ID closure & benign `G ≃g H`",
            st73,
        )

        # ST-74: Negative (R12-NHDS + NB-3 + NB-4) — Layer-1 `𝓝`/`ℤ` quote guards, `include_str`/`addInstance`, & `/\`/`=<<` lexer closure
        def st74():
            # R12-NHDS / R12-Z: rejected directly at Stage 2 (`_lex_lean4_single_pass`) with "Ambiguous"!
            r12_nhds_cases = [
                ("R12_nhds_dblquote", "def _d := let 𝓝 := #[42]; 𝓝[0]''\"'.toLt\ntheorem evil : False := sorry\n-- \""),
                ("R12_nhds_space_quote", "def _d := let 𝓝 := #[42]; 𝓝[0]' '\"'.toLt\ntheorem evil : False := sorry\n-- \""),
                ("R12_nhds_nl_quote", "def _d := let 𝓝 := #[42]; 𝓝[0]'\n'\"'.toLt\ntheorem evil : False := sorry\n-- \""),
                ("R12_nhds_paren_quote", "def _d := let 𝓝 := #[42]; 𝓝[0]'('\"'.toLt\ntheorem evil : False := sorry\n-- \""),
                ("R12_Z_dblquote", "def _d := let ℤ := #[42]; ℤ[0]''\"'.toLt\ntheorem evil : False := sorry\n-- \""),
                ("R12_Z_space_quote", "def _d := let ℤ := #[42]; ℤ[0]' '\"'.toLt\ntheorem evil : False := sorry\n-- \""),
            ]
            for lbl, src_case in r12_nhds_cases:
                try:
                    _lex_lean4_single_pass(src_case)
                except VerifyError as exc:
                    if "Ambiguous" not in str(exc):
                        raise RuntimeError(f"ST-74 {lbl} unexpected error: {exc!r}")
                    continue
                raise RuntimeError(f"ST-74 {lbl} unexpectedly PASSED _lex_lean4_single_pass")

            # NB-3: `include_str` & `Lean.Meta.addInstance` rejected unmasked at Stage 3 via verify_lean_file!
            nb3_cases = [
                ("NB3_include_str", "def _inc (p : System.FilePath) : String := include_str p", "include_str"),
                ("NB3_addInstance", "def _ai := Lean.Meta.addInstance", "addInstance"),
            ]
            for idx_c, (lbl, snippet, req) in enumerate(nb3_cases):
                p_bad = tmp / f"st74_nb3_{idx_c}.lean"
                txt = valid_lean_src.replace("\nend ShannonC7\n", f"\n{snippet}\nend ShannonC7\n", 1)
                p_bad.write_text(txt, encoding="utf-8")
                try:
                    verify_lean_file(p_bad, None)
                except VerifyError as exc:
                    if req not in str(exc):
                        raise RuntimeError(f"ST-74 {lbl} masked: got {str(exc)!r}, expected {req!r}")
                    continue
                raise RuntimeError(f"ST-74 {lbl} unexpectedly PASSED")

            # NB-4: Layer-1 `_lex_lean4_single_pass` + `_check_lean_hygiene` exposes `sorry` after `/\`, `=<<`, `^<`, `*...<`, `...<`, `<...<`!
            nb4_cases = [
                ("NB4_and_block", "theorem _t : True /\\/- \" -/\n  True := ⟨trivial, trivial⟩\ntheorem evil : False := sorry\n-- \""),
                ("NB4_bindl_line", "def _t (f g : Nat) := f =<<-- \"\ntheorem evil : False := sorry\n-- \""),
                ("NB4_caretlt_line", "def _t (f g : Nat) := f ^<-- \"\ntheorem evil : False := sorry\n-- \""),
                ("NB4_stardotslt_line", "def _t (f g : Nat) := f *...<-- \"\ntheorem evil : False := sorry\n-- \""),
                ("NB4_dotslt_line", "def _t (f g : Nat) := f ...<-- \"\ntheorem evil : False := sorry\n-- \""),
                ("NB4_ltdotslt_line", "def _t (f g : Nat) := f <...<-- \"\ntheorem evil : False := sorry\n-- \""),
            ]
            for lbl, src_case in nb4_cases:
                toks_nb4, _ = _lex_lean4_single_pass(src_case)
                try:
                    _check_lean_hygiene(toks_nb4, f"<{lbl}>")
                except VerifyError as exc:
                    if "sorry" not in str(exc):
                        raise RuntimeError(f"ST-74 {lbl} masked: got {str(exc)!r}, expected 'sorry'")
                    continue
                raise RuntimeError(f"ST-74 {lbl} unexpectedly PASSED Layer-1 hygiene")

        expect_pass(
            "ST-74 negative (R12-NHDS+NB-3+NB-4) Layer-1 𝓝/ℤ quote guards, include_str/addInstance, & /\\=<< lexer closure",
            st74,
        )

        # ST-75: Negative (R14-BASE) — Tightened base-gadget bounds (`MAX_BASE_GADGETS=4`, `MAX_BASE_DIM=12`, `MAX_BASE_WORDS=512`, `MAX_BASE_PAIRWISE_WORK=2_500_000`) < 0.05s CPU
        def st75():
            def check_r14_base(lbl: str, fn, req: str) -> None:
                t0 = time.process_time()
                try:
                    fn()
                except VerifyError as exc:
                    dt = time.process_time() - t0
                    if req not in str(exc):
                        raise RuntimeError(f"ST-75 {lbl} unexpected error: {exc!r} (expected {req!r})")
                    if dt >= 0.05:
                        raise RuntimeError(f"ST-75 {lbl} exceeded 0.05s CPU: {dt:.4f}s")
                    return
                raise RuntimeError(f"ST-75 {lbl} unexpectedly PASSED")

            if MAX_BASE_GADGETS != 4 or MAX_BASE_DIM != 12 or MAX_BASE_WORDS != 512 or MAX_BASE_PAIRWISE_WORK != 2_500_000:
                raise RuntimeError("ST-75 unexpected MAX_BASE_* constants")

            # 1) 5 base gadgets > MAX_BASE_GADGETS=4
            w_5g = _make_mini_c7_1_witness()
            w_5g["base_gadgets"] = [dict(w_5g["base_gadgets"][0]) for _ in range(5)]
            check_r14_base("R14_base_5_gadgets", lambda: verify_witness_dict(w_5g, enforce_frontier_floor=False), "MAX_BASE_GADGETS")

            # 2) dim=13 > MAX_BASE_DIM=12
            w_d13 = _make_mini_c7_1_witness()
            w_d13["base_gadgets"][0]["dim"] = 13
            check_r14_base("R14_base_dim_13", lambda: verify_witness_dict(w_d13, enforce_frontier_floor=False), "MAX_BASE_DIM")

            # 3) 513 words > MAX_BASE_WORDS=512
            w_513w = _make_mini_c7_1_witness()
            w_513w["base_gadgets"][0]["I"] = [[0]] * 513
            check_r14_base("R14_base_513_words", lambda: verify_witness_dict(w_513w, enforce_frontier_floor=False), "MAX_BASE_WORDS")

            # 4) Single layered gadget dim=12, |I|=|X|=|Y|=500 -> work = 9,000,000 > MAX_BASE_PAIRWISE_WORK=2,500,000
            w_work = _make_mini_c7_1_witness()
            w_work["base_gadgets"][0] = {
                "dim": 12,
                "I": [[0] * 12] * 500,
                "X": [[0] * 12] * 500,
                "ports": [],
                "interior_layer": {"ports_int": [], "Y": [[0] * 12] * 500},
            }
            check_r14_base("R14_base_work_9M", lambda: verify_witness_dict(w_work, enforce_frontier_floor=False), "MAX_BASE_PAIRWISE_WORK")

            # 5) Cumulative 4 gadgets each under single limit (dim=12, |I|=260 -> 811,200 each; 4x = 3,244,800 > 2,500,000)
            w_cum = _make_mini_c7_1_witness()
            g_sub = {"dim": 12, "I": [[0] * 12] * 260, "X": [], "ports": []}
            w_cum["base_gadgets"] = [dict(g_sub) for _ in range(4)]
            check_r14_base("R14_base_cum_work_3_2M", lambda: verify_witness_dict(w_cum, enforce_frontier_floor=False), "MAX_BASE_PAIRWISE_WORK")

        expect_pass(
            "ST-75 negative (R14-BASE) base-gadget MAX_BASE_* & MAX_BASE_PAIRWISE_WORK budget rejected <0.05s CPU",
            st75,
        )

        expected_test_count = 75
        if len(tests) != expected_test_count:
            raise RuntimeError(f"Expected {expected_test_count} self-tests, found {len(tests)}")
        for idx_t, (t_name, _, _) in enumerate(tests, start=1):
            if not t_name.startswith(f"ST-{idx_t:02d} "):
                raise RuntimeError(f"Self-test #{idx_t} has unexpected label {t_name!r}")

        passed = 0
        failed = 0
        for name, should_pass, fn in tests:
            try:
                fn()
                ok = should_pass
                detail = "OK" if ok else "UNEXPECTED PASS"
            except VerifyError as exc:
                ok = not should_pass
                detail = f"rejected as expected ({exc})" if ok else f"UNEXPECTED FAIL ({exc})"
            except Exception as exc:
                ok = False
                detail = f"UNEXPECTED {type(exc).__name__} ({exc})"
            if ok:
                passed += 1
                print(f"[PASS] {name}: {detail}")
            else:
                failed += 1
                print(f"[FAIL] {name}: {detail}")

    print(f"\n[verify_witness --self-test] {passed}/{len(tests)} passed, {failed} failed")
    return 0 if failed == 0 else 1


def main() -> int:
    parser = argparse.ArgumentParser(description="Independent pure-stdlib witness & Lean verifier.")
    parser.add_argument("--witness", action="append", type=pathlib.Path, help="Witness JSON path(s)")
    parser.add_argument("--verify-lean", type=pathlib.Path, help="Lean FrontierLower.lean path to cross-check")
    parser.add_argument("--self-test", action="store_true", help="Run isolated positive & negative mutation suite")
    args = parser.parse_args()

    if not args.self_test and not args.witness and not args.verify_lean:
        parser.print_usage(sys.stderr)
        return 2

    if args.self_test:
        rc = run_self_test()
        if rc != 0:
            return rc

    last_summary = None
    if args.witness:
        for wp in args.witness:
            try:
                data = _load_json_file_strict(wp)
                summary = verify_witness_dict(data, enforce_frontier_floor=True)
                last_summary = summary
                print(
                    f"[PASS] Witness {wp}: id={summary['witness_id']} dim={summary['final_dim']} "
                    f"bound={summary['num']}/{summary['den']} N_digits={len(str(summary['N_exact']))}"
                )
            except (OSError, UnicodeDecodeError, json.JSONDecodeError, ValueError, RecursionError, VerifyError) as exc:
                print(f"[FAIL] Witness {wp}: {exc}", file=sys.stderr)
                return 1

    if args.verify_lean:
        try:
            res = verify_lean_file(args.verify_lean, last_summary)
            print(
                f"[PASS] Lean {args.verify_lean}: bound={res['num']}/{res['den']} "
                f"card_digits={len(str(res['card']))} dag_ops={res['n_ops']} gamma6_terms={res['n_terms']} hygiene=CLEAN"
            )
        except (OSError, UnicodeDecodeError, ValueError, RecursionError, VerifyError) as exc:
            print(f"[FAIL] Lean {args.verify_lean}: {exc}", file=sys.stderr)
            return 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
