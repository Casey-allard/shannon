#!/usr/bin/env python3
"""Independent stdlib-only exact-arithmetic, hygiene, axiom, witness & obstruction verifier.

Zero third-party packages: Python 3.12 standard library ONLY.
Used both as an importable library by verify/tiers/*.py & verify/self_test.py
and as a standalone CLI verification utility.
"""

from __future__ import annotations

import argparse
import bisect
from dataclasses import dataclass
from fractions import Fraction
import json
import math
from pathlib import Path
import re
import sys
from typing import Any, Callable, Iterable, NamedTuple, Sequence

# Guard Python 3.12+ integer stringification limit for d >= 500 powers.
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(100000)


def _is_strict_int(x: object) -> bool:
    """Return True iff `x` is a genuine Python `int` and NOT a `bool`."""
    return isinstance(x, int) and not isinstance(x, bool)


def _safe_int_preview(x: object, max_bits: int = 665) -> str:
    """Safely format an integer (or arbitrary object) for diagnostics without hitting
    Python 3.12's 100,000-digit int-to-str limit (~665 bits ~= 200 decimal digits).
    """
    if _is_strict_int(x):
        if x.bit_length() > max_bits:
            sign = "-" if x < 0 else ""
            return f"{sign}<int bit_length={x.bit_length()}>"
        try:
            return str(x)
        except Exception:
            sign = "-" if x < 0 else ""
            return f"{sign}<int bit_length={x.bit_length()}>"
    try:
        return repr(x)
    except Exception:
        return f"<{type(x).__name__} unprintable>"


safe_int_preview = _safe_int_preview

# ---------------------------------------------------------------------------
# 1. Exact Mathematical Constants & Milestone Anchors
# ---------------------------------------------------------------------------

FLOOR_LOWER = Fraction(3258805369885, 10**12)            # BPZ v1 mandatory floor (d=200)
BPZ_LEAN_RECORD = Fraction(3258827985920007, 10**15)     # BPZ Aug 2026 Lean 4.32.2 record
TANDON_RECORD = Fraction(3258832620353, 10**12)          # Tandon Aug 2026 unrefereed record

LOVASZ_8_LOWER = Fraction(331766720, 10**8)
LOVASZ_8_UPPER = Fraction(331766721, 10**8)
LOVASZ_LOWER_RAT = Fraction(3317667207394, 10**12)       # Strictly < theta(C7)
LOVASZ_UPPER_RAT = Fraction(3317667207395, 10**12)       # Contract upper bound (> theta(C7))
LOVASZ_15_LOWER = Fraction(3317667207394095, 10**15)     # True 15-digit floor
LOVASZ_15_UPPER = Fraction(3317667207394096, 10**15)     # 15-digit ceiling
LOVASZ_CUBIC_TRAP = Fraction(33176672073945, 10**13)     # < LOVASZ_UPPER_RAT yet > theta(C7)!

THETA_C7_30DIGITS = "3.317667207394095392733208298072"

COMPL_LOWER_RAT = Fraction(2109916264174, 10**12)        # < theta(C7^c)
COMPL_UPPER_RAT = Fraction(2109916264175, 10**12)        # > theta(C7^c)

GAO_D200_EXACT_N = (
    4085567963379990282748597333793399773399910167372462112610203714626938509773125898252337545387866277249
)
BPZ_D200_EXACT_N = (
    4089635995108338053456272492117641008738901835089431264388780413340766441486608118807897325023935704961
)

ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
EXPLICITLY_FORBIDDEN_AXIOMS = frozenset(
    {"sorryAx", "Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler"}
)

REQUIRED_MAIN_AXIOM_DECLS = (
    "ShannonC7.c7_shannonCapacity_tendsto",
    "ShannonC7.alpha_c7_pow1",
    "ShannonC7.alpha_c7_pow2",
    "ShannonC7.alpha_c7_pow3",
    "ShannonC7.c7_upper_lovasz",
    "ShannonC7.c7_upper_rational",
    "ShannonC7.c7_lovasz_unattainable",
    "ShannonC7.c7_lower_frontier",
    "ShannonC7.c7_shannonCapacity_sandwich",
    "ShannonC7.c7_compl_sandwich",
    "ShannonC7.c5_shannonCapacity_eq_sqrt_five",
    "ShannonC7.oddCycle_upper_lovasz",
)

# Exact 24 declarations audited by #print axioms in verify/e2e_audit.lean
REQUIRED_AUDIT_AXIOM_DECLS = REQUIRED_MAIN_AXIOM_DECLS + (
    "ShannonC7.c7_lower_num",
    "ShannonC7.c7_lower_den",
    "ShannonC7.lovaszThetaC7",
    "ShannonC7.shannonCapacity",
    "ShannonC7.strongPowPi",
    "ShannonC7.OpenQuestion_StrictGap",
    "ShannonC7.OpenQuestion_ExactValue",
    "E2EAudit.textbook_eq_project",
    "E2EAudit.audit_textbook_sandwich",
    "E2EAudit.audit_c7_lower_den_pos",
    "E2EAudit.audit_c7_lower_floor",
    "E2EAudit.audit_c7_lower_lt_upper",
)

# ---------------------------------------------------------------------------
# 2. Lean 4.32.2 Single-Pass Fail-Closed Pure-Math Lexer + Hygiene Scanner
# ---------------------------------------------------------------------------


class LeanToken(NamedTuple):
    kind: str  # "IDENT" | "STRING" | "CHAR" | "NUMBER" | "PUNCT" | "OTHER"
    text: str
    line: int
    col: int
    start: int
    end: int
    is_french_quoted: bool = False


@dataclass(frozen=True, slots=True)
class HygieneViolation:
    path: str
    line: int
    col: int
    rule: str
    token: str
    message: str

    def to_dict(self) -> dict:
        return {
            "path": self.path,
            "line": self.line,
            "col": self.col,
            "rule": self.rule,
            "token": self.token,
            "message": self.message,
        }


# Exact Lean v4.32.2 char/string/comment/ident helpers (Init/Meta/Defs.lean:101-135,
# Lean/Parser/Basic.lean:537-587, 740-809).
_CHAR_LITERAL_RE = re.compile(r"'(?:[^'\\]|\\[nrt\\'\"0]|\\x[0-9a-fA-F]{2}|\\u[0-9a-fA-F]{4})'")
_ASCII_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'?!]*")
_PLAIN_STR_STOP_RE = re.compile(r'[\\"]')
_PLAIN_STR_BRACE_STOP_RE = re.compile(r'[\\"{]')
_BLOCK_COMMENT_STOP_RE = re.compile(r"/-|-/")

_HEX_DIGITS = frozenset("0123456789abcdefABCDEF")
_BIN_DIGITS = frozenset("01")
_OCT_DIGITS = frozenset("01234567")

# Option A Fail-Closed Pure-Math Policy:
# ONLY the 3 unconditionally reserved pure-Init interpolators are lexed as interpolatedStr.
# All other 16 Lean/Lake/Aesop interpolatedStr triggers (including m!, v!, trace[, dbg_trace,
# throwError*, logNamed*, report*Issue!, trace_goal, aesop_trace*) and all parser/syntax
# extension commands are explicitly forbidden fail-closed.
_PURE_BUILTIN_INTERPOLATORS = frozenset({"s!", "f!", "println!"})
_PURE_INTERP_PREFIXES = tuple(
    sorted(
        {
            interp[:k]
            for interp in _PURE_BUILTIN_INTERPOLATORS
            for k in range(1, len(interp) + 1)
        },
        key=len,
        reverse=True,
    )
)
_FORBIDDEN_DBG_TRACE_KW = frozenset({"dbg_trace", "idbg"})
_FORBIDDEN_META_SYNTAX_KW = frozenset({
    "syntax", "declare_syntax_cat", "syntax_cat", "macro", "macro_rules",
    "elab", "elab_rules", "binder_predicate", "notation3", "register_parser_alias",
    "run_cmd", "run_elab", "run_meta", "by_elab", "run_tac",
    "initialize", "builtin_initialize", "prelude", "init_quot",
    "register_simp_attr", "register_sym_simp", "register_sym_dsimp",
    "register_linter_set", "register_option", "register_builtin_option",
    "register_error_explanation",
    "run_io", "register_try?_tactic", "declare_simp_like_tactic",
    "tactic_extension", "register_tactic_tag", "deprecated_syntax",
    "by_elabq", "run_tacq",
})
_FORBIDDEN_META_SYNTAX_ALWAYS = frozenset({
    # Interpolated-string parser internals
    "interpolatedStr", "interpolatedStrFn", "interpolatedStrNoAntiquot",
    "interpolatedStrKind", "interpolatedStrLitKind", "expandInterpolatedStr",
    # Parser registration attributes (Lean/Parser/{Extension,Attr,Do,Level,Syntax,Term/Basic}.lean)
    "term_parser", "tactic_parser", "command_parser", "doElem_parser",
    "syntax_parser", "stx_parser", "leading_parser", "trailing_parser",
    "prio_parser", "attr_parser", "prec_parser",
    "builtin_term_parser", "builtin_tactic_parser", "builtin_command_parser",
    "builtin_doElem_parser", "builtin_syntax_parser",
    "builtin_prio_parser", "builtin_attr_parser", "builtin_prec_parser",
    "builtin_level_parser", "builtin_structInstFieldDecl_parser",
    "run_parser_attribute_hooks", "run_builtin_parser_attribute_hooks",
    # Elaborator, macro & pretty-printer hooks (ALL Lean v4.32.2 mkElabAttribute & KeyedDeclsAttribute)
    "macro_expander", "builtin_macro",
    "term_elab", "builtin_term_elab",
    "tactic_elab", "builtin_tactic",
    "command_elab", "builtin_command_elab",
    "doElem_elab", "builtin_doElem_elab",
    "doElem_control_info", "builtin_doElem_control_info",
    "inductive_elab", "builtin_inductive_elab",
    "grind_tactic", "builtin_grind_tactic",
    "try_tactic", "builtin_try_tactic", "try_suggestion",
    "sym_simproc", "builtin_sym_simproc",
    "sym_dsimproc", "builtin_sym_dsimproc",
    "sym_discharger", "builtin_sym_discharger",
    "quot_precheck", "builtin_quot_precheck",
    "app_unexpander", "delab", "builtin_delab", "app_delab",
    "builtin_formatter", "builtin_parenthesizer",
    "category_parenthesizer", "builtin_category_parenthesizer",
    # Simproc / dsimproc / cbv_simproc / propagator / compiler-pass / linter / LSP / doc hooks
    "simproc", "dsimproc", "simproc_decl", "dsimproc_decl",
    "builtin_simproc", "builtin_dsimproc", "builtin_simproc_decl", "builtin_dsimproc_decl",
    "simproc_pattern", "builtin_simproc_pattern",
    "simprocAttr", "simprocBuiltinAttr",
    "sevalproc", "builtin_sevalproc", "sevalprocAttr", "sevalprocBuiltinAttr",
    "cbv_simproc", "cbv_simproc_decl", "builtin_cbv_simproc", "builtin_cbv_simproc_decl",
    "cbv_simproc_pattern", "builtin_cbv_simproc_pattern",
    "cbvSimprocAttr", "cbvSimprocBuiltinAttr",
    "grind_propagator", "builtin_grind_propagator", "grindPropagatorBuiltinAttr",
    "bv_normalize_proc", "builtin_bv_normalize_proc", "bvNormalizeProcBuiltinAttr",
    "cpass", "builtin_env_linter",
    "command_code_action", "builtin_command_code_action", "hole_code_action",
    "server_rpc_method",
    "doc_role", "builtin_doc_role", "doc_code_block", "builtin_doc_code_block",
    "doc_directive", "builtin_doc_directive", "doc_command", "builtin_doc_command",
    "doc_code_suggestions", "builtin_doc_code_suggestions",
    "doc_code_block_suggestions", "builtin_doc_code_block_suggestions",
    "builtin_init", "builtin_incremental", "combinator_formatter", "combinator_parenthesizer",
    "missing_docs_handler", "builtin_missing_docs_handler",
    "unused_variables_ignore_fn", "builtin_unused_variables_ignore_fn",
    "code_action_provider", "builtin_code_action_provider",
    "widget_module", "builtin_widget_module",
    "test_runner", "library_suggestions", "tactic_alt", "tactic_tag", "tactic_name",
    "tactic_code_action", "commentBody", "versoCommentBody", "ProofWidgets", "Jsx", "Qq",
})
# Closed positive whitelist of verified Lean v4.32.2 / Batteries / Mathlib pure-math attributes
# (0 `term` args, 0 `[`/`]` brackets, 0 `unsafe`/`evalConst*`/meta hooks).
_ALLOWED_PURE_MATH_ATTRS = frozenset({
    "simp", "ext", "coe", "refl", "symm", "trans", "congr", "norm_cast", "push_cast",
    "wf_preprocess", "grind", "grind!", "grind?", "grind!?",
    "reducible", "irreducible", "semireducible", "inline", "always_inline", "noinline",
    "macro_inline", "specialize", "nospecialize", "instance", "default_instance", "class",
    "recursor", "match_pattern", "pp_dot", "pp_using_anonymous_constructor", "expose",
    "elab_without_expected_type", "elab_as_elim", "deprecated", "deprecated_arg",
    "inherit_doc", "suggest_for", "nolint", "gcongr", "mono", "measurability", "continuity",
})
_FORBIDDEN_META_API_KW = frozenset({
    "m!", "v!", "throwError", "throwErrorAt", "throwNamedError", "throwNamedErrorAt",
    "reportIssue!", "reportDbgIssue!", "reportEMatchIssue!",
    "trace_goal", "aesop_trace", "aesop_trace!",
})
_FORBIDDEN_META_API_ALWAYS = frozenset({
    "modifyEnv", "setEnv", "addDecl", "addDeclCore", "addDeclCheck",
    "addDeclWithoutChecking", "addAndCompile", "addConstAsync",
    "setCheckedSync", "compileDecl",
    "addAndCompileUnsafe", "addAndCompileNonRec", "addAndCompilePartialRec",
    "mkSorry", "mkLabeledSorry", "admitGoal",
    "evalConst", "evalConstCheck", "evalExpr", "evalExprCore", "evalExpr'",
    "registerBuiltinAttribute", "registerTagAttribute", "registerParametricAttribute",
    "registerBuiltinParserAttribute", "registerBuiltinDynamicParserAttribute",
    "registerDerivingHandler", "registerSimproc", "registerBuiltinSimproc",
    "registerBuiltinDSimproc", "registerCbvSimproc", "registerBuiltinCbvSimproc",
})
_NOTATION_INTRO_KW = frozenset({"notation", "prefix", "infix", "infixl", "infixr", "postfix"})
# Strictly globally reserved Lean v4.32.2 command-start keywords (Lean/Parser/Command.lean).
# NEVER add non-reserved words like `lemma` here!
_NOTATION_END_KW = frozenset({
    "def", "theorem", "abbrev", "structure", "inductive", "coinductive", "class",
    "instance", "axiom", "opaque", "example", "end", "namespace", "section",
    "variable", "universe", "open", "import", "set_option", "attribute",
    "private", "protected", "public", "noncomputable", "partial", "unsafe",
    "mutual", "deriving", "export", "include", "omit", "with_weak_namespace",
})
_NOTATION_LHS_RESET_PUNCT = frozenset({";", ",", "{", "}", "[", "]", "#"})
_NOTATION_LHS_RESET_OTHER = frozenset({"=", "⇒", "|"})
_NOTATION_BINDER_PREV_KW = frozenset({"fun", "λ", "let"})
_LEAN_ASCII_WS = frozenset({" ", "\t", "\n", "\r"})
_LEAN_ASCII_INLINE_WS = frozenset({" ", "\t", "\r"})
_MULTI_DOT_PREFIX_CHARS = frozenset({".", "/", "→", "≃"})
_INIT_QUOTE_SUFFIX_OP_PREV = frozenset({"×", "⊕", "]", "Σ"})
_SCOPED_QUOTE_SUFFIX_OP_PREV = frozenset({"#", "∘", "∑", "∏", "⊗", "⟧", "∀", "∃", "ˢ", "ₗ", "ᶠ"})
_AMBIGUOUS_RAW_STR_PREV = frozenset({"→", "↪", "≃", "~", "≤", "<"})
_FORBIDDEN_MULTI_ATOM_END_CHARS = (
    frozenset({"-", "/", "<", "\\"}) | _INIT_QUOTE_SUFFIX_OP_PREV | _SCOPED_QUOTE_SUFFIX_OP_PREV
)
_PUNCT_CHARS = frozenset(".@[](){},:;#`")
_ATTR_PREFIX_KW = frozenset({"attribute"})
_ATTR_SCOPE_KW = frozenset({"local", "scoped"})
_TRUST_AXIOM_LEAVES = frozenset({"ofReduceBool", "ofReduceNat", "trustCompiler"})
_NOTATION_OPEN_DELIMS = {"{": "}", "(": ")", "[": "]"}
_NOTATION_ALL_DELIMS = frozenset({"{", "}", "(", ")", "[", "]"})
_FORBIDDEN_DSL_IMPORT_ROOTS = frozenset({"ProofWidgets", "Qq"})
_ALLOWED_HASH_COMMANDS = frozenset({
    "eval", "eval!", "check", "check_failure", "check_assertions",
    "print", "reduce", "guard", "guard_expr", "guard_msgs", "synth", "where", "exit",
})
_HASH_CMD_PREFIXES = (
    "eval", "check", "print", "reduce", "guard", "synth", "where", "exit",
    "version", "with_exporting", "show_", "dump_", "discr_tree", "grind_lint",
    "info_trees", "import_", "help", "push", "pull", "adaptation_note",
    "count_heartbeats", "defeq_abuse", "min_imports", "minimize_imports",
    "list_linters", "aesop_", "allow_unused", "clear_deprecations",
    "click_suggestions", "long_", "redundant_imports", "reset_min_imports",
    "rw?", "stacks_tags", "kerodon_tags", "wikidata_tags", "lmfdb_tags",
    "string_diagram", "trans_imports", "unfold?", "reexport", "search",
    "loogle", "leansearch", "statesearch", "unused_transitive_imports",
    "html", "widget", "parse", "simp", "conv", "whnf", "norm_num",
    "find", "lint", "explode", "instances", "time", "test", "sample",
    "browse", "computability", "create_deprecated", "demo", "expr_graph", "log_keys",
)
_NON_IDENT_OP_SUFFIXES: dict[str, tuple[str, ...]] = {
    "→": ("C_c", "CO", "CP", "Co", "C₀", "bᵢ", "qᵢ", "g", "o", "r"),
    "↪": ("g", "o", "r"), "≃": ("g", "o", "r"), "~": ("m", "r"),
    "≤": ("c", "i", "m", "r", "s"), "<": ("i", "m", "r"), "⊕": ("g",), "×": ("ℂ",),
    "∘": ("SL", "L"), "∂": ("L", "R", "𝔻"), "≺": ("i",), "≼": ("i",),
    "⋙": ("rq", "q"), "⥤": ("rq", "q"), "𝟙": ("rq", "_"), "𝟭": ("rq", "q"),
    "|": ("_ₕ", "_ₗ", "_"), "∣": ("_",), "⊤": ("_",), "⊥": ("_",), "λ": ("_",), "⟫": ("_",),
    "[": ("PMOD", "SMOD", "ZMOD", "MOD"), "*": ("o",), "+": ("o",), "=": ("QL", "Q"),
    "₀": ("o",), "ₐ": ("c",), "ₗ": ("c",), "ⁱ": ("L",), "₂": ("F₁",), "⁻": ("_",), "'": ("o",), "]": ("_",),
}
_FORBIDDEN_GLUED_TAIL_KW = (
    frozenset({"sorry", "sorryAx", "admit", "axiom", "unsafe", "unsafeCast", "lcProof",
               "implemented_by", "extern", "native_decide", "skipKernelTC", "attribute", "import"})
    | _TRUST_AXIOM_LEAVES | _FORBIDDEN_DBG_TRACE_KW | _FORBIDDEN_META_SYNTAX_KW
    | _FORBIDDEN_META_SYNTAX_ALWAYS | _FORBIDDEN_META_API_KW | _FORBIDDEN_META_API_ALWAYS
    | _NOTATION_INTRO_KW | _PURE_BUILTIN_INTERPOLATORS
)
_FORBIDDEN_GLUED_TAIL_TUPLE = tuple(_FORBIDDEN_GLUED_TAIL_KW)


def _is_lean_letter_like(ch: str) -> bool:
    """Match Lean v4.32.2 `Init/Meta/Defs.lean:101-109` `isLetterLike` exactly."""
    cp = ord(ch)
    return (
        (0x03B1 <= cp <= 0x03C9 and cp != 0x03BB)
        or (0x0391 <= cp <= 0x03A9 and cp != 0x03A0 and cp != 0x03A3)
        or (0x03CA <= cp <= 0x03FB)
        or (0x1F00 <= cp <= 0x1FFE)
        or (0x2100 <= cp <= 0x214F)
        or (0x1D49C <= cp <= 0x1D59F)
        or (0x00C0 <= cp <= 0x00FF and cp != 0x00D7 and cp != 0x00F7)
        or (0x0100 <= cp <= 0x017F)
    )


def _is_lean_subscript_alnum(ch: str) -> bool:
    """Match Lean v4.32.2 `Init/Meta/Defs.lean:111-118` `isSubScriptAlnum` exactly."""
    cp = ord(ch)
    return (0x2080 <= cp <= 0x2089) or (0x2090 <= cp <= 0x209C) or (0x1D62 <= cp <= 0x1D6A) or cp == 0x2C7C


def _is_ident_start(ch: str) -> bool:
    """Match Lean v4.32.2 `Init/Meta/Defs.lean:120-121` `isIdFirst`."""
    return ("a" <= ch <= "z") or ("A" <= ch <= "Z") or ch == "_" or _is_lean_letter_like(ch)


def _is_ident_cont(ch: str) -> bool:
    """Match Lean v4.32.2 `Init/Meta/Defs.lean:133-134` `isIdRest` (blocks `ᶜ`, `⁻¹`, `λ`, `Π`, `Σ`)."""
    return (
        ("a" <= ch <= "z") or ("A" <= ch <= "Z") or ("0" <= ch <= "9")
        or ch in ("_", "'", "!", "?") or _is_lean_letter_like(ch) or _is_lean_subscript_alnum(ch)
    )


def _advance_pos(text: str, start: int, end: int, line: int, col: int) -> tuple[int, int]:
    chunk = text[start:end]
    nl = chunk.count("\n")
    if nl == 0:
        return line, col + (end - start)
    return line + nl, len(chunk) - chunk.rfind("\n")


def _is_qualified_before(tokens: Sequence[LeanToken], prev_idx: int, target_start: int) -> bool:
    """Return True iff the identifier/raw-string at `target_start` is qualified by `tokens[prev_idx]`.

    Matches Lean v4.32.2 (`Lean/Parser/Basic.lean:921-1046`, `Lean/Parser/Term.lean:409-417, 906-925`):
    - `#` is NEVER a qualifier (`0#s!"..."`, `0#r"\\"` are unqualified).
    - Contiguous `` ` `` qualifies via `nameLit` (`_is_forbidden_notation_atom` blocks custom `` *` ``).
    - Contiguous `.` qualifies via `identFnAux`/`Term.proj`/`Term.dotIdent` ONLY when standalone
      (NOT preceded contiguously by `.`/`/`/`→`/`≃` from `..`/`...`/`*...`/`<...`/`/.`/`→.`/`≃.`).
    """
    if prev_idx < 0:
        return False
    prev = tokens[prev_idx]
    if prev.kind != "PUNCT" or prev.end != target_start:
        return False
    if prev.text == "`":
        return True
    if prev.text == ".":
        if prev_idx == 0:
            return True
        before_dot = tokens[prev_idx - 1]
        if before_dot.end < prev.start:
            return True
        if before_dot.text in _MULTI_DOT_PREFIX_CHARS:
            return False
        return True
    return False


def _is_unqualified_tok(tokens: Sequence[LeanToken], idx: int) -> bool:
    """Return True iff `tokens[idx]` is NOT qualified by a contiguous standalone `.` or `` ` ``."""
    return not _is_qualified_before(tokens, idx - 1, tokens[idx].start)


def _decode_lean_str_lit(raw: str) -> str:
    """Decode a Lean v4.32.2 plain or raw string literal (for notation LHS atom verification)."""
    if not raw:
        return ""
    if raw[0] == "r":
        q = raw.find('"')
        if q == -1:
            return ""
        end_idx = len(raw) - 1 - (q - 1)
        return raw[q + 1 : end_idx] if end_idx >= q + 1 and raw[end_idx] == '"' else ""
    if len(raw) < 2 or raw[0] != '"' or raw[-1] != '"':
        return ""
    out: list[str] = []
    k = 1
    limit = len(raw) - 1
    simple_esc = {"n": "\n", "r": "\r", "t": "\t", "0": "\x00", "\\": "\\", '"': '"', "'": "'"}
    while k < limit:
        ch = raw[k]
        if ch != "\\":
            out.append(ch)
            k += 1
            continue
        k += 1
        if k >= limit:
            break
        esc = raw[k]
        if esc in simple_esc:
            out.append(simple_esc[esc])
            k += 1
        elif esc == "x" and k + 2 < limit and all(c in _HEX_DIGITS for c in raw[k + 1 : k + 3]):
            out.append(chr(int(raw[k + 1 : k + 3], 16)))
            k += 3
        elif esc == "u" and k + 4 < limit and all(c in _HEX_DIGITS for c in raw[k + 1 : k + 5]):
            out.append(chr(int(raw[k + 1 : k + 5], 16)))
            k += 5
        elif esc in ("\n", "\r"):
            while k < limit and raw[k] in ("\r", "\n"):
                k += 1
            while k < limit and raw[k] in _LEAN_ASCII_INLINE_WS:
                k += 1
        else:
            out.append(esc)
            k += 1
    return "".join(out)


def _is_pure_dotted_ident(toks: Sequence[LeanToken]) -> bool:
    """Return True iff `toks` is a single contiguous `IDENT(.IDENT)*` chain (no French quotes/gaps)."""
    if not toks or len(toks) % 2 == 0:
        return False
    for k, t in enumerate(toks):
        if k % 2 == 0:
            if t.kind != "IDENT" or t.is_french_quoted:
                return False
        elif t.kind != "PUNCT" or t.text != ".":
            return False
        if k > 0 and t.start != toks[k - 1].end:
            return False
    return True


def _is_forbidden_notation_atom(atom: str) -> bool:
    """Return True iff a trimmed notation/mixfix LHS atom can desync Lean v4.32.2 lexing."""
    if not atom:
        return False
    if (
        '"' in atom or "'" in atom or "«" in atom or "»" in atom
        or "--" in atom or "/-" in atom or "-/" in atom or "@[" in atom
        or atom.endswith(".") or atom.endswith("`")
        or atom in _NOTATION_BINDER_PREV_KW
        or (len(atom) >= 2 and (any(c in _NOTATION_ALL_DELIMS for c in atom) or atom[-1] in _FORBIDDEN_MULTI_ATOM_END_CHARS))
        or (len(atom) >= 3 and atom.endswith("⁻¹"))
    ):
        return True
    if atom in _PURE_BUILTIN_INTERPOLATORS:
        return True
    atom_toks, _, _, _, _ = _lex_lean4_single_pass(atom)
    if atom_toks:
        last = atom_toks[-1]
        if (
            last.kind == "IDENT" and not last.is_french_quoted
            and _is_unqualified_tok(atom_toks, len(atom_toks) - 1)
            and (last.text in _PURE_BUILTIN_INTERPOLATORS or (len(atom_toks) >= 2 and last.text in _PURE_INTERP_PREFIXES))
        ):
            return True
        if len(atom_toks) >= 2 and last.kind in ("IDENT", "NUMBER") and not _is_pure_dotted_ident(atom_toks):
            return True
    base = atom.rstrip("#")
    if base.endswith("r"):
        hashes = len(atom) - len(base)
        if hashes > 0 and len(base) == 1:
            return True
        ptoks, perrs, _, _, _ = _lex_lean4_single_pass(atom + '""' + ("#" * hashes))
        if perrs or (ptoks and ptoks[-1].kind == "STRING" and 0 < ptoks[-1].start < len(atom)):
            return True
    return False


def _is_ambiguous_dot_run(tokens: Sequence[LeanToken], dot_idx: int) -> bool:
    """Return True iff `tokens[dot_idx]` ends a dot run ambiguous with `Term.dotIdent` (`....`, `/.`, `→.`, `≃.`, `|>..`)."""
    dots = 1
    k = dot_idx - 1
    while k >= 0 and dots < 4 and tokens[k].kind == "PUNCT" and tokens[k].text == "." and tokens[k].end == tokens[k + 1].start:
        dots += 1
        k -= 1
    if dots >= 4:
        return True
    if k >= 0 and tokens[k].end == tokens[k + 1].start:
        if tokens[k].text in ("/", "→", "≃"):
            return True
        if dots >= 2 and tokens[k].text == ">" and k >= 1 and tokens[k - 1].end == tokens[k].start and tokens[k - 1].text == "|":
            return True
    return False


def _ambiguous_glued_ident_reason(
    tokens: Sequence[LeanToken], ident_text: str, source: str, i: int, j: int
) -> tuple[str, str] | None:
    """Detect Lean v4.32.2 `Trie.matchPrefix` splitting on `#`-commands and non-ident-start ops in O(|ident|)."""
    if not tokens or tokens[-1].end != i:
        return None
    prev_t = tokens[-1]
    n = len(source)
    nxt_ch = source[j] if j < n else ""
    if prev_t.kind == "PUNCT" and prev_t.text == "#":
        if ident_text == "v" and nxt_ch == "[":
            return None
        after_term = (
            len(tokens) >= 2 and tokens[-2].end == prev_t.start
            and (tokens[-2].kind in ("NUMBER", "IDENT") or (tokens[-2].kind == "PUNCT" and tokens[-2].text in (")", "]", "}")))
        )
        if ident_text not in _ALLOWED_HASH_COMMANDS and (
            not after_term
            or ident_text.startswith(_HASH_CMD_PREFIXES)
            or (
                ident_text not in _PURE_BUILTIN_INTERPOLATORS
                and (
                    nxt_ch in ('"', "'", "#", "[", ".", "-", "/")
                    or "'" in ident_text
                    or "logNamed" in ident_text
                    or ident_text.endswith(_FORBIDDEN_GLUED_TAIL_TUPLE)
                )
            )
        ):
            return f"#{ident_text}", f"Forbidden or unspaced `#`-command `#{ident_text}` under pure-math policy"
        return None
    if prev_t.kind == "PUNCT" and prev_t.text == "." and ident_text in _PURE_BUILTIN_INTERPOLATORS and _is_ambiguous_dot_run(tokens, len(tokens) - 1):
        return f".{ident_text}", f"Ambiguous multi-dot operator glued to interpolator `{ident_text}`"
    sufs = _NON_IDENT_OP_SUFFIXES.get(prev_t.text)
    if not sufs:
        return None
    for suf in sufs:
        if ident_text.startswith(suf) and len(ident_text) > len(suf):
            rem = ident_text[len(suf):]
            rlen = len(rem)
            q = 0
            while q < rlen and "0" <= rem[q] <= "9":
                if rem[q] == "0" and q + 1 < rlen and rem[q + 1] in ("x", "X", "b", "B", "o", "O"):
                    dg = _HEX_DIGITS if rem[q + 1] in ("x", "X") else (_BIN_DIGITS if rem[q + 1] in ("b", "B") else _OCT_DIGITS)
                    q += 2
                    while q < rlen and (rem[q] in dg or rem[q] == "_"):
                        q += 1
                else:
                    q += 1
                    while q < rlen and (("0" <= rem[q] <= "9") or rem[q] == "_"):
                        q += 1
                    if q + 1 < rlen and rem[q] in ("e", "E") and "0" <= rem[q + 1] <= "9":
                        q += 2
                        while q < rlen and (("0" <= rem[q] <= "9") or rem[q] == "_"):
                            q += 1
            if q > 0:
                rem = rem[q:]
                if not rem and nxt_ch == ".":
                    p, had_exp = j + 1, False
                    while p < n and (("0" <= source[p] <= "9") or source[p] == "_"):
                        p += 1
                    if p < n and source[p] in ("e", "E"):
                        k = p + 1 + (1 if p + 1 < n and source[p + 1] in ("+", "-") else 0)
                        if k < n and "0" <= source[k] <= "9":
                            had_exp = True
                            p = k + 1
                            while p < n and (("0" <= source[p] <= "9") or source[p] == "_"):
                                p += 1
                    if p > j + 1 and p < n and (_is_ident_start(source[p]) or source[p] in ('"', "'") or (had_exp and source[p] == ".")):
                        return f"{prev_t.text}{ident_text}.", f"Ambiguous `{prev_t.text}{suf}` operator glued to decimal/scientific literal"
                elif rem in ("e", "E") and nxt_ch in ("+", "-") and j + 1 < n and "0" <= source[j + 1] <= "9":
                    p = j + 2
                    while p < n and (("0" <= source[p] <= "9") or source[p] == "_"):
                        p += 1
                    if p < n and (_is_ident_start(source[p]) or source[p] in (".", '"', "'")):
                        return f"{prev_t.text}{ident_text}{nxt_ch}", f"Ambiguous `{prev_t.text}{suf}` operator glued to signed scientific literal"
            if rem and (
                rem.startswith("'") or (rem == "r" and nxt_ch in ('"', "#"))
                or rem in _FORBIDDEN_GLUED_TAIL_KW or rem.startswith("logNamed")
                or (rem == "trace" and nxt_ch == "[")
                or (rem == "D" and nxt_ch in (".", "-", "/"))
            ):
                return f"{prev_t.text}{ident_text}", f"Ambiguous `{prev_t.text}{suf}` operator glued to `{rem}`"
    return None


def _is_attr_head_pos(tokens: Sequence[LeanToken], bracket_stack: Sequence[bool], in_attr_count: int) -> bool:
    """Return True iff the next token sits at top-level attribute-head position inside `@[...]` / `attribute [...]`."""
    if in_attr_count <= 0 or not bracket_stack or not bracket_stack[-1] or not tokens:
        return False
    prev = tokens[-1]
    return (
        (prev.kind == "PUNCT" and prev.text in ("[", ","))
        or (prev.kind == "IDENT" and not prev.is_french_quoted and prev.text in _ATTR_SCOPE_KW)
    )


def _lex_lean4_single_pass(
    source: str, path: str = "<memory>"
) -> tuple[list[LeanToken], list[HygieneViolation], list[tuple[int, int]], set[int], set[int]]:
    """Single-pass, provably O(N), zero-backtracking Lean v4.32.2 lexer under Option A.

    Returns `(tokens, errors, comment_spans, attr_tok_indices, meta_attr_tok_indices)`.
    """
    tokens: list[LeanToken] = []
    errors: list[HygieneViolation] = []
    comment_spans: list[tuple[int, int]] = []
    attr_tok_indices: set[int] = set()
    meta_attr_tok_indices: set[int] = set()

    if "\x00" in source:
        nul_idx = source.find("\x00")
        errors.append(HygieneViolation(
            path, source[:nul_idx].count("\n") + 1, nul_idx - source.rfind("\n", 0, nul_idx),
            "NUL_BYTE", "\\x00", "Forbidden NUL byte (\\x00) in Lean source",
        ))

    n = len(source)
    i = 0
    line = 1
    col = 1
    interp_brace_stack: list[list[int]] = []
    bracket_stack: list[bool] = []
    in_attr_count = 0

    def finish_comment_block(pos: int) -> int | None:
        depth = 1
        p = pos
        while depth > 0:
            m = _BLOCK_COMMENT_STOP_RE.search(source, p)
            if m is None:
                return None
            depth += 1 if m.group(0) == "/-" else -1
            p = m.end()
        return p

    def skip_doc_leading_ws(pos: int) -> tuple[int, bool]:
        p = pos
        while p < n:
            c = source[p]
            if c in _LEAN_ASCII_WS:
                p += 1
            elif c == "-" and p + 1 < n and source[p + 1] == "-":
                nl = source.find("\n", p + 2)
                p = n if nl == -1 else nl + 1
            elif c == "/" and p + 1 < n and source[p + 1] == "-" and not (p + 2 < n and source[p + 2] in ("-", "!")):
                end_bc = finish_comment_block(p + 3 if p + 2 < n else n)
                if end_bc is None:
                    return n, False
                p = end_bc
            else:
                break
        return p, True

    def lex_interp_body(pos: int, str_line: int, str_col: int, cur_line: int, cur_col: int) -> tuple[int, int, int]:
        seg_start = pos
        j = pos
        while True:
            m = _PLAIN_STR_BRACE_STOP_RE.search(source, j)
            if m is None or (source[m.start()] == "\\" and m.start() + 1 >= n):
                errors.append(HygieneViolation(
                    path, str_line, str_col, "UNCLOSED_STRING", '"', "Unterminated interpolated string literal"
                ))
                nl, nc = _advance_pos(source, pos, n, cur_line, cur_col)
                return n, nl, nc
            mp = m.start()
            mc = source[mp]
            if mc == "\\":
                j = mp + 2
                continue
            if mc == '"':
                end_p = mp + 1
                tokens.append(LeanToken("STRING", source[seg_start:end_p], cur_line, cur_col, seg_start, end_p))
                nl, nc = _advance_pos(source, pos, end_p, cur_line, cur_col)
                return end_p, nl, nc
            if mp > seg_start:
                tokens.append(LeanToken("STRING", source[seg_start:mp], cur_line, cur_col, seg_start, mp))
            b_line, b_col = _advance_pos(source, pos, mp, cur_line, cur_col)
            tokens.append(LeanToken("PUNCT", "{", b_line, b_col, mp, mp + 1))
            interp_brace_stack.append([1, str_line, str_col])
            return mp + 1, b_line, b_col + 1

    while i < n:
        ch = source[i]

        if ch in _LEAN_ASCII_WS:
            if ch == "\n":
                line += 1
                col = 1
                i += 1
            else:
                j = i + 1
                while j < n and source[j] in _LEAN_ASCII_INLINE_WS:
                    j += 1
                col += j - i
                i = j
            continue

        if (
            (ch == "/" and i + 1 < n and source[i + 1] == "/")
            or (ch == "<" and i + 1 < n and source[i + 1] == "-")
            or (ch == "\\" and i + 1 < n and source[i + 1] == "/")
        ):
            if ch == "/" and tokens and tokens[-1].end == i and tokens[-1].text in ("D", "<"):
                k = i + 2
                while k < n and source[k] == "/":
                    k += 1
                if k < n and source[k] == "-":
                    errors.append(HygieneViolation(
                        path, line, col, "FORBIDDEN_META_SYNTAX", f"{tokens[-1].text}{source[i : k + 1]}",
                        f"Ambiguous `{tokens[-1].text}/` operator immediately before comment/dash sequence",
                    ))
            tokens.append(LeanToken("OTHER", source[i : i + 2], line, col, i, i + 2))
            col += 2
            i += 2
            continue

        if ch == "-" and i + 1 < n and source[i + 1] == "-":
            if tokens and tokens[-1].end == i and tokens[-1].text == "D":
                errors.append(HygieneViolation(path, line, col, "FORBIDDEN_META_SYNTAX", "D--", "Ambiguous `D-` operator immediately before `-`"))
            nl = source.find("\n", i + 2)
            end_c = n if nl == -1 else nl
            comment_spans.append((i, end_c))
            col += end_c - i
            i = end_c
            continue

        if ch == "/" and i + 1 < n and source[i + 1] == "-":
            if tokens and tokens[-1].end == i and tokens[-1].text in ("D", "<"):
                errors.append(HygieneViolation(path, line, col, "FORBIDDEN_META_SYNTAX", f"{tokens[-1].text}/-", f"Ambiguous `{tokens[-1].text}/` operator immediately before `-`"))
            c_line, c_col = line, col
            if i + 2 < n and source[i + 2] in ("-", "!"):
                ws_end, ws_ok = skip_doc_leading_ws(i + 3)
                end_c = finish_comment_block(ws_end) if ws_ok else None
            else:
                end_c = finish_comment_block(i + 3 if i + 2 < n else n)
            if end_c is None:
                errors.append(HygieneViolation(
                    path, c_line, c_col, "UNCLOSED_BLOCK_COMMENT", "/-", "Unterminated block/doc comment"
                ))
                comment_spans.append((i, n))
                line, col = _advance_pos(source, i, n, line, col)
                i = n
                break
            comment_spans.append((i, end_c))
            line, col = _advance_pos(source, i, end_c, line, col)
            i = end_c
            continue

        if ch == "r" and not _is_qualified_before(tokens, len(tokens) - 1, i):
            k = i + 1
            while k < n and source[k] == "#":
                k += 1
            if k < n and source[k] == '"':
                if tokens and tokens[-1].end == i and (
                    tokens[-1].text in _AMBIGUOUS_RAW_STR_PREV
                    or (tokens[-1].kind == "PUNCT" and tokens[-1].text == "." and _is_ambiguous_dot_run(tokens, len(tokens) - 1))
                ):
                    errors.append(HygieneViolation(
                        path, line, col, "FORBIDDEN_META_SYNTAX", source[i - 1 : k + 1],
                        f"Ambiguous `{tokens[-1].text}r` operator immediately before string literal",
                    ))
                hashes = k - (i + 1)
                r_line, r_col = line, col
                pos = k + 1
                closed_end = -1
                if hashes == 0:
                    q = source.find('"', pos)
                    if q != -1:
                        closed_end = q + 1
                else:
                    while pos < n:
                        q = source.find('"', pos)
                        if q == -1 or q + 1 + hashes > n:
                            break
                        h = q + 1
                        need_end = h + hashes
                        while h < need_end and source[h] == "#":
                            h += 1
                        if h == need_end:
                            closed_end = h
                            break
                        pos = h
                if closed_end == -1:
                    errors.append(HygieneViolation(
                        path, r_line, r_col, "UNCLOSED_STRING", source[i : k + 1], "Unterminated raw string literal"
                    ))
                    line, col = _advance_pos(source, i, n, line, col)
                    i = n
                    break
                tokens.append(LeanToken("STRING", source[i:closed_end], r_line, r_col, i, closed_end))
                line, col = _advance_pos(source, i, closed_end, line, col)
                i = closed_end
                continue

        if ch == '"':
            s_line, s_col = line, col
            if (
                tokens
                and tokens[-1].kind == "IDENT"
                and not tokens[-1].is_french_quoted
                and tokens[-1].text in _PURE_BUILTIN_INTERPOLATORS
                and _is_unqualified_tok(tokens, len(tokens) - 1)
            ):
                i, line, col = lex_interp_body(i + 1, s_line, s_col, s_line, s_col + 1)
                continue
            j = i + 1
            closed_end = -1
            while True:
                m = _PLAIN_STR_STOP_RE.search(source, j)
                if m is None:
                    break
                mp = m.start()
                if source[mp] == "\\":
                    if mp + 1 >= n:
                        break
                    j = mp + 2
                    continue
                closed_end = mp + 1
                break
            if closed_end == -1:
                errors.append(HygieneViolation(path, s_line, s_col, "UNCLOSED_STRING", '"', "Unterminated string literal"))
                line, col = _advance_pos(source, i, n, line, col)
                i = n
                break
            tokens.append(LeanToken("STRING", source[i:closed_end], s_line, s_col, i, closed_end))
            line, col = _advance_pos(source, i, closed_end, line, col)
            i = closed_end
            continue

        if ch == "«":
            g_line, g_col = line, col
            end_g = source.find("»", i + 1)
            if end_g == -1:
                errors.append(HygieneViolation(
                    path, g_line, g_col, "UNCLOSED_IDENT", "«", "Unterminated French-quoted identifier `«...»`"
                ))
                line, col = _advance_pos(source, i, n, line, col)
                i = n
                break
            ident_text = source[i + 1 : end_g]
            tok_end = end_g + 1
            if _is_attr_head_pos(tokens, bracket_stack, in_attr_count):
                if ident_text == "extern":
                    attr_tok_indices.add(len(tokens))
                elif ident_text != "implemented_by" and (ident_text not in _ALLOWED_PURE_MATH_ATTRS or (tok_end < n and source[tok_end] == ".")):
                    meta_attr_tok_indices.add(len(tokens))
            tokens.append(LeanToken("IDENT", ident_text, g_line, g_col, i, tok_end, is_french_quoted=True))
            line, col = _advance_pos(source, i, tok_end, line, col)
            i = tok_end
            continue

        if _is_ident_start(ch):
            m_asc = _ASCII_IDENT_RE.match(source, i)
            j = m_asc.end() if m_asc is not None else i + 1
            while j < n and _is_ident_cont(source[j]):
                j += 1
            ident_text = source[i:j]
            glued = _ambiguous_glued_ident_reason(tokens, ident_text, source, i, j)
            if glued is not None:
                errors.append(HygieneViolation(path, line, col, "FORBIDDEN_META_SYNTAX", glued[0], glued[1]))
            if _is_attr_head_pos(tokens, bracket_stack, in_attr_count):
                if ident_text == "extern":
                    attr_tok_indices.add(len(tokens))
                elif ident_text != "implemented_by" and ((j < n and source[j] == ".") or (ident_text not in _ATTR_SCOPE_KW and ident_text not in _ALLOWED_PURE_MATH_ATTRS)):
                    meta_attr_tok_indices.add(len(tokens))
            tokens.append(LeanToken("IDENT", ident_text, line, col, i, j))
            col += j - i
            i = j
            continue

        if ch == "'":
            if tokens and tokens[-1].end == i and tokens[-1].text in _INIT_QUOTE_SUFFIX_OP_PREV:
                tokens.append(LeanToken("PUNCT", "'", line, col, i, i + 1))
                col += 1
                i += 1
                continue
            is_scoped_q = bool(
                tokens and tokens[-1].end == i and (
                    tokens[-1].text in _SCOPED_QUOTE_SUFFIX_OP_PREV
                    or (tokens[-1].text == "¹" and len(tokens) >= 2 and tokens[-2].end == tokens[-1].start and tokens[-2].text == "⁻")
                )
            )
            if i + 1 < n and source[i + 1] == "'":
                if is_scoped_q:
                    errors.append(HygieneViolation(
                        path, line, col, "FORBIDDEN_META_SYNTAX", "''",
                        "Ambiguous quote-suffix operator immediately before `''`",
                    ))
                tokens.append(LeanToken("OTHER", "''", line, col, i, i + 2))
                col += 2
                i += 2
                continue
            m_ch = _CHAR_LITERAL_RE.match(source, i)
            if m_ch is not None:
                if is_scoped_q:
                    errors.append(HygieneViolation(
                        path, line, col, "FORBIDDEN_META_SYNTAX", source[i : m_ch.end()],
                        "Ambiguous quote-suffix operator immediately before char literal",
                    ))
                else:
                    c_end = m_ch.end()
                    tokens.append(LeanToken("CHAR", source[i:c_end], line, col, i, c_end))
                    line, col = _advance_pos(source, i, c_end, line, col)
                    i = c_end
                    continue
            tokens.append(LeanToken("PUNCT", "'", line, col, i, i + 1))
            col += 1
            i += 1
            continue

        if "0" <= ch <= "9":
            j = i + 1
            is_qual_dot = bool(
                tokens and tokens[-1].kind == "PUNCT" and tokens[-1].text == "." and _is_qualified_before(tokens, len(tokens) - 1, i)
            )
            is_dioph_const_dot = bool(
                is_qual_dot and len(tokens) >= 2
                and tokens[-2].kind == "IDENT" and not tokens[-2].is_french_quoted and tokens[-2].text == "D"
                and tokens[-2].end == tokens[-1].start and _is_unqualified_tok(tokens, len(tokens) - 2)
            )
            if is_qual_dot and not is_dioph_const_dot:
                while j < n and "0" <= source[j] <= "9":
                    j += 1
            elif ch == "0" and j < n and source[j] in ("x", "X", "b", "B", "o", "O"):
                prefix = source[j].lower()
                digits = _HEX_DIGITS if prefix == "x" else (_BIN_DIGITS if prefix == "b" else _OCT_DIGITS)
                j += 1
                while j < n and (source[j] in digits or source[j] == "_"):
                    j += 1
            else:
                while j < n and "0" <= source[j] <= "9":
                    j += 1
                digit_end = j
                while j < n and (("0" <= source[j] <= "9") or source[j] == "_"):
                    j += 1
                if j < n and source[j] == "." and not (j + 1 < n and source[j + 1] == "."):
                    if j + 1 < n and "0" <= source[j + 1] <= "9":
                        j += 2
                        while j < n and (("0" <= source[j] <= "9") or source[j] == "_"):
                            j += 1
                    elif j + 1 < n and source[j + 1] in ("e", "E"):
                        k = j + 2 + (1 if j + 2 < n and source[j + 2] in ("+", "-") else 0)
                        if k < n and "0" <= source[k] <= "9":
                            j += 1
                if j < n and source[j] in ("e", "E"):
                    k = j + 1 + (1 if j + 1 < n and source[j + 1] in ("+", "-") else 0)
                    if k < n and "0" <= source[k] <= "9":
                        j = k + 1
                        while j < n and (("0" <= source[j] <= "9") or source[j] == "_"):
                            j += 1
                if is_dioph_const_dot and (
                    "_" in source[digit_end:j]
                    or (j > digit_end and j < n and (_is_ident_start(source[j]) or source[j] in ('"', "'", "«")))
                ):
                    errors.append(HygieneViolation(
                        path, line, col, "FORBIDDEN_META_SYNTAX", f"D.{source[i:j]}",
                        "Ambiguous `D.` field-index vs `Dioph` numeral literal",
                    ))
            tokens.append(LeanToken("NUMBER", source[i:j], line, col, i, j))
            col += j - i
            i = j
            continue

        if ch in _PUNCT_CHARS:
            if ch in ("(", "[", "{") and tokens and tokens[-1].kind == "PUNCT" and tokens[-1].text == "`" and tokens[-1].end == i:
                errors.append(HygieneViolation(
                    path, line, col, "FORBIDDEN_META_SYNTAX", f"`{ch}",
                    f"Forbidden syntax quotation `` `{ch} `` under pure-math policy",
                ))
            if ch == "[":
                is_attr_open = bool(
                    tokens and (
                        (tokens[-1].kind == "PUNCT" and tokens[-1].text == "@" and tokens[-1].end == i)
                        or (
                            tokens[-1].kind == "IDENT"
                            and not tokens[-1].is_french_quoted
                            and tokens[-1].text in _ATTR_PREFIX_KW
                            and _is_unqualified_tok(tokens, len(tokens) - 1)
                        )
                    )
                )
                bracket_stack.append(is_attr_open)
                if is_attr_open:
                    in_attr_count += 1
            elif ch == "]":
                if bracket_stack and bracket_stack.pop():
                    in_attr_count -= 1
            elif ch == "{":
                if interp_brace_stack:
                    interp_brace_stack[-1][0] += 1
            elif ch == "}":
                tokens.append(LeanToken("PUNCT", "}", line, col, i, i + 1))
                col += 1
                i += 1
                if interp_brace_stack:
                    if interp_brace_stack[-1][0] > 1:
                        interp_brace_stack[-1][0] -= 1
                    else:
                        _, sl, sc = interp_brace_stack.pop()
                        i, line, col = lex_interp_body(i, sl, sc, line, col)
                continue
            tokens.append(LeanToken("PUNCT", ch, line, col, i, i + 1))
            col += 1
            i += 1
            continue

        tokens.append(LeanToken("OTHER", ch, line, col, i, i + 1))
        col += 1
        i += 1

    if interp_brace_stack and not any(e.rule == "UNCLOSED_STRING" for e in errors):
        _, sl, sc = interp_brace_stack[0]
        errors.append(HygieneViolation(
            path, sl, sc, "UNCLOSED_STRING", '"', "Unterminated interpolated string literal (unclosed `{`)"
        ))

    return tokens, errors, comment_spans, attr_tok_indices, meta_attr_tok_indices


def _lex_lean4(
    source: str, path: str = "<memory>"
) -> tuple[list[LeanToken], list[HygieneViolation], list[tuple[int, int]]]:
    """Lex Lean 4 (v4.32.2) source in a single O(N) pass. Returns (tokens, errors, comment_spans)."""
    tokens, errors, comment_spans, _, _ = _lex_lean4_single_pass(source, path=path)
    return tokens, errors, comment_spans


def tokenize_lean4(
    source: str, path: str = "<memory>"
) -> tuple[list[LeanToken], list[HygieneViolation]]:
    """Lex Lean 4 source accurately (comments, strings, raw/interpolated strings, chars, French quotes)."""
    tokens, errors, _ = _lex_lean4(source, path=path)
    return tokens, errors


def strip_lean_comments(source: str) -> str:
    """Return Lean source with line, nested block, and doc comments replaced by spaces (preserving newlines)."""
    _, _, comment_spans = _lex_lean4(source)
    if not comment_spans:
        return source
    out: list[str] = []
    prev = 0
    for cs, ce in comment_spans:
        if cs > prev:
            out.append(source[prev:cs])
        out.append("".join("\n" if ch == "\n" else " " for ch in source[cs:ce]))
        prev = ce
    if prev < len(source):
        out.append(source[prev:])
    return "".join(out)


def read_lean_source_strict(
    path: Path, display_path: str | None = None
) -> tuple[str | None, list[HygieneViolation]]:
    """Read a Lean source file strictly: reject unreadable files, NUL bytes, and invalid UTF-8."""
    label = display_path or str(path)
    try:
        raw = path.read_bytes()
    except OSError as exc:
        return None, [HygieneViolation(label, 1, 1, "READ_ERROR", "", f"Could not read file: {exc}")]

    viols: list[HygieneViolation] = []
    if b"\x00" in raw:
        idx = raw.find(b"\x00")
        viols.append(HygieneViolation(
            label, raw[:idx].count(b"\n") + 1, idx - raw.rfind(b"\n", 0, idx),
            "NUL_BYTE", "\\x00", "Forbidden NUL byte (\\x00) in Lean source",
        ))
    try:
        src = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        viols.append(HygieneViolation(label, 1, 1, "INVALID_UTF8", "", f"Invalid UTF-8 encoding: {exc}"))
        return None, viols
    return src, viols


def _extract_dotted_name(tokens: Sequence[LeanToken], idx: int) -> tuple[str, int]:
    """Starting at IDENT tokens[idx], merge contiguous `.IDENT` segments with zero whitespace."""
    parts = [tokens[idx].text]
    end_idx = idx
    while (
        end_idx + 2 < len(tokens)
        and tokens[end_idx + 1].kind == "PUNCT"
        and tokens[end_idx + 1].text == "."
        and tokens[end_idx + 2].kind == "IDENT"
        and tokens[end_idx + 1].start == tokens[end_idx].end
        and tokens[end_idx + 2].start == tokens[end_idx + 1].end
    ):
        parts.append(tokens[end_idx + 2].text)
        end_idx += 2
    return ".".join(parts), end_idx


def _extract_imports(tokens: Sequence[LeanToken]) -> list[tuple[str, LeanToken]]:
    """Extract all `import <Module.Path>` statements (honoring `not is_french_quoted` & unqualified `import`)."""
    imports: list[tuple[str, LeanToken]] = []
    i = 0
    n = len(tokens)
    while i < n:
        tok = tokens[i]
        if tok.kind == "IDENT" and tok.text == "import" and not tok.is_french_quoted and _is_unqualified_tok(tokens, i):
            j = i + 1
            if j < n and tokens[j].kind == "IDENT" and tokens[j].text == "all" and not tokens[j].is_french_quoted:
                j += 1
            if j < n and tokens[j].kind == "IDENT":
                mod_name, end_idx = _extract_dotted_name(tokens, j)
                imports.append((mod_name, tokens[j]))
                i = end_idx + 1
                continue
        i += 1
    return imports


def _scan_tokens_and_imports(
    tokens: Sequence[LeanToken],
    path: str,
    mode: str,
    *,
    check_missing_main: bool = True,
    attr_tok_indices: set[int] | None = None,
    meta_attr_tok_indices: set[int] | None = None,
) -> list[HygieneViolation]:
    """Scan an already-lexed Lean 4 token stream for forbidden tokens, Option A rules, and imports in O(N)."""
    violations: list[HygieneViolation] = []
    n = len(tokens)
    scanned_dotted_end = -1
    emitted_dotted: set[int] = set()
    in_notation_lhs = False
    notation_paren_depth = 0
    notation_delim_stack: list[str] = []
    notation_delim_err = False
    notation_start_tok: LeanToken | None = None
    has_first_order = False
    eq_quote_toks: list[LeanToken] = []

    def _emit(tok: LeanToken, rule: str, label: str, msg: str) -> None:
        violations.append(HygieneViolation(path, tok.line, tok.col, rule, label, msg))

    def _close_notation_lhs() -> None:
        nonlocal in_notation_lhs, notation_paren_depth, notation_delim_err, notation_start_tok
        if in_notation_lhs and (notation_delim_stack or notation_delim_err) and notation_start_tok is not None:
            _emit(
                notation_start_tok, "FORBIDDEN_META_SYNTAX", notation_start_tok.text,
                "Forbidden unbalanced delimiter atom (`{}`/`()`/`[]`) in notation/mixfix declaration",
            )
        in_notation_lhs = False
        notation_paren_depth = 0
        notation_delim_stack.clear()
        notation_delim_err = False
        notation_start_tok = None

    for idx, tok in enumerate(tokens):
        if in_notation_lhs:
            if tok.kind == "STRING":
                decoded_atom = _decode_lean_str_lit(tok.text).strip(" \t\n\r")
                if _is_forbidden_notation_atom(decoded_atom):
                    _emit(tok, "FORBIDDEN_META_SYNTAX", decoded_atom, f"Forbidden notation/mixfix LHS atom `{decoded_atom}`")
                elif decoded_atom in _NOTATION_ALL_DELIMS:
                    if notation_paren_depth > 0:
                        _emit(tok, "FORBIDDEN_META_SYNTAX", decoded_atom, f"Forbidden `{decoded_atom}` atom inside parenthesized notation group")
                    elif decoded_atom in _NOTATION_OPEN_DELIMS:
                        notation_delim_stack.append(_NOTATION_OPEN_DELIMS[decoded_atom])
                    elif notation_delim_stack and notation_delim_stack[-1] == decoded_atom:
                        notation_delim_stack.pop()
                    else:
                        notation_delim_err = True
                continue
            if tok.kind == "PUNCT":
                if tok.text == "(":
                    notation_paren_depth += 1
                    continue
                if tok.text == ")":
                    if notation_paren_depth > 0:
                        notation_paren_depth -= 1
                    else:
                        _close_notation_lhs()
                    continue
                if notation_paren_depth == 0 and tok.text in _NOTATION_LHS_RESET_PUNCT:
                    _close_notation_lhs()
                    continue
            elif tok.kind == "OTHER" and notation_paren_depth == 0 and tok.text in _NOTATION_LHS_RESET_OTHER:
                _close_notation_lhs()
                continue

        if tok.kind == "OTHER" and tok.text == "=" and idx + 1 < n and tokens[idx + 1].start == tok.end and (
            tokens[idx + 1].kind == "CHAR" or (tokens[idx + 1].kind == "OTHER" and tokens[idx + 1].text == "''")
        ):
            eq_quote_toks.append(tok)
        if tok.kind != "IDENT":
            continue
        if tok.text in ("FirstOrder", "ModelTheory"):
            has_first_order = True

        if not tok.is_french_quoted and _is_unqualified_tok(tokens, idx):
            if tok.text in _NOTATION_INTRO_KW:
                if tok.text == "notation" or (
                    idx + 1 < n and tokens[idx + 1].kind == "PUNCT" and tokens[idx + 1].text == ":"
                ):
                    _close_notation_lhs()
                    in_notation_lhs = True
                    notation_start_tok = tok
            elif in_notation_lhs and notation_paren_depth == 0 and tok.text in _NOTATION_END_KW:
                _close_notation_lhs()

        if idx > scanned_dotted_end and (
            (idx + 2 < n and tokens[idx + 1].kind == "PUNCT" and tokens[idx + 1].text == ".") or "." in tok.text
        ):
            dotted, end_idx = _extract_dotted_name(tokens, idx)
            scanned_dotted_end = end_idx
            if end_idx > idx or "." in tok.text:
                segments = [seg.strip("«»") for seg in dotted.split(".")]
                if segments[-1] in _TRUST_AXIOM_LEAVES or any(seg in _TRUST_AXIOM_LEAVES for seg in segments):
                    emitted_dotted.update(range(idx, end_idx + 1))
                    _emit(tok, "FORBIDDEN_TRUST_AXIOM", dotted, f"Forbidden compiler-trust reference `{dotted}`")
                if segments[-1] == "skipKernelTC" or "skipKernelTC" in segments:
                    emitted_dotted.update(range(idx, end_idx + 1))
                    _emit(tok, "FORBIDDEN_SKIP_KERNEL", dotted, f"Forbidden kernel-bypass option `{dotted}`")

        word = tok.text.strip("«»")
        if word in ("sorry", "sorryAx"):
            _emit(tok, "FORBIDDEN_SORRY", word, f"Forbidden incomplete proof token `{word}`")
        elif word == "admit":
            _emit(tok, "FORBIDDEN_ADMIT", word, "Forbidden incomplete proof tactic `admit`")
        elif word == "axiom":
            _emit(tok, "FORBIDDEN_AXIOM", word, "Forbidden custom `axiom` declaration")
        elif word in ("unsafe", "unsafeCast", "lcProof"):
            _emit(tok, "FORBIDDEN_UNSAFE", word, f"Forbidden unsound escape token `{word}`")
        elif word == "implemented_by":
            _emit(tok, "FORBIDDEN_IMPLEMENTED_BY", word, "Forbidden `@[implemented_by]` kernel/runtime substitution")
        elif word == "extern":
            if (idx + 1 < n and tokens[idx + 1].kind == "STRING") or (attr_tok_indices is not None and idx in attr_tok_indices):
                _emit(tok, "FORBIDDEN_EXTERN", word, "Forbidden `@[extern]` external FFI override")
        elif word == "native_decide":
            _emit(tok, "FORBIDDEN_NATIVE_DECIDE", word, "Forbidden `native_decide` tactic (introduces Lean.ofReduceBool)")
        elif word in _TRUST_AXIOM_LEAVES:
            if idx not in emitted_dotted:
                _emit(tok, "FORBIDDEN_TRUST_AXIOM", word, f"Forbidden compiler-trust identifier `{word}`")
        elif word == "skipKernelTC":
            if idx not in emitted_dotted:
                _emit(tok, "FORBIDDEN_SKIP_KERNEL", word, "Forbidden kernel-bypass option `skipKernelTC`")
        elif not tok.is_french_quoted and word in _FORBIDDEN_DBG_TRACE_KW:
            _emit(tok, "FORBIDDEN_DBG_TRACE", word, f"Forbidden debug-trace construct `{word}` under pure-math policy")
        elif (
            (not tok.is_french_quoted and word in _FORBIDDEN_META_SYNTAX_KW)
            or (word in _FORBIDDEN_META_SYNTAX_ALWAYS)
            or (meta_attr_tok_indices is not None and idx in meta_attr_tok_indices)
        ):
            _emit(tok, "FORBIDDEN_META_SYNTAX", word, f"Forbidden metaprogramming/parser syntax `{word}` under pure-math policy")
        elif word in _FORBIDDEN_META_API_ALWAYS or (
            not tok.is_french_quoted
            and (
                word in _FORBIDDEN_META_API_KW
                or word.startswith("logNamed")
                or (
                    word == "trace"
                    and idx + 1 < n
                    and tokens[idx + 1].kind == "PUNCT"
                    and tokens[idx + 1].text == "["
                    and tokens[idx + 1].start == tok.end
                )
            )
        ):
            tok_label = "trace[" if word == "trace" else word
            _emit(tok, "FORBIDDEN_META_API", tok_label, f"Forbidden compiler/meta API `{tok_label}` under pure-math policy")

    _close_notation_lhs()
    if has_first_order and eq_quote_toks:
        for eq_tok in eq_quote_toks:
            _emit(eq_tok, "FORBIDDEN_META_SYNTAX", "='", "Ambiguous `FirstOrder` `='` operator immediately before quote/char literal")

    seen_main = False
    for mod_name, mod_tok in _extract_imports(tokens):
        if mod_name == "Mathlib":
            _emit(mod_tok, "WHOLESALE_MATHLIB_IMPORT", mod_name, "Wholesale `import Mathlib` forbidden by RAM/leaf-import guardrail")
        elif mod_name.split(".", 1)[0] in _FORBIDDEN_DSL_IMPORT_ROOTS:
            _emit(mod_tok, "FORBIDDEN_META_SYNTAX", mod_name, f"Forbidden DSL/widget/metaprogramming import `{mod_name}` under pure-math policy")
        if mode == "audit":
            if mod_name == "ShannonC7.Main":
                seen_main = True
            elif mod_name == "ShannonC7" or mod_name.startswith("ShannonC7."):
                _emit(mod_tok, "OPAQUE_BOX_VIOLATION", mod_name, f"Opaque-box violation: audit module must NOT import `{mod_name}` (only `ShannonC7.Main` allowed)")

    if mode == "audit" and check_missing_main and not seen_main:
        violations.append(HygieneViolation(path, 1, 1, "MISSING_MAIN_IMPORT", "ShannonC7.Main", "Audit module must import `ShannonC7.Main`"))

    return violations


def scan_lean_hygiene(
    source: str, path: str = "<memory>", mode: str = "impl"
) -> list[HygieneViolation]:
    """Scan Lean 4 source in a single O(N) pass under the Option A Fail-Closed Pure-Math Policy."""
    if mode not in ("impl", "audit"):
        raise ValueError(f"Invalid hygiene scan mode: {mode!r}")
    tokens, errors, _, attr_tok_indices, meta_attr_tok_indices = _lex_lean4_single_pass(source, path=path)
    return errors + _scan_tokens_and_imports(
        tokens, path, mode, attr_tok_indices=attr_tok_indices, meta_attr_tok_indices=meta_attr_tok_indices
    )


# ---------------------------------------------------------------------------
# 3. `#print axioms` Parser, `E2E_CONST` Extractor & Whitelist Verifier
# ---------------------------------------------------------------------------

_AXIOM_HEAD_RE = re.compile(
    r"(?P<none>does not depend on any axioms)|depends on axioms:\s*\["
)
_E2E_CONST_RE = re.compile(
    r"^[ \t]*E2E_CONST[ \t]+([A-Za-z0-9_]+)[ \t]*=[ \t]*(\d+)[ \t\r]*$",
    re.MULTILINE,
)
_UNKNOWN_CONST_PREFIX_RE = re.compile(r"unknown\s+(?:constant|identifier)\s+", re.IGNORECASE)


def _extract_axiom_decl_before(output: str, end_idx: int, min_start: int) -> str | None:
    """Extract the Lean 4 declaration name preceding `end_idx` in strict O(end_idx - min_start)."""
    if end_idx <= min_start:
        return None
    line_start = output.rfind("\n", min_start, end_idx) + 1
    if line_start < min_start:
        line_start = min_start
    last_ch = output[end_idx - 1]
    if last_ch == "`":
        open_bt = output.rfind("`", line_start, end_idx - 1)
        if open_bt == -1 or open_bt + 1 >= end_idx - 1:
            return None
        return output[open_bt + 1 : end_idx - 1].strip()
    if last_ch == "'":
        j = end_idx - 2
        while j >= line_start:
            c = output[j]
            if c == "»":
                open_g = output.rfind("«", line_start, j)
                if open_g == -1:
                    return None
                j = open_g - 1
                continue
            if c == "'":
                if j == line_start or output[j - 1] in " \t\r\n:;":
                    if j + 1 >= end_idx - 1:
                        return None
                    return output[j + 1 : end_idx - 1].strip()
                j -= 1
                continue
            if c in " \t\r\n:;«":
                return None
            j -= 1
        return None
    return None


def _extract_unknown_consts(raw_output: str) -> list[str]:
    """Extract unknown constant/identifier names from Lean diagnostics in strict O(N) time."""
    out: list[str] = []
    n = len(raw_output)
    pos = 0
    cached_line_end = -1
    no_close_g_line_end = -1
    no_close_bt_line_end = -1
    while pos < n:
        m = _UNKNOWN_CONST_PREFIX_RE.search(raw_output, pos)
        if m is None:
            break
        j = m.end()
        if j >= n:
            break
        if j >= cached_line_end:
            le = raw_output.find("\n", j)
            cached_line_end = n if le == -1 else le
        line_end = cached_line_end
        q = raw_output[j]
        if q == "`":
            if line_end == no_close_bt_line_end:
                pos = j + 1
                continue
            end_bt = raw_output.find("`", j + 1, line_end)
            if end_bt != -1 and end_bt > j + 1:
                out.append(raw_output[j + 1 : end_bt])
                pos = end_bt + 1
            else:
                if end_bt == -1:
                    no_close_bt_line_end = line_end
                pos = j + 1
            continue
        if q == "'":
            k = j + 1
            last_q = -1
            while k < line_end:
                c = raw_output[k]
                if c == "«":
                    if line_end == no_close_g_line_end:
                        break
                    close_g = raw_output.find("»", k + 1, line_end)
                    if close_g == -1:
                        no_close_g_line_end = line_end
                        break
                    k = close_g + 1
                    continue
                if c in " \t\r:;":
                    break
                if c == "'":
                    nxt_ch = raw_output[k + 1] if k + 1 < line_end else ""
                    if (
                        nxt_ch == ""
                        or nxt_ch in " \t\r\n,;:)"
                        or (
                            nxt_ch == "."
                            and (k + 2 >= line_end or raw_output[k + 2] in " \t\r\n,.;:)")
                        )
                    ):
                        last_q = k
                        k += 1
                        break
                k += 1
            if last_q > j + 1:
                out.append(raw_output[j + 1 : last_q])
                pos = last_q + 1
            else:
                pos = max(k, j + 1)
            continue
        pos = j
    return out


def parse_print_axioms(output: str) -> dict[str, set[str]]:
    """Parse Lean 4 `#print axioms` output (including multi-line wrapped lists) in strict O(N) time.

    Merges duplicate reports for the same declaration via set union so a later clean
    line can never mask an earlier unauthorized axiom (e.g. `sorryAx` / `Lean.ofReduceBool`).
    """
    parsed: dict[str, set[str]] = {}
    n = len(output)
    pos = 0
    prev_end = 0
    cached_close_bracket = -2  # -2 = unsearched, -1 = no `]` remaining
    while pos < n:
        m = _AXIOM_HEAD_RE.search(output, pos)
        if m is None:
            break
        m_start = m.start()
        m_end = m.end()
        ws_end = m_start
        while ws_end > prev_end and output[ws_end - 1].isspace():
            ws_end -= 1
        decl = _extract_axiom_decl_before(output, ws_end, prev_end) if ws_end < m_start else None
        if m.group("none") is not None:
            if decl:
                parsed.setdefault(decl, set())
            prev_end = m_end
            pos = m_end
        else:
            if not decl:
                prev_end = m_end
                pos = m_end
                continue
            if cached_close_bracket != -1 and cached_close_bracket < m_end:
                cached_close_bracket = output.find("]", m_end)
            if cached_close_bracket == -1:
                prev_end = m_end
                pos = m_end
                continue
            close_idx = cached_close_bracket
            body = output[m_end:close_idx]
            axioms = {item.strip() for item in body.split(",") if item.strip()}
            parsed.setdefault(decl, set()).update(axioms)
            prev_end = close_idx + 1
            pos = close_idx + 1
    return parsed


def parse_e2e_consts(output: str) -> dict[str, int]:
    """Parse kernel-evaluated `E2E_CONST key=value` lines emitted by `e2e_audit.lean`."""
    result: dict[str, int] = {}
    for m in _E2E_CONST_RE.finditer(output):
        raw_digits = m.group(2)
        if len(raw_digits) > 100000:
            continue
        result[m.group(1)] = int(raw_digits)
    return result


def verify_axiom_whitelist(
    parsed: dict[str, set[str]],
    required_decls: Sequence[str] = REQUIRED_AUDIT_AXIOM_DECLS,
    whitelist: frozenset[str] = ALLOWED_AXIOMS,
    raw_output: str = "",
) -> tuple[bool, str, dict]:
    """Verify every required declaration is reported and uses ONLY whitelisted axioms."""
    unknowns = (
        _extract_unknown_consts(raw_output)
        if raw_output
        else []
    )
    if not parsed:
        return (
            False,
            "EMPTY_AXIOM_OUTPUT",
            {"parsed_count": 0, "unknown_consts": unknowns},
        )

    missing = [d for d in required_decls if d not in parsed]
    violations: list[dict] = []
    for decl, axs in sorted(parsed.items()):
        bad = sorted(axs - whitelist)
        if bad:
            flagged = sorted(axs & EXPLICITLY_FORBIDDEN_AXIOMS)
            violations.append(
                {
                    "decl": decl,
                    "disallowed": bad,
                    "explicitly_forbidden": flagged,
                    "all_axioms": sorted(axs),
                }
            )

    if violations:
        return (
            False,
            "AXIOM_VIOLATION",
            {
                "violations": violations,
                "missing": missing,
                "unknown_consts": unknowns,
                "checked_count": len(parsed),
            },
        )

    if missing:
        return (
            False,
            "MISSING_AXIOM_REPORT",
            {
                "missing": missing,
                "present_count": len(parsed),
                "required_count": len(required_decls),
                "unknown_consts": unknowns,
            },
        )

    if unknowns:
        return (
            False,
            "MISSING_AXIOM_REPORT",
            {"unknown_consts": unknowns, "present_count": len(parsed)},
        )

    return (
        True,
        "OK",
        {
            "checked_count": len(parsed),
            "required_count": len(required_decls),
            "axioms_used": sorted({a for axs in parsed.values() for a in axs}),
        },
    )


# ---------------------------------------------------------------------------
# 4. Exact Integer, Rational, Cubic & Spectral PSD Math Verifiers
# ---------------------------------------------------------------------------


def _format_ratio_down(p: int, q: int, digits: int = 20) -> str:
    """Exact floor decimal formatting of `p / q` (`q > 0`) without Fraction GCD overhead."""
    approx_int_bits = max(0, abs(p).bit_length() - q.bit_length())
    if approx_int_bits > 200000:
        sign = "-" if p < 0 else ""
        return f"{sign}<int ~2^{approx_int_bits}>"
    if digits <= 0:
        return str(p // q)
    scale = 10**digits
    scaled = (p * scale) // q  # Python // is exact floor division for all signs
    if scaled < 0:
        mag = -scaled
        return f"-{mag // scale}.{mag % scale:0{digits}d}"
    return f"{scaled // scale}.{scaled % scale:0{digits}d}"


def format_fraction_down(frac: Fraction, digits: int = 20) -> str:
    """Format an exact Fraction truncated downward (floor) to `digits` decimal places.

    Uses exact arbitrary-precision integer floor division (zero Decimal precision limits,
    zero scientific notation like '0E-12', handles negative/zero/tiny/giant fractions).
    """
    if not isinstance(frac, Fraction):
        raise TypeError(f"frac must be a Fraction, got {type(frac).__name__}")
    if not _is_strict_int(digits):
        raise TypeError(f"digits must be an int, got {type(digits).__name__}")
    if digits > 50000:
        raise ValueError(
            f"digits={_safe_int_preview(digits)} exceeds maximum supported precision (50000)"
        )
    return _format_ratio_down(frac.numerator, frac.denominator, digits)


def _safe_ratio_preview(p: int, q: int, digits: int = 20, max_int_digits: int = 200) -> str:
    """Format `p / q` (`q > 0`) safely for diagnostics without constructing a reduced Fraction."""
    max_int_digits = max(0, max_int_digits)
    p_bits = abs(p).bit_length()
    q_bits = q.bit_length()
    approx_int_bits = max(0, p_bits - q_bits)
    if approx_int_bits >= max_int_digits * 3 and (
        approx_int_bits >= (max_int_digits * 3322) // 1000 + 2
        or abs(p) >= q * (10**max_int_digits)
    ):
        sign = "-" if p < 0 else ""
        return f"{sign}<rational ~2^{approx_int_bits} (num_bits={p_bits}, den_bits={q_bits})>"
    return _format_ratio_down(p, q, digits)


def _safe_fraction_preview(frac: Fraction, digits: int = 20, max_int_digits: int = 200) -> str:
    """Format a Fraction safely for diagnostic strings, capping astronomical integers to a bit-length preview."""
    return _safe_ratio_preview(frac.numerator, frac.denominator, digits, max_int_digits)


def check_nat_pow_bound(num: int, den: int, d: int, N: int) -> tuple[bool, str]:
    """Exact integer verification of `num^d <= den^d * N` without stringifying giant powers."""
    if not _is_strict_int(d) or d <= 0:
        return False, f"Invalid exponent d={_safe_int_preview(d)} (must be positive int)"
    if not _is_strict_int(den) or den <= 0:
        return False, f"Invalid denominator den={_safe_int_preview(den)} (must be positive int)"
    if not _is_strict_int(num) or num < 0:
        return False, f"Invalid numerator num={_safe_int_preview(num)} (must be non-negative int)"
    if not _is_strict_int(N) or N < 0:
        return False, f"Invalid cardinality N={_safe_int_preview(N)} (must be non-negative int)"

    lhs = pow(num, d)
    rhs = pow(den, d) * N
    if lhs <= rhs:
        return (
            True,
            f"Exact integer power inequality holds for d={_safe_int_preview(d)} (lhs_bits={lhs.bit_length()}, rhs_bits={rhs.bit_length()})",
        )
    preview = _safe_ratio_preview(num, den, 15)
    return (
        False,
        f"Rounded-up violation: ({preview}...)^d > N for d={_safe_int_preview(d)} (lhs_bits={lhs.bit_length()}, rhs_bits={rhs.bit_length()})",
    )


def cubic_p_num(num: int, den: int) -> int:
    """Exact numerator of p(num/den) = (num^3 + 7*num^2*den - 49*num*den^2 + 49*den^3) / den^3.

    Since den > 0 implies den^3 > 0, sign(p(num/den)) == sign(cubic_p_num(num, den))
    with zero Fraction GCD overhead.
    """
    d2 = den * den
    return ((num + 7 * den) * num - 49 * d2) * num + 49 * d2 * den


def cubic_p(t: Fraction) -> Fraction:
    """Minimal polynomial of theta(C7): p(t) = t^3 + 7*t^2 - 49*t + 49."""
    n, d = t.numerator, t.denominator
    return Fraction(cubic_p_num(n, d), d * d * d)


def cubic_p_deriv(t: Fraction) -> Fraction:
    """Derivative p'(t) = 3*t^2 + 14*t - 49 = (3*t - 7)*(t + 7)."""
    return 3 * t * t + 14 * t - 49


def cubic_compl_q(u: Fraction) -> Fraction:
    """Minimal polynomial of theta(C7^c) = 7 / theta(C7): q(u) = u^3 - 7*u^2 + 7*u + 7."""
    return u * u * u - 7 * u * u + 7 * u + 7


def bisect_theta_c7(steps: int = 150) -> tuple[Fraction, Fraction, str]:
    """Exact rational bisection of theta(C7) in [3, 4] via sign of p(t)."""
    if not _is_strict_int(steps) or steps <= 0:
        raise ValueError(f"steps must be a positive int, got {_safe_int_preview(steps)}")
    lo = Fraction(3, 1)
    hi = Fraction(4, 1)
    for _ in range(steps):
        mid = (lo + hi) / 2
        if cubic_p(mid) < 0:
            lo = mid
        else:
            hi = mid
    # Verify lo and hi agree to 30 decimal digits
    lo_str = format_fraction_down(lo, 30)
    hi_str = format_fraction_down(hi, 30)
    if lo_str != hi_str:
        raise ValueError(
            f"bisect_theta_c7(steps={steps}) did not converge to 30 decimal digits: lo={lo_str}, hi={hi_str}"
        )
    return lo, hi, lo_str


def verify_cubic_irreducibility_and_roots() -> tuple[bool, str, dict]:
    """Verify Q-irreducibility, mod-3 irreducibility, 3-root moduli separation,
    exact 8/12/15-digit brackets, and 30-digit bisection of theta(C7).
    """
    # 1. Rational Root Theorem: divisors of 49 are +/- 1, +/- 7, +/- 49
    rat_candidates = (-49, -7, -1, 1, 7, 49)
    rat_evals = {r: int(cubic_p(Fraction(r))) for r in rat_candidates}
    if any(v == 0 for v in rat_evals.values()):
        return False, "MATH_MISMATCH", {"rat_evals": rat_evals}

    # 2. Mod-3 irreducibility: p(0)=1, p(1)=2, p(2)=2 (mod 3)
    mod3 = {x: (x**3 + 7 * x**2 - 49 * x + 49) % 3 for x in (0, 1, 2)}
    if any(v == 0 for v in mod3.values()):
        return False, "MATH_MISMATCH", {"mod3": mod3}

    # 3. Derivative critical points and strict monotonicity on [7/3, inf)
    crit = Fraction(7, 3)
    if cubic_p_deriv(crit) != 0 or cubic_p(crit) != Fraction(-392, 27):
        return False, "MATH_MISMATCH", {"crit_val": str(cubic_p(crit))}
    if cubic_p_deriv(crit + Fraction(1, 10**6)) <= 0 or cubic_p_deriv(Fraction(3)) <= 0:
        return False, "MATH_MISMATCH", {"monotonicity": False}

    # 4. Three real roots separated in (-12,-11), (1,2), (3,4) => |r2| < 2 < 3 < |r3| < 4 < 11 < |r1|
    brackets_ok = (
        cubic_p(Fraction(-12)) < 0 < cubic_p(Fraction(-11))
        and cubic_p(Fraction(1)) > 0 > cubic_p(Fraction(2))
        and cubic_p(Fraction(3)) < 0 < cubic_p(Fraction(4))
    )
    if not brackets_ok:
        return False, "MATH_MISMATCH", {"brackets_ok": False}

    # 5. Exact 8-, 12-, 15-digit brackets and cubic trap
    enclosures_ok = (
        cubic_p(LOVASZ_8_LOWER) < 0 < cubic_p(LOVASZ_8_UPPER)
        and cubic_p(LOVASZ_LOWER_RAT) < 0 < cubic_p(LOVASZ_UPPER_RAT)
        and cubic_p(LOVASZ_15_LOWER) < 0 < cubic_p(LOVASZ_15_UPPER)
        and LOVASZ_CUBIC_TRAP < LOVASZ_UPPER_RAT
        and cubic_p(LOVASZ_CUBIC_TRAP) > 0
    )
    if not enclosures_ok:
        return False, "MATH_MISMATCH", {"enclosures_ok": False}

    # 6. Exact 30-digit bisection
    lo, hi, digits30 = bisect_theta_c7(150)
    if digits30 != THETA_C7_30DIGITS:
        return False, "MATH_MISMATCH", {"digits30": digits30, "expected": THETA_C7_30DIGITS}

    return (
        True,
        "OK",
        {
            "rat_evals": rat_evals,
            "mod3": mod3,
            "theta_c7_30digits": digits30,
            "bisection_width_lt_1e_35": (hi - lo) < Fraction(1, 10**35),
        },
    )


def verify_c7_fourier_psd(
    perturb_nonadj: float = 0.0, perturb_beta: float = 0.0
) -> tuple[bool, str, dict]:
    """Verify Rank-4 Fourier dual PSD certificate W_7 - beta_7 J >= 0 and primal optimal SDP X on C_7."""
    c = math.cos(math.pi / 7.0)
    theta = (7.0 * c) / (1.0 + c)
    beta = (1.0 / theta) + perturb_beta

    # Build 7x7 W_7 = I + (1/(2 cos(pi/7))) A(C_7) with optional non-edge perturbation
    W = [[0.0] * 7 for _ in range(7)]
    for i in range(7):
        W[i][i] = 1.0
        for j in range(7):
            dist = min((i - j) % 7, (j - i) % 7)
            if dist == 1:
                W[i][j] = 1.0 / (2.0 * c)
            elif dist == 2 and perturb_nonadj != 0.0:
                W[i][j] = perturb_nonadj

    # Check diagonal == 1 and non-edge == 0
    max_diag_err = max(abs(W[i][i] - 1.0) for i in range(7))
    max_nonadj_err = 0.0
    for i in range(7):
        for j in range(7):
            dist = min((i - j) % 7, (j - i) % 7)
            if dist >= 2:
                max_nonadj_err = max(max_nonadj_err, abs(W[i][j]))

    if max_diag_err > 1e-12:
        return False, "MATH_MISMATCH", {"reason": "diag != 1", "max_diag_err": max_diag_err}
    if max_nonadj_err > 1e-12:
        return False, "MATH_MISMATCH", {"reason": "nonadj != 0", "max_nonadj_err": max_nonadj_err}

    # Eigenvalues of circulant M = W - beta * J on Fourier modes m = 0..6
    M0 = [W[0][j] - beta for j in range(7)]
    eigs = []
    for m in range(7):
        lam = sum(M0[j] * math.cos(2.0 * math.pi * m * j / 7.0) for j in range(7))
        eigs.append(lam)

    min_eig = min(eigs)
    if min_eig < -1e-11:
        return False, "MATH_MISMATCH", {"reason": "not PSD", "min_eig": min_eig, "eigs": eigs}

    zero_modes = [m for m, val in enumerate(eigs) if abs(val) < 1e-11]
    pos_modes = [m for m, val in enumerate(eigs) if val > 1e-6]
    if zero_modes != [0, 3, 4] or pos_modes != [1, 2, 5, 6]:
        return (
            False,
            "MATH_MISMATCH",
            {"reason": "unexpected mode structure", "zero_modes": zero_modes, "pos_modes": pos_modes},
        )

    # Primal optimal SDP matrix X: X_{0,d} = (cos(pi/7) + cos(6*pi*d/7)) / (7*(1 + cos(pi/7)))
    X0 = [(c + math.cos(6.0 * math.pi * d / 7.0)) / (7.0 * (1.0 + c)) for d in range(7)]
    primal_nonneg = all(v >= -1e-14 for v in X0)
    primal_trace = 7.0 * X0[0]
    primal_obj = 7.0 * sum(X0)
    if not primal_nonneg or abs(primal_trace - 1.0) > 1e-12 or abs(primal_obj - theta) > 1e-11:
        return (
            False,
            "MATH_MISMATCH",
            {"primal_nonneg": primal_nonneg, "primal_trace": primal_trace, "primal_obj": primal_obj},
        )

    return (
        True,
        "OK",
        {
            "theta": theta,
            "rank": len(pos_modes),
            "zero_modes": zero_modes,
            "pos_modes": pos_modes,
            "lambda_1": eigs[1],
            "lambda_2": eigs[2],
            "primal_obj": primal_obj,
        },
    )


def verify_c7_compl_psd() -> tuple[bool, str, dict]:
    """Verify complement C_7^c exact cubic q(u), Rank-2 dual PSD certificate,
    theta(C_7) * theta(C_7^c) = 7, and 17^(1/4) < theta(C_7^c).
    """
    c = math.cos(math.pi / 7.0)
    theta_c7 = (7.0 * c) / (1.0 + c)
    theta_compl = 1.0 + 1.0 / c
    if abs(theta_c7 * theta_compl - 7.0) > 1e-12:
        return False, "MATH_MISMATCH", {"product": theta_c7 * theta_compl}

    # Exact decreasing cubic bracket for q(u) = u^3 - 7u^2 + 7u + 7
    if not (cubic_compl_q(COMPL_LOWER_RAT) > 0 > cubic_compl_q(COMPL_UPPER_RAT)):
        return False, "MATH_MISMATCH", {"compl_bracket": False}

    # Exact integer sandwich: 2^4 < 17 < (2109916264174 / 10^12)^4
    if not (2**4 < 17 and 17 * (10**12) ** 4 < 2109916264174**4):
        return False, "MATH_MISMATCH", {"compl_pow4": False}

    # Rank-2 dual PSD certificate: beta = c/(1+c), W_{i,j} = beta + (1-beta) cos(6*pi*(i-j)/7)
    beta = c / (1.0 + c)
    W0 = [beta + (1.0 - beta) * math.cos(6.0 * math.pi * d / 7.0) for d in range(7)]
    # In C_7^c, non-edges are distance 1 and 6; diagonal is 1.
    if abs(W0[0] - 1.0) > 1e-12 or abs(W0[1]) > 1e-12 or abs(W0[6]) > 1e-12:
        return False, "MATH_MISMATCH", {"W0": W0}

    M0 = [W0[d] - beta for d in range(7)]
    eigs = [
        sum(M0[d] * math.cos(2.0 * math.pi * m * d / 7.0) for d in range(7))
        for m in range(7)
    ]
    if min(eigs) < -1e-11:
        return False, "MATH_MISMATCH", {"eigs": eigs}
    pos_modes = [m for m, v in enumerate(eigs) if v > 1e-6]
    if pos_modes != [3, 4]:
        return False, "MATH_MISMATCH", {"pos_modes": pos_modes}

    return (
        True,
        "OK",
        {
            "theta_compl": theta_compl,
            "product": theta_c7 * theta_compl,
            "rank": len(pos_modes),
            "pos_modes": pos_modes,
        },
    )


def verify_odd_cycle_lovasz_table() -> tuple[bool, str, dict]:
    """Verify theta(C_{2k+1}) = (2k+1)cos(pi/(2k+1)) / (1+cos(pi/(2k+1))) for k=1..7 and k=100."""
    table = {}
    for k in (1, 2, 3, 4, 5, 6, 7, 100):
        n = 2 * k + 1
        c = math.cos(math.pi / n)
        th = (n * c) / (1.0 + c)
        frac_clique = n / 2.0
        if not (th < frac_clique):
            return False, "MATH_MISMATCH", {"k": k, "theta": th, "frac_clique": frac_clique}
        table[n] = th

    if abs(table[3] - 1.0) > 1e-12:
        return False, "MATH_MISMATCH", {"C3": table[3]}
    if abs(table[5] - math.sqrt(5.0)) > 1e-12:
        return False, "MATH_MISMATCH", {"C5": table[5]}
    if abs(table[7] - 3.3176672073940954) > 1e-12:
        return False, "MATH_MISMATCH", {"C7": table[7]}
    if not (100.4 < table[201] < 100.5):
        return False, "MATH_MISMATCH", {"C201": table[201]}

    return True, "OK", {"table": table}


def check_frontier_rational_bounds(num: int, den: int) -> tuple[bool, str, dict]:
    """Exact cross-multiplied Fraction & cubic-root validation of `c7_lower_num / c7_lower_den`."""
    if not _is_strict_int(num) or not _is_strict_int(den):
        return False, "BOUNDS_VIOLATION", {"reason": "num and den must be strict integers (not bool)"}
    if den <= 0:
        return False, "BOUNDS_VIOLATION", {"reason": f"Non-positive denominator den={_safe_int_preview(den)}"}
    if num <= 0:
        return False, "BOUNDS_VIOLATION", {"reason": f"Non-positive numerator num={_safe_int_preview(num)}"}

    dec20 = _safe_ratio_preview(num, den, 20)
    # Keep JSON diagnostics safe even for astronomical integers (> 200 digits)
    num_out: int | str = num if num.bit_length() <= 665 else f"<int bit_length={num.bit_length()}>"
    den_out: int | str = den if den.bit_length() <= 665 else f"<int bit_length={den.bit_length()}>"

    fl_n, fl_d = FLOOR_LOWER.numerator, FLOOR_LOWER.denominator
    lo_n, lo_d = LOVASZ_LOWER_RAT.numerator, LOVASZ_LOWER_RAT.denominator
    up_n, up_d = LOVASZ_UPPER_RAT.numerator, LOVASZ_UPPER_RAT.denominator
    bpz_n, bpz_d = BPZ_LEAN_RECORD.numerator, BPZ_LEAN_RECORD.denominator
    tan_n, tan_d = TANDON_RECORD.numerator, TANDON_RECORD.denominator

    if num * fl_d < fl_n * den:
        return (
            False,
            "BOUNDS_VIOLATION",
            {
                "reason": f"Lower bound {dec20} is below mandatory BPZ v1 floor 3.258805369885",
                "decimal_20": dec20,
                "num": num_out,
                "den": den_out,
            },
        )
    if num * up_d >= up_n * den:
        return (
            False,
            "BOUNDS_VIOLATION",
            {
                "reason": f"Lower bound {dec20} meets or exceeds Lovasz upper ceiling 3.317667207395",
                "decimal_20": dec20,
                "num": num_out,
                "den": den_out,
            },
        )
    # Catch values sneaking into (theta(C7), 3317667207395 / 10^12) via exact zero-GCD integer cubic_p_num.
    # For num/den <= LOVASZ_LOWER_RAT, strict monotonicity of p on [7/3, inf) & p(LOVASZ_LOWER_RAT) < 0 guarantee p < 0.
    if num * lo_d > lo_n * den and cubic_p_num(num, den) >= 0:
        return (
            False,
            "BOUNDS_VIOLATION",
            {
                "reason": f"Lower bound {dec20} exceeds true theta(C7) (cubic p(val) >= 0)",
                "decimal_20": dec20,
                "num": num_out,
                "den": den_out,
            },
        )

    gap_num = up_n * den - num * up_d
    gap_den = up_d * den
    return (
        True,
        "OK",
        {
            "num": num_out,
            "den": den_out,
            "decimal_20": dec20,
            "beats_floor": True,
            "beats_bpz_lean": num * bpz_d >= bpz_n * den,
            "strictly_beats_bpz_lean": num * bpz_d > bpz_n * den,
            "beats_tandon": num * tan_d >= tan_n * den,
            "strictly_beats_tandon": num * tan_d > tan_n * den,
            "gap_to_upper_rat_20": _format_ratio_down(gap_num, gap_den, 20),
        },
    )


# ---------------------------------------------------------------------------
# 5. Profile.star Algebra, ValidTuple Conflict/Privacy Verifier & Trie7
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Profile:
    a: int
    b: int
    c: int
    d: int

    def _safe_repr(self) -> str:
        return (
            f"Profile(a={_safe_int_preview(self.a)}, b={_safe_int_preview(self.b)}, "
            f"c={_safe_int_preview(self.c)}, d={_safe_int_preview(self.d)})"
        )

    def validate(self) -> tuple[bool, str]:
        if not all(_is_strict_int(x) for x in (self.a, self.b, self.c, self.d)):
            return False, f"Non-integer profile entry in {self._safe_repr()}"
        if min(self.a, self.b, self.c, self.d) < 0:
            return False, f"Negative profile entry in {self._safe_repr()}"
        if self.b > self.a:
            return False, f"Profile invariant violated: b={_safe_int_preview(self.b)} > a={_safe_int_preview(self.a)}"
        if self.d > self.c:
            return False, f"Profile invariant violated: d={_safe_int_preview(self.d)} > c={_safe_int_preview(self.c)}"
        return True, "OK"


def profile_star(p: Profile, q: Profile) -> Profile:
    if not isinstance(p, Profile):
        raise TypeError(f"p must be a Profile, got {type(p).__name__}")
    if not isinstance(q, Profile):
        raise TypeError(f"q must be a Profile, got {type(q).__name__}")
    ok_p, msg_p = p.validate()
    if not ok_p:
        raise ValueError(msg_p)
    ok_q, msg_q = q.validate()
    if not ok_q:
        raise ValueError(msg_q)
    res = Profile(
        a=(p.a - p.b) * (q.a - q.b) + p.c * q.b + p.b * q.c,
        b=p.d * q.b + p.b * q.d,
        c=p.c * q.c,
        d=p.d * q.d + (p.c - p.d) * (q.c - q.d),
    )
    ok_r, msg_r = res.validate()
    if not ok_r:
        raise ValueError(msg_r)
    return res


def split_tree_pow(base: Profile, k: int) -> Profile:
    """Balanced split tree for k-fold Profile.star recursion."""
    if not isinstance(base, Profile):
        raise TypeError(f"base must be a Profile, got {type(base).__name__}")
    ok_b, msg_b = base.validate()
    if not ok_b:
        raise ValueError(msg_b)
    if not _is_strict_int(k) or k <= 0:
        raise ValueError(f"k must be a positive integer, got {_safe_int_preview(k)}")
    memo: dict[int, Profile] = {1: base}

    def solve(m: int) -> Profile:
        if m in memo:
            return memo[m]
        left = m // 2
        right = m - left
        res = profile_star(solve(left), solve(right))
        memo[m] = res
        return res

    return solve(k)


def verify_profile_dp() -> tuple[bool, str, dict]:
    """Verify Itty (134753), Gao 103-digit M40, BPZ 103-digit M40, closed forms,
    and exact integer peak-at-k=40 turnover (a_40 > a_20^2 and a_40^3 > a_60^2).
    """
    gao_base = Profile(367, 8, 367, 321)
    bpz_base = Profile(367, 8, 367, 322)

    itty = profile_star(gao_base, gao_base)
    if itty.a != 134753 or itty.a - 367**2 != 64:
        return False, "MATH_MISMATCH", {"itty_a": itty.a}

    gao40 = split_tree_pow(gao_base, 40)
    bpz40 = split_tree_pow(bpz_base, 40)
    if gao40.a != GAO_D200_EXACT_N or bpz40.a != BPZ_D200_EXACT_N:
        return False, "MATH_MISMATCH", {"gao40_match": gao40.a == GAO_D200_EXACT_N, "bpz40_match": bpz40.a == BPZ_D200_EXACT_N}

    # Closed-form check at k=40:
    # Gao: c_k = 367^k, d_k = (367^k + 275^k)/2, b_k = 2*(367^k - 275^k)/23
    # BPZ: c_k = 367^k, d_k = (367^k + 277^k)/2, b_k = 4*(367^k - 277^k)/45
    c40 = 367**40
    if (
        gao40.c != c40
        or gao40.d != (c40 + 275**40) // 2
        or gao40.b != 2 * (c40 - 275**40) // 23
        or bpz40.c != c40
        or bpz40.d != (c40 + 277**40) // 2
        or bpz40.b != 4 * (c40 - 277**40) // 45
    ):
        return False, "MATH_MISMATCH", {"closed_form_ok": False}

    # Exact integer peak-at-k=40 turnover for BPZ homogeneous recursion:
    bpz20 = split_tree_pow(bpz_base, 20)
    bpz60 = split_tree_pow(bpz_base, 60)
    bpz100 = split_tree_pow(bpz_base, 100)
    if not (bpz40.a > bpz20.a**2 and bpz40.a**3 > bpz60.a**2 and bpz40.a**5 > bpz100.a**2):
        return False, "MATH_MISMATCH", {"peak_turnover_ok": False}

    # Exact 12-digit floor checks
    ok_gao_lo, _ = check_nat_pow_bound(3258789153908, 10**12, 200, gao40.a)
    ok_gao_hi, _ = check_nat_pow_bound(3258789153909, 10**12, 200, gao40.a)
    ok_bpz_lo, _ = check_nat_pow_bound(3258805369885, 10**12, 200, bpz40.a)
    ok_bpz_hi, _ = check_nat_pow_bound(3258805369886, 10**12, 200, bpz40.a)
    if not (ok_gao_lo and not ok_gao_hi and ok_bpz_lo and not ok_bpz_hi):
        return False, "MATH_MISMATCH", {"floor_checks_ok": False}

    return (
        True,
        "OK",
        {
            "itty_a": itty.a,
            "gao40_digits": len(str(gao40.a)),
            "bpz40_digits": len(str(bpz40.a)),
            "peak_turnover_ok": True,
        },
    )


def verify_valid_tuple(
    adj_fn: Callable[[object, object], bool],
    I_verts: Sequence[object],
    S_verts: Sequence[object],
    X_verts: Sequence[object],
    f0: dict[object, object],
    f1: dict[object, object],
) -> tuple[bool, str, dict]:
    """Graph-level ValidTuple conflict, toggle_S, privacy, and disjointness verifier.

    Input contract:
      - `adj_fn` must be callable.
      - `I_verts`, `S_verts`, `X_verts` must be `list` or `tuple` of hashable vertices
        (e.g. `int` or `tuple[int, ...]`, NOT mutable lists/dicts).
      - `f0`, `f1` must be Python `dict`s mapping vertices in `S_verts` to hashable vertices.
      - Malformed inputs return `(False, "MATH_MISMATCH", ...)` cleanly (zero `TypeError`/`IndexError`).

    Checks:
      1. I_verts and X_verts are duplicate-free independent sets.
      2. S_verts is duplicate-free and S <= I.
      3. For every s in S: f0[s], f1[s] exist and satisfy the `toggle_S` invariant:
         `(f0[s] == s and f1[s] != s) or (f1[s] == s and f0[s] != s)`
         (enforcing both `f0[s] != f1[s]` and `s in {f0[s], f1[s]}` so `ValidTuple.star`
         pieces remain independent), and closed neighborhoods satisfy
         `N[f0[s]] cap I == {s}` and `N[f1[s]] cap I == {s}` (privacy!).
      4. Distinct toggle images across S do not collide/conflict pairwise:
         f0(S) is independent, f1(S) is independent.
      5. Disjointness on X: X cap N[f0(S)] cap N[f1(S)] == empty.
      6. Computes exact profile (a=|I|, b=|S|, c=|X|, d=|X \\ (N[f0(S)] cup N[f1(S)])|).
    """
    if not callable(adj_fn):
        return False, "MATH_MISMATCH", {"reason": f"adj_fn must be callable, got {type(adj_fn).__name__}"}
    for name, seq in (("I", I_verts), ("S", S_verts), ("X", X_verts)):
        if not isinstance(seq, (list, tuple)):
            return (
                False,
                "MATH_MISMATCH",
                {"reason": f"{name}_verts must be a list or tuple, got {type(seq).__name__}"},
            )
    for name, mapping in (("f0", f0), ("f1", f1)):
        if not isinstance(mapping, dict):
            return False, "MATH_MISMATCH", {"reason": f"{name} must be a dict, got {type(mapping).__name__}"}

    def _checked_vertex_set(
        label: str, verts: Sequence[object]
    ) -> tuple[set[object] | None, tuple[bool, str, dict] | None]:
        try:
            vset = set(verts)
        except TypeError as exc:
            return None, (False, "MATH_MISMATCH", {"reason": f"Unhashable vertex in {label}: {exc}"})
        if len(vset) != len(verts):
            return None, (False, "DUPLICATE_VERTEX", {"set": label})
        return vset, None

    def _safe_sorted(items: Iterable[object]) -> list[object]:
        try:
            return sorted(items)  # type: ignore[type-var]
        except TypeError:
            return sorted(items, key=_safe_int_preview)

    I_set, err_i = _checked_vertex_set("I", I_verts)
    if err_i is not None or I_set is None:
        return err_i or (False, "MATH_MISMATCH", {"reason": "Invalid I_verts"})
    X_set, err_x = _checked_vertex_set("X", X_verts)
    if err_x is not None or X_set is None:
        return err_x or (False, "MATH_MISMATCH", {"reason": "Invalid X_verts"})
    S_set, err_s = _checked_vertex_set("S", S_verts)
    if err_s is not None or S_set is None:
        return err_s or (False, "MATH_MISMATCH", {"reason": "Invalid S_verts"})

    if not S_set.issubset(I_set):
        return False, "MATH_MISMATCH", {"reason": "S is not a subset of I"}

    # Independence of I and X
    for name, verts in (("I", I_verts), ("X", X_verts)):
        for i in range(len(verts)):
            for j in range(i + 1, len(verts)):
                if adj_fn(verts[i], verts[j]):
                    return False, "CONFLICT_EDGE", {"set": name, "u": verts[i], "v": verts[j]}

    def closed_nbr(u: object, v: object) -> bool:
        return u == v or adj_fn(u, v)

    f0_imgs: list[object] = []
    f1_imgs: list[object] = []
    for s in S_verts:
        if s not in f0 or s not in f1:
            return False, "MATH_MISMATCH", {"reason": f"Missing toggle image for s={_safe_int_preview(s)}"}
        u0, u1 = f0[s], f1[s]
        for lbl, img in (("f0", u0), ("f1", u1)):
            try:
                hash(img)
            except TypeError as exc:
                return (
                    False,
                    "MATH_MISMATCH",
                    {"reason": f"Unhashable toggle image in {lbl}[{_safe_int_preview(s)}]: {exc}"},
                )
        if not ((u0 == s and u1 != s) or (u1 == s and u0 != s)):
            return (
                False,
                "MATH_MISMATCH",
                {
                    "reason": f"Toggle invariant toggle_S violated for s={_safe_int_preview(s)}: require f0[s] != f1[s] and s in {{f0[s], f1[s]}}",
                    "s": s,
                    "f0": u0,
                    "f1": u1,
                },
            )
        f0_imgs.append(u0)
        f1_imgs.append(u1)
        # Privacy check: N[u0] cap I == {s} and N[u1] cap I == {s}
        hit0 = {v for v in I_verts if closed_nbr(u0, v)}
        hit1 = {v for v in I_verts if closed_nbr(u1, v)}
        if hit0 != {s}:
            return False, "PRIVACY_VIOLATION", {"toggle": "f0", "s": s, "hits": _safe_sorted(hit0)}
        if hit1 != {s}:
            return False, "PRIVACY_VIOLATION", {"toggle": "f1", "s": s, "hits": _safe_sorted(hit1)}

    # Check f0(S) and f1(S) are independent sets (no cross-toggle collisions)
    for label, imgs in (("f0(S)", f0_imgs), ("f1(S)", f1_imgs)):
        _, err_imgs = _checked_vertex_set(label, imgs)
        if err_imgs is not None:
            return err_imgs
        for i in range(len(imgs)):
            for j in range(i + 1, len(imgs)):
                if adj_fn(imgs[i], imgs[j]):
                    return False, "CONFLICT_EDGE", {"set": label, "u": imgs[i], "v": imgs[j]}

    # Disjointness on X: no x in X can be in both N[f0(S)] and N[f1(S)]
    n0 = {x for x in X_verts if any(closed_nbr(u0, x) for u0 in f0_imgs)}
    n1 = {x for x in X_verts if any(closed_nbr(u1, x) for u1 in f1_imgs)}
    overlap = n0 & n1
    if overlap:
        return False, "DISJOINTNESS_VIOLATION", {"overlap": _safe_sorted(overlap)}

    d_count = len(X_set - (n0 | n1))
    prof = Profile(a=len(I_verts), b=len(S_verts), c=len(X_verts), d=d_count)
    ok_p, msg_p = prof.validate()
    if not ok_p:
        return False, "MATH_MISMATCH", {"reason": msg_p}

    return True, "OK", {"profile": (prof.a, prof.b, prof.c, prof.d)}


def build_synthetic_c7_valid_tuple() -> tuple[list[int], list[int], list[int], dict[int, int], dict[int, int]]:
    """Minimal verified ValidTuple on C_7 with profile (a=3, b=1, c=2, d=2)."""
    I_verts = [0, 2, 4]
    S_verts = [0]
    X_verts = [2, 4]
    f0 = {0: 0}
    f1 = {0: 6}
    return I_verts, S_verts, X_verts, f0, f1


class Trie7:
    """Reference Radix-7 Trie implementing exact strong-power C_7 independence & disjointness."""

    __slots__ = ("depth", "present", "children")

    def __init__(self, depth: int, present: bool = False) -> None:
        self.depth = depth
        self.present = present
        self.children: list[Trie7 | None] = [None] * 7 if depth > 0 else []

    @classmethod
    def from_vertices(cls, vertices: Sequence[Sequence[int]], d: int) -> tuple["Trie7 | None", str, dict]:
        if not _is_strict_int(d) or d < 0:
            return None, "MATH_MISMATCH", {"reason": f"Invalid dimension d={_safe_int_preview(d)} (must be non-negative int)"}
        if not isinstance(vertices, (list, tuple)):
            return None, "MATH_MISMATCH", {"reason": "vertices must be a list or tuple"}
        root = cls(d, present=False)
        for idx, v in enumerate(vertices):
            if not isinstance(v, (list, tuple)) or len(v) != d:
                return None, "MATH_MISMATCH", {"reason": f"Malformed vertex at index {idx}: expected tuple/list of length {_safe_int_preview(d)}"}
            node = root
            for coord in v:
                if not _is_strict_int(coord) or not (0 <= coord < 7):
                    return None, "MATH_MISMATCH", {"reason": f"Invalid ZMod 7 coordinate {_safe_int_preview(coord)} at index {idx}"}
                nxt = node.children[coord]
                if nxt is None:
                    nxt = cls(node.depth - 1, present=False)
                    node.children[coord] = nxt
                node = nxt
            if node.present:
                return None, "DUPLICATE_VERTEX", {"index": idx, "vertex": tuple(v)}
            node.present = True
        return root, "OK", {"card": root.card()}

    def card(self) -> int:
        if self.depth == 0:
            return 1 if self.present else 0
        return sum(ch.card() for ch in self.children if ch is not None)

    @staticmethod
    def _no_conflict(t1: "Trie7 | None", t2: "Trie7 | None") -> bool:
        """True iff no vertex in t1 is equal or C_7^d-adjacent to any vertex in t2."""
        if t1 is None or t2 is None:
            return True
        if t1.depth == 0:
            return not (t1.present and t2.present)
        for u in range(7):
            c1 = t1.children[u]
            if c1 is None:
                continue
            for dv in (-1, 0, 1):
                c2 = t2.children[(u + dv) % 7]
                if c2 is not None and not Trie7._no_conflict(c1, c2):
                    return False
        return True

    def is_indep(self) -> bool:
        """Exact recursive strong-power C_7^d independence check (matches Lean Trie7.isIndep)."""
        if self.depth == 0:
            return True
        for u in range(7):
            cu = self.children[u]
            if cu is None:
                continue
            if not cu.is_indep():
                return False
            cv = self.children[(u + 1) % 7]
            if cv is not None and not Trie7._no_conflict(cu, cv):
                return False
        return True

    def disjoint(self, other: "Trie7") -> bool:
        if not isinstance(other, Trie7):
            raise TypeError(f"other must be a Trie7, got {type(other).__name__}")
        if self.depth != other.depth:
            return False
        if self.depth == 0:
            return not (self.present and other.present)
        for u in range(7):
            c1 = self.children[u]
            c2 = other.children[u]
            if c1 is not None and c2 is not None and not c1.disjoint(c2):
                return False
        return True


# ---------------------------------------------------------------------------
# 6. Graph Adjacencies, Strong-Power Witness Verifier & Canonical Witnesses
# ---------------------------------------------------------------------------


def c5_adj(u: int, v: int) -> bool:
    return u != v and ((u - v) % 5 in (1, 4))


def c7_adj(u: int, v: int) -> bool:
    return u != v and ((u - v) % 7 in (1, 6))


def c7_compl_adj(u: int, v: int) -> bool:
    return u != v and ((u - v) % 7 in (2, 3, 4, 5))


def gilbert32_adj(u: int, v: int) -> bool:
    return u != v and ((u ^ v).bit_count() in (1, 2))


def verify_strong_power_independent_set(
    vertices: Sequence[Sequence[int]],
    adj_fn: Callable[[int, int], bool],
    d: int,
    domain_size: int | None = None,
) -> tuple[bool, str, dict]:
    """Verify exact strong-power independence, tuple lengths, coordinate bounds, and uniqueness."""
    if not callable(adj_fn):
        return False, "MATH_MISMATCH", {"reason": f"adj_fn must be callable, got {type(adj_fn).__name__}"}
    if not _is_strict_int(d) or d <= 0:
        return False, "MATH_MISMATCH", {"reason": f"Invalid strong-power dimension d={_safe_int_preview(d)} (must be positive int)"}
    if domain_size is not None and (not _is_strict_int(domain_size) or domain_size <= 0):
        return False, "MATH_MISMATCH", {"reason": f"Invalid domain_size={_safe_int_preview(domain_size)} (must be positive int)"}
    if not isinstance(vertices, (list, tuple)):
        return False, "MATH_MISMATCH", {"reason": "vertices must be a list or tuple"}
    seen: dict[tuple[int, ...], int] = {}
    norm: list[tuple[int, ...]] = []
    for idx, raw in enumerate(vertices):
        if not isinstance(raw, (list, tuple)) or len(raw) != d:
            return (
                False,
                "MATH_MISMATCH",
                {"reason": f"Malformed vertex at index {idx}: expected tuple of length {_safe_int_preview(d)}"},
            )
        coords: list[int] = []
        for coord in raw:
            if not _is_strict_int(coord):
                return False, "MATH_MISMATCH", {"reason": f"Non-integer coordinate {_safe_int_preview(coord)} at index {idx}"}
            if domain_size is not None and not (0 <= coord < domain_size):
                return (
                    False,
                    "MATH_MISMATCH",
                    {"reason": f"Coordinate {_safe_int_preview(coord)} out of range [0, {_safe_int_preview(domain_size)}) at index {idx}"},
                )
            coords.append(coord)
        tup = tuple(coords)
        if tup in seen:
            return (
                False,
                "DUPLICATE_VERTEX",
                {"first_index": seen[tup], "dup_index": idx, "vertex": list(tup)},
            )
        seen[tup] = idx
        norm.append(tup)

    n = len(norm)
    for i in range(n):
        x = norm[i]
        for j in range(i + 1, n):
            y = norm[j]
            # Independent in G^d iff there exists coordinate k with x[k] != y[k] and not adj(x[k], y[k])
            independent = False
            for k in range(d):
                if x[k] != y[k] and not adj_fn(x[k], y[k]):
                    independent = True
                    break
            if not independent:
                return (
                    False,
                    "CONFLICT_EDGE",
                    {"i": i, "j": j, "u": list(x), "v": list(y)},
                )

    return True, "OK", {"card": n, "d": d}


# Empirically verified canonical witnesses
WITNESS_C5_POW2: tuple[tuple[int, ...], ...] = (
    (0, 0), (1, 2), (2, 4), (3, 1), (4, 3),
)

WITNESS_C7_POW1: tuple[tuple[int, ...], ...] = (
    (0,), (2,), (4,),
)

WITNESS_C7_POW2: tuple[tuple[int, ...], ...] = (
    (0, 0), (0, 2), (1, 4), (2, 0), (2, 2),
    (3, 4), (4, 1), (4, 6), (5, 3), (6, 5),
)

WITNESS_C7_POW3: tuple[tuple[int, ...], ...] = (
    (0, 1, 1), (0, 4, 2), (0, 4, 4), (0, 6, 0), (0, 6, 5),
    (1, 1, 4), (1, 1, 6), (1, 3, 0), (1, 6, 3),
    (2, 1, 2), (2, 3, 3), (2, 3, 5), (2, 5, 6), (2, 6, 1),
    (3, 0, 4), (3, 0, 6), (3, 2, 0), (3, 4, 1), (3, 5, 4),
    (4, 0, 2), (4, 2, 5), (4, 3, 3), (4, 4, 6),
    (5, 0, 5), (5, 1, 0), (5, 3, 1), (5, 5, 2), (5, 5, 4), (5, 6, 0),
    (6, 0, 3), (6, 2, 3), (6, 2, 5), (6, 4, 6),
)

WITNESS_C7_COMPL_POW4: tuple[tuple[int, ...], ...] = (
    (0, 0, 0, 0),
    (0, 0, 1, 3), (0, 1, 3, 0), (1, 3, 0, 0), (3, 0, 0, 6),
    (0, 0, 6, 4), (0, 6, 4, 0), (6, 4, 0, 0), (4, 0, 0, 1),
    (1, 2, 6, 3), (2, 6, 3, 6), (6, 3, 6, 5), (3, 6, 5, 1),
    (6, 5, 1, 4), (5, 1, 4, 1), (1, 4, 1, 2), (4, 1, 2, 6),
)

WITNESS_GILBERT32_POW2: tuple[tuple[int, ...], ...] = (
    (3, 3), (6, 12), (12, 17), (24, 6), (17, 24),
    (5, 22), (10, 26), (20, 11), (9, 13), (18, 21),
    (7, 25), (14, 7), (28, 28), (25, 19), (19, 14),
    (11, 20), (22, 18), (13, 10), (26, 9), (21, 5),
)


def build_c7_pow5_linear_343() -> list[tuple[int, int, int, int, int]]:
    """Baumert et al. (1971) 343-word linear subspace in C_7^5:
    kernel over F_7 of H = [[1,0,1,1,3], [0,1,2,4,1]].
    """
    words: list[tuple[int, int, int, int, int]] = []
    for x2 in range(7):
        for x3 in range(7):
            for x4 in range(7):
                x0 = (-(x2 + x3 + 3 * x4)) % 7
                x1 = (-(2 * x2 + 4 * x3 + x4)) % 7
                words.append((x0, x1, x2, x3, x4))
    return words


def build_polak_schrijver_clean_327() -> list[tuple[int, int, int, int, int]]:
    """Polak-Schrijver quantized cyclic seed in C_7^5 yielding exact 327 conflict-free words."""
    shift = (40, 123, 40, 123, 40)
    mult = (1, 7, 49, 343, 2401)
    raw = []
    for t in range(382):
        w = tuple(int(((t * mult[k] + shift[k]) % 382) / 54.5) for k in range(5))
        raw.append(w)
    # Remove any vertex involved in any conflict (including duplicates)
    n = len(raw)
    bad = [False] * n
    for i in range(n):
        xi = raw[i]
        for j in range(i + 1, n):
            xj = raw[j]
            if all(xi[k] == xj[k] or c7_adj(xi[k], xj[k]) for k in range(5)):
                bad[i] = True
                bad[j] = True
    return [raw[i] for i in range(n) if not bad[i]]


def verify_witness_json(path: Path) -> tuple[bool, str, dict]:
    """Validate an external JSON witness artifact `{graph, d, vertices[, num, den]}`."""
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return False, "MISSING_FILE", {"path": str(path)}
    except Exception as exc:
        return False, "MATH_MISMATCH", {"path": str(path), "error": str(exc)}

    if not isinstance(data, dict):
        return False, "MATH_MISMATCH", {"path": str(path), "reason": "JSON root is not an object"}
    if "vertices" not in data or "d" not in data:
        return False, "MATH_MISMATCH", {"path": str(path), "reason": "Missing required `d` or `vertices` keys"}

    graph = data.get("graph", "C7")
    graph_map: dict[str, tuple[Callable[[int, int], bool], int]] = {
        "C7": (c7_adj, 7),
        "C7_compl": (c7_compl_adj, 7),
        "C5": (c5_adj, 5),
        "SasonGilbert32": (gilbert32_adj, 32),
    }
    if not isinstance(graph, str) or graph not in graph_map:
        return False, "MATH_MISMATCH", {"reason": f"Unsupported graph `{graph!r}`"}
    adj_fn, dom = graph_map[graph]
    d = data["d"]
    if not _is_strict_int(d) or d <= 0:
        return False, "MATH_MISMATCH", {"reason": f"Invalid dimension `d`={_safe_int_preview(d)} (must be positive int)"}
    verts = data["vertices"]
    if not isinstance(verts, list) or len(verts) == 0:
        return False, "MATH_MISMATCH", {"reason": "Empty or non-list `vertices`"}

    ok, code, info = verify_strong_power_independent_set(verts, adj_fn, d, domain_size=dom)
    if not ok:
        return False, code, info

    if "num" in data or "den" in data:
        if "num" not in data or "den" not in data:
            return False, "BOUNDS_VIOLATION", {"reason": "Witness JSON must provide both `num` and `den` when specifying a bound", **info}
        ok_p, msg_p = check_nat_pow_bound(data["num"], data["den"], d, len(verts))
        if not ok_p:
            return False, "BOUNDS_VIOLATION", {"reason": msg_p, **info}

    return True, "OK", {"graph": graph, **info}


# ---------------------------------------------------------------------------
# 7. Exact Rational Linear Algebra & All 5 Obstruction Graphs
# ---------------------------------------------------------------------------


def exact_rational_rank(matrix: Sequence[Sequence[int | Fraction]]) -> int:
    """Exact Gaussian elimination over Q (zero floating-point rounding)."""
    rows = [[Fraction(x) for x in row] for row in matrix]
    if not rows:
        return 0
    m = len(rows)
    n = len(rows[0])
    rank = 0
    for col in range(n):
        pivot = None
        for r in range(rank, m):
            if rows[r][col] != 0:
                pivot = r
                break
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        pv = rows[rank][col]
        rows[rank] = [val / pv for val in rows[rank]]
        for r in range(m):
            if r != rank and rows[r][col] != 0:
                factor = rows[r][col]
                rows[r] = [rows[r][c] - factor * rows[rank][c] for c in range(n)]
        rank += 1
        if rank == m:
            break
    return rank


def build_srg27_adjacency() -> list[list[int]]:
    """Build exact 27x27 adjacency matrix of Schlafli complement srg(27, 10, 1, 5):
    vertices = 6 lines a_0..a_5 (0..5), 6 lines b_0..b_5 (6..11), 15 lines c_{ij} (12..26).
    """
    labels: list[tuple[str, tuple[int, ...]]] = []
    for i in range(6):
        labels.append(("a", (i,)))
    for i in range(6):
        labels.append(("b", (i,)))
    for i in range(6):
        for j in range(i + 1, 6):
            labels.append(("c", (i, j)))

    def is_adj(u: tuple[str, tuple[int, ...]], v: tuple[str, tuple[int, ...]]) -> bool:
        tu, iu = u
        tv, iv = v
        if u == v:
            return False
        if (tu, tv) == ("a", "b") or (tu, tv) == ("b", "a"):
            return iu[0] != iv[0]
        if tu in ("a", "b") and tv == "c":
            return iu[0] in iv
        if tv in ("a", "b") and tu == "c":
            return iv[0] in iu
        if tu == "c" and tv == "c":
            return len(set(iu) & set(iv)) == 0
        return False

    A = [[1 if is_adj(labels[i], labels[j]) else 0 for j in range(27)] for i in range(27)]
    return A


def verify_srg27_obstruction() -> tuple[bool, str, dict]:
    """Verify srg(27,10,1,5) parameters, alpha >= 6, theta = 9, exact rank_Q(I - A) = 7 < 9,
    and complement srg(27,16,10,8) rank_Q(I - A_bar) = 27 and rank_Q(4I - A_bar) = 21 (> 3 = alpha).
    """
    A = build_srg27_adjacency()
    n = 27
    # Check symmetry, looplessness, 10-regularity, lambda=1, mu=5
    for i in range(n):
        if A[i][i] != 0:
            return False, "MATH_MISMATCH", {"reason": "self-loop"}
        deg = sum(A[i])
        if deg != 10:
            return False, "MATH_MISMATCH", {"reason": f"deg({i})={deg} != 10"}
        for j in range(i + 1, n):
            if A[i][j] != A[j][i]:
                return False, "MATH_MISMATCH", {"reason": "asymmetric"}
            common = sum(A[i][k] * A[j][k] for k in range(n))
            expected = 1 if A[i][j] == 1 else 5
            if common != expected:
                return False, "MATH_MISMATCH", {"reason": f"common({i},{j})={common} != {expected}"}

    # Verify {a_0..a_5} is an independent set of size 6
    for i in range(6):
        for j in range(i + 1, 6):
            if A[i][j] != 0:
                return False, "CONFLICT_EDGE", {"u": i, "v": j}

    # Verify I - A is a Haemers fitting matrix (diag != 0, non-edges == 0) with exact rank 7
    M = [[(1 if i == j else -A[i][j]) for j in range(n)] for i in range(n)]
    for i in range(n):
        if M[i][i] == 0:
            return False, "MATH_MISMATCH", {"reason": "zero diagonal"}
        for j in range(n):
            if i != j and A[i][j] == 0 and M[i][j] != 0:
                return False, "MATH_MISMATCH", {"reason": "non-edge nonzero in fitting matrix"}
    rank_g = exact_rational_rank(M)
    if rank_g != 7:
        return False, "MATH_MISMATCH", {"rank_Q_I_minus_A": rank_g, "expected": 7}

    # Complement srg(27, 16, 10, 8): eigenvalues 16^(1), 4^(6), -2^(20)
    # => I - A_bar has eigenvalues -15^(1), -3^(6), 3^(20) (exact rank 27 > 3 = alpha(G_bar))
    # => 4I - A_bar has eigenvalues -12^(1), 0^(6), 6^(20) (exact rank 21 > 3 = alpha(G_bar))
    M_bar_1 = [[(1 if i == j else -(1 - A[i][j])) for j in range(n)] for i in range(n)]
    rank_bar_1 = exact_rational_rank(M_bar_1)
    M_bar_4 = [[(4 if i == j else -(1 - A[i][j])) for j in range(n)] for i in range(n)]
    rank_bar_4 = exact_rational_rank(M_bar_4)
    if rank_bar_1 != 27 or rank_bar_4 != 21:
        return (
            False,
            "MATH_MISMATCH",
            {"rank_Q_I_minus_A_bar": rank_bar_1, "rank_Q_4I_minus_A_bar": rank_bar_4},
        )

    return (
        True,
        "OK",
        {
            "n": 27,
            "k": 10,
            "lambda": 1,
            "mu": 5,
            "alpha": 6,
            "lovasz_theta": 9,
            "haemers_rank": rank_g,
            "compl_I_minus_A_rank": rank_bar_1,
            "compl_4I_minus_A_rank": rank_bar_4,
        },
    )


def verify_gilbert32_obstruction() -> tuple[bool, str, dict]:
    """Verify Sason's 32-vertex Gilbert graph: 15-regular, 240 edges, alpha=4,
    20-vertex witness in G^2, exact Krawtchouk LP theta=16/3 and Schrijver theta'=4.
    """
    n = 32
    edges = 0
    for u in range(n):
        deg = sum(1 for v in range(n) if gilbert32_adj(u, v))
        if deg != 15:
            return False, "MATH_MISMATCH", {"u": u, "deg": deg}
        edges += deg
    edges //= 2
    if edges != 240:
        return False, "MATH_MISMATCH", {"edges": edges}

    # Verify 4-vertex independent set in G_32
    alpha4 = [(0,), (7,), (28,), (27,)]
    ok4, code4, _ = verify_strong_power_independent_set(alpha4, gilbert32_adj, 1, domain_size=32)
    if not ok4:
        return False, code4, {"alpha4": False}

    # Verify exact 20-vertex independent set in G_32^2 (proving Theta(G_32) >= sqrt(20) > 4)
    ok20, code20, info20 = verify_strong_power_independent_set(
        WITNESS_GILBERT32_POW2, gilbert32_adj, 2, domain_size=32
    )
    if not ok20 or info20["card"] != 20:
        return False, code20, {"witness_20": info20}

    # Exact Krawtchouk eigenvalues for Hamming scheme H(5,2):
    # K_w(j) = sum_r (-1)^r C(j,r) C(5-j, w-r).
    # For weight-distribution vector a = (1, 0, 0, a3, a4, a5):
    #   PSD condition: for all j=0..5, sum_w a_w * K_w(j) >= 0.
    def krawtchouk(w: int, j: int) -> int:
        total = 0
        for r in range(w + 1):
            if r <= j and (w - r) <= (5 - j):
                total += ((-1) ** r) * math.comb(j, r) * math.comb(5 - j, w - r)
        return total

    # Lovasz theta = 16/3 achieved at (a3, a4, a5) = (1/3, 1/3, -2/3)
    # Objective: 1 + C(5,3)*a3 + C(5,4)*a4 + C(5,5)*a5 = 1 + 10/3 + 5/3 - 2/3 = 16/3
    lov_a = {0: Fraction(1), 3: Fraction(1, 3), 4: Fraction(1, 3), 5: Fraction(-2, 3)}
    lov_obj = sum(math.comb(5, w) * val for w, val in lov_a.items())
    # By Krawtchouk reciprocity: C(5, w) * K_j(w) = C(5, j) * K_w(j),
    # so the dual eigenvalue sign matches sum_w a_w * K_w(j) >= 0.
    lov_psd = all(sum(lov_a[w] * krawtchouk(w, j) for w in lov_a) >= 0 for j in range(6))
    if lov_obj != Fraction(16, 3) or not lov_psd:
        return False, "MATH_MISMATCH", {"lov_obj": str(lov_obj), "lov_psd": lov_psd}

    # Schrijver theta' = 4 achieved at nonnegative (a3, a4, a5) = (1/5, 1/5, 0)
    # Objective: 1 + 10*(1/5) + 5*(1/5) + 0 = 4
    sch_a = {0: Fraction(1), 3: Fraction(1, 5), 4: Fraction(1, 5), 5: Fraction(0)}
    sch_obj = sum(math.comb(5, w) * val for w, val in sch_a.items())
    sch_psd = all(sum(sch_a[w] * krawtchouk(w, j) for w in sch_a) >= 0 for j in range(6))
    sch_nonneg = all(val >= 0 for val in sch_a.values())
    if sch_obj != Fraction(4, 1) or not sch_psd or not sch_nonneg:
        return False, "MATH_MISMATCH", {"sch_obj": str(sch_obj), "sch_psd": sch_psd}

    # Prove Schrijver's 4 < sqrt(20) strictly in integers: 4^2 = 16 < 20
    if not (sch_obj * sch_obj < 20 < lov_obj * lov_obj):
        return False, "MATH_MISMATCH", {"order": False}

    return (
        True,
        "OK",
        {
            "n": 32,
            "degree": 15,
            "edges": 240,
            "alpha": 4,
            "alpha_pow2_ge": 20,
            "schrijver_theta_prime": "4",
            "lovasz_theta": "16/3",
        },
    )


def verify_c5_obstruction() -> tuple[bool, str, dict]:
    """Verify C_5 obstruction invariants: alpha=2, alpha(C_5^2)=5, Theta(C_5)=sqrt(5)."""
    ok5, code5, info5 = verify_strong_power_independent_set(
        WITNESS_C5_POW2, c5_adj, 2, domain_size=5
    )
    if not ok5 or info5["card"] != 5:
        return False, code5, info5
    # Verify alpha(C_5) = 2 (no 3-element independent set in C_5)
    for a in range(5):
        for b in range(a + 1, 5):
            for c in range(b + 1, 5):
                if not (c5_adj(a, b) or c5_adj(a, c) or c5_adj(b, c)):
                    return False, "MATH_MISMATCH", {"unexpected_3set": (a, b, c)}
    return True, "OK", {"n": 5, "alpha": 2, "alpha_pow2": 5, "theta_sq": 5}


def verify_obstruction_graphs() -> tuple[bool, str, dict]:
    """Verify all 5 obstruction graphs: C_5, SasonGilbert32, SRG27, C_7, C_7_compl."""
    results = {}
    for name, fn in (
        ("C5", verify_c5_obstruction),
        ("SasonGilbert32", verify_gilbert32_obstruction),
        ("SRG27", verify_srg27_obstruction),
        ("C7", verify_c7_fourier_psd),
        ("C7_compl", verify_c7_compl_psd),
    ):
        ok, code, info = fn()
        results[name] = {"ok": ok, "code": code, **info}
        if not ok:
            return False, code, {"failed_graph": name, "results": results}
    return True, "OK", results


def validate_upper_bound_claim(graph_name: str, bound: Fraction) -> tuple[bool, str]:
    """Exact rational obstruction gate: reject any claimed upper bound below proven Theta(G) floor."""
    if not isinstance(bound, Fraction):
        return False, f"Invalid bound type {type(bound).__name__} on {graph_name} (expected Fraction)"
    if bound <= 0:
        return False, f"Non-positive upper bound {_safe_fraction_preview(bound, 8)} on {graph_name}"
    p, q = bound.numerator, bound.denominator

    if graph_name == "C5":
        # Theta(C_5) = sqrt(5) => must satisfy (p/q)^2 >= 5
        if p * p < 5 * q * q:
            return False, f"OBSTRUCTION_VIOLATION on C5: {_safe_fraction_preview(bound, 8)} < sqrt(5) (2.23606797...)"
        return True, "Valid upper bound on C5 (>= sqrt(5))"

    if graph_name == "SasonGilbert32":
        # alpha(G_32^2) >= 20 => Theta(G_32) >= sqrt(20) => must satisfy (p/q)^2 >= 20
        if p * p < 20 * q * q:
            return False, f"OBSTRUCTION_VIOLATION on SasonGilbert32: {_safe_fraction_preview(bound, 8)} < sqrt(20) (4.47213595...)"
        return True, "Valid upper bound on SasonGilbert32 (>= sqrt(20))"

    if graph_name == "SRG27":
        # alpha(srg27) = 6 => must satisfy bound >= 6 (Haemers 7 < Lovasz 9 passes)
        if bound < Fraction(6, 1):
            return False, f"OBSTRUCTION_VIOLATION on SRG27: {_safe_fraction_preview(bound, 8)} < alpha = 6"
        return True, "Valid upper bound on SRG27 (>= 6)"

    if graph_name == "C7":
        # Proven lower bound >= FLOOR_LOWER = 3258805369885 / 10^12
        if bound < FLOOR_LOWER:
            return False, f"OBSTRUCTION_VIOLATION on C7: {_safe_fraction_preview(bound, 12)} < proven floor 3.258805369885"
        return True, "Valid upper bound on C7 (>= proven floor)"

    if graph_name == "C7_compl":
        # alpha(C_7^c^4) >= 17 => must satisfy (p/q)^4 >= 17
        if p**4 < 17 * (q**4):
            return False, f"OBSTRUCTION_VIOLATION on C7_compl: {_safe_fraction_preview(bound, 8)} < 17^(1/4) (2.03054318...)"
        return True, "Valid upper bound on C7_compl (>= 17^(1/4))"

    return False, f"Unknown obstruction graph `{graph_name}`"


# ---------------------------------------------------------------------------
# 8. Lean Constant Extractor & Report Consistency / Honesty Verifier
# ---------------------------------------------------------------------------

_LEAN_DECL_BOUNDARY_WORDS = frozenset(
    {
        # Declaration modifiers (Lean v4.32.2 Command.lean:68-121, Term.lean:583-586)
        "private",
        "public",
        "protected",
        "meta",
        "noncomputable",
        "unsafe",
        "partial",
        "nonrec",
        "local",
        "scoped",
        # Module header starters (Module/Syntax.lean:17-25)
        "module",
        "prelude",
        "import",
        # Core declaration keywords (Command.lean:187-287 + Mathlib)
        "def",
        "abbrev",
        "theorem",
        "lemma",
        "opaque",
        "instance",
        "axiom",
        "example",
        "inductive",
        "coinductive",
        "structure",
        "class",
        "deriving",
        "alias",
        # Declaration-body trailers (Command.lean:170)
        "where",
        "termination_by",
        "decreasing_by",
        # Scope, section, and environment commands (Command.lean:288-1010)
        "namespace",
        "section",
        "end",
        "open",
        "export",
        "attribute",
        "set_option",
        "variable",
        "universe",
        "mutual",
        "initialize",
        "builtin_initialize",
        "with_weak_namespace",
        "include",
        "omit",
        "unlock_limits",
        "assert_not_exists",
        "assert_not_imported",
        "add_decl_doc",
        "deprecated_syntax",
        "deprecated_module",
        "recommended_spelling",
        "register_tactic_tag",
        "tactic_extension",
        "register_error_explanation",
        "init_quot",
        # Syntax, macro, elab & notation commands (Syntax.lean:74-140)
        "macro",
        "macro_rules",
        "syntax",
        "declare_syntax_cat",
        "elab",
        "elab_rules",
        "notation",
        "prefix",
        "infix",
        "infixl",
        "infixr",
        "postfix",
        "binder_predicate",
        # Init/Core commands (Init/Notation.lean, Init/Simproc.lean, Init/CbvSimproc.lean)
        "run_cmd",
        "run_elab",
        "run_meta",
        "seal",
        "unseal",
        "simproc",
        "dsimproc",
        "simproc_decl",
        "dsimproc_decl",
        "builtin_simproc",
        "builtin_dsimproc",
        "cbv_simproc",
        "cbv_simproc_decl",
        "unif_hint",
        "register_simp_attr",
        "register_option",
        "register_builtin_option",
        "register_linter_set",
    }
)

_MAX_NAT_EVAL_DEPTH = 64
_MAX_NAT_LITERAL_DIGITS = 60000
_MAX_NAT_EVAL_BITS = 250000


def _eval_nat_tokens(toks: Sequence[LeanToken]) -> int | None:
    """Safely evaluate simple positive Nat arithmetic tokens (no eval(), bounded depth & bits):
    supports integer literals (with `_`), `(expr)`, Lean type ascriptions `(expr : ℕ)` /
    `(expr : Nat)`, right-associative `^`, `*`, `+`, and `-` (Nat saturating/exact).
    """
    if not toks:
        return None
    pos = 0
    nt = len(toks)

    def peek() -> LeanToken | None:
        return toks[pos] if pos < nt else None

    def parse_add(depth: int) -> int | None:
        nonlocal pos
        if depth > _MAX_NAT_EVAL_DEPTH:
            return None
        left = parse_mul(depth)
        if left is None:
            return None
        while pos < nt and toks[pos].text in ("+", "-"):
            op = toks[pos].text
            pos += 1
            right = parse_mul(depth)
            if right is None:
                return None
            if op == "+":
                if max(left.bit_length(), right.bit_length()) + 1 > _MAX_NAT_EVAL_BITS:
                    return None
                left = left + right
            else:
                left = max(0, left - right)
        return left

    def parse_mul(depth: int) -> int | None:
        nonlocal pos
        if depth > _MAX_NAT_EVAL_DEPTH:
            return None
        left = parse_pow(depth)
        if left is None:
            return None
        while pos < nt and toks[pos].text == "*":
            pos += 1
            right = parse_pow(depth)
            if right is None:
                return None
            if left.bit_length() + right.bit_length() > _MAX_NAT_EVAL_BITS:
                return None
            left = left * right
        return left

    def parse_pow(depth: int) -> int | None:
        """Iterative right-associative exponentiation (`a ^ b ^ c == a ^ (b ^ c)`), depth-capped."""
        nonlocal pos
        if depth > _MAX_NAT_EVAL_DEPTH:
            return None
        base = parse_atom(depth)
        if base is None:
            return None
        bases = [base]
        while pos < nt and toks[pos].text == "^":
            if len(bases) > _MAX_NAT_EVAL_DEPTH:
                return None
            pos += 1
            nxt = parse_atom(depth)
            if nxt is None:
                return None
            bases.append(nxt)
        acc = bases[-1]
        for b in reversed(bases[:-1]):
            if acc < 0 or acc > 5000:
                return None
            if b > 1 and b.bit_length() * acc > 200000:
                return None
            acc = pow(b, acc)
        return acc

    def parse_atom(depth: int) -> int | None:
        nonlocal pos
        if depth > _MAX_NAT_EVAL_DEPTH:
            return None
        tok = peek()
        if tok is None:
            return None
        if tok.kind == "NUMBER":
            pos += 1
            cleaned = tok.text.replace("_", "")
            if not cleaned.isdigit() or len(cleaned) > _MAX_NAT_LITERAL_DIGITS:
                return None
            return int(cleaned)
        if tok.kind == "PUNCT" and tok.text == "(":
            if depth >= _MAX_NAT_EVAL_DEPTH:
                return None
            pos += 1
            val = parse_add(depth + 1)
            if val is None:
                return None
            # Optional Lean type ascription `: Nat` or `: ℕ` (or `: _root_.Nat`)
            if pos < nt and toks[pos].kind == "PUNCT" and toks[pos].text == ":":
                pos += 1
                if pos >= nt or toks[pos].kind != "IDENT":
                    return None
                type_name, end_idx = _extract_dotted_name(toks, pos)
                leaf = type_name.split(".")[-1].strip("«»")
                if leaf not in ("Nat", "ℕ"):
                    return None
                pos = end_idx + 1
            if pos >= nt or not (toks[pos].kind == "PUNCT" and toks[pos].text == ")"):
                return None
            pos += 1
            return val
        return None

    result = parse_add(0)
    if result is None or pos != nt:
        return None
    return result


def _extract_static_bounds_from_file(path: Path) -> dict[str, int]:
    """Extract `c7_lower_num` / `c7_lower_den` from a Lean file using `tokenize_lean4`."""
    src, enc_viols = read_lean_source_strict(path)
    if src is None or enc_viols:
        return {}
    tokens, _ = tokenize_lean4(src, path=str(path))
    found: dict[str, int] = {}
    nt = len(tokens)
    i = 0
    while i < nt:
        tok = tokens[i]
        if tok.kind == "IDENT" and tok.text in ("def", "abbrev"):
            j = i + 1
            if j < nt and tokens[j].kind == "IDENT":
                dotted, name_end = _extract_dotted_name(tokens, j)
                leaf = dotted.split(".")[-1].strip("«»")
                if leaf in ("c7_lower_num", "c7_lower_den"):
                    # Advance until contiguous `:=` (may span multiple lines for type annotations)
                    k = name_end + 1
                    assign_end: int | None = None
                    while k + 1 < nt:
                        tk = tokens[k]
                        if tk.kind == "PUNCT" and tk.text == ":" and tokens[k + 1].text == "=" and tokens[k + 1].start == tk.end:
                            assign_end = k + 2
                            break
                        if tk.kind == "IDENT" and tk.text in _LEAN_DECL_BOUNDARY_WORDS:
                            break
                        if tk.kind == "PUNCT" and tk.text in ("#", "@"):
                            break
                        k += 1
                    if assign_end is not None:
                        # Collect RHS tokens until next declaration / command boundary
                        rhs: list[LeanToken] = []
                        paren_depth = 0
                        r = assign_end
                        while r < nt:
                            tr = tokens[r]
                            if tr.kind == "PUNCT" and tr.text == "(":
                                paren_depth += 1
                            elif tr.kind == "PUNCT" and tr.text == ")":
                                if paren_depth == 0:
                                    break
                                paren_depth -= 1
                            elif paren_depth == 0:
                                if tr.kind == "IDENT" and tr.text in _LEAN_DECL_BOUNDARY_WORDS:
                                    break
                                if tr.kind == "PUNCT" and tr.text in ("#", "@", ";"):
                                    break
                            rhs.append(tr)
                            r += 1
                        val = _eval_nat_tokens(rhs)
                        if val is not None:
                            found[leaf] = val
                        i = r
                        continue
        i += 1
    return found


def extract_main_bounds(
    main_lean_path: Path, eval_consts: dict[str, int] | None = None
) -> tuple[bool, str, dict]:
    """Extract exact `(c7_lower_num, c7_lower_den)` preferring kernel `#eval` constants,
    falling back to `tokenize_lean4`-driven static parsing of `ShannonC7/Main.lean`
    (and `ShannonC7/FrontierLower.lean` if `Main.lean` re-exports them).
    """
    if (
        eval_consts
        and "c7_lower_num" in eval_consts
        and "c7_lower_den" in eval_consts
        and _is_strict_int(eval_consts["c7_lower_num"])
        and _is_strict_int(eval_consts["c7_lower_den"])
    ):
        return (
            True,
            "OK",
            {
                "c7_lower_num": eval_consts["c7_lower_num"],
                "c7_lower_den": eval_consts["c7_lower_den"],
                "source": "lean_eval",
            },
        )

    if not main_lean_path.is_file():
        return False, "MISSING_FILE", {"path": str(main_lean_path)}

    found = _extract_static_bounds_from_file(main_lean_path)
    source_tag = "static_main_lean"

    if "c7_lower_num" not in found or "c7_lower_den" not in found:
        frontier_path = main_lean_path.parent / "FrontierLower.lean"
        if frontier_path.is_file():
            fl_found = _extract_static_bounds_from_file(frontier_path)
            for key in ("c7_lower_num", "c7_lower_den"):
                if key not in found and key in fl_found:
                    found[key] = fl_found[key]
                    source_tag = "static_frontier_lower_lean"

    if "c7_lower_num" not in found or "c7_lower_den" not in found:
        return (
            False,
            "REPORT_MISMATCH",
            {
                "reason": "Could not statically extract c7_lower_num / c7_lower_den from Main.lean or FrontierLower.lean (run Lean audit for kernel #eval values)",
                "found_keys": sorted(found.keys()),
            },
        )

    return (
        True,
        "OK",
        {
            "c7_lower_num": found["c7_lower_num"],
            "c7_lower_den": found["c7_lower_den"],
            "source": source_tag,
        },
    )


# ---------------------------------------------------------------------------
# 8b. Option A-Report: Fail-Closed Clean Report & Exact-Fraction Math Verifier
# ---------------------------------------------------------------------------

_PLACEHOLDER_RE = re.compile(r"\b(?:TODO|TBD|FIXME|XXX)\b")
_MD_LINK_RE = re.compile(r"!?\[([^\[\]\n]+)\]\(([^()\s\n]+)\)")
_LATEX_TEXT_CMD_RE = re.compile(
    r"\\(?:text|texttt|textrm|textbf|textit|mathrm|mathbf|mathit|mathsf|mathtt|operatorname|emph|boxed|fbox)\s*\{([^{}\n]*)\}"
)
_LATEX_THIN_GROUP_RE = re.compile(r"(?<=\d)\\,(?=\d{3}(?!\d))")
_LATEX_SPACE_RE = re.compile(r"\\(?:[,;:!]|q?quad\b|(?:l|c|v)?dots\b|(?:display|text|script(?:script)?)style\b)")
_INLINE_DELIM_WORD_RE = re.compile(r"(?<=\w)(?:`+|\$\$?)(?=\w)")
_MATH_DELIM_RE = re.compile(r"\$\$|\$|\\\(|\\\)|\\\[|\\\]")
_MD_EMPH_STAR_RE = re.compile(r"(?<![\d)\]}])(\*{1,3})(?=\S)([^*\n]+?)(?<=\S)\1(?![\d(\[{])")
_MD_EMPH_UNDER_RE = re.compile(r"(?<!\w)(_{1,2})(?=\S)((?:[^_\n]|(?<=\w)_(?=\w))+?)(?<=\S)\1(?!\w)")
_LEADING_BLOCK_PREFIX_RE = re.compile(r"^(?:[^\S\n]*>)*(?:[^\S\n]*(?:#{1,6}|[-*+]|\d+[.)])[^\S\n]+|[^\S\n]*)")
_WS_RUN_RE = re.compile(r"[^\S\n]+")
_TABLE_SEP_ROW_RE = re.compile(
    r"^\s*(?:\|\s*:?-{2,}:?(?:\s*\|\s*:?-{2,}:?)*(?:\s*\|)?|:?-{2,}:?(?:\s*\|\s*:?-{2,}:?)+(?:\s*\|)?)\s*$"
)
_UNESCAPED_PIPE_RE = re.compile(r"(?<!\\)\|")
_ABBREV_WORDS = frozenset({"al", "vs", "cf", "eg", "ie", "thm", "prop", "cor", "lem", "sec", "fig", "eq", "approx", "cand", "ref", "no", "vol", "dr", "prof", "st", "inc", "jan", "feb", "mar", "apr", "jun", "jul", "aug", "sep", "sept", "oct", "nov", "dec", "ch", "def", "app", "mr", "ms", "mrs", "ed", "eds", "pp", "proc"})
_NON_INITIAL_PREV_WORDS = frozenset({"theorem", "thm", "lemma", "lem", "proposition", "prop", "corollary", "cor", "section", "sec", "appendix", "app", "chapter", "ch", "table", "figure", "fig", "case", "part", "track", "gate", "option", "group", "phase", "tier", "step", "method", "graph", "matrix", "set", "code", "orbit", "profile", "probe", "class", "type", "bound", "vertex", "vertices", "edge", "cycle", "power", "dimension", "column", "row", "line", "model", "label", "tag", "variant", "version", "item", "point", "node", "block", "clause", "rule", "axiom", "family", "space", "ring", "field", "module", "file", "dir", "in", "on", "for", "as", "is", "be", "to", "at", "equals"})
_SENT_START_WORDS = frozenset({"we", "our", "this", "it", "the", "a", "an", "in", "on", "at", "by", "for", "to", "from", "with", "of", "as", "if", "but", "or", "and", "nor", "not", "no", "never", "however", "moreover", "furthermore", "therefore", "thus", "hence", "next", "then", "now", "here", "there", "note", "see", "all", "both", "each", "every", "some", "any", "such", "these", "those", "that", "also", "since", "although", "though", "because", "while", "whereas", "when", "where", "after", "before", "instead", "rather", "finally", "first", "second", "third", "similarly", "conversely", "specifically", "notably", "indeed", "clearly", "overall", "summary", "results", "conclusion", "proof", "theorem", "lemma", "corollary", "proposition", "table", "figure", "section", "appendix"})


def _read_report_text_strict(path: Path) -> tuple[str | None, str, dict]:
    """Read a Markdown report strictly: reject missing, unreadable, NUL bytes, and invalid UTF-8."""
    if not path.is_file():
        return None, "MISSING_FILE", {"path": str(path), "reason": f"Missing {path.name}"}
    try:
        raw = path.read_bytes()
    except OSError as exc:
        return None, "REPORT_MISMATCH", {"path": str(path), "rule": "READ_ERROR", "reason": f"Could not read {path.name}: {exc}"}
    if b"\x00" in raw:
        idx = raw.find(b"\x00")
        line, col = raw[:idx].count(b"\n") + 1, idx - raw.rfind(b"\n", 0, idx)
        return None, "REPORT_MISMATCH", {"path": str(path), "rule": "NUL_BYTE", "line": line, "col": col, "reason": f"{path.name} contains forbidden NUL byte (\\x00) at line {line}, col {col}"}
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        return None, "REPORT_MISMATCH", {"path": str(path), "rule": "INVALID_UTF8", "reason": f"{path.name} is not valid UTF-8: {exc}"}
    return text.lstrip("\ufeff").replace("\r\n", "\n").replace("\r", "\n"), "OK", {}


def _normalize_markdown_inline(s: str, strip_block_prefix: bool = False) -> str:
    """Normalize Markdown/LaTeX inline formatting on a single line or table cell in O(N)."""
    if strip_block_prefix:
        s = _LEADING_BLOCK_PREFIX_RE.sub("", s)
    if "[" in s and "](" in s:
        s = _MD_LINK_RE.sub(r"\1", s)
    if "\\" in s:
        for _ in range(2):
            s_new = _LATEX_TEXT_CMD_RE.sub(r"\1", s)
            if s_new == s: break
            s = s_new
        s = _LATEX_SPACE_RE.sub(" ", _LATEX_THIN_GROUP_RE.sub(",", s.replace(r"\_", "_")))
    if "…" in s: s = s.replace("…", " ")
    if "`" in s or "$" in s: s = _INLINE_DELIM_WORD_RE.sub(" ", s).replace("`", "")
    if "$" in s or "\\" in s: s = _MATH_DELIM_RE.sub("", s)
    if "*" in s or "_" in s:
        for _ in range(2):
            prev = s
            s = _MD_EMPH_UNDER_RE.sub(r"\2", _MD_EMPH_STAR_RE.sub(r"\2", s))
            if s == prev: break
    return _WS_RUN_RE.sub(" ", s).strip()


def _parse_code_fence(stripped: str) -> tuple[str, int] | None:
    if not stripped or stripped[0] not in ("`", "~"): return None
    ch, k, n = stripped[0], 0, len(stripped)
    while k < n and stripped[k] == ch: k += 1
    return (ch, k) if k >= 3 else None


def _is_gfm_table_line(stripped: str, in_table: bool, next_is_sep: bool) -> tuple[bool, bool]:
    is_sep = bool(_TABLE_SEP_ROW_RE.match(stripped))
    if stripped.startswith("|") or is_sep: return True, is_sep
    if "|" not in stripped or not _UNESCAPED_PIPE_RE.search(stripped): return False, False
    if next_is_sep: return True, False
    if in_table and not stripped.startswith(("```", "~~~", ">")):
        rest = stripped.lstrip("#")
        if not (1 <= len(stripped) - len(rest) <= 6 and rest[:1].isspace() and not rest.lstrip().startswith("|")):
            return True, False
    return False, False


def _collapse_display_math_tagged(raw_lines: list[str]) -> list[tuple[str, bool]]:
    r"""Collapse multi-line `$$...$$` / `\[...\]` blocks (incl. blockquotes & odd openers) in strict O(N)."""
    out, i, n, fc_ch, fc_len, dd_skip_until, lb_skip_until, pending = [], 0, len(raw_lines), "", 0, -1, -1, None
    while i < n:
        from_pending = pending is not None
        raw_cur, pending = (pending if from_pending else raw_lines[i]), None
        s = raw_cur.strip()
        if not from_pending:
            fc = _parse_code_fence(s)
            if fc is not None:
                if not fc_ch: fc_ch, fc_len = fc[0], fc[1]
                elif fc[0] == fc_ch and fc[1] >= fc_len and not s[fc[1] :].strip(): fc_ch, fc_len = "", 0
                out.append((raw_cur, False)); i += 1; continue
        if not fc_ch:
            in_bq = s.startswith(">")
            s_nb = s.lstrip("> \t") if in_bq else s
            if (s_nb.startswith("$$") and s_nb.count("$$") >= 2 and s_nb.count("$$") % 2 == 0 and s_nb.rstrip(".,;:!?)").endswith("$$")) or (s_nb.startswith(r"\[") and s_nb.rfind(r"\]") > s_nb.rfind(r"\[") and s_nb.rstrip(".,;:!?)").endswith(r"\]")):
                out.append((raw_cur, True)); i += 1; continue
            dd_open = i >= dd_skip_until and "$$" in s and s.count("$$") % 2 == 1
            lb_open = i >= lb_skip_until and r"\[" in s and s.rfind(r"\[") > s.rfind(r"\]")
            opener, closer = ("$$", "$$") if (dd_open and (not lb_open or s.rfind("$$") > s.rfind(r"\["))) else ((r"\[", r"\]") if lb_open else (None, None))
            if opener is not None and closer is not None:
                pre, post = s.rsplit(opener, 1)
                body, j, closed_ok = [p for p in (pre.strip(), post.strip()) if p], i + 1, False
                while j < n:
                    sj = raw_lines[j].strip()
                    sj_c = sj.lstrip("> \t") if (in_bq and sj.startswith(">")) else sj
                    if _parse_code_fence(sj) is not None or (in_bq and _parse_code_fence(sj_c) is not None): break
                    cp = sj_c.find(closer)
                    if cp != -1:
                        bef, aft = sj_c[:cp].strip(), sj_c[cp + len(closer) :].strip()
                        if bef: body.append(bef)
                        joined, is_dm_blk = " ".join(body), not pre.strip().lstrip("> \t")
                        if aft and (("$$" in aft and aft.count("$$") % 2 == 1) or (r"\[" in aft and aft.rfind(r"\[") > aft.rfind(r"\]"))):
                            out.append((joined, is_dm_blk)); pending = ("> " + aft) if in_bq else aft; i = j; closed_ok = True; break
                        if aft: joined = joined + aft if aft[0] in ".,;:!?)" else f"{joined} {aft}"
                        out.append((joined, is_dm_blk)); i = j + 1; closed_ok = True; break
                    if sj_c: body.append(sj_c)
                    j += 1
                if not closed_ok:
                    if closer == "$$": dd_skip_until = max(dd_skip_until, j)
                    else: lb_skip_until = max(lb_skip_until, j)
                    out.append((raw_cur, False)); i += 1
                continue
        out.append((raw_cur, False)); i += 1
    return out


def _collapse_display_math_lines(raw_lines: list[str]) -> list[str]:
    return [ln for ln, _ in _collapse_display_math_tagged(raw_lines)]


def _normalize_markdown_document(text: str) -> str:
    """Normalize Markdown: strip code-fence markers, collapse display math, emit canonical leading `| ` on GFM tables."""
    lines = _collapse_display_math_lines(text.split("\n"))
    n_lines, out_lines, in_table, fc_ch, fc_len = len(lines), [], False, "", 0
    for idx, line in enumerate(lines):
        stripped = line.strip()
        fc = _parse_code_fence(stripped)
        if fc is not None:
            if not fc_ch:
                fc_ch, fc_len, in_table = fc[0], fc[1], False; out_lines.append(""); continue
            if fc[0] == fc_ch and fc[1] >= fc_len and not stripped[fc[1] :].strip():
                fc_ch, fc_len, in_table = "", 0, False; out_lines.append(""); continue
        if not stripped: in_table = False; out_lines.append(""); continue
        if fc_ch: in_table = False; out_lines.append(_normalize_markdown_inline(line)); continue
        next_sep = idx + 1 < n_lines and bool(_TABLE_SEP_ROW_RE.match(lines[idx + 1].strip()))
        is_tbl, is_sep = _is_gfm_table_line(stripped, in_table, next_sep)
        if is_tbl:
            in_table = in_table or is_sep
            joined = " | ".join(_normalize_markdown_inline(c.strip()) for c in _UNESCAPED_PIPE_RE.split(stripped)).strip()
            out_lines.append(joined if joined.startswith("|") else "| " + joined)
        else:
            in_table = False; out_lines.append(_normalize_markdown_inline(line, strip_block_prefix=True))
    return "\n".join(out_lines)


# --- Single-Pass O(N) Sentence, Table-Cell & Same-Clause Prefix Splitter ---

_SENT_SEP_RE = re.compile(r"[\n;!?.]")
_PAREN_OR_NL_RE = re.compile(r"[(\[\])\n]")
_SET_BUILDER_BINDER_RE = re.compile(r"^[\w\\,∈⊆⊂×⊠^()\[\]{} \t]+$")
_CLAUSE_NEGATION_RE = re.compile(
    r"\b(?:not|never|nobody|neither|nor"
    r"|(?<!with )(?<!using )(?<!having )(?<!requiring )no\s+(?:one|such|exact\s+(?:value|solution)|(?:(?:mathematical|known|valid|formal|lean(?:\s*4)?|pure[- ]kernel|upper|lower|finite|rigorous|published|verified|certified)\s+){0,3}(?:proof|claim|bound|result|theorem|certificate|verification|evidence|guarantee|solution|way))\b"
    r"|without\s+(?:proving|claiming|establishing|showing|certifying|verifying|solving|implying|assuming|concluding|asserting"
    r"|having\s+(?:proved|proven|claimed|established|shown|certified|verified|solved)|(?:a|any)\s+(?:proof|claim|certificate|verification)\s+(?:that|of))\b"
    r"|(?:remains?|is|are|stays?|kept|still)\s+(?:an?\s+)?(?:(?:70-year|famous|longstanding|well-known|classic|still)\s+)?open(?:\s+(?:(?:problem|question|conjecture|issue|matter)\s+)?(?:whether|if))?\b"
    r"|open\s+(?:whether|if|(?:problem|question|conjecture|issue|matter)\s+(?:whether|if))\b"
    r"|cannot|can't|couldn't|isn't|aren't|wasn't|weren't|haven't|hasn't|didn't|doesn't|don't|won't|wouldn't"
    r"|(?:does|do|did|is|are|was|were|has|have)\s+not|false|impossible|unproven|unproved|fails?|failed|failing"
    r"|refut(?:e|es|ed|ing)|contradict(?:s|ed|ing)?|disprov(?:e|es|ed|en)|invalid|falsified|ruled\s+out|rules\s+out|unable|whether)\b",
    re.IGNORECASE,
)
_NEGATABLE_FALSE_WORDS = frozenset({"false", "impossible", "invalid", "wrong", "untrue", "refuted", "disproved", "disproven", "falsified", "ruled", "contradicted", "open", "unproven", "unproved", "fail", "fails", "failed", "failing", "unable"})
_NEG_BRIDGE_WORDS = frozenset({"yet", "been", "be", "being", "remain", "remains", "stay", "stays", "actually", "provably", "really", "ever", "even", "still", "currently", "completely", "at", "all", "longer", "remotely", "possibly", "truly", "strictly", "fully", "wholly", "entirely", "totally"})
_PRIVATIVE_CUES = frozenset({"without", "zero", "0", "free", "no", "avoid", "avoids", "avoiding", "eliminating", "eliminates", "excluding", "lacking"})
_ATTR_TCB_NOUN_RE = re.compile(r"^(?:(?:external|custom|extra|additional|non-standard|lean(?:\s*4)?|kernel)\s+)?(?:axioms?|assumptions?|conjectures?|hypothes(?:is|es)|warnings?|gaps?|checks?|tests?|steps?|lemmas?|dependencies|tactics?)\b", re.IGNORECASE)
_CLAUSE_CUT_RE = re.compile(
    r"(?:[;!?:\u2014]|--| \u2013 |(?<!\d),|,(?!\d{3}(?!\d))"
    r"|\b(?:but|however|whereas|while|although|though|nevertheless|nonetheless|instead|rather)\b|(?<!not )(?<!nor )(?<!n't )\byet\b"
    r"|\band\s+(?:(?:formally|independently|now|here|successfully)\s+)?(?:we|our|this\s+(?:work|proof|formalization|report|paper)|(?:theorem|lemma|proposition|corollary)\s+[\w.-]+"
    r"|it\s+(?:is|was|has\s+been)\s+(?:(?:formally|now|here|independently|successfully)\s+)?(?:proved|proven|certified|verified|established|shown|demonstrated)"
    r"|proves|proved|proven|certifies|certified|verifies|verified|establishes|established|shows|showed|demonstrates|demonstrated|solves|solved|claims|claimed|obtains|obtained)\b)",
    re.IGNORECASE,
)
_TCB_NEG_AND_RE = re.compile(
    r"\b(?:not|never|cannot|can't|couldn't|won't|wouldn't|didn't|doesn't|don't|haven't|hasn't)\s+(?:(?:yet|ever)\s+)?"
    r"(?:(?:us(?:e|es|ed|ing)|rel(?:y(?:ing)?|ies|ied)\s+on|need(?:s|ed|ing)?|requir(?:e|es|ed|ing)|ha(?:ve|s|ving|d)|contain(?:s|ed|ing)?|depend(?:s|ed|ing)?\s+on|invok(?:e|es|ed|ing)|includ(?:e|es|ed|ing)|leav(?:e|es|ing)|left|assum(?:e|es|ed|ing)|introduc(?:e|es|ed|ing))"
    r"\s+(?:(?:a|an|the|any|custom|external|extra|non-standard|unverified|unproven|unproved)\s+){0,2}(?:sorry(?:ax)?|admit|native_decide|lean\.ofreduce(?:bool|nat)|(?:lean\.)?trustcompiler|axioms?|conjectures?|assumptions?|hypothes(?:is|es)|warnings?|gaps?|unsafe|partial|tactics?)|fail(?:s|ed|ing)?)\b[^\n]{0,100}?\band\b",
    re.IGNORECASE,
)
_POS_CLAIM_START_RE = re.compile(
    r"^(?:we\s|our\s|this\s|(?:theorem|lemma|proposition|corollary)\s+|(?:(?:formally|independently|now|here|successfully)\s+)?"
    r"(?:proves|proved|proven|certifies|certified|verifies|verified|establishes|established|shows|showed|demonstrates|demonstrated|solves|solved|claims|claimed|obtains|obtained)\b)",
    re.IGNORECASE,
)
_SELF_POS_CLAIM_RE = re.compile(
    r"\b(?:(?:we|our(?:\s+[\w-]+){0,5}|this\s+(?:work|proof|formalization|report|paper)|(?:theorem|lemma|proposition|corollary)\s+[\w.-]+)\s+"
    r"(?:(?:have|has)\s+)?(?:(?:formally|independently|now|here|successfully)\s+){0,2}"
    r"(?:proves?|proved|proven|certif(?:y|ies|ied)|verif(?:y|ies|ied)|establish(?:es|ed)?|shows?|showed|shown|demonstrat(?:e|es|ed)|claim(?:s|ed)?|obtain(?:s|ed)?|solv(?:e|es|ed))"
    r"|it\s+(?:is|was|has\s+been)\s+(?:(?:formally|independently|now|here|successfully)\s+){0,2}(?:proved|proven|certified|verified|established|shown|demonstrated))\b",
    re.IGNORECASE,
)
_TCB_NOUN_TAIL_RE = re.compile(r"\b(?:axioms?|warnings?|gaps?|limits?|conjectures?|assumptions?|sorry(?:ax)?|admit|native_decide|unsafe|partial|lean\.ofreduce(?:bool|nat))\b", re.IGNORECASE)
_PAREN_FRESH_CLAIM_RE = re.compile(
    _SELF_POS_CLAIM_RE.pattern
    + r"|\b(?:proves?|proved|proven|proving|certif(?:y|ies|ied|ying)|verif(?:y|ies|ied|ying)|establish(?:es|ed|ing)?|shows?|showed|shown|demonstrat(?:e|es|ed|ing))\s+"
    + r"(?:(?:(?:in|via|using)\s+(?:the\s+)?(?:pure(?:[- ]kernel)?\s+)?(?:lean(?:\s*4)?(?:\s+kernel)?|pure[- ]kernel)|without\s+(?:sorry(?:ax)?|admit|native_decide|(?:custom\s+)?axioms?)|here|formally|independently)\s+){0,2}"
    + r"(?:that\s+)?(?:Θ|\\?Theta|α|\\?alpha|shannonCapacity)\b"
    + r"|\b(?:is|was|has\s+been)\s+(?:(?:formally|independently|now|here)\s+){0,2}(?:proved|proven|certified|verified|established)\b",
    re.IGNORECASE,
)


def _is_abbrev_dot(s: str, dot_i: int, min_pos: int) -> bool:
    if dot_i >= min_pos + 3 and s[dot_i - 3 : dot_i].lower() in ("e.g", "i.e") and (dot_i - 3 == min_pos or not s[dot_i - 4].isalpha()): return True
    k = dot_i - 1
    while k >= min_pos and s[k].isalpha(): k -= 1
    word = s[k + 1 : dot_i]
    if word.lower() in _ABBREV_WORDS: return True
    if len(word) == 1 and word.isupper() and dot_i + 1 < len(s) and s[dot_i + 1] in " \t":
        pk = k
        while pk >= min_pos and s[pk] in " \t": pk -= 1
        if pk >= min_pos and (s[pk] in "=<>≤≥+*/∈⊆⊂~≈:" or (s[pk] == "-" and not (pk > min_pos and s[pk - 1] == "."))): return False
        if pk >= min_pos and s[pk].isalpha():
            pw = pk
            while pw >= min_pos and s[pw].isalpha(): pw -= 1
            if s[pw + 1 : pk + 1].lower() in _NON_INITIAL_PREV_WORDS: return False
        nk = dot_i + 1
        while nk < len(s) and s[nk] in " \t": nk += 1
        if nk < len(s) and s[nk].isupper():
            ne = nk + 1
            while ne < len(s) and s[ne].isalpha(): ne += 1
            nw = s[nk:ne]
            if (len(nw) == 1 and ne < len(s) and s[ne] in ".'") or (len(nw) >= 2 and nw[1].islower() and nw.lower() not in _SENT_START_WORDS): return True
    return False


def _is_neg_bridge(w: str) -> bool:
    return w in _NEG_BRIDGE_WORDS or w in ("a", "an", "just", "anymore") or (len(w) >= 4 and w.endswith("ly") and w.isalpha())


def _has_direct_clause_negation(prefix: str, next_text: str = "") -> bool:
    for m in _CLAUSE_NEGATION_RE.finditer(prefix):
        tok = m.group(0).lower().strip()
        is_open_tok = tok.endswith(" open") or tok.startswith("open ") or " open " in tok
        if tok in ("not", "never", "cannot") or tok.endswith((" not", "n't")):
            nxt = [w.rstrip(".,;:!?)").lower() for w in prefix[m.end() :].lstrip().split(None, 6)[:6]]
            if any(nxt[k] in _NEGATABLE_FALSE_WORDS and all(_is_neg_bridge(x) for x in nxt[:k]) for k in range(len(nxt))): continue
        elif tok in _NEGATABLE_FALSE_WORDS or tok == "ruled out" or is_open_tok or tok == "whether":
            prev = [w.lstrip("([{\"'").lower() for w in prefix[max(0, m.start() - 64) : m.start()].rstrip().rsplit(None, 8)[-8:]]
            pi, steps = len(prev) - 1, 0
            if tok == "whether":
                while pi >= 0 and steps < 3 and (_is_neg_bridge(prev[pi]) or prev[pi] in ("problem", "question", "conjecture", "issue", "matter")): pi -= 1; steps += 1
                if pi >= 0 and prev[pi] in _NEGATABLE_FALSE_WORDS:
                    pi -= 1; steps = 0
                    while pi >= 0 and steps < 5 and _is_neg_bridge(prev[pi]): pi -= 1; steps += 1
                    if pi >= 0 and (prev[pi] in ("not", "never", "no", "neither", "nor", "cannot") or prev[pi].endswith("n't")): continue
            else:
                while pi >= 0 and steps < 5 and _is_neg_bridge(prev[pi]): pi -= 1; steps += 1
                if pi >= 0 and (prev[pi] in ("not", "never", "no", "neither", "nor", "cannot") or prev[pi].endswith("n't")): continue
                if tok in _NEGATABLE_FALSE_WORDS and _ATTR_TCB_NOUN_RE.match(prefix[m.end() :].lstrip()) and any(w in _PRIVATIVE_CUES for w in prev): continue
        if tok == "without assuming" and prefix[m.end() :].strip().lower() not in ("", "that"): continue
        tail = prefix[m.end() :] + next_text
        if (tok.startswith(("without ", "no ")) or is_open_tok) and (_SELF_POS_CLAIM_RE.search(tail) or (tok.startswith(("without ", "no ")) and _TCB_NOUN_TAIL_RE.search(prefix[m.end() :]))):
            continue
        return True
    if next_text and next_text.lower().startswith(("exact value", "exact solution")):
        pw = prefix.rstrip().lower().rsplit(None, 2)
        if pw and pw[-1] == "no" and (len(pw) < 2 or pw[-2] not in ("with", "using", "having", "requiring")):
            return True
    return False


def _split_sentences_safe(text: str) -> list[tuple[int, int]]:
    """Split text into sentence spans in O(N) preserving decimals, filenames, abbreviations, and short balanced parens."""
    spans, n, paren_spans, n_sp, sp_idx, start, pos = [], len(text), None, 0, 0, 0, 0
    while pos < n:
        m = _SENT_SEP_RE.search(text, pos)
        if m is None: break
        i, ch = m.start(), text[m.start()]
        if ch != "\n":
            if paren_spans is None:
                paren_spans = []
                if "(" in text or "[" in text:
                    raw, ps, bs = [], [], []
                    for pm in _PAREN_OR_NL_RE.finditer(text):
                        pc, pi = pm.group(0), pm.start()
                        if pc == "\n": ps.clear(); bs.clear()
                        elif pc == "(": ps.append(pi)
                        elif pc == ")" and ps:
                            s0 = ps.pop()
                            if not ps and not bs and pi - s0 <= 200: raw.append((s0, pi))
                        elif pc == "[": bs.append(pi)
                        elif pc == "]" and bs:
                            s0 = bs.pop()
                            if not ps and not bs and pi - s0 <= 200: raw.append((s0, pi))
                    for s0, e0 in sorted(raw):
                        if paren_spans and s0 <= paren_spans[-1][1]: paren_spans[-1] = (paren_spans[-1][0], max(paren_spans[-1][1], e0))
                        else: paren_spans.append((s0, e0))
                n_sp = len(paren_spans)
            while sp_idx < n_sp and paren_spans[sp_idx][1] < i: sp_idx += 1
            if sp_idx < n_sp and paren_spans[sp_idx][0] < i < paren_spans[sp_idx][1]:
                pos = paren_spans[sp_idx][1] + 1; continue
        if ch != ".":
            spans.append((start, i)); pos = i + 1
            while pos < n and text[pos].isspace() and text[pos] != "\n": pos += 1
            start = pos; continue
        j = i + 1
        while j < n and text[j] in ")\"']": j += 1
        if j == n or text[j].isspace():
            if (i + 1 < n and text[i + 1] == ".") or (i > 0 and text[i - 1] == "."): pos = i + 1; continue
            if _is_abbrev_dot(text, i, start): pos = i + 1; continue
            spans.append((start, j)); pos = j
            while pos < n and text[pos].isspace() and text[pos] != "\n": pos += 1
            start = pos; continue
        pos = i + 1
    if start <= n: spans.append((start, n))
    return spans


def _split_line_table_cells(line: str) -> list[tuple[int, int]]:
    """Split a single line on table-pipe boundaries in strict O(len(line)), preserving `{ x | P(x) }` set-builders."""
    n_ln, lead = len(line), 0
    while lead < n_ln and line[lead] in " \t": lead += 1
    if lead < n_ln and line[lead] == "|":
        spans, seg_s, i = [], lead + 1, lead + 1
        while i < n_ln:
            p = line.find("|", i)
            if p == -1: break
            if p > 0 and line[p - 1] == "\\": i = p + 1; continue
            spans.append((seg_s, p)); seg_s = i = p + 1
        if seg_s < n_ln: spans.append((seg_s, n_ln))
        return spans or [(0, n_ln)]
    if " | " not in line: return [(0, n_ln)]
    spans, seg_s, sf = [], 0, 0
    while True:
        p = line.find(" | ", sf)
        if p == -1: spans.append((seg_s, n_ln)); return spans
        lb, bd = -1, 0
        for bi in range(p - 1, max(seg_s, p - 36) - 1, -1):
            if line[bi] == "}": bd += 1
            elif line[bi] == "{":
                if bd == 0: lb = bi; break
                bd -= 1
        if lb != -1:
            rb, bd = -1, 1
            for bi in range(p + 3, min(n_ln, p + 200)):
                if line[bi] == "{": bd += 1
                elif line[bi] == "}":
                    bd -= 1
                    if bd == 0: rb = bi; break
            binder = line[lb + 1 : p]
            if rb != -1 and len(binder) <= 32 and _SET_BUILDER_BINDER_RE.match(binder) and not _CLAUSE_NEGATION_RE.search(binder) and " | " not in line[p + 3 : rb]:
                sf = p + 3; continue
        spans.append((seg_s, p)); seg_s = sf = p + 3


def _same_clause_prefix(
    text: str, pos: int, max_chars: int = 180, line_cell_cache: dict[tuple[int, int], tuple[list[int], list[tuple[int, int]]]] | None = None
) -> str:
    """Return immediate-clause prefix preceding `pos` in O(1) amortized time (unlimited-depth disjoint reverse scan)."""
    ls = text.rfind("\n", 0, pos) + 1
    le = text.find("\n", pos)
    le = len(text) if le == -1 else le
    key = (ls, le)
    if line_cell_cache is not None and key in line_cell_cache:
        starts, cells = line_cell_cache[key]
    else:
        cells = _split_line_table_cells(text[ls:le])
        starts = [c[0] for c in cells]
        if line_cell_cache is not None: line_cell_cache[key] = (starts, cells)
    rel = pos - ls
    ci = bisect.bisect_right(starts, rel) - 1
    cs = ls + cells[ci][0] if (0 <= ci < len(cells) and cells[ci][0] <= rel < cells[ci][1]) else ls
    raw = text[max(cs, pos - max_chars) : pos]
    pref = raw
    if "(" in raw or "[" in raw:
        ps, bs, closed = [], [], []
        for ii, ch in enumerate(raw):
            if ch == "(": ps.append(ii)
            elif ch == ")" and ps: closed.append((ps.pop(), ii + 1))
            elif ch == "[": bs.append(ii)
            elif ch == "]" and bs: closed.append((bs.pop(), ii + 1))
        if closed:
            out, cur = [], 0
            for s0, e0 in sorted(closed):
                if s0 >= cur: out.extend((raw[cur:s0], " ")); cur = e0
                elif e0 > cur: cur = e0
            out.append(raw[cur:]); pref = "".join(out)
    cut, np = 0, len(pref)
    for m in _CLAUSE_CUT_RE.finditer(pref): cut = max(cut, m.end())
    for m in _TCB_NEG_AND_RE.finditer(pref, cut): cut = max(cut, m.end())
    tail_w = pref[cut:].rstrip().lower()
    if (tail_w.endswith((" and", "(and", "[and")) or tail_w == "and") and _POS_CLAIM_START_RE.match(text[pos : pos + 48]): return ""
    pi = pref.find(".", cut)
    while pi != -1:
        nxt = pi + 1
        if (nxt == np or pref[nxt].isspace()) and not (pi > 0 and pref[pi - 1] == ".") and not (nxt < np and pref[nxt] == "."):
            if not _is_abbrev_dot(pref, pi, cut): cut = max(cut, nxt)
        pi = pref.find(".", pi + 1)
    if "(" in pref[cut:] or "[" in pref[cut:]:
        opens = [i for i in range(cut, np) if pref[i] in "(["]
        for oi in range(len(opens) - 1, -1, -1):
            op_pos, seg_end = opens[oi], (np if oi == len(opens) - 1 else opens[oi + 1])
            if _PAREN_FRESH_CLAIM_RE.search(pref[op_pos + 1 : seg_end] + (text[pos : pos + 64] if oi == len(opens) - 1 else "")):
                cut = max(cut, op_pos + 1); break
    return pref[cut:]


# --- Exact-Fraction Numeric & Standard Symbolic Math Evaluator (Zero Float) ---

_MAX_ARITH_BITS = 512
_SUP_DIGIT_MAP = str.maketrans("⁺⁻⁰¹²³⁴⁵⁶⁷⁸⁹", "+-0123456789")
_PAREN_SIZE_ANY_RE = re.compile(r"\\(?:left|right|biggl?|biggr?|bigl?|bigr?|bigg?)(?![A-Za-z])", re.IGNORECASE)
_PAREN_ARITH_TOK_RE = re.compile(
    r"((?:\d+(?:(?:,|\{,\})\d{3})*(?:\.\d+)?|\.\d+)(?:[eE][+\-−]?\d+)?)|(\*\*)|(\\[A-Za-z]+)|([⁰¹²³⁴⁵⁶⁷⁸⁹]+)|([+\-−*/÷·⋅∗×^(){}⌊⌋⌈⌉√])|(\S)"
)


def _parse_bounded_fraction(raw_num: str, *, exact: bool = False) -> Fraction | None:
    """Parse a positive decimal/comma-grouped number into a Fraction, returning None if >= 10^6."""
    c = raw_num.replace("{,}", "").replace(",", "")
    ip, fp = c.split(".", 1) if "." in c else (c, "")
    ins = ip.lstrip("0") or "0"
    if len(ins) > 6: return None
    if exact:
        fp = fp.rstrip("0")
        if len(fp) > 100: return None
    elif len(fp) > 100:
        fp = fp[:100] + ("1" if any(ch != "0" for ch in fp[100:]) else "")
    return Fraction(int(ins + fp), 10 ** len(fp)) if fp else Fraction(int(ins), 1)


def _is_impossible_finite_val(val: Fraction, power: int, is_strict: bool) -> bool:
    thr = 108 if power == 4 else 367
    return (val <= thr) if is_strict else (val < thr)


def _parse_exact_arith_num(num_s: str) -> Fraction | None:
    """Parse a constant decimal or scientific-notation literal in 100% exact `Fraction` arithmetic ONLY."""
    if "e" not in num_s and "E" not in num_s: return _parse_bounded_fraction(num_s, exact=True)
    if "," in num_s: return None
    ms, es = num_s.split("e", 1) if "e" in num_s else num_s.split("E", 1)
    es = es.replace("−", "-")
    es_u = es[1:] if es[:1] in "+-" else es
    if not ms or ms.count(".") > 1 or not ms.replace(".", "", 1).isdigit() or not es_u.isdigit() or len(es_u) > 6: return None
    ip, fp = ms.split(".", 1) if "." in ms else (ms, "")
    digits = (ip + fp).lstrip("0")
    if not digits: return Fraction(0)
    sd = digits.rstrip("0")
    shift = int(es) - len(fp) + (len(digits) - len(sd))
    if shift < 0:
        fd = -shift
        if fd > 100 or max(0, len(sd) - fd) > 154: return None
        val = Fraction(int(sd), 10**fd)
    else:
        if len(sd) + shift > 154: return None
        val = Fraction(int(sd) * (10**shift), 1)
    return None if (val.numerator.bit_length() > _MAX_ARITH_BITS or val.denominator.bit_length() > _MAX_ARITH_BITS) else val


def _int_exact_root(n: int, q: int) -> int | None:
    """Return exact integer `r >= 0` with `r ** q == n`, or `None` if `n` is not an exact `q`-th power."""
    if n < 0 or q < 2: return None
    if n <= 1: return n
    if q == 2:
        r = math.isqrt(n)
        return r if r * r == n else None
    lo, hi = 1, 1 << ((n.bit_length() + q - 1) // q)
    while lo <= hi:
        mid = (lo + hi) >> 1; p = mid**q
        if p == n: return mid
        lo, hi = (mid + 1, hi) if p < n else (lo, mid - 1)
    return None


def _eval_simple_paren_arith(inner: str) -> Fraction | None:
    """Evaluate a pure constant algebraic/LaTeX expression in 100% exact `Fraction` arithmetic ONLY."""
    if not inner or len(inner) > 16384: return None
    toks: list[tuple[str, object]] = []
    cmd_op = {"cdot": "*", "times": "*", "ast": "*", "div": "/", "choose": "choose", "lfloor": "⌊", "rfloor": "⌋", "lceil": "⌈", "rceil": "⌉"}
    cmd_fn = {"frac": "frac", "dfrac": "frac", "tfrac": "frac", "binom": "binom", "dbinom": "binom", "tbinom": "binom", "sqrt": "sqrt"}
    for m in _PAREN_ARITH_TOK_RE.finditer(_PAREN_SIZE_ANY_RE.sub(" ", inner)):
        num_s, pow_s, cmd_s, sup_s, sym_s, other_s = m.groups()
        if other_s is not None: return None
        if num_s is not None:
            v = _parse_exact_arith_num(num_s)
            if v is None: return None
            toks.append(("NUM", v))
        elif pow_s is not None: toks.append(("OP", "^"))
        elif cmd_s is not None:
            cn = cmd_s[1:].lower()
            if cn in cmd_op: toks.append(("OP", cmd_op[cn]))
            elif cn in cmd_fn: toks.append(("CMD", cmd_fn[cn]))
            elif cn in ("displaystyle", "textstyle", "scriptstyle", "scriptscriptstyle"): continue
            else: return None
        elif sup_s is not None:
            s_dig = sup_s.translate(_SUP_DIGIT_MAP)
            if len(s_dig) > 30: return None
            toks.append(("SUP", s_dig))
        elif sym_s is not None:
            toks.append(("CMD", "sqrt") if sym_s == "√" else ("OP", "-" if sym_s == "−" else ("/" if sym_s == "÷" else ("*" if sym_s in "·⋅∗×" else sym_s))))
    if not toks: return None
    ntoks, idx = len(toks), 0

    def _chk(val: Fraction) -> Fraction | None:
        return None if (val.numerator.bit_length() > _MAX_ARITH_BITS or val.denominator.bit_length() > _MAX_ARITH_BITS) else val

    def _pow_int_exact(base: Fraction, exp_i: int) -> Fraction | None:
        if exp_i == 0 or base == 1: return Fraction(1)
        if base == 0: return None if exp_i < 0 else Fraction(0)
        if base == -1: return Fraction(-1 if (exp_i & 1) else 1)
        b, ae = (Fraction(1, 1) / base, -exp_i) if exp_i < 0 else (base, exp_i)
        return None if ae * (max(abs(b.numerator), b.denominator).bit_length() - 1) > _MAX_ARITH_BITS else _chk(b**ae)

    def _pow_exact(base: Fraction, exp: Fraction) -> Fraction | None:
        if exp.denominator == 1: return _pow_int_exact(base, exp.numerator)
        if base < 0 or (base == 0 and exp < 0): return None
        if base == 0 or base == 1: return base
        q = exp.denominator
        if q < 2 or q > 8: return None
        rn, rd = _int_exact_root(base.numerator, q), _int_exact_root(base.denominator, q)
        return None if (rn is None or rd is None) else _pow_int_exact(Fraction(rn, rd), exp.numerator)

    def _binom_exact(nv: Fraction | None, kv: Fraction | None) -> Fraction | None:
        if nv is None or kv is None or nv.denominator != 1 or kv.denominator != 1 or nv.numerator < 0 or kv.numerator < 0: return None
        ni, ki = nv.numerator, kv.numerator
        if ki > ni: return Fraction(0)
        r = min(ki, ni - ki)
        return Fraction(1) if r == 0 else (_chk(Fraction(ni, 1)) if r == 1 else (None if ni > 500 else _chk(Fraction(math.comb(ni, r), 1))))

    def _p_expr(d: int) -> Fraction | None:
        nonlocal idx
        left = _p_add(d)
        while left is not None and idx < ntoks and toks[idx] == ("OP", "choose"):
            idx += 1; left = _binom_exact(left, _p_add(d))
        return left

    def _p_add(d: int) -> Fraction | None:
        nonlocal idx
        left = _p_term(d)
        while left is not None and idx < ntoks and toks[idx][0] == "OP" and toks[idx][1] in ("+", "-"):
            op = toks[idx][1]; idx += 1; right = _p_term(d)
            left = None if right is None else _chk(left + right if op == "+" else left - right)
        return left

    def _p_term(d: int) -> Fraction | None:
        nonlocal idx
        left = _p_unary(d)
        while left is not None and idx < ntoks:
            tk, tv = toks[idx]
            if tk == "OP" and tv in ("*", "/"):
                idx += 1; right = _p_unary(d)
                left = None if (right is None or (tv == "/" and right == 0)) else _chk(left * right if tv == "*" else left / right)
            elif (tk == "OP" and tv in ("(", "{", "⌊", "⌈")) or tk == "CMD":
                right = _p_unary(d); left = None if right is None else _chk(left * right)
            else: break
        return left

    def _p_unary(d: int) -> Fraction | None:
        nonlocal idx
        neg = False
        while idx < ntoks and toks[idx][0] == "OP" and toks[idx][1] in ("+", "-"):
            neg ^= (toks[idx][1] == "-"); idx += 1
        val = _p_pow(d)
        return None if val is None else (-val if neg else val)

    def _p_pow(d: int) -> Fraction | None:
        nonlocal idx
        base = _p_atom(d)
        while base is not None and idx < ntoks:
            tk, tv = toks[idx]
            if tk == "SUP": idx += 1; base = _pow_int_exact(base, int(str(tv)))
            elif tk == "OP" and tv == "^":
                if d >= 8: return None
                idx += 1
                if idx < ntoks and toks[idx] == ("OP", "{"):
                    idx += 1; ev = _p_expr(d + 1)
                    if ev is None or idx >= ntoks or toks[idx] != ("OP", "}"): return None
                    idx += 1
                else:
                    ev = _p_unary(d + 1)
                    if ev is None: return None
                base = _pow_exact(base, ev)
            else: break
        return base

    def _p_arg(d: int) -> Fraction | None:
        nonlocal idx
        if idx >= ntoks or d >= 8: return None
        if toks[idx] == ("OP", "{"):
            idx += 1; val = _p_expr(d + 1)
            if val is None or idx >= ntoks or toks[idx] != ("OP", "}"): return None
            idx += 1; return val
        return _p_atom(d + 1)

    def _p_atom(d: int) -> Fraction | None:
        nonlocal idx
        if idx >= ntoks: return None
        tk, tv = toks[idx]
        if tk == "NUM": idx += 1; return tv  # type: ignore[return-value]
        if tk == "OP" and tv in ("(", "{", "⌊", "⌈") and d < 8:
            idx += 1; val = _p_expr(d + 1)
            if val is None or idx >= ntoks or toks[idx] != ("OP", {"(": ")", "{": "}", "⌊": "⌋", "⌈": "⌉"}[str(tv)]): return None
            idx += 1
            return Fraction(math.floor(val), 1) if tv == "⌊" else (Fraction(math.ceil(val), 1) if tv == "⌈" else val)
        if tk == "CMD" and d < 8:
            idx += 1
            if tv == "sqrt":
                av = _p_arg(d)
                if av is None or av < 0: return None
                if av == 0: return Fraction(0)
                rn, rd = math.isqrt(av.numerator), math.isqrt(av.denominator)
                return Fraction(rn, rd) if (rn * rn == av.numerator and rd * rd == av.denominator) else None
            av = _p_arg(d); bv = _p_arg(d) if av is not None else None
            return _binom_exact(av, bv) if tv == "binom" else (None if (av is None or bv is None or bv == 0) else _chk(av / bv))
        return None

    res = _p_expr(0)
    return res if (res is not None and idx == ntoks) else None


# --- Fail-Closed Exact-Solution & Impossible Finite-Power Upper Bound Checker ---

_C7_SYM_PAT = r"C(?:_\{7\}|_?7|₇)"
_FALSE_EXACT_CLAIMS = (
    re.compile(
        r"(?:we\s+)?(?:have\s+)?(?:proves?|proved|proven|certif(?:y|ies|ied)|verif(?:y|ies|ied)|establish(?:es|ed)?|shows?|showed|shown|demonstrat(?:e|es|ed))\s+"
        r"(?:(?:(?:in|via|using)\s+(?:the\s+)?(?:pure(?:[- ]kernel)?\s+)?(?:lean(?:\s*4)?(?:\s+kernel)?|pure[- ]kernel|this\s+(?:work|paper|formalization)|our\s+(?:work|formalization))|without\s+(?:sorry|admit|native_decide|(?:custom\s+)?axioms?)|here|formally|exactly)\s+){0,3}"
        r"(?:that\s+)?(?:(?:Θ|\\?Theta)\s*\(\s*" + _C7_SYM_PAT + r"\s*\)|shannonCapacity\s*\(\s*(?:SimpleGraph\.)?cycleGraph\s+7\s*\))\s*="
        r"(?!\s*(?:\\?lim(?![A-Za-z])|\\?sup(?![A-Za-z])|sSup(?![A-Za-z])|shannonCapacity(?:Textbook)?(?![A-Za-z])|(?-i:Θ|\\?Theta)\s*\())",
        re.IGNORECASE,
    ),
    re.compile(r"exact\s+value\s+of\s+(?:Θ|\\?Theta)\s*\(\s*" + _C7_SYM_PAT + r"\s*\)\s+(?:is\s+|has\s+been\s+)?(?:proven|proved|solved)\b", re.IGNORECASE),
    re.compile(r"solved\s+the\s+70-year\s+open\s+problem\s+exactly", re.IGNORECASE),
    re.compile(r"exact\s+solution\s+(?:is\s+)?(?:proven|proved)\s+in\s+lean", re.IGNORECASE),
)
_UPPER_FINITE_BOUND_RE = re.compile(
    r"(?:α|\\?alpha)\s*\(\s*"
    + _C7_SYM_PAT
    + r"\s*(?:(?:\^\s*(?:\{\s*)?(?:(?:\\?boxtimes|⊠)\s*)?|\*\*\s*)(4|5)(?:\s*\})?|(?:(?:\\?boxtimes|⊠)\s*)?(⁴|⁵))\s*\)\s*"
    r"(≤|<=|\\leqslant(?![A-Za-z])|\\leq(?![A-Za-z])|\\le(?![A-Za-z])|=|<|\\lt(?![A-Za-z]))\s*"
    r"((?:\d+(?:(?:,|\{,\})\d{3})*(?:\.\d+)?|\.\d+)(?:[eE][+\-−]?\d+)?(?!\.\d|,\d|\{,\}\d|\w)|[({⌊⌈√+\-−]|\\(?:(?:d|t)?frac|(?:d|t)?binom|lfloor|lceil|sqrt|left|biggl?|bigl?|bigg?)(?![A-Za-z]))",
    re.IGNORECASE,
)
_UNARY_MINUS_CONT_PAT = r"(?:-(?!-)|−)(?:[ \t]*(?:\+|-(?!-)|−)){0,15}[ \t]*(?:\d|\.\d|(?:(?![aA] (?!(?:for|where|when|with)\b)[A-Za-z]{2})[A-Za-z])(?![A-Za-z])|[({⌊⌈√\\])"
_CHAIN_REL_OP_RE = re.compile(
    r"^[ \t]*(?:<=|≤|\\leqslant(?![A-Za-z])|\\leq(?![A-Za-z])|\\le(?![A-Za-z])|=|<|\\lt(?![A-Za-z]))",
    re.IGNORECASE,
)
_COMPOUND_RHS_CONT_RE = re.compile(
    r"^[ \t]*(?:[\^+*/·⋅∗×÷⁰¹²³⁴⁵⁶⁷⁸⁹⌊⌈√{αϑΘ]|" + _UNARY_MINUS_CONT_PAT
    + r"|\\(?:cdot|times|ast|div|(?:d|t)?frac|lfloor|lceil|(?:d|t)?binom|choose|sqrt|alpha|vartheta|Theta|left|biggl?|bigl?|bigg?)(?![A-Za-z]))",
    re.IGNORECASE,
)
_PAREN_LATEX_CMD_RE = re.compile(r"\\([A-Za-z]+)")
_SYMBOLIC_GRAPH_INV_RE = re.compile(r"(?:\\(?:alpha|vartheta|Theta|theta)(?![A-Za-z])|[αϑΘθ])", re.IGNORECASE)
_SCI_EXP_STRIP_RE = re.compile(r"(?<=\d)[eE][+\-−]?\d+")
_CITATION_BRACKET_RE = re.compile(r"^(?:\d+[A-Za-z]?|[A-Za-z])(?:[ \t]*[,–-][ \t]*(?:\d+[A-Za-z]?|[A-Za-z]))*$")
_FOR_VAR_ASSIGN_RE = re.compile(r"^[ \t]*(?:,[ \t]*|\([ \t]*)?(?:for|where|with)[ \t]+([A-Za-z])[ \t]*=(?![=>])[ \t]*", re.IGNORECASE)
_MATH_UNICODE_CHARS = frozenset("αϑΘθπ⊠·⋅∗×÷√⌊⌋⌈⌉−⁰¹²³⁴⁵⁶⁷⁸⁹₀₁₂₃₄₅₆₇₈₉")
_MATH_PAREN_CMDS = frozenset(
    {
        "alpha", "vartheta", "theta", "beta", "gamma", "delta", "lambda", "pi",
        "frac", "dfrac", "tfrac", "binom", "dbinom", "tbinom", "choose", "lfloor", "rfloor", "lceil", "rceil", "sqrt",
        "cdot", "times", "ast", "div", "pm", "mp", "left", "right", "big", "bigl", "bigr", "bigg", "biggl", "biggr",
        "boxtimes", "cos", "sin", "tan", "sec", "log", "ln", "exp", "max", "min",
    }
)


def _find_false_exact_claim(norm_text: str) -> str | None:
    cache: dict[tuple[int, int], tuple[list[int], list[tuple[int, int]]]] = {}
    for pat in _FALSE_EXACT_CLAIMS:
        for m in pat.finditer(norm_text):
            if not _has_direct_clause_negation(_same_clause_prefix(norm_text, m.start(), line_cell_cache=cache), norm_text[m.start() : m.start() + 64]):
                return m.group(0)
    return None


def _is_pure_const_math_expr(expr_str: str) -> bool:
    s = expr_str.strip()
    return bool(s) and not _SYMBOLIC_GRAPH_INV_RE.search(s) and not any(ch.isalpha() for ch in _SCI_EXP_STRIP_RE.sub("", _PAREN_LATEX_CMD_RE.sub(" ", s)))


def _eval_rhs_segment_impossible(seg_str: str, power: int, is_strict: bool) -> tuple[str, str] | None:
    s = seg_str.strip()
    if not s or s == "+": return None
    if "e" in s or "E" in s:
        if "," not in s and all(c in "0123456789.eE+-−" for c in s):
            ms, es = s.split("e", 1) if "e" in s else s.split("E", 1)
            ms_u = ms[1:] if ms.startswith("+") else ms
            es_u = es[1:] if es.startswith("+") else es.replace("−", "-")
            if ms_u and ms_u.count(".") <= 1 and ms_u.replace(".", "", 1).isdigit() and es_u.isdigit() and len(es_u) <= 6:
                ip, fp = ms_u.split(".", 1) if "." in ms_u else (ms_u, "")
                inz = ip.lstrip("0")
                if (inz or fp.lstrip("0")) and (int(es_u) + (len(inz) - 1 if inz else -(len(fp) - len(fp.lstrip("0")) + 1))) >= 6: return None
    else:
        c = s.replace("{,}", "").replace(",", "")
        c_u = c[1:] if c.startswith("+") else c
        if c_u and c_u.count(".") <= 1 and c_u.replace(".", "", 1).isdigit() and len(c_u.split(".", 1)[0].lstrip("0") or "0") > 6: return None
    op_s = "<" if is_strict else "<="
    val = _eval_simple_paren_arith(s)
    if val is not None: return (op_s, s) if _is_impossible_finite_val(val, power, is_strict) else None
    c = s.replace("{,}", "").replace(",", "")
    c_u = c[1:] if c.startswith("+") else c
    if c_u and c_u.count(".") <= 1 and c_u.replace(".", "", 1).isdigit():
        ip, fp = c_u.split(".", 1) if "." in c_u else (c_u, "")
        thr, iv = (108 if power == 4 else 367), int(ip.lstrip("0") or "0")
        return (op_s, s) if (iv < thr or (is_strict and iv == thr and not fp.rstrip("0"))) else None
    return (op_s, s) if _is_pure_const_math_expr(s) else None


def _is_meta_paren(inner: str, had_space: bool, has_size_cmd: bool, had_prior_math: bool, has_after_op: bool, has_for_assign: bool = False, has_rel_after: bool = False) -> bool:
    if not inner or any(c in inner for c in "=<>≤≥%;:?!'\"") or any(ord(c) > 127 and c not in _MATH_UNICODE_CHARS for c in inner): return True
    if any(cm.group(1).lower() not in _MATH_PAREN_CMDS for cm in _PAREN_LATEX_CMD_RE.finditer(inner)): return True
    no_cmd = _PAREN_LATEX_CMD_RE.sub(" ", inner)
    if any(no_cmd[i].isalpha() and (no_cmd[i + 1].isalpha() or no_cmd[i + 1] == ".") for i in range(len(no_cmd) - 1)): return True
    if not has_after_op:
        if len(inner) == 4 and inner.isdigit() and 1900 <= int(inner) <= 2100: return True
        if had_space and not has_size_cmd and "-" in inner:
            parts = inner.split("-")
            if len(parts) == 2 and all(len(p) == 4 and p.isdigit() for p in parts) and 1900 <= int(parts[0]) < int(parts[1]) <= 2100: return True
    if "," in inner:
        i = inner.find(",")
        while i != -1:
            if not (i > 0 and inner[i - 1].isdigit() and i + 3 < len(inner) and inner[i + 1 : i + 4].isdigit() and (i + 4 == len(inner) or not inner[i + 4].isdigit())): return True
            i = inner.find(",", i + 1)
    if len(inner) == 1 and inner.isalpha() and not has_after_op and not has_for_assign: return True
    if had_space and not has_size_cmd and not has_after_op and not had_prior_math and not has_rel_after:
        if inner[0] in "+-−" and not has_for_assign: return True
        if _SYMBOLIC_GRAPH_INV_RE.search(inner): return True
        if _is_pure_const_math_expr(inner):
            iv = _eval_simple_paren_arith(inner)
            if iv is not None and iv >= 1: return True
        elif not has_for_assign:
            return True
    return False


def _scan_upper_rhs_impossible(text: str, expr_start: int, scan_from: int, power: int, is_strict: bool, max_end: int) -> tuple[str, str, int] | None:
    """Unified O(N) scanner for standalone, parenthesized, and compound standard-math upper-bound RHS (zero fail-open)."""
    n, limit = len(text), min(len(text), max_end)
    j, pd, bd, brd, top_p, top_b, top_p_sz = scan_from, 0, 0, 0, -1, -1, False
    seg_start, cur_strict, segments = expr_start, is_strict, []

    def _pre_non_binop(ep: int, start: int = -1) -> bool:
        t = text[seg_start if start < 0 else start : ep].rstrip()
        return bool(t) and not (t[-1] in "+-−*/^·⋅∗×÷" or t.endswith(("\\cdot", "\\times", "\\ast", "\\div")))

    def _starts_prose_word(p2: int) -> bool:
        while p2 < limit and text[p2] in " \t": p2 += 1
        if p2 >= limit or not text[p2].isalnum(): return False
        p2e = p2
        while p2e < limit and (text[p2e].isalnum() or text[p2e] == "-"): p2e += 1
        w = text[p2:p2e]
        return len(w) >= 2 and any(c.isalpha() for c in w) and w.lower() not in ("where", "when", "for", "if", "with", "in", "is", "of", "to", "by", "from", "and", "or")

    def _chain_after_close(close_pos: int) -> int | None:
        nonlocal cur_strict, pd, bd, brd, top_p, top_b, top_p_sz, seg_start
        cp = close_pos + 1
        while cp < limit:
            m_rel = _CHAIN_REL_OP_RE.match(text[cp : min(limit, cp + 32)])
            if m_rel is not None:
                op_tok = m_rel.group(0).strip().lower()
                cur_strict = cur_strict or (op_tok in ("<", "\\lt"))
                pd = bd = brd = 0; top_p = top_b = -1; top_p_sz = False
                seg_start = cp + m_rel.end()
                return seg_start
            while cp < limit and text[cp] in " \t": cp += 1
            if cp >= limit or text[cp] not in "([": return None
            o_ch, c_ch, dep, cp = text[cp], (")" if text[cp] == "(" else "]"), 1, cp + 1
            while cp < limit and text[cp] not in "\n|" and dep > 0:
                if text[cp] == o_ch: dep += 1
                elif text[cp] == c_ch: dep -= 1
                cp += 1
            if dep != 0: return None
        return None

    def _skip_open_delim_to_chain(start_j: int) -> int | None:
        if pd > 0 and top_p >= seg_start: o_ch, c_ch, dep = "(", ")", pd
        elif brd > 0 and top_b >= seg_start: o_ch, c_ch, dep = "[", "]", brd
        elif bd > 0: o_ch, c_ch, dep = "{", "}", bd
        else: return None
        p = start_j
        while p < limit and text[p] not in "\n|":
            if text[p] == o_ch: dep += 1
            elif text[p] == c_ch:
                dep -= 1
                if dep == 0: return _chain_after_close(p)
            p += 1
        return None

    def _next_spaced_paren_is_math(start_p: int) -> bool:
        p = start_p
        while p < limit and text[p] in " \t": p += 1
        if p >= limit or text[p] != "(": return False
        dep, q = 1, p + 1
        while q < limit and text[q] not in "\n|" and dep > 0:
            if text[q] == "(": dep += 1
            elif text[q] == ")": dep -= 1
            q += 1
        if dep != 0: return bool(frag := text[p + 1 : min(q, p + 64)].strip()) and _is_pure_const_math_expr(frag)
        nxt_in = _PAREN_SIZE_ANY_RE.sub("", text[p + 1 : q - 1]).strip()
        aft_q = text[q : min(limit, q + 64)]; aft_l = aft_q.lstrip(" \t")
        aft_m = bool(_COMPOUND_RHS_CONT_RE.match(aft_q)) or aft_q.startswith("(") or (aft_l.startswith("(") and len(aft_l) > 1 and not (aft_l[1].isalpha() and len(aft_l) > 2 and aft_l[2].isalpha()))
        return not _is_meta_paren(nxt_in, True, False, True, aft_m, bool(_FOR_VAR_ASSIGN_RE.match(aft_q)), False)

    def _emit_open_or(ep: int) -> None:
        if pd > 0 and top_p >= seg_start:
            if top_p > seg_start and bd == 0 and brd == 0:
                ins = text[top_p + 1 : min(ep, top_p + 64)].strip()
                if ins and _is_pure_const_math_expr(ins) and (text[top_p - 1] not in " \t" or (ins[0] not in "+-−" and not (len(ins) == 4 and ins.isdigit() and 1900 <= int(ins) <= 2100) and ((iv := _eval_simple_paren_arith(ins)) is None or iv < 1))):
                    segments.append((text[seg_start : min(ep, top_p + 64)], cur_strict, min(ep, top_p + 64))); return
            if _pre_non_binop(top_p): segments.append((text[seg_start:top_p], cur_strict, top_p)); return
        elif brd > 0 and top_b >= seg_start and _pre_non_binop(top_b):
            segments.append((text[seg_start:top_b], cur_strict, top_b)); return
        elif pd == 0 and bd == 0 and brd == 0:
            segments.append((text[seg_start:ep], cur_strict, ep)); return
        cand_s = text[seg_start : min(ep, seg_start + 128)]
        if _is_pure_const_math_expr(cand_s): segments.append((cand_s, cur_strict, min(ep, seg_start + 128)))

    while j < limit:
        ch = text[j]
        if ch in " \t": j += 1; continue
        if ch in "\n|": _emit_open_or(j); break
        if pd == 0 and bd == 0 and brd == 0:
            if ch in "=≤<≥>":
                op_e = j + (2 if ch in "<>" and j + 1 < limit and text[j + 1] == "=" else 1)
                segments.append((text[seg_start:j], cur_strict, j))
                if ch in ">≥": break
                cur_strict = cur_strict or (op_e == j + 1 and ch == "<"); j = seg_start = op_e; continue
            if ch == "\\":
                k = j + 1
                while k < limit and text[k].isalpha(): k += 1
                cmd = text[j + 1 : k].lower()
                if cmd in ("le", "leq", "leqslant", "lt", "ge", "geq", "geqslant", "gt"):
                    segments.append((text[seg_start:j], cur_strict, j))
                    if cmd.startswith("g"): break
                    cur_strict = cur_strict or (cmd == "lt"); j = seg_start = k; continue
                if k > j + 1 and cmd not in _MATH_PAREN_CMDS: _emit_open_or(j); break
                j = k if k > j + 1 else j + 1; continue
            if ch in "-−":
                if ch == "-" and j + 1 < limit and text[j + 1] == "-": segments.append((text[seg_start:j], cur_strict, j)); break
                pa = j + 1
                while pa < limit and text[pa] in " \t": pa += 1
                if pa < limit and text[pa].isalpha():
                    pw = pa + 1
                    while pw < limit and text[pw].isalpha(): pw += 1
                    if pw - pa >= 2: segments.append((text[seg_start:j], cur_strict, j)); break
                    if text[pa] in ("a", "A") and _starts_prose_word(pw):
                        segments.append((text[seg_start:j], cur_strict, j)); break
            if ch in ";!?)]}:—–\"'”’" or (ch in ".," and not (j + 1 < n and text[j + 1].isdigit())):
                segments.append((text[seg_start:j], cur_strict, j)); break
        if ch == "(":
            if pd == 0 and bd == 0 and brd == 0:
                top_p = j; pre_t = text[seg_start:j].rstrip(); tail_w = pre_t[max(0, len(pre_t) - 10) :]
                m_sz = _PAREN_SIZE_ANY_RE.search(tail_w)
                top_p_sz = bool(m_sz and m_sz.end() == len(tail_w) and "r" not in m_sz.group(0)[1:].lower())
            pd += 1; j += 1; continue
        if ch == ")":
            if pd > 0:
                pd -= 1
                if pd == 0 and bd == 0 and brd == 0 and top_p >= seg_start:
                    if top_p > seg_start and _pre_non_binop(top_p):
                        inner_p = _PAREN_SIZE_ANY_RE.sub("", text[top_p + 1 : j]).strip()
                        after_w = text[j + 1 : min(limit, j + 64)]
                        has_after = bool(_COMPOUND_RHS_CONT_RE.match(after_w)) or after_w.startswith("(") or _next_spaced_paren_is_math(j + 1)
                        has_for, has_rel = bool(_FOR_VAR_ASSIGN_RE.match(after_w)), bool(_CHAIN_REL_OP_RE.match(after_w))
                        if _is_meta_paren(inner_p, text[top_p - 1] in " \t", top_p_sz, bool(text[scan_from:top_p].strip()), has_after, has_for, has_rel):
                            segments.append((text[seg_start:top_p], cur_strict, top_p))
                            nxt_j = _chain_after_close(j)
                            if nxt_j is not None: j = nxt_j; continue
                            break
                    top_p, top_p_sz = -1, False
                j += 1; continue
            if bd == 0 and brd == 0: segments.append((text[seg_start:j], cur_strict, j))
            break
        if ch in "{}":
            if ch == "{": bd += 1
            elif bd > 0: bd -= 1
            else:
                if pd == 0 and brd == 0: segments.append((text[seg_start:j], cur_strict, j))
                break
            j += 1; continue
        if ch == "[":
            if pd == 0 and bd == 0 and brd == 0: top_b = j
            brd += 1; j += 1; continue
        if ch == "]":
            if brd > 0:
                brd -= 1
                if brd == 0 and pd == 0 and bd == 0 and top_b >= seg_start:
                    pre_b = text[seg_start:top_b].rstrip().lower()
                    if top_b > seg_start and text[top_b - 1] in " \t" and _pre_non_binop(top_b) and not pre_b.endswith(("\\sqrt", "\\left", "\\big", "\\bigl", "\\bigg", "\\biggl")):
                        ib, has_b_after = text[top_b + 1 : j].strip(), bool(_COMPOUND_RHS_CONT_RE.match(text[j + 1 : min(limit, j + 25)]))
                        if (not has_b_after and (not ib or _CITATION_BRACKET_RE.match(ib) or any(c in ib for c in "=<>≤≥%;:?!'\""))) or (has_b_after and ib and _CITATION_BRACKET_RE.match(ib) and not _is_pure_const_math_expr(ib) and any(c.isdigit() or c in ",–-" for c in ib)):
                            segments.append((text[seg_start:top_b], cur_strict, top_b))
                            nxt_j = _chain_after_close(j)
                            if nxt_j is not None: j = nxt_j; continue
                            break
                    top_b = -1
                j += 1; continue
            if pd == 0 and bd == 0: segments.append((text[seg_start:j], cur_strict, j))
            break
        if ch == "\\":
            k = j + 1
            while k < limit and text[k].isalpha(): k += 1
            if k > j + 1 and text[j + 1 : k].lower() not in _MATH_PAREN_CMDS:
                _emit_open_or(j)
                nxt_j = _skip_open_delim_to_chain(k)
                if nxt_j is not None: j = nxt_j; continue
                break
            j = k if k > j + 1 else j + 1; continue
        if ch.isalpha():
            k = j + 1
            while k < limit and text[k].isalpha(): k += 1
            if k - j >= 2:
                _emit_open_or(j - 1 if (j > seg_start and text[j - 1] in " \t") else j)
                nxt_j = _skip_open_delim_to_chain(k)
                if nxt_j is not None: j = nxt_j; continue
                break
            if pd == 0 and bd == 0 and brd == 0 and text[j] in ("a", "A", "I") and j > seg_start and text[j - 1] in " \t" and _pre_non_binop(j) and _starts_prose_word(k):
                _emit_open_or(j - 1); break
            j = k; continue
        j += 1
    else: _emit_open_or(j)
    if not segments: return None
    post_end = segments[-1][2]
    for_sub: tuple[str, str] | None = None
    m_for = _FOR_VAR_ASSIGN_RE.match(text[post_end : min(limit, post_end + 32)])
    if m_for is not None:
        rs = post_end + m_for.end(); rp = rb = 0; top_rp, p, rhs_end = -1, rs, limit
        while p < limit:
            c = text[p]
            if c in " \t": p += 1; continue
            if c in "\n|=<>≤≥%;:?!'\"”’—–": rhs_end = top_rp if (rp > 0 and top_rp > rs and _pre_non_binop(top_rp, rs)) else p; break
            if rp == 0 and rb == 0:
                if c in ")]}" or (c == "." and not (p + 1 < limit and text[p + 1].isdigit())) or (c == "," and not (p > rs and text[p - 1].isdigit() and p + 3 < limit and text[p + 1 : p + 4].isdigit() and (p + 4 == limit or not text[p + 4].isdigit()))) or (c == "[" and not text[rs:p].rstrip().lower().endswith("\\sqrt")): rhs_end = p; break
                if c in "-−":
                    if c == "-" and p + 1 < limit and text[p + 1] == "-": rhs_end = p; break
                    pa = p + 1
                    while pa < limit and text[pa] in " \t": pa += 1
                    pw = pa
                    while pw < limit and text[pw].isalpha(): pw += 1
                    if pw - pa >= 2 or (pw - pa == 1 and text[pa] in ("a", "A") and _starts_prose_word(pw)): rhs_end = p; break
            if c == "(":
                if rp == 0 and rb == 0: top_rp = p
                rp += 1; p += 1; continue
            if c == ")":
                if rp == 0: rhs_end = p; break
                rp -= 1
                if rp == 0 and rb == 0:
                    if top_rp > rs and text[top_rp - 1] in " \t" and _pre_non_binop(top_rp, rs) and len(in_r := text[top_rp + 1 : p].strip()) == 4 and in_r.isdigit() and 1900 <= int(in_r) <= 2100 and not _COMPOUND_RHS_CONT_RE.match(text[p + 1 : min(limit, p + 25)]): rhs_end = top_rp; break
                    top_rp = -1
                p += 1; continue
            if c in "{}":
                if c == "{": rb += 1
                elif rb > 0: rb -= 1
                else: rhs_end = p; break
                p += 1; continue
            if c == "\\":
                k = p + 1
                while k < limit and text[k].isalpha(): k += 1
                if k > p + 1 and text[p + 1 : k].lower() not in _MATH_PAREN_CMDS: rhs_end = top_rp if (rp > 0 and top_rp > rs and _pre_non_binop(top_rp, rs)) else p; break
                p = k if k > p + 1 else p + 1; continue
            if c.isalpha():
                if c in "eE" and p > rs and text[p - 1].isdigit() and p + 1 < limit and (text[p + 1].isdigit() or (text[p + 1] in "+-−" and p + 2 < limit and text[p + 2].isdigit())): p += 1; continue
                k = p + 1
                while k < limit and text[k].isalpha(): k += 1
                if k - p >= 2: rhs_end = top_rp if (rp > 0 and top_rp > rs and _pre_non_binop(top_rp, rs)) else p; break
                if rp == 0 and rb == 0 and text[p] in ("a", "A", "I") and p > rs and text[p - 1] in " \t" and _pre_non_binop(p, rs) and _starts_prose_word(k): rhs_end = p; break
                p = k; continue
            p += 1
        v_expr = text[rs:rhs_end].strip()
        if v_expr and _is_pure_const_math_expr(v_expr): for_sub = (m_for.group(1), v_expr)
    for s_txt, s_strict, _ in segments:
        hit = _eval_rhs_segment_impossible(s_txt, power, s_strict)
        if hit is not None: return hit[0], hit[1], post_end
        if for_sub is not None and not _is_pure_const_math_expr(s_txt):
            var_c, val_s = for_sub
            sub_parts, si, sn = [], 0, len(s_txt)
            while si < sn:
                if s_txt[si] == "\\":
                    sk = si + 1
                    while sk < sn and s_txt[sk].isalpha(): sk += 1
                    sub_parts.append(s_txt[si:sk]); si = sk; continue
                if s_txt[si] == var_c and (si == 0 or not s_txt[si - 1].isalpha()) and (si + 1 == sn or not s_txt[si + 1].isalpha()):
                    sub_parts.append(f"({val_s})"); si += 1; continue
                sub_parts.append(s_txt[si]); si += 1
            sub_txt = "".join(sub_parts)
            if sub_txt != s_txt:
                hit2 = _eval_rhs_segment_impossible(sub_txt, power, s_strict)
                if hit2 is not None: return hit2[0], hit2[1], post_end
    return None


def _find_impossible_upper_claim(norm_text: str) -> dict | None:
    """Return first unnegated impossible finite-power upper bound on C_7^4 (<108) or C_7^5 (<367) (fail-closed, zero post-negation)."""
    sup_map = {"⁴": 4, "⁵": 5}
    cache: dict[tuple[int, int], tuple[list[int], list[tuple[int, int]]]] = {}
    matches = list(_UPPER_FINITE_BOUND_RE.finditer(norm_text))
    n_matches = len(matches)
    for mi, m in enumerate(matches):
        max_end = matches[mi + 1].start() if mi + 1 < n_matches else len(norm_text)
        power = int(m.group(1)) if m.group(1) is not None else sup_map[m.group(2)]
        is_strict = m.group(3).lower() in ("<", "\\lt")
        scan_from = m.end() if (m.group(4)[0].isdigit() or m.group(4)[0] == ".") else m.start(4)
        hit = _scan_upper_rhs_impossible(norm_text, m.start(4), scan_from, power, is_strict, max_end)
        if hit is None or _has_direct_clause_negation(_same_clause_prefix(norm_text, m.start(), line_cell_cache=cache)): continue
        thr = 108 if power == 4 else 367
        return {"reason": f"Impossible alpha(C_7^{power}) {hit[0]} {hit[1]} (contradicts known alpha(C_7^{power}) >= {thr})", "match": norm_text[m.start() : hit[2]]}
    return None


# --- Fail-Closed Clean Lower-Bound Separation & Honesty Engine ---

@dataclass(frozen=True)
class _BoundCandidate:
    start: int
    end: int
    raw: str
    value: Fraction
    is_decimal: bool


_LOVASZ_UPPER_NUM = LOVASZ_UPPER_RAT.numerator
_LOVASZ_UPPER_DEN = LOVASZ_UPPER_RAT.denominator
_LOVASZ_MIN_PLAUSIBLE = Fraction(3317, 1000)
_LOWER_DEC_CAND_RE = re.compile(r"(?<![\w.])(0*3\.[23]\d+)(?!\.\d|\w)")
_LOWER_SCI_CAND_RE = re.compile(r"(?<![\w.])((?:\d+(?:\.\d+)?|\.\d+)[eE][+\-−]?\d+)(?!\.\d|\w)")
_FRAC_NUM_PAT = r"\d{1,3}(?:(?:,|\{,\})\d{3})+(?:\.\d+)?|\d+\.\d+|\.\d+|\d{3,}"
_FRAC_DEN_BODY = (
    r"10\s*(?:\^|\*\*)\s*(?:\{\s*[+\-−]?\d+\s*\}|\(\s*[+\-−]?\d+\s*\)|[+\-−]?\d+)"
    r"|10\s*[⁺⁻]?[⁰¹²³⁴⁵⁶⁷⁸⁹]+|1(?:\.0+)?[eE][+\-−]?\d+"
    r"|\d{1,3}(?:(?:,|\{,\})\d{3})+(?:\.\d+)?|\d+\.\d+|\.\d+|\d{2,}"
)
_BOUND_FRAC_RE = re.compile(r"(?:\(\s*(" + _FRAC_NUM_PAT + r")\s*\)|(?<![\w./}])(?<!\d,)(" + _FRAC_NUM_PAT + r"))\s*(?:/|÷)\s*(?:\(\s*(" + _FRAC_DEN_BODY + r")\s*\)|(" + _FRAC_DEN_BODY + r")(?!\.\d|\w))")
_LATEX_FRAC_RE = re.compile(r"\\(?:d|t)?frac\s*\{\s*(?:\(\s*(" + _FRAC_NUM_PAT + r")\s*\)|(" + _FRAC_NUM_PAT + r"))\s*\}\s*\{\s*(?:\(\s*(" + _FRAC_DEN_BODY + r")\s*\)|(" + _FRAC_DEN_BODY + r"))\s*\}")
_LOWER_LATEX_SCI_RE = re.compile(
    r"(?<![\w.}])(?<!\d,)((?:\d{1,3}(?:(?:,|\{,\})\d{3})+(?:\.\d+)?|\d+(?:\.\d+)?|\.\d+))\s*"
    r"(?:\\(?:times|cdot|ast)(?![A-Za-z])|[×·⋅∗*])\s*"
    r"(10\s*(?:\^|\*\*)\s*(?:\{\s*[+\-−]?\d+\s*\}|\(\s*[+\-−]?\d+\s*\)|[+\-−]?\d+)|10\s*[⁺⁻]?[⁰¹²³⁴⁵⁶⁷⁸⁹]+)(?!\.\d|\w)"
)
_NEGATED_NATIVE_DECIDE_RE = re.compile(
    r"\b(?:non[- ]native_decide\b|(?:no|zero|without|0|free\s+of|not(?:\s+(?:using|relying\s+on))?|"
    r"(?:does|do|did)\s+not\s+(?:use|rely\s+on)|never\s+(?:uses?|using|relies\s+on)|instead\s+of|rather\s+than|avoids?|avoiding|eliminat(?:e|es|ed|ing)|replac(?:e|es|ed|ing))\s+"
    r"(?:(?:lean\s*\.\s*ofReduceBool|sorry(?:Ax)?|admit|custom\s+axioms?|axioms?|unsafe)\s*(?:,\s*(?:or|and)\b|/|\bor\b|,|\band\b)\s*)*native_decide\b)",
    re.IGNORECASE,
)
_SELF_LEAN_CERT_RE = re.compile(
    r"\b(?:lean(?:\s*4)?\b|pure[- ]kernel\b|pure_kernel_claim\b|(?:machine|kernel|mechanically)[- ](?:checked|verified|certified|proved|proven)\b"
    r"|(?:formally|newly|now|actually|already)\s+(?:verified|verifies|certified|certifies|formalized|formalizes|proven|proved|proves|checked|checks|confirmed|confirms|established|establishes|validated|validates)\b"
    r"|(?:certified|verified|formalized|proven|proved)\s+(?:(?:lower\s+)?bound\b|(?:at|to)\b|(?=:|=))"
    r"|our\s+(?:[\w-]+\s+){0,4}(?:formalization|proof|certificate|theorem|certif(?:y|ies|ied)|formaliz(?:e|es|ed)|proves?|proved|proven|check(?:s|ed)?|establish(?:es|ed)?|verif(?:y|ies|ied)(?!\s+(?:\S+\s+){0,2}in\s+(?:python|c\+\+\d*|rust|julia|gap|sage|matlab)\b))\b"
    r"|we\s+(?:have\s+)?(?:(?:formally|independently|now|successfully)\s+){0,2}(?:certif(?:y|ied)|formaliz(?:e|ed)|proves?|proved|proven|check(?:s|ed)?|verif(?:y|ies|ied)(?!\s+(?:\S+\s+){0,2}in\s+(?:python|c\+\+\d*|rust|julia|gap|sage|matlab)\b))\b"
    r"|this\s+(?:formalization|proof)\b"
    r"|this\s+(?:work|project|report|paper)\s+(?:(?:formally|independently|now|successfully)\s+){0,2}(?:certif(?:y|ies|ied)|formaliz(?:e|es|ed)|proves?|proved|proven|check(?:s|ed)?|establish(?:es|ed)?|verif(?:y|ies|ied)(?!\s+(?:\S+\s+){0,2}in\s+(?:python|c\+\+\d*|rust|julia|gap|sage|matlab)\b))\b)",
    re.IGNORECASE,
)
_CERT_CELL_EXCL = r"(?:python|c\+\+|rust|julia|gap|sage|matlab|unformalized|unverified|uncertified|heuristic|external|\b(?:not|no|never|pending|awaiting|outside|without)\b)"
_STANDALONE_CERT_CELL_RE = re.compile(
    r"^\s*(?:lean(?:\s*4)?|formally\s+(?:verified|certified|proven|proved|checked|formalized)|certified|verified|formalized|proven|proved)"
    r"(?:(?:\s*\((?![^()\n]{0,48}" + _CERT_CELL_EXCL + r")[^()\n]{0,48}\)|\s*\[(?![^\[\]\n]{0,48}" + _CERT_CELL_EXCL + r")[^\[\]\n]{0,48}\]){1,2}"
    r"|\s*(?:[,;:—–]|-(?!\w))\s*(?![^\n|]{0,48}" + _CERT_CELL_EXCL + r")[^\n|]{0,48})?\s*$",
    re.IGNORECASE,
)
_AFFIRM_CELL_RE = re.compile(
    r"^\s*(?:yes|true|pass(?:ed)?|ok|done|complete(?:d)?|confirmed|✓|✔|✅|☑)"
    r"(?:\s*\((?![^()\n]{0,40}" + _CERT_CELL_EXCL + r")[^()\n]{0,40}\)|\s*\[(?![^\[\]\n]{0,40}" + _CERT_CELL_EXCL + r")[^\[\]\n]{0,40}\]"
    r"|\s*(?:[,;:—–]|-(?!\w))\s*(?![^\n|]{0,40}" + _CERT_CELL_EXCL + r")[^\n|]{0,40})?\s*$",
    re.IGNORECASE,
)
_LEAN_NEG_DOUBLE_WORDS = frozenset({"pending", "awaiting", "separate", "distinct", "excluded", "outside", "target", "targeted", "candidate", "planned", "queued", "without", "no", "lack", "lacks", "lacking", "missing"})
_TCB_AFTER_CERT_RE = re.compile(
    r"^(?:(?:pure[- ]kernel|lean(?:\s*4)?|kernel)\s+){0,2}(?:(?:custom|external|extra|non-standard|unproven|unverified)\s+){0,2}"
    r"(?:sorry(?:ax)?|admit|native_decide|lean\.ofreduce(?:bool|nat)|axioms?|warnings?|gaps?|unsafe|partial|tactics?|conjectures?|assumptions?)\b",
    re.IGNORECASE,
)
_LEAN_CERT_NEG_RE = re.compile(
    r"\b(?:(?:not(?:\s+(?:yet|currently|still))?(?:\s+been)?|never(?:\s+been)?)"
    r"(?:\s+(?:a|an|in|part\s+of|included\s+in)|(?:\s+(?:formally|independently))?(?:\s+(?:formalized|certified|verified|proven|proved|checked)\s+(?:in|by|via|as))?)?"
    r"|(?:did|do|does|have|has|had|could|can|is|are|was|were)\s+not(?:\s+(?:yet|currently|still))?(?:\s+been)?"
    r"|(?:didn't|doesn't|don't|haven't|hasn't|couldn't|cannot|can't)(?:\s+yet)?"
    r"|(?:pending|awaiting)(?:\s+(?:certification|verification|formalization|inclusion)\s+(?:in|by|into))?"
    r"|(?:separate|distinct|excluded)\s+from|outside(?:\s+of)?|(?:target(?:ed)?|candidate|planned|queued)\s+for"
    r"|without(?:\s+(?:a|an|any))?|no|lacks?|lacking|missing"
    r")(?:\s+(?:the|a|an|our|this|main|current|existing|pure[- ]kernel|lean(?:\s*4)?)){0,4}\s*$",
    re.IGNORECASE,
)
_SELF_BRAG_RE = re.compile(
    r"\b(?:beats?|beating|surpass(?:es|ed|ing)?|exceeds?|exceeded|exceeding|outperforms?|outperformed|outperforming|"
    r"breaks?|breaking|tops?|topping|defeats?|defeating|eclips(?:e|es|ed|ing)|bests?|besting|overtak(?:e|es|en|ing)|overtook|"
    r"shatter(?:s|ed|ing)?|outstrip(?:s|ped|ping)?|leapfrog(?:s|ged|ging)?|"
    r"strictly\s+(?:improves?\s+(?:upon|on|over)|above|higher\s+than|greater\s+than|better\s+than)|"
    r"new\s+(?:world\s+)?record|world\s+record|target-beating|record-breaking)\b",
    re.IGNORECASE,
)
_BRAG_NEG_RE = re.compile(
    r"\b(?:not(?:\s+yet)?|never|no|didn't|doesn't|don't|haven't|hasn't|couldn't|cannot|can't|"
    r"(?:did|do|does|have|has|had|could|can)\s+not(?:\s+yet)?|"
    r"(?:failed|fails|unable|aims?|aiming|seeks?|seeking|goal\s+(?:is\s+)?|attempt(?:s|ed|ing)?|tries?|trying|hoping)\s+to|without"
    r")(?:\s+(?:achieve|reach|set|establish|claim|a|an|the)){0,2}\s*$",
    re.IGNORECASE,
)
_EXT_OR_UNFORMALIZED_RE = re.compile(
    r"\b(?:bpz|buys|polak|zuiddam|tandon|gao|itty|schrijver|vesel|mathew|baumert|einsteinarena|tao\s+constant|"
    r"external|literature|benchmark|prior|previous|historical|baseline|preprint|unrefereed|native_decide|"
    r"unformalized|unverified|uncertified|heuristic|candidate|c\+\+(?:\d*)?|rust|python|search|exploration|computational|empirical|hypothetical|"
    r"not\s+(?:(?:yet|still|currently)\s+)?(?:been\s+)?(?:(?:formally|independently)\s+)?(?:formalized|certified|verified|proven|proved|checked|able\s+to\s+(?:formalize|certify|verify|prove))|"
    r"(?:not\s+(?:yet|currently|still)|pending|awaiting)(?:\s+(?:a|an|the|our|this))?\s+(?:pure[- ]kernel\s+)?lean(?:\s*4)?|"
    r"(?:pending|awaiting)\s+(?:certification|verification|formalization)|(?:outside(?:\s+of)?|separate\s+from)\s+(?:(?:the|our|this)\s+)?(?:pure[- ]kernel\s+)?lean)\b",
    re.IGNORECASE,
)
_EXT_TAG_INVALID_PRE_RE = re.compile(r"\b(?:previously|formerly|originally|initially|no\s+longer|not(?:\s+(?:just|only|merely|an?))?)\s+$", re.IGNORECASE)
_HEADER_UPPER_RE = re.compile(r"(?<![A-Za-z])(?:upper(?:\s+bound)?|lov[aá]sz|lovaszTheta(?:C7)?|ϑ|\\?vartheta|ceiling|relaxation)(?![A-Za-z])", re.IGNORECASE)
_HEADER_LOWER_RE = re.compile(r"\blower(?:\s+bound)?\b", re.IGNORECASE)
_UPPER_PROSE_CUE_RE = re.compile(r"(?<![A-Za-z])(?:upper\s+bound|lov[aá]sz|lovaszTheta(?:C7)?|ϑ|\\?vartheta|ceiling|relaxation|sandwich|gap|interval)(?![A-Za-z])", re.IGNORECASE)
_UPPER_OP_BEFORE_RE = re.compile(r"(?:<=|≤|\\leqslant(?![A-Za-z])|\\leq(?![A-Za-z])|\\le(?![A-Za-z])|<|\\lt(?![A-Za-z]))(?:\s*[~≈(])*\s*$", re.IGNORECASE)
_SELF_SUBJ_RE = re.compile(r"\b(?:our|we|this\s+(?:work|project|paper|formalization|proof)|track\s+l\d*|campaign)\b", re.IGNORECASE)
_EXT_OLDER_BENCH_BRAG_RE = re.compile(r"\b(?:beats?|beating|surpass(?:es|ed|ing)?|exceeds?|exceeded)\s+(?:gao|itty|polak|schrijver|vesel)\b", re.IGNORECASE)
_PURE_NEG_NON_ACHIEVE_RE = re.compile(
    r"^\s*(?:we|our\s+(?:pure[- ]kernel\s+)?(?:formalization|proof|lean(?:\s*4)?(?:\s+formalization|\s+proof|\s+bound)?))\s+"
    r"(?:(?:did|do|does|have|has|had|are|is)\s+not|didn't|doesn't|don't|haven't|hasn't)\s+(?:(?:yet|formally|independently)\s+){0,2}"
    r"(?:achieve|achieved|reach|reached|formalize|formalized|certify|certified|certifying|verify|verified|prove|proved|proven)\b",
    re.IGNORECASE,
)
_PURE_NEG_MID_RE = re.compile(
    r"^\s*(?:(?:the|a|an|our|this|external|unrefereed|unformalized|prior|c\+\+(?:\d*)?|rust|python|candidate|preprint|bpz(?:'s)?|tandon(?:'s)?|gao(?:'s)?|aug(?:ust)?\.?|jul(?:y)?\.?|202\d|record|bound|value|of)\s+){0,6}$",
    re.IGNORECASE,
)
_MD_LIST_OR_RULE_RE = re.compile(r"^(?:[-*+]\s+|\d+[.)]\s+|[-*_](?:\s*[-*_]){2,}\s*$)")
_PURE_NEG_TAIL_RE = re.compile(r"^(?:in\s+(?:(?:the|our|this)\s+)?(?:pure[- ]kernel\s+)?lean(?:\s*4)?(?:\s+kernel)?)?$", re.IGNORECASE)


def _bounded_sig_in_range(sig: str) -> Fraction | None:
    if not sig.startswith(("32", "33")): return None
    v = Fraction(int(sig[:61]) * 10 + 1, 10**61) if len(sig) > 61 else Fraction(int(sig), 10 ** (len(sig) - 1))
    return v if (Fraction(325, 100) <= v <= LOVASZ_UPPER_RAT) else None


def _parse_lower_num_sig_exp(raw: str) -> tuple[str, int] | None:
    """Parse an exact positive decimal, scientific, comma-grouped, or power-of-10 literal into `(sig_digits, exp10)`."""
    s = raw.replace("{,}", "").replace(",", "").replace(" ", "").replace("\t", "")
    if not s: return None
    if s.startswith("10") and len(s) > 2 and s[2] in "^*⁺⁻⁰¹²³⁴⁵⁶⁷⁸⁹":
        ex = (s[4:] if s[2:4] == "**" else (s[3:] if s[2] == "^" else s[2:].translate(_SUP_DIGIT_MAP))).strip("{}()").replace("−", "-")
        sgn, ed = (-1 if ex.startswith("-") else 1), ex.lstrip("+-").lstrip("0") or "0"
        return ("1", sgn * int(ed)) if (ed.isdigit() and len(ed) <= 6) else None
    if "e" in s or "E" in s:
        ms, es = s.split("e", 1) if "e" in s else s.split("E", 1)
        es = es.replace("−", "-")
        sgn, ed = (-1 if es.startswith("-") else 1), es.lstrip("+-").lstrip("0") or "0"
        if not ed.isdigit() or len(ed) > 6: return None
        exp_add = sgn * int(ed)
    else: ms, exp_add = s, 0
    ip, fp = ms.split(".", 1) if "." in ms else (ms, "")
    nz = (ip + fp).lstrip("0")
    if not nz: return None
    sig = nz.rstrip("0")
    return sig, len(nz) - len(sig) - len(fp) + exp_add


def _extract_lower_candidates(segment: str) -> list[_BoundCandidate]:
    """Extract all decimal, scientific, LaTeX `× 10^k`, ASCII/Unicode fraction, and LaTeX \\frac candidates in `[3.25, LOVASZ_UPPER_RAT]`."""
    cands, dec_cache, frac_cache = [], {}, {}
    if "3." in segment:
        for m in _LOWER_DEC_CAND_RE.finditer(segment):
            ds = m.group(1)
            if ds not in dec_cache:
                w, f = ds.split(".", 1)
                dec_cache[ds] = _bounded_sig_in_range(w.lstrip("0") + f.rstrip("0"))
            if dec_cache[ds] is not None: cands.append(_BoundCandidate(m.start(), m.end(), ds, dec_cache[ds], True))
    if "e" in segment or "E" in segment:
        for m in _LOWER_SCI_CAND_RE.finditer(segment):
            pe = _parse_lower_num_sig_exp(ss := m.group(1))
            if pe is not None and len(pe[0]) - 1 + pe[1] == 0 and (v := _bounded_sig_in_range(pe[0])) is not None: cands.append(_BoundCandidate(m.start(), m.end(), ss, v, True))
    if "10" in segment and any(ch in segment for ch in ("\\", "×", "·", "⋅", "∗", "*")):
        for m in _LOWER_LATEX_SCI_RE.finditer(segment):
            np, pp = _parse_lower_num_sig_exp(m.group(1)), _parse_lower_num_sig_exp(m.group(2))
            if np is not None and pp is not None and len(np[0]) - 1 + np[1] + pp[1] == 0 and (v := _bounded_sig_in_range(np[0])) is not None: cands.append(_BoundCandidate(m.start(), m.end(), m.group(0), v, True))
    for trigger, pat in (("/", _BOUND_FRAC_RE), ("÷", _BOUND_FRAC_RE), ("frac", _LATEX_FRAC_RE)):
        if trigger not in segment or (trigger == "÷" and "/" in segment): continue
        for m in pat.finditer(segment):
            np, dp = _parse_lower_num_sig_exp(m.group(1) or m.group(2)), _parse_lower_num_sig_exp(m.group(3) or m.group(4))
            if np is None or dp is None: continue
            n_sig, n_exp = np; d_sig, d_exp = dp; shift = n_exp - d_exp; v = None
            if d_sig == "1":
                if len(n_sig) - 1 + shift == 0: v = _bounded_sig_in_range(n_sig)
            elif (diff := len(n_sig) + shift - len(d_sig)) in (0, 1):
                if len(n_sig) <= 200 and len(d_sig) <= 200:
                    num, den = int(n_sig) * (10**shift if shift > 0 else 1), int(d_sig) * (10 ** (-shift) if shift < 0 else 1)
                    if 100 * num >= 325 * den and num * _LOVASZ_UPPER_DEN <= _LOVASZ_UPPER_NUM * den:
                        if (fk := (num, den)) not in frac_cache: frac_cache[fk] = Fraction(num, den)
                        v = frac_cache[fk]
                else:
                    n_hi, d_lo = int(n_sig[:60].ljust(60, "0")), int(d_sig[: 60 - diff].ljust(60 - diff, "0"))
                    if 100 * (n_hi + 1) >= 325 * d_lo and n_hi * _LOVASZ_UPPER_DEN <= _LOVASZ_UPPER_NUM * (d_lo + 1): v = Fraction(n_hi, d_lo + 1)
            if v is not None: cands.append(_BoundCandidate(m.start(), m.end(), m.group(0), v, False))
    if len(cands) > 1: cands.sort(key=lambda c: c.start)
    return cands


def _has_unnegated_match(text: str, pat: re.Pattern[str], neg_pat: re.Pattern[str], window: int) -> bool:
    for m in pat.finditer(text):
        win = text[max(0, m.start() - window) : m.start()]
        nm = neg_pat.search(win)
        if nm is None: return True
        if neg_pat is _LEAN_CERT_NEG_RE and (fw := nm.group(0).strip().split(None, 1)[0].lower()) in _LEAN_NEG_DOUBLE_WORDS:
            prev = [w.lstrip("([{\"'").lower() for w in win[: nm.start()].rstrip().rsplit(None, 6)[-6:]]
            pi, steps = len(prev) - 1, 0
            while pi >= 0 and steps < 5 and _is_neg_bridge(prev[pi]): pi -= 1; steps += 1
            if pi >= 0 and (prev[pi] in ("not", "never", "no", "neither", "nor", "cannot") or prev[pi].endswith("n't")): return True
            if fw in ("no", "without", "lack", "lacks", "lacking", "missing") and _TCB_AFTER_CERT_RE.match(text[m.end() : min(len(text), m.end() + 64)].lstrip()): return True
    return False


def _record_inflated(
    inflated: list[dict], cands: list[_BoundCandidate], seg: str, display: str, actual: Fraction, actual_12: str, has_lean: bool, has_brag: bool, has_ext: bool, has_up_cue: bool
) -> None:
    for cand in cands:
        if cand.value <= actual: continue
        if cand.value >= _LOVASZ_MIN_PLAUSIBLE:
            if not (has_up_cue or _UPPER_OP_BEFORE_RE.search(seg[max(0, cand.start - 24) : cand.start])) and (has_lean or has_brag):
                inflated.append({"claimed": cand.raw, "actual_12": actual_12, "line": display[:120]})
        elif has_lean or has_brag or not has_ext:
            inflated.append({"claimed": cand.raw, "actual_12": actual_12, "line": display[:120]})


def _find_inflated_lower_claims(text: str, actual: Fraction, actual_12: str) -> list[dict]:
    """Fail-closed Option A-Report lower-bound separation & honesty verifier (per prose sentence or Markdown table row)."""
    inflated: list[dict] = []
    tagged = _collapse_display_math_tagged(text.split("\n"))
    n_lines, hdr_flags, prev_cells, in_tbl, fc_ch, fc_len, idx = len(tagged), None, None, False, "", 0, 0
    while idx < n_lines:
        raw_line, is_dm = tagged[idx]
        stripped = raw_line.strip()
        fc = _parse_code_fence(stripped)
        if fc is not None:
            if not fc_ch: fc_ch, fc_len, in_tbl, hdr_flags, prev_cells = fc[0], fc[1], False, None, None; idx += 1; continue
            if fc[0] == fc_ch and fc[1] >= fc_len and not stripped[fc[1] :].strip(): fc_ch, fc_len = "", 0; idx += 1; continue
        if not stripped: hdr_flags = prev_cells = None; in_tbl = False; idx += 1; continue
        next_sep = (not fc_ch) and idx + 1 < n_lines and bool(_TABLE_SEP_ROW_RE.match(tagged[idx + 1][0].strip()))
        is_tbl, is_sep = (False, False) if fc_ch else _is_gfm_table_line(stripped, in_tbl, next_sep)
        if is_tbl:
            if is_sep:
                hdr_flags = (
                    [(bool(_HEADER_UPPER_RE.search(h)) and not bool(_HEADER_LOWER_RE.search(h)), _has_unnegated_match(hs := _NEGATED_NATIVE_DECIDE_RE.sub(" ", h), _SELF_LEAN_CERT_RE, _LEAN_CERT_NEG_RE, 80) or bool(_STANDALONE_CERT_CELL_RE.match(hs.rstrip("?")))) for h in prev_cells]
                    if prev_cells is not None else None
                )
                in_tbl = True; idx += 1; continue
            parts = _UNESCAPED_PIPE_RE.split(stripped)
            if stripped.startswith("|") and parts: parts = parts[1:]
            if stripped.endswith("|") and not stripped.endswith(r"\|") and parts: parts = parts[:-1]
            cells = [_normalize_markdown_inline(c.strip()) for c in parts]
            prev_cells = cells
            if next_sep: idx += 1; continue
            cell_cands = [_extract_lower_candidates(c) for c in cells]
            if any(cand.value > actual for cl in cell_cands for cand in cl):
                csan = [_NEGATED_NATIVE_DECIDE_RE.sub(" ", c) for c in cells]
                r_lean = any(_has_unnegated_match(cs, _SELF_LEAN_CERT_RE, _LEAN_CERT_NEG_RE, 80) or bool(_STANDALONE_CERT_CELL_RE.match(cs)) or (hdr_flags is not None and ci < len(hdr_flags) and hdr_flags[ci][1] and bool(_AFFIRM_CELL_RE.match(cs))) for ci, cs in enumerate(csan))
                r_brag = any(_has_unnegated_match(cs, _SELF_BRAG_RE, _BRAG_NEG_RE, 64) for cs in csan)
                r_ext = any(_has_unnegated_match(cs, _EXT_OR_UNFORMALIZED_RE, _EXT_TAG_INVALID_PRE_RE, 32) for cs in csan)
                if r_brag and r_ext and not r_lean and not any(_SELF_SUBJ_RE.search(cs) for cs in csan):
                    r_brag = any(_has_unnegated_match(_EXT_OLDER_BENCH_BRAG_RE.sub(" ", cs), _SELF_BRAG_RE, _BRAG_NEG_RE, 64) for cs in csan)
                r_up = any(_UPPER_PROSE_CUE_RE.search(c) for c in cells)
                for ci, cands in enumerate(cell_cands):
                    if not cands: continue
                    c_up, c_lean = hdr_flags[ci] if (hdr_flags is not None and ci < len(hdr_flags)) else (False, False)
                    eff_cands = ([] if r_ext else [c for c in cands if c.value < _LOVASZ_MIN_PLAUSIBLE]) if (c_up and not r_lean and not c_lean and not r_brag) else cands
                    if eff_cands: _record_inflated(inflated, eff_cands, cells[ci], stripped, actual, actual_12, r_lean or c_lean, r_brag, r_ext, r_up or c_up)
            idx += 1; continue

        hdr_flags = prev_cells = None; in_tbl = False
        norm_line = _normalize_markdown_inline(raw_line, strip_block_prefix=(not fc_ch))
        if not fc_ch and norm_line:
            parts, is_hdr, last_dm = [norm_line], stripped.startswith("#"), is_dm
            def _unwrap_para(c_raw: str, c_str: str, cur_i: int) -> int:
                while cur_i + 1 < n_lines and not c_raw.endswith("  ") and not c_str.startswith("#"):
                    nxt_rf, nxt_dm_u = tagged[cur_i + 1]; nxt_s = nxt_rf.strip(); nxt_bq = nxt_s.startswith(">"); nxt_b = nxt_s.lstrip("> \t") if nxt_bq else nxt_s
                    if not nxt_b or nxt_dm_u or _parse_code_fence(nxt_b) is not None or nxt_b.startswith("#") or (nxt_bq and not c_str.startswith(">") and c_str.startswith(("**", "__")) and ":" in c_str[:60]) or _MD_LIST_OR_RULE_RE.match(nxt_b) or (nxt_b.startswith(("**", "__")) and ":" in nxt_b[:60]): break
                    last_p = parts[-1]; end_t = last_p.rstrip(")\"']")
                    if end_t.endswith(("!", "?")): break
                    if end_t.endswith("."):
                        if not last_p.endswith("."): break
                        tail_buf, tlen = [], 0
                        for p_i in range(len(parts) - 1, -1, -1):
                            tail_buf.append(parts[p_i]); tlen += len(parts[p_i]) + 1
                            if tlen >= 48: break
                        tail_s = " ".join(reversed(tail_buf))[-48:]
                        if not _is_abbrev_dot(f"{tail_s} {nxt_b[:48]}", len(tail_s) - 1, 0): break
                    if _is_gfm_table_line(nxt_s, False, cur_i + 2 < n_lines and bool(_TABLE_SEP_ROW_RE.match(tagged[cur_i + 2][0].strip())))[0]: break
                    if (nxt_p := _normalize_markdown_inline(nxt_rf, strip_block_prefix=nxt_bq)): parts.append(nxt_p)
                    c_raw, c_str = nxt_rf, nxt_s; cur_i += 1
                return cur_i
            if not last_dm: idx = _unwrap_para(raw_line, stripped, idx)
            while idx + 1 < n_lines:
                last_p = parts[-1]
                ends_col = last_p.endswith(":") or (is_hdr and len(parts) == 1)
                ends_open = (not (is_hdr and len(parts) == 1)) and (not last_p.rstrip(")\"']").endswith((".", "!", "?")))
                if not (ends_col or ends_open): break
                look = idx + 1
                while look < n_lines and not tagged[look][0].strip().lstrip("> \t"): look += 1
                if look >= n_lines: break
                nxt_rf, nxt_dm = tagged[look]; nxt_raw = nxt_rf.strip(); nxt_b = nxt_raw.lstrip("> \t") if nxt_raw.startswith(">") else nxt_raw
                if not nxt_b or _parse_code_fence(nxt_b) is not None or nxt_b.startswith("#") or _is_gfm_table_line(nxt_raw, False, look + 1 < n_lines and bool(_TABLE_SEP_ROW_RE.match(tagged[look + 1][0].strip())))[0]: break
                nxt_norm = _normalize_markdown_inline(nxt_rf, strip_block_prefix=True)
                if not nxt_norm: break
                if nxt_dm or (last_dm and ends_open and not _MD_LIST_OR_RULE_RE.match(nxt_b) and not (nxt_b.startswith(("**", "__")) and ":" in nxt_b[:60]) and (nxt_norm[0].islower() or nxt_norm[0] in ",;:—–" or (look == idx + 1 and nxt_norm[0] == "(" and len(nxt_norm) > 1 and nxt_norm[1].islower()))) or (ends_col and (nxt_c := _extract_lower_candidates(nxt_norm)) and nxt_c[0].start == 0):
                    parts.append(nxt_norm); idx = look; last_dm = nxt_dm
                    if not last_dm: idx = _unwrap_para(nxt_rf, nxt_raw, idx)
                else: break
            norm_line = " ".join(parts) if len(parts) > 1 else parts[0]
        line_cands = _extract_lower_candidates(norm_line)
        if any(c.value > actual for c in line_cands):
            for ss, se in _split_sentences_safe(norm_line):
                sent = norm_line[ss:se].strip()
                if not sent: continue
                sc = _extract_lower_candidates(sent)
                if not any(c.value > actual for c in sc): continue
                ssan = _NEGATED_NATIVE_DECIDE_RE.sub(" ", sent)
                s_brag = _has_unnegated_match(ssan, _SELF_BRAG_RE, _BRAG_NEG_RE, 64)
                if len(sc) == 1 and not s_brag and "(" not in sent and "[" not in sent and not _CLAUSE_CUT_RE.search(sent):
                    m_pneg = _PURE_NEG_NON_ACHIEVE_RE.match(sent)
                    if m_pneg is not None and _PURE_NEG_MID_RE.match(sent[m_pneg.end() : sc[0].start]) and _PURE_NEG_TAIL_RE.match(sent[sc[0].end :].strip(" .")):
                        continue
                _record_inflated(
                    inflated, sc, sent, sent, actual, actual_12,
                    _has_unnegated_match(ssan, _SELF_LEAN_CERT_RE, _LEAN_CERT_NEG_RE, 80),
                    s_brag,
                    _has_unnegated_match(ssan, _EXT_OR_UNFORMALIZED_RE, _EXT_TAG_INVALID_PRE_RE, 32),
                    bool(_UPPER_PROSE_CUE_RE.search(sent)),
                )
        idx += 1
    return inflated


# --- Public Report Verification Entrypoints ---

def verify_results_md(
    results_path: Path, lower_num: int | None = None, lower_den: int | None = None
) -> tuple[bool, str, dict]:
    """Audit `RESULTS.md` for strict UTF-8/zero-NUL, completeness, honesty, and exact bound fidelity."""
    text, rcode, rinfo = _read_report_text_strict(results_path)
    if text is None: return False, rcode, rinfo
    if len(text.strip()) < 200: return False, "REPORT_MISMATCH", {"reason": "RESULTS.md is empty or too short (< 200 chars)"}
    placeholders = _PLACEHOLDER_RE.findall(text)
    if placeholders: return False, "REPORT_MISMATCH", {"reason": f"Unresolved placeholder(s) in RESULTS.md: {placeholders[:5]}"}

    norm_doc = _normalize_markdown_document(text)
    false_claim = _find_false_exact_claim(norm_doc)
    if false_claim is not None: return False, "HONESTY_VIOLATION", {"reason": f"False exact-solution claim detected in RESULTS.md: {false_claim!r}"}
    imp_upper = _find_impossible_upper_claim(norm_doc)
    if imp_upper is not None: return False, "REPORT_MISMATCH", imp_upper

    low, missing = norm_doc.lower(), []
    if not any(k in low for k in ("open", "openquestion", "gap")): missing.append("open-problem/gap status")
    if not any(k in text or k in norm_doc for k in ("3.317667", "3317667207395", "lovaszThetaC7", "Lovász", "Lovasz", "vartheta", "ϑ")): missing.append("Lovasz upper bound")
    if not ("33" in text and "10" in text): missing.append("exact small powers (3, 10, 33)")
    if not any(k in text or k in norm_doc for k in ("propext", "Classical.choice", "Quot.sound", "pure kernel", "pure-kernel")): missing.append("TCB / axiom summary")
    if missing: return False, "REPORT_MISMATCH", {"reason": f"RESULTS.md missing required sections/facts: {', '.join(missing)}"}

    if lower_num is not None or lower_den is not None:
        if not (_is_strict_int(lower_num) and _is_strict_int(lower_den) and lower_den > 0 and lower_num > 0):
            return False, "BOUNDS_VIOLATION", {"reason": "Invalid lower_num / lower_den supplied to verify_results_md"}
        actual = Fraction(lower_num, lower_den)
        actual_12 = _safe_fraction_preview(actual, 12)
        num_ok = lower_num.bit_length() <= 300000 and str(lower_num) in text
        dec_ok = (not actual_12.startswith("<")) and (actual_12[:10] in text or actual_12[:10] in norm_doc)
        if not (num_ok or dec_ok):
            return False, "REPORT_MISMATCH", {"reason": f"RESULTS.md does not cite achieved Lean bound {actual_12} (num={_safe_int_preview(lower_num)})", "expected_decimal_12": actual_12}
        inflated = _find_inflated_lower_claims(text, actual, actual_12)
        if inflated: return False, "REPORT_MISMATCH", {"reason": f"RESULTS.md inflates/rounds up Lean-verified lower bound above {actual_12}", "inflated": inflated}
    return True, "OK", {"path": str(results_path), "bytes": len(text)}


def verify_research_report(
    report_path: Path, kind: str, lower_num: int | None = None, lower_den: int | None = None
) -> tuple[bool, str, dict]:
    """Audit `LOWER_RESEARCH_REPORT.md` or `UPPER_RESEARCH_REPORT.md`."""
    text, rcode, rinfo = _read_report_text_strict(report_path)
    if text is None: return False, rcode, rinfo
    if len(text.strip()) < 150: return False, "REPORT_MISMATCH", {"reason": f"{report_path.name} is empty or too short"}
    placeholders = _PLACEHOLDER_RE.findall(text)
    if placeholders: return False, "REPORT_MISMATCH", {"reason": f"Unresolved placeholder(s) in {report_path.name}: {placeholders[:5]}"}

    norm_doc = _normalize_markdown_document(text)
    low = norm_doc.lower()
    if kind == "lower":
        false_claim = _find_false_exact_claim(norm_doc)
        if false_claim is not None: return False, "HONESTY_VIOLATION", {"reason": f"False exact-solution claim detected in {report_path.name}: {false_claim!r}"}
        imp_upper = _find_impossible_upper_claim(norm_doc)
        if imp_upper is not None: return False, "REPORT_MISMATCH", imp_upper
        if lower_num is not None or lower_den is not None:
            if not (_is_strict_int(lower_num) and _is_strict_int(lower_den) and lower_den > 0 and lower_num > 0):
                return False, "BOUNDS_VIOLATION", {"reason": "Invalid lower_num / lower_den supplied to verify_research_report"}
            actual = Fraction(lower_num, lower_den)
            actual_12 = _safe_fraction_preview(actual, 12)
            inflated = _find_inflated_lower_claims(text, actual, actual_12)
            if inflated: return False, "REPORT_MISMATCH", {"reason": f"LOWER_RESEARCH_REPORT.md inflates certified bound {inflated[0]['claimed']} > {actual_12}", "inflated": inflated}
            num_ok = lower_num.bit_length() <= 300000 and str(lower_num) in text
            dec_ok = (not actual_12.startswith("<")) and (actual_12[:9] in text or actual_12[:9] in norm_doc)
            if not (num_ok or dec_ok): return False, "REPORT_MISMATCH", {"reason": f"LOWER_RESEARCH_REPORT.md does not mention achieved bound {actual_12}"}
        return True, "OK", {"path": str(report_path), "bytes": len(text)}

    if kind == "upper":
        false_claim = _find_false_exact_claim(norm_doc)
        if false_claim is not None: return False, "HONESTY_VIOLATION", {"reason": f"False exact-solution claim: {false_claim!r}"}
        missing = []
        if "33" not in text: missing.append("alpha(C_7^3)=33")
        if not any(k in low for k in ("115", "112", "392", "c_7^4", "c_{7}^4", "c7^4", "c₇^4", "c₇⁴", "fourth power", "c_7^{\\", "c_7^{⊠")): missing.append("C_7^4 upper bound audit")
        if not any(k in low for k in ("bukh", "bi–tang", "bi-tang", "sason", "obstruction", "barrier", "gilbert", "srg(27", "haemers")): missing.append("obstruction/barrier analysis")
        if missing: return False, "REPORT_MISMATCH", {"reason": f"UPPER_RESEARCH_REPORT.md missing: {', '.join(missing)}"}
        imp_upper = _find_impossible_upper_claim(norm_doc)
        if imp_upper is not None: return False, "REPORT_MISMATCH", imp_upper
        return True, "OK", {"path": str(report_path), "bytes": len(text)}

    return False, "MATH_MISMATCH", {"reason": f"Unknown report kind {kind!r}"}


# ---------------------------------------------------------------------------
# 9. Standalone CLI Entrypoint
# ---------------------------------------------------------------------------


def _cli(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Standalone exact-arithmetic, hygiene, axiom, witness & obstruction verifier"
    )
    parser.add_argument("--hygiene", type=Path, help="Run Lean 4 hygiene scanner on a .lean file")
    parser.add_argument("--mode", choices=("impl", "audit"), default="impl", help="Hygiene scan mode")
    parser.add_argument("--axioms", type=Path, help="Verify #print axioms output from a text file")
    parser.add_argument("--cubic", action="store_true", help="Verify cubic irreducibility, brackets & PSD certificates")
    parser.add_argument("--obstructions", action="store_true", help="Verify all 5 obstruction graphs")
    parser.add_argument("--verify-witness", type=Path, help="Verify a JSON witness file")
    parser.add_argument("--project-dir", type=Path, help="Run full independent math/witness/hygiene audit on project dir")
    args = parser.parse_args(argv)

    if args.hygiene:
        if not args.hygiene.is_file():
            print(json.dumps({"ok": False, "code": "MISSING_FILE", "path": str(args.hygiene)}))
            return 1
        src, enc_viols = read_lean_source_strict(args.hygiene)
        if src is None:
            print(
                json.dumps(
                    {
                        "ok": False,
                        "code": "HYGIENE_VIOLATION",
                        "violations": [v.to_dict() for v in enc_viols],
                    },
                    indent=2,
                )
            )
            return 1
        viols = scan_lean_hygiene(src, path=str(args.hygiene), mode=args.mode)
        ok = len(viols) == 0
        print(json.dumps({"ok": ok, "violations": [v.to_dict() for v in viols]}, indent=2))
        return 0 if ok else 1

    if args.axioms:
        if not args.axioms.is_file():
            print(json.dumps({"ok": False, "code": "MISSING_FILE", "path": str(args.axioms)}))
            return 1
        raw = args.axioms.read_text(encoding="utf-8", errors="replace")
        parsed = parse_print_axioms(raw)
        ok, code, info = verify_axiom_whitelist(parsed, required_decls=REQUIRED_AUDIT_AXIOM_DECLS, raw_output=raw)
        print(json.dumps({"ok": ok, "code": code, "info": info}, indent=2))
        return 0 if ok else 1

    if args.cubic:
        ok1, c1, i1 = verify_cubic_irreducibility_and_roots()
        ok2, c2, i2 = verify_c7_fourier_psd()
        ok3, c3, i3 = verify_c7_compl_psd()
        ok = ok1 and ok2 and ok3
        print(json.dumps({"ok": ok, "cubic": i1, "c7_psd": i2, "compl_psd": i3}, indent=2))
        return 0 if ok else 1

    if args.obstructions:
        ok, code, info = verify_obstruction_graphs()
        print(json.dumps({"ok": ok, "code": code, "info": info}, indent=2))
        return 0 if ok else 1

    if args.verify_witness:
        ok, code, info = verify_witness_json(args.verify_witness)
        print(json.dumps({"ok": ok, "code": code, "info": info}, indent=2))
        return 0 if ok else 1

    if args.project_dir:
        ok_cub, _, i_cub = verify_cubic_irreducibility_and_roots()
        ok_obs, _, i_obs = verify_obstruction_graphs()
        ok_dp, _, i_dp = verify_profile_dp()
        ok_w = all(
            verify_strong_power_independent_set(w, fn, d, dom)[0]
            for w, fn, d, dom in (
                (WITNESS_C5_POW2, c5_adj, 2, 5),
                (WITNESS_C7_POW1, c7_adj, 1, 7),
                (WITNESS_C7_POW2, c7_adj, 2, 7),
                (WITNESS_C7_POW3, c7_adj, 3, 7),
                (WITNESS_C7_COMPL_POW4, c7_compl_adj, 4, 7),
            )
        )
        ok_b, code_b, info_b = extract_main_bounds(args.project_dir / "ShannonC7" / "Main.lean")
        ok_all = ok_cub and ok_obs and ok_dp and ok_w and ok_b
        print(
            json.dumps(
                {
                    "ok": ok_all,
                    "cubic": ok_cub,
                    "obstructions": ok_obs,
                    "profile_dp": ok_dp,
                    "witnesses": ok_w,
                    "main_bounds": {"ok": ok_b, "code": code_b, **info_b},
                },
                indent=2,
            )
        )
        return 0 if ok_all else 1

    parser.print_help()
    return 2


if __name__ == "__main__":
    raise SystemExit(_cli())
