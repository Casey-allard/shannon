#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REPO_ROOT_REAL="$(python3 -c 'import os, sys; print(os.path.realpath(sys.argv[1]))' "$REPO_ROOT")"
CALLER_PWD="$(pwd)"
export PATH="$HOME/.elan/bin:$PATH"

DO_BUILD=0
VERBOSE=0
RAW_ARGS=()
END_OF_OPTS=0

for arg in "$@"; do
  if [ "$END_OF_OPTS" -eq 1 ]; then
    RAW_ARGS+=("$arg")
    continue
  fi
  case "$arg" in
    --) END_OF_OPTS=1 ;;
    --build) DO_BUILD=1 ;;
    --verbose|-v) VERBOSE=1 ;;
    -h|--help)
      cat <<'USAGE'
Usage: scripts/verify_axioms.sh [--build] [--verbose] [--] [MODULE_OR_FILE ...]

Audits Lean 4 modules/files under ShannonC7/ for:
  1. Static code hygiene via Lean 4's own real parser (`Lean.Parser.parseHeader` +
     `Lean.Parser.parseCommand`) under the Positive-Whitelist Fail-Closed Pure-Math
     Stage 1 Policy:
     - Closed top-level command whitelist: allows standard Lean/Mathlib proof
       declarations, scopes (`section` excl. `meta section`, `namespace`, `end`,
       `open`, `export`, `variable`, `universe`, `include`, `omit`, `set_option`,
       `unlock_limits`, `attribute`), declarative term notations (`notation`,
       `mixfix`: `infixl`/`infixr`/`infix`/`prefix`/`postfix`, `scoped[NS]` on
       `notation`/`mixfix`/`attribute`), pure diagnostics (`#check`, `#print`,
       `#reduce`, etc.), and standard wrappers (`in`, `with_weak_namespace`,
       `with_exporting`, `#time`, `#guard_msgs`, `#guard_panic`, `#info_trees`,
       `mutual`); FAILS CLOSED on all arbitrary metaprogramming (`macro`,
       `macro_rules`, `syntax`, `syntax_abbrev`, `declare_syntax_cat`, `elab`,
       `elab_rules`, `binder_predicate`, `run_cmd`, `run_elab`, `run_meta`,
       `#eval`, `#eval!`, `initialize`, `builtin_initialize`, `simproc*`,
       `notation3`, `sudo set_option`, `#exit`, mid-file `import`, etc.).
     - Strict symbolic-only `isSafeNotationAtom` (both in-file against `baseEnv`'s
       token table and pre-import against `builtinTokenTable` + 117 core extra
       non-alpha tokens): rejects ALL ASCII letters/digits, `Lean.isIdFirst`/
       `Lean.isIdRest` characters, non-ASCII whitespace/zero-width/invisible/
       format/control characters, `/` and `-` comment-boundary characters,
       quotes/delimiters/sigils (`!`, `$`, `` ` ``, etc.), atom-less notations,
       and ALL already-registered core parser tokens, permitting only clean
       mathematical operator symbols (e.g. `"⊠"`).
     - Zero-RCE exact scope/option/namespace/declarative-notation tracking
       (`elabNamespace`, `elabSection`, `elabEnd`, `elabSetOption`,
       `elabOpenStage1`, syntax-only `elabNotationStage1`/`elabMixfixStage1`,
       exact Lean `registerNamePrefixes` namespace tracking across `declaration`/
       `classAbbrev`/`lemma`/`alias`/`mutual` incl. signature/binder-type `match`/
       destructuring `fun`, shadowed binder/`let`/`fun` tracking, trivial single-
       arm var/unit `match` fidelity, `declValEqns` `where`, `whereStructInst`,
       `match`/`let rec`/recursion aux-decl synthesis with `Elab.async` fidelity,
       exact `Command.in` `setDelimitsLocal 1`, and `#guard_msgs`/`#info_trees`
       isolation failing closed on error-dropping/error-expecting/`substring` or
       `#guard_panic` declarations).
     - Exact import-set subprocess isolation (`--plan`/`--bucket`), isolated
       cached Stage 1 driver module (`VERIFY_AXIOMS_S1_MOD_DIR` stripped from
       `searchPathRef`), completion sentinel, and safe output-path guard.
     - Pre-import local `.olean` guard (BEFORE `importModules`): closed POSITIVE
       WHITELIST of 95 verified passive Lean core extensions (startup-verified
       via `checkAllowedCoreExtsRegistered`) + 12 passive Batteries/Mathlib
       extensions + 5 structurally audited extensions (`parserExtension`,
       `macroAttribute`, `appUnexpanderAttribute`, `metaExt`, `declMetaExt`),
       failing closed on ALL unlisted/unknown/executable/Aesop/Simps/RPC/widget/
       FFI/compiler-pass extensions; fail-closed multi-part `module` stub
       merging; closed constant whitelists, fail-closed literal `Name`/`Syntax`
       construction checks, embedded-literal checks, exact 1-to-1
       `(kind, headTarget)` unexpander coupling, and binder-free `autoParam`
       `Lean.Syntax` (`_auto_*` / `_autoParam`) audits (+ post-import
       `KeyedDeclsAttribute` sanitization defense-in-depth).
     - Deep `Lean.Syntax` AST walk (incl. `nameLitKind`, `isGenuineSkippedLeaf`):
       closed POSITIVE ATTRIBUTE WHITELIST (33 simple + 57 custom-syntax + 70
       erase verified zero-`evalConst` pure-math attributes, recursively enforced
       on nested `(attr := ...)` — failing closed on ALL unlisted/meta/Aesop/
       Simps/RPC/widget/FFI/delab/cpass attributes); positive config whitelists
       for `decide` and `linarith`/`nlinarith`; unified `isForbiddenOptionName`
       (`debug.*`, `sat.*`, `compiler.*`, `bootstrap.*`, `internal.*`,
       `interpreter.*`, `aesop.*`, `says.*`, `leansearchclient.*`,
       `statesearch.*`, `allowUnsafeReducibility`, `warn.sorry`,
       `trace.profiler.{output,serve}`, incl. `Grind.setOption` with recursive
       suffix extraction); package-wide
       evaluator/admit-tactic AST blocklist (`by_elab`, `by_elabq`, `run_tac`,
       `run_tacq`, `include_str`, `trace`, `idbg`, `impossible`, `apply?`,
       `exact?`, `try?`, `Aesop` tactics & clauses, `eval%`, `from_lrat`,
       `pi_*_bound`, `success_if_fail_with_msg`, `hint`, `extract_goal`,
       `plausible`, `with_panel_widgets`, `mk_rpc_widget%`, `LeanSearchClient`,
       `Lake.DSL.{runIO,evalVer,verLit}`, `bv_decide*`, etc.); and 76
       defense-in-depth `forbiddenTokens`.
  2. Freshness of compiled .olean artifacts (`lake build --no-build`; when --build
     is given for in-repo targets, builds target .oleans prior to Stage 1).
  3. True Lean 4 C++ kernel replay (`Lean.Environment.replay` with trustLevel := 0
     on top of path-verified sysroot + .lake/packages base modules) across all
     target and transitive local modules, direct `Kernel.Environment` transitive
     axiom walk (`axioms ⊆ {propext, Classical.choice, Quot.sound}`), pre-replay
     rejection of custom axioms / quotients / unsafe / @[implemented_by] / @[extern]
     / @[init], duplicate-constant and `partMap`-aware cross-part consistency
     across regular and `module` (.olean/.olean.server/.olean.private/.ir)
     artifacts, and anti-spoof verification of every compiler-generated
     `_unsafe_rec` helper (`Kernel.isDefEq`, substituted kernel typecheck,
     `u.type` & body axiom audit, `recExt`, `!isNoncomputable`, class-codomain
     `thmInfo`, `eqnInfoExt`, safe non-Prop abbrev `_f`/`_sunfold`, structural
     re-compilation with kernel `isDefEq`, direct 1-step WF/PF/PropPF fixpoint
     unfolding with `usesIHAsCall` + `propRecSkeletonEq`, and verified
     `Meta.getUnfoldEqnFor?` equation types).

Arguments may be module names (e.g. ShannonC7.Defs) or relative/absolute .lean
paths (e.g. ShannonC7/Defs.lean or /abs/path/to/ShannonC7/Defs.lean).
Explicit ./ and ../ paths resolve strictly against the caller's working directory;
bare .lean paths check the caller's working directory before the repository root.
Duplicate targets are deduplicated preserving order.
Defaults to all .lean files currently present under ShannonC7/.
USAGE
      exit 0
      ;;
    -*)
      echo "ERROR: Unknown option: $arg" >&2
      echo "Run '$0 --help' for usage." >&2
      exit 2
      ;;
    *) RAW_ARGS+=("$arg") ;;
  esac
done

cd "$REPO_ROOT"

array_contains() {
  local -n __ac_arr="$1"
  local needle="$2"
  local existing
  for existing in "${__ac_arr[@]}"; do
    if [ "$existing" = "$needle" ]; then
      return 0
    fi
  done
  return 1
}

add_unique() {
  local -n __au_arr="$1"
  local val="$2"
  if ! array_contains "$1" "$val"; then
    __au_arr+=("$val")
  fi
}

FILES=()
MODS=()
EXTERNAL_FILES=()

if [ "${#RAW_ARGS[@]}" -eq 0 ]; then
  if [ ! -d "$REPO_ROOT/ShannonC7" ]; then
    echo "ERROR: Directory $REPO_ROOT/ShannonC7 does not exist." >&2
    exit 1
  fi
  while IFS= read -r f; do
    add_unique FILES "$f"
    mod="${f%.lean}"
    mod="${mod//\//.}"
    add_unique MODS "$mod"
  done < <(find ShannonC7 -type f -name '*.lean' | LC_ALL=C sort)
else
  for item in "${RAW_ARGS[@]}"; do
    if [ -z "$item" ]; then
      echo "ERROR: Empty target argument." >&2
      exit 1
    fi
    if [[ "$item" == *.lean ]]; then
      candidate=""
      if [[ "$item" == /* ]]; then
        candidate="$item"
      elif [[ "$item" == ./* || "$item" == ../* ]]; then
        candidate="$CALLER_PWD/$item"
      elif [ -f "$CALLER_PWD/$item" ]; then
        candidate="$CALLER_PWD/$item"
      elif [ -f "$REPO_ROOT/$item" ]; then
        candidate="$REPO_ROOT/$item"
      else
        echo "ERROR: Target Lean file not found: $item" >&2
        exit 1
      fi
      if [ ! -f "$candidate" ]; then
        echo "ERROR: Target Lean file not found: $item" >&2
        exit 1
      fi
      abs="$(python3 -c 'import os, sys; print(os.path.realpath(sys.argv[1]))' "$candidate")"
      if [[ "$abs" == "$REPO_ROOT_REAL/"* ]]; then
        rel="${abs#"$REPO_ROOT_REAL/"}"
        mod="${rel%.lean}"
        mod="${mod//\//.}"
        add_unique FILES "$rel"
        add_unique MODS "$mod"
      else
        if ! array_contains FILES "$abs"; then
          FILES+=("$abs")
          EXTERNAL_FILES+=("$item")
        fi
      fi
    else
      if [[ "$item" == /* || "$item" == ./* || "$item" == ../* || "$item" == */* || "$item" == .* || "$item" == *. || "$item" == *..* ]]; then
        echo "ERROR: Target Lean file not found: $item" >&2
        exit 1
      fi
      f="${item//./\/}.lean"
      if [ ! -f "$REPO_ROOT/$f" ]; then
        echo "ERROR: Target Lean file not found: $f" >&2
        exit 1
      fi
      abs="$(python3 -c 'import os, sys; print(os.path.realpath(sys.argv[1]))' "$REPO_ROOT/$f")"
      if [[ "$abs" != "$REPO_ROOT_REAL/"* ]]; then
        echo "ERROR: File is outside repository root ($REPO_ROOT): $item" >&2
        exit 1
      fi
      rel="${abs#"$REPO_ROOT_REAL/"}"
      mod="${rel%.lean}"
      mod="${mod//\//.}"
      add_unique FILES "$rel"
      add_unique MODS "$mod"
    fi
  done
fi

if [ "${#FILES[@]}" -eq 0 ]; then
  echo "ERROR: No Lean files found to audit." >&2
  exit 1
fi

TMP_DIR="$(mktemp -d)"
chmod 700 "$TMP_DIR"
trap 'rm -rf "$TMP_DIR"' EXIT

# When --build is requested for in-repo targets, build .oleans first so cross-module
# imports (e.g. ShannonC7/Fekete.lean importing ShannonC7.Defs) exist for Lean.Parser.
if [ "$DO_BUILD" -eq 1 ] && [ "${#EXTERNAL_FILES[@]}" -eq 0 ]; then
  echo "=== [pre-1/3] Building target .olean artifacts (--build) ==="
  LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" lake build "${MODS[@]}"
fi

echo "=== [1/3] Static hygiene scan via Lean 4 parser (${#FILES[@]} file(s)) ==="
STAGE1_FILE="$TMP_DIR/Stage1Audit.lean"
cat > "$STAGE1_FILE" <<'STAGE1_LEAN'
import Lean

open Lean Parser Elab Command
open Lean.Parser.Term hiding macroArg

private def pathIsUnder (child parent : System.FilePath) : Bool :=
  let c := child.toString
  let p := parent.toString
  let pSlash := if p.endsWith "/" then p else p ++ "/"
  c.startsWith pSlash

private def hasSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

def forbiddenTokens : Std.HashSet String :=
  Std.HashSet.ofList [
    "sorry",
    "sorryAx",
    "admit",
    "admitGoal",
    "axiom",
    "unsafe",
    "partial",
    "implemented_by",
    "extern",
    "native_decide",
    "ofReduceBool",
    "ofReduceNat",
    "reduceBool",
    "reduceNat",
    "trustCompiler",
    "skipKernelTC",
    "byAsSorry",
    "proofAsSorry",
    "terminalTacticsAsSorry",
    "unsafeCast",
    "lcProof",
    "addDecl",
    "addDeclCore",
    "addDeclWithoutChecking",
    "addAndCompile",
    "addAndCompilePartialRec",
    "addAndCompileUnsafe",
    "addAsAxiom",
    "addDeclUnsafe",
    "addPreDefinitions",
    "addPreDefsFromUnary",
    "addNonRec",
    "addAndCompileNonRec",
    "addConstAsync",
    "compileDecl",
    "compileDecls",
    -- Defense-in-depth escape / evaluator / sorry-synthesis tokens (all 0 hits in ShannonC7/)
    "by_elab",
    "by_elabq",
    "include_str",
    "run_tac",
    "run_tacq",
    "run_cmd",
    "run_elab",
    "run_meta",
    "run_io",
    "bv_decide",
    "bv_decide?",
    "bv_check",
    "leading_parser",
    "trailing_parser",
    "mstop",
    "mkSorry",
    "mkLabeledSorry",
    "mkSyntheticSorryFor",
    "from_lrat",
    "idbg",
    "eval%",
    "evalExpr",
    "evalExpr'",
    "evalExprCore",
    "evalExprWithElab",
    "evalTerm",
    "evalTermAt",
    "evalTermOrExprWithElab",
    "evalTermWithRef",
    "evalConst",
    "evalConstCheck",
    "evalConstUnsafe",
    "dbg_trace",
    "dbgTrace",
    "dbgTraceVal",
    "dbgTraceIfShared",
    "dbgSleep",
    "dbgStackTrace",
    "aesop_trace[",
    "aesop_trace!["
  ]

private def hasForbiddenIdentWord (s : String) : Bool := Id.run do
  let mut acc := ""
  for ch in s.toList do
    if ch.isAlphanum || ch == '_' then
      acc := acc.push ch
    else
      if !acc.isEmpty && forbiddenTokens.contains acc then
        return true
      acc := ""
  if !acc.isEmpty && forbiddenTokens.contains acc then
    return true
  return false

def checkNameForbidden (n : Name) : Option String :=
  n.components.findSome? fun comp =>
    match comp with
    | .str .anonymous s => if forbiddenTokens.contains s then some s else none
    | _ => none

-- Unified forbidden `set_option` predicate: blocks `debug.*` (incl. `_root_.debug.*`),
-- external solver / compile-time I/O / HTTP server / compiler / bootstrap / internal /
-- interpreter / Aesop / search-client / sorry-suppression / unsafe-reducibility options.
private def isForbiddenOptionName (n : Name) : Bool :=
  let comps := n.eraseMacroScopes.components
  let comps := match comps with
    | .str .anonymous "_root_" :: rest => rest
    | _ => comps
  match comps with
  | .str .anonymous "debug" :: _ => true
  | .str .anonymous "sat" :: _ => true
  | .str .anonymous "compiler" :: _ => true
  | .str .anonymous "bootstrap" :: _ => true
  | .str .anonymous "internal" :: _ => true
  | .str .anonymous "interpreter" :: _ => true
  | .str .anonymous "aesop" :: _ => true
  | .str .anonymous "says" :: _ => true
  | .str .anonymous "leansearchclient" :: _ => true
  | .str .anonymous "statesearch" :: _ => true
  | .str .anonymous "allowUnsafeReducibility" :: _ => true
  | .str .anonymous "warn" :: .str .anonymous "sorry" :: _ => true
  | .str .anonymous "trace" :: .str .anonymous "profiler" :: .str .anonymous "output" :: _ => true
  | .str .anonymous "trace" :: .str .anonymous "profiler" :: .str .anonymous "serve" :: _ => true
  | _ => false

-- Exact closed set of non-ASCII-letter tokens registered in Lean v4.32.2 `Init` + `Lean`
-- beyond `Lean.Parser.builtinTokenTable` (117 tokens, empirically verified).
-- Guarantees both `prelude` files and pre-import `.olean` audits reject 100% of core tokens
-- without calling `importModules` before `preCheckImports`.
private def coreExtraNonAlphaTokens : Std.HashSet String :=
  Std.HashSet.ofList [
    "!=", "!~>", "#", "#[", "%", "%[", "&&", "&&&",
    "*...", "*...*", "*...<", "*...=", "*>", "++",
    ",*,?", ",+", ",+,?", "...", "...*", "...<", "...=",
    "/", "//", "/\\", ":=~", ":=ₐ", ":=ₛ", ":~", ":ₐ", ":ₛ",
    "<$>", "<&&>", "<&>", "<*", "<*>", "<+:", "<->",
    "<...", "<...*", "<...<", "<...=", "<:+", "<:+:", "<;>",
    "<<<", "<=<", "<|>", "<||>", "=", "=<<", "==", "=~", "=ₐ", "=ₛ",
    ">", ">=", ">=>", ">>", ">>=", ">>>", "\\", "\\/", "]'",
    "^", "^^", "^^^", "|>", "||", "|||", "~", "~>", "~~~",
    "¬", "×", "×'", "Σ", "Σ'", "•", "‹", "›", "⁻¹",
    "↑", "→ₑ", "↓", "↔", "↥", "⇐", "⇑", "⇒", "∃", "∅", "∈", "∉", "∎",
    "∘", "∣", "∧", "∧ₑ", "∨", "∩", "∪", "≈", "≍", "≟", "≠",
    "≤", "≥", "⊂", "⊃", "⊆", "⊇", "⊕", "⊕'", "⊢", "⌜", "⌝", "□"
  ]

private def isForbiddenNotationChar (c : Char) : Bool :=
  ('A' <= c && c <= 'Z') ||
  ('a' <= c && c <= 'z') ||
  ('0' <= c && c <= '9') ||
  Lean.isIdFirst c ||
  Lean.isIdRest c ||
  c.val < 0x20 ||
  (c.val >= 0x7f && c.val <= 0x9f) ||
  c.isWhitespace ||
  c.val == 0x00a0 || c.val == 0x00ad || c.val == 0x034f ||
  c.val == 0x061c || c.val == 0x1680 || c.val == 0x180e ||
  (c.val >= 0x2000 && c.val <= 0x200f) ||
  (c.val >= 0x2028 && c.val <= 0x202f) ||
  (c.val >= 0x205f && c.val <= 0x206f) ||
  c.val == 0x3000 ||
  (c.val >= 0xfe00 && c.val <= 0xfe0f) ||
  c.val == 0xfeff ||
  (c.val >= 0xfff9 && c.val <= 0xfffd) ||
  (c.val >= 0xe0000 && c.val <= 0xe01ef) ||
  c == '"' || c == '\'' || c == '`' ||
  c == '«' || c == '»' || c == '\\' ||
  c == '/' || c == '-' || c == '!' ||
  c == '#' || c == '$' || c == '@' || c == ';' ||
  c == '(' || c == ')' || c == '[' || c == ']' ||
  c == '{' || c == '}' || c == ','

-- Strict Symbolic-Only Notation Atom Predicate (Mandate #2 Pillar 3):
-- Enforced BOTH pre-import (with `Lean.Parser.builtinTokenTable.get`)
-- AND in-file (with `Lean.Parser.getTokenTable baseEnv`).
private def isSafeNotationAtom (tokTable : TokenTable) (s : String) : Bool :=
  let t := s.trimAscii.toString
  !t.isEmpty &&
  !t.toList.any isForbiddenNotationChar &&
  !t.endsWith "!" &&
  !hasSubstr t "/-" &&
  !hasSubstr t "-/" &&
  !hasSubstr t "--" &&
  (tokTable.find? t).isNone &&
  !coreExtraNonAlphaTokens.contains t

private def forbiddenNotationKinds : NameSet :=
  ({} : NameSet)
    |>.insert strLitKind
    |>.insert charLitKind
    |>.insert interpolatedStrLitKind
    |>.insert nameLitKind
    |>.insert choiceKind
    |>.insert nullKind
    |>.insert ``Lean.Parser.Command.docComment
    |>.insert ``Lean.Parser.Command.moduleDoc

private def forbiddenAstKinds : NameSet :=
  ({} : NameSet)
    -- Command metaprogramming & immediate execution
    |>.insert ``Lean.Parser.Command.macro
    |>.insert ``Lean.Parser.Command.macro_rules
    |>.insert ``Lean.Parser.Command.syntax
    |>.insert ``Lean.Parser.Command.syntaxAbbrev
    |>.insert ``Lean.Parser.Command.syntaxCat
    |>.insert ``Lean.Parser.Command.elab
    |>.insert ``Lean.Parser.Command.elab_rules
    |>.insert ``Lean.Parser.Command.binderPredicate
    |>.insert ``Lean.Parser.Command.initialize
    |>.insert ``Lean.Parser.Command.eval
    |>.insert ``Lean.Parser.Command.evalBang
    |>.insert ``Lean.Parser.Command.init_quot
    |>.insert ``Lean.Parser.Command.InternalSyntax.end_local_scope
    |>.insert ``Lean.runCmd
    |>.insert ``Lean.runElab
    |>.insert ``Lean.runMeta
    |>.insert ``Lean.Parser.Command.meta
    |>.insert ``Lean.Parser.Command.computedFields
    |>.insert `Lean.Parser.simprocPattern
    |>.insert `Lean.Parser.simprocPatternBuiltin
    |>.insert `Lean.Parser.cbvSimprocPattern
    |>.insert `Lean.Parser.cbvSimprocPatternBuiltin
    |>.insert `Lean.Parser.Command.registerSimpAttr
    |>.insert ``Lean.Option.registerOption
    |>.insert ``Lean.Option.registerBuiltinOption
    |>.insert ``Lean.Parser.Tactic.declareSimpLikeTactic
    |>.insert ``Lean.Elab.Command.aux_def
    |>.insert `Aesop.Frontend.Parser.declareRuleSets
    |>.insert `Mathlib.Notation3.notation3
    -- Term / tactic escapes, evaluators, admit-tactics & diagnostics
    |>.insert ``Lean.byElab
    |>.insert ``Lean.includeStr
    |>.insert ``Lean.Parser.Tactic.runTac
    |>.insert ``Lean.Parser.Term.leading_parser
    |>.insert ``Lean.Parser.Term.trailing_parser
    |>.insert ``Lean.Parser.Tactic.nativeDecide
    |>.insert ``Lean.Parser.Tactic.tacticStop_
    |>.insert ``Lean.Parser.Tactic.mstopMacro
    |>.insert `Lean.Parser.Tactic.mstop
    |>.insert `Lean.Parser.Tactic.trace
    |>.insert ``Lean.Parser.Tactic.traceMessage
    |>.insert ``Lean.Parser.Tactic.traceState
    |>.insert ``Lean.Parser.Tactic.Conv.convTrace_state
    |>.insert ``Lean.Parser.Tactic.dbgTrace
    |>.insert ``Lean.Parser.Term.dbgTrace
    |>.insert ``Lean.Parser.Term.doDbgTrace
    |>.insert ``Lean.Parser.Tactic.sleep
    |>.insert ``Lean.Parser.Tactic.bvDecideMacro
    |>.insert ``Lean.Parser.Tactic.bvTraceMacro
    |>.insert `Lean.Parser.Tactic.bvDecide
    |>.insert `Lean.Parser.Tactic.bvCheck
    |>.insert `Lean.Parser.Tactic.bvTrace
    |>.insert ``Lean.Parser.Term.idbg
    |>.insert ``Lean.Parser.Term.doIdbg
    |>.insert ``Lean.Parser.Tactic.impossible
    |>.insert ``Lean.Parser.Tactic.apply?
    |>.insert ``Lean.Parser.Tactic.exact?
    |>.insert ``Lean.Parser.Syntax.exact?
    |>.insert ``Lean.Parser.Tactic.tryTrace
    -- Qq
    |>.insert `Qq.termBy_elabq_
    |>.insert `Qq.«tacticRun_tacq_=>_»
    -- Aesop (direct tactics + ALL tactic_clauses used by aesop_graph/aesop_cat/finiteness/etc.)
    |>.insert `Aesop.Frontend.Parser.aesopTactic
    |>.insert `Aesop.Frontend.Parser.aesopTactic?
    |>.insert `Aesop.Frontend.saturate
    |>.insert `Aesop.Frontend.saturate?
    |>.insert `Aesop.Frontend.tacticForward____
    |>.insert `Aesop.Frontend.tacticForward?____
    |>.insert `Aesop.Frontend.Parser.«tactic_clause(Add_)»
    |>.insert `Aesop.Frontend.Parser.«tactic_clause(Config:=_)»
    |>.insert `Aesop.Frontend.Parser.«tactic_clause(Simp_config:=_)»
    -- Mathlib evaluators & admit-tactics
    |>.insert `Mathlib.Meta.eval_expr
    |>.insert `Mathlib.Tactic.Sat.termFrom_lrat___
    |>.insert `Real.«tacticPi_lower_bound[_,,]»
    |>.insert `Real.«tacticPi_upper_bound[_,,]»
    |>.insert `Mathlib.Tactic.successIfFailWithMsg
    |>.insert `Mathlib.Tactic.Hint.hintStx
    |>.insert `Mathlib.Tactic.ExtractGoal.extractGoal
    -- Plausible
    |>.insert `plausibleSyntax
    -- ProofWidgets
    |>.insert `ProofWidgets.withPanelWidgetsTacticStx
    |>.insert `ProofWidgets.«termMk_rpc_widget%_»
    -- LeanSearchClient (compile-time HTTP/curl queries)
    |>.insert `LeanSearchClient.leansearch_search_term
    |>.insert `LeanSearchClient.leansearch_search_tactic
    |>.insert `LeanSearchClient.statesearch_search_tactic
    |>.insert `LeanSearchClient.search_term
    |>.insert `LeanSearchClient.search_tactic
    |>.insert `LeanSearchClient.loogle_term
    |>.insert `LeanSearchClient.loogle_tactic
    |>.insert `LeanSearchClient.just_loogle_tactic
    -- Lake DSL
    |>.insert `Lake.DSL.runIO
    |>.insert `Lake.DSL.evalVer
    |>.insert `Lake.DSL.verLit

private def readModDataAll (modName : Name) : IO (ModuleData × Array ModuleData × Array CompactedRegion) := do
  let mFile ← Lean.findOLean modName
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {modName} does not exist"
  let (mainData, mainReg) ← Lean.readModuleData mFile
  if !mainData.isModule then
    let mut allParts := #[mainData]
    let mut allRegs := #[mainReg]
    let irFile := mFile.withExtension "ir"
    if (← irFile.pathExists) then
      let (irData, irReg) ← Lean.readModuleData irFile
      allParts := allParts.push irData
      allRegs := allRegs.push irReg
    return (mainData, allParts, allRegs)
  let sFile := OLeanLevel.server.adjustFileName mFile
  let pFile := OLeanLevel.private.adjustFileName mFile
  let parts ← Lean.readModuleDataParts #[mFile, sFile, pFile]
  let mut allParts := parts.map (·.1)
  let mut allRegs := parts.map (·.2)
  let irFile := mFile.withExtension "ir"
  if (← irFile.pathExists) then
    let (irData, irReg) ← Lean.readModuleData irFile
    allParts := allParts.push irData
    allRegs := allRegs.push irReg
  match parts[2]? with
  | some (privData, _) => return (privData, allParts, allRegs)
  | none => throw <| IO.userError s!"missing .olean.private part for module {modName}"

private structure PreCheckState where
  visited : NameSet := {}
  errors : Array String := #[]
  keptRegions : Array CompactedRegion := #[]

private def metaExtName : Name :=
  (Name.mkNum `_private.Lean.Compiler.MetaAttr 0) ++ `Lean.metaExt

private def declMetaExtName : Name :=
  (Name.mkNum `_private.Lean.Compiler.MetaAttr 0) ++ `Lean.declMetaExt

-- Closed POSITIVE WHITELIST of verified 100% passive Lean v4.32.2 core persistent extensions
-- (95 registered extensions verified at startup; ZERO evalConst/evalExpr/IO/FFI/RPC/widgets/passes).
private def allowedUntrustedCoreExts : Array Name := #[
  -- Compiler LCNF / IR / Codegen passive metadata (20)
  `Lean.Compiler.LCNF.UnreachableBranches.functionSummariesExt,
  `Lean.Compiler.LCNF.baseExt,
  `Lean.Compiler.LCNF.impureSigExt,
  `Lean.Compiler.LCNF.monoExt,
  `Lean.Compiler.LCNF.monoTypeExt,
  `Lean.Compiler.LCNF.postponedCompileDeclsExt,
  `Lean.Compiler.LCNF.specExtension,
  `Lean.Compiler.inlineAttrs,
  `Lean.Compiler.nospecializeAttr,
  `Lean.Compiler.specializeAttr,
  `Lean.Compiler.weakSpecializeAttr,
  `Lean.IR.UnboxResult.unboxAttr,
  `Lean.IR.declMapExt,
  `Lean.neverExtractAttr,
  (Name.mkNum `_private.Lean.Compiler.LCNF.MonoTypes 0) ++ `Lean.Compiler.LCNF.trivialStructureInfoExt,
  (Name.mkNum `_private.Lean.Compiler.LCNF.Specialize 0) ++ `Lean.Compiler.LCNF.Specialize.specCacheExt,
  (Name.mkNum `_private.Lean.Compiler.LCNF.ToImpureType 0) ++ `Lean.Compiler.LCNF.ctorLayoutExt,
  (Name.mkNum `_private.Lean.Compiler.LCNF.ToImpureType 0) ++ `Lean.Compiler.LCNF.impureTrivialStructureInfoExt,
  (Name.mkNum `_private.Lean.Compiler.LCNF.ToImpureType 0) ++ `Lean.Compiler.LCNF.impureTypeExt,
  (Name.mkNum `_private.Lean.Compiler.ModPkgExt 0) ++ `Lean.modPkgExt,
  -- Kernel / structure / inductive / recursion / equation passive metadata (25)
  `Lean.Elab.PartialFixpoint.eqnInfoExt,
  `Lean.Elab.Structural.eqnInfoExt,
  `Lean.Elab.Term.elabAsElim,
  `Lean.Elab.Term.elabWithoutExpectedTypeAttr,
  `Lean.Elab.WF.eqnInfoExt,
  `Lean.aliasExtension,
  `Lean.auxParentProjInfoExt,
  `Lean.auxRecExt,
  `Lean.backwardDefeqAttr,
  `Lean.classExtension,
  `Lean.defeqAttr,
  `Lean.matchPatternAttr,
  `Lean.noConfusionExt,
  `Lean.noncomputableExt,
  `Lean.projectionFnInfoExt,
  `Lean.protectedExt,
  (Name.mkNum `_private.Lean.AuxRecursor 0) ++ `Lean.sparseCasesOnExt,
  (Name.mkNum `_private.Lean.Meta.Constructions.SparseCasesOn 0) ++ `Lean.Meta.sparseCasesOnInfoExt,
  (Name.mkNum `_private.Lean.Namespace 0) ++ `Lean.namespacesExt,
  (Name.mkNum `_private.Lean.OriginalConstKind 0) ++ `Lean.privateConstKindsExt,
  (Name.mkNum `_private.Lean.Structure 0) ++ `Lean.structureExt,
  (Name.mkNum `_private.Lean.Util.CollectAxioms 0) ++ `Lean.exportedAxiomsExt,
  `recExt,
  `reducibilityCore,
  `reducibilityExtra,
  -- Pure-math proof / typeclass / simp / coercion / relation / grind passive databases (30)
  `Lean.Meta.Ext.extExtension,
  `Lean.Meta.Grind.grindExt,
  `Lean.Meta.Grind.normExt,
  `Lean.Meta.Match.Extension.extension,
  `Lean.Meta.Monotonicity.monotoneExt,
  `Lean.Meta.NormCast.normCastExt.down,
  `Lean.Meta.NormCast.normCastExt.squash,
  `Lean.Meta.NormCast.normCastExt.up,
  `Lean.Meta.NormCast.pushCastExt,
  `Lean.Meta.Rfl.reflExt,
  `Lean.Meta.Symm.symmExt,
  `Lean.Meta.coeDeclAttr,
  `Lean.Meta.coeExt,
  `Lean.Meta.completionBlackListExt,
  `Lean.Meta.congrExtension,
  `Lean.Meta.congrKindsExt,
  `Lean.Meta.customEliminatorExt,
  `Lean.Meta.defaultInstanceExtension,
  `Lean.Meta.eqnOptionsExt,
  `Lean.Meta.funIndInfoExt,
  `Lean.Meta.instanceExtension,
  `Lean.Meta.matcherLikeExt,
  `Lean.Meta.recursorAttribute,
  `Lean.Meta.simpExtension,
  `Lean.Meta.unificationHintExtension,
  (Name.mkNum `_private.Lean.Meta.MethodSpecs 0) ++ `Lean.methodSpecsAttr,
  (Name.mkNum `_private.Lean.Meta.MethodSpecs 0) ++ `Lean.methodSpecsSimpExtension,
  (Name.mkNum `_private.Lean.Meta.Tactic.Grind.EMatchTheorem 0) ++ `Lean.Meta.Grind.symbolPrioExt,
  (Name.mkNum `_private.Lean.Elab.Tactic.Grind.Annotated 0) ++ `Lean.Elab.Tactic.Grind.grindAnnotatedExt,
  `bool_to_prop,
  -- Passive docs / source ranges / deprecation / PP flags / module uses / indexes (20)
  `Lean.Elab.Command.assertExistsExt,
  `Lean.Elab.deprecatedArgExt,
  `Lean.Elab.deprecatedSyntaxExt,
  `Lean.Linter.deprecatedAttr,
  `Lean.Linter.lintLogExt,
  `Lean.Parser.Term.Doc.recommendedSpellingByNameExt,
  `Lean.Parser.Term.Doc.recommendedSpellingExt,
  `Lean.declRangeExt,
  `Lean.deprecatedModuleExt,
  `Lean.docStringExt,
  `Lean.indirectModUseExt,
  `Lean.ppNoDotAttr,
  `Lean.ppUsingAnonymousConstructorAttr,
  (Name.mkNum `_private.Lean.DocString.Extension 0) ++ `Lean.inheritDocStringExt,
  (Name.mkNum `_private.Lean.DocString.Extension 0) ++ `Lean.moduleDocExt,
  (Name.mkNum `_private.Lean.ExtraModUses 0) ++ `Lean.extraModUses,
  (Name.mkNum `_private.Lean.ExtraModUses 0) ++ `Lean.isExtraRevModUseExt,
  `envLinterSnapshotExt,
  `sineQueNon,
  `symbolFrequency
]

-- Closed POSITIVE WHITELIST of verified 100% passive Batteries/Mathlib pure-math data extensions (12).
-- Deliberately EXCLUDES all Aesop rule sets (`default`, `builtin`, `Bound`, `Continuous`, `Measurable`, ...),
-- all `Simps.*` (`Simps.notationClassAttr`, `Simps.structureExt`, `simpsAttr`),
-- `ProofWidgets.exprPresenters`, `Mathlib.Tactic.GCongr.forwardExt`,
-- `NormNum`/`Positivity`/`Polynomial`/`TacticAnalysis`, and Batteries linters/code actions.
private def allowedUntrustedExternalExts : Array Name := #[
  `Batteries.Tactic.Alias.aliasExt,
  `Batteries.Tactic.Lint.nolintAttr,
  `Batteries.Tactic.transExt,
  `Mathlib.Meta.FunProp.funPropDeclsExt,
  `Mathlib.Meta.FunProp.lambdaTheoremsExt,
  `Mathlib.Meta.FunProp.functionTheoremsExt,
  `Mathlib.Meta.FunProp.transitionTheoremsExt,
  `Mathlib.Meta.FunProp.morTheoremsExt,
  `Mathlib.Tactic.GCongr.gcongrExt,
  `Mathlib.Tactic.ToAdditive.translations,
  `Mathlib.Tactic.ToDual.translations,
  `mono
]

private def allowedUntrustedPassiveExtSet : NameSet :=
  (allowedUntrustedCoreExts ++ allowedUntrustedExternalExts).foldl (fun s n => s.insert n) {}

private def auditedUntrustedCoreExts : Array Name := #[
  ``Lean.Parser.parserExtension,
  ``Lean.Elab.macroAttribute,
  ``Lean.PrettyPrinter.Delaborator.appUnexpanderAttribute,
  metaExtName,
  declMetaExtName
]

private def checkAllowedCoreExtsRegistered : IO Unit := do
  let exts ← Lean.persistentEnvExtensionsRef.get
  let regSet : NameSet := exts.foldl (fun s e => s.insert e.name) {}
  for extName in allowedUntrustedCoreExts ++ auditedUntrustedCoreExts do
    if !regSet.contains extName then
      IO.eprintln s!"Stage1Audit internal error: unregistered allowedUntrustedCoreExts entry '{extName}'"
      IO.Process.exit 2

private partial def getCodomainHead (e : Expr) : Expr :=
  match e.consumeMData with
  | .forallE _ _ b _ => getCodomainHead b
  | .letE _ _ _ b _ => getCodomainHead b
  | e' => e'.getAppFn.consumeMData

private def isRawParserCodomain (ty : Expr) : Bool :=
  match getCodomainHead ty with
  | .const fnName _ =>
    fnName == ``Lean.Parser.Parser ||
    fnName == ``Lean.Parser.TrailingParser ||
    fnName == ``Lean.Parser.ParserFn ||
    fnName == ``Lean.Parser.Category
  | _ => false

private def isParserDescrCodomain (ty : Expr) : Bool :=
  match getCodomainHead ty with
  | .const fnName _ =>
    fnName == ``Lean.ParserDescr ||
    fnName == ``Lean.TrailingParserDescr
  | _ => false

private def isStrictParserDescrType (ty : Expr) : Bool :=
  match ty.consumeMData with
  | .const fnName [] =>
    fnName == ``Lean.ParserDescr ||
    fnName == ``Lean.TrailingParserDescr
  | _ => false

private def evalStrLitExpr? (e : Expr) : Option String :=
  match e.consumeMData with
  | .lit (.strVal s) => some s
  | _ => none

private def evalBoolExpr? (e : Expr) : Option Bool :=
  match e.consumeMData with
  | .const ``Bool.true [] => some true
  | .const ``Bool.false [] => some false
  | _ => none

private partial def evalNatExpr? (e : Expr) : Option Nat :=
  let e := e.consumeMData
  match e with
  | .lit (.natVal n) => some n
  | .const ``Nat.zero [] => some 0
  | .app f a =>
    match f.consumeMData with
    | .const ``Nat.succ [] => (· + 1) <$> evalNatExpr? a
    | _ =>
      let fn := e.getAppFn.consumeMData
      let args := e.getAppArgs
      match fn with
      | .const c [.zero] =>
        if c == ``OfNat.ofNat && args.size == 3 && args[0]!.consumeMData == .const ``Nat [] then
          match args[1]!.consumeMData with
          | .lit (.natVal n) =>
            let inst := args[2]!.consumeMData
            let instFn := inst.getAppFn.consumeMData
            let instArgs := inst.getAppArgs
            if instFn == .const ``instOfNatNat [] && instArgs.size == 1 then
              match instArgs[0]!.consumeMData with
              | .lit (.natVal m) => if m == n then some n else none
              | _ => none
            else none
          | _ => none
        else none
      | _ => none
  | _ => none

private def evalMkStrArgs? (args : Array Expr) : Option Name :=
  args.foldlM (init := Name.anonymous) fun acc a => do
    let s ← evalStrLitExpr? a
    return Name.str acc s

private partial def unwrapAppAux (cur : Expr) (revArgs : Array Expr) : Expr × Array Expr :=
  match cur.consumeMData with
  | .app f a => unwrapAppAux f (revArgs.push a)
  | fn => (fn, revArgs.reverse)

private def unwrapApp (e : Expr) : Expr × Array Expr :=
  unwrapAppAux e #[]

private partial def evalNameExpr? (e : Expr) : Option Name :=
  let (fn, args) := unwrapApp e
  match fn with
  | .const c [] =>
    if c == ``Lean.Name.anonymous && args.isEmpty then
      some Name.anonymous
    else if (c == ``Lean.Name.str || c == ``Lean.Name.mkStr) && args.size == 2 then do
      let p ← evalNameExpr? args[0]!
      let s ← evalStrLitExpr? args[1]!
      return Name.str p s
    else if (c == ``Lean.Name.num || c == ``Lean.Name.mkNum) && args.size == 2 then do
      let p ← evalNameExpr? args[0]!
      let n ← evalNatExpr? args[1]!
      return Name.num p n
    else if (c == ``Lean.Name.mkSimple || c == ``Lean.Name.mkStr1) && args.size == 1 then
      evalMkStrArgs? args
    else if c == ``Lean.Name.mkStr2 && args.size == 2 then evalMkStrArgs? args
    else if c == ``Lean.Name.mkStr3 && args.size == 3 then evalMkStrArgs? args
    else if c == ``Lean.Name.mkStr4 && args.size == 4 then evalMkStrArgs? args
    else if c == ``Lean.Name.mkStr5 && args.size == 5 then evalMkStrArgs? args
    else if c == ``Lean.Name.mkStr6 && args.size == 6 then evalMkStrArgs? args
    else if c == ``Lean.Name.mkStr7 && args.size == 7 then evalMkStrArgs? args
    else if c == ``Lean.Name.mkStr8 && args.size == 8 then evalMkStrArgs? args
    else
      none
  | _ => none

-- Returns `some hasAtom` iff `e` is a valid pure-term-notation `ParserDescr` body,
-- where `hasAtom = true` iff at least one verified symbolic atom is present.
private partial def isSafeTermNotationBodyExpr (tokTable : TokenTable) (e : Expr) : Option Bool :=
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  match fn with
  | .const c [] =>
    if c == ``Lean.ParserDescr.binary && args.size == 3 then
      if evalNameExpr? args[0]! == some `andthen then
        match isSafeTermNotationBodyExpr tokTable args[1]!, isSafeTermNotationBodyExpr tokTable args[2]! with
        | some h1, some h2 => some (h1 || h2)
        | _, _ => none
      else none
    else if c == ``Lean.ParserDescr.symbol && args.size == 1 then
      match evalStrLitExpr? args[0]! with
      | some s => if isSafeNotationAtom tokTable s then some true else none
      | none => none
    else if c == ``Lean.ParserDescr.unicodeSymbol && args.size == 3 then
      match evalStrLitExpr? args[0]!, evalStrLitExpr? args[1]!, evalBoolExpr? args[2]! with
      | some s1, some s2, some _ =>
        if isSafeNotationAtom tokTable s1 && isSafeNotationAtom tokTable s2 then some true else none
      | _, _, _ => none
    else if c == ``Lean.ParserDescr.cat && args.size == 2 then
      if evalNameExpr? args[0]! == some `term && (evalNatExpr? args[1]!).isSome then
        some false
      else none
    else
      none
  | _ => none

private def isSafeTermNotationParserDescrExpr (tokTable : TokenTable) (e : Expr) : Option Name :=
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  match fn with
  | .const c [] =>
    if c == ``Lean.ParserDescr.node && args.size == 3 then
      match evalNameExpr? args[0]!, evalNatExpr? args[1]! with
      | some kind, some _ =>
        if !kind.isAnonymous && !forbiddenNotationKinds.contains kind &&
           !forbiddenAstKinds.contains kind &&
           isSafeTermNotationBodyExpr tokTable args[2]! == some true then
          some kind
        else none
      | _, _ => none
    else if c == ``Lean.ParserDescr.trailingNode && args.size == 4 then
      match evalNameExpr? args[0]!, evalNatExpr? args[1]!, evalNatExpr? args[2]! with
      | some kind, some _, some _ =>
        if !kind.isAnonymous && !forbiddenNotationKinds.contains kind &&
           !forbiddenAstKinds.contains kind &&
           isSafeTermNotationBodyExpr tokTable args[3]! == some true then
          some kind
        else none
      | _, _, _ => none
    else
      none
  | _ => none

-- Closed constant whitelists for Lean compiler-generated notation macros, unexpanders,
-- and `autoParam` `Lean.Syntax` constants in untrusted `.olean`s.
private def commonQuotSyntaxConsts : NameSet :=
  ({} : NameSet)
    |>.insert ``Applicative.toPure
    |>.insert ``Array
    |>.insert ``Array.empty
    |>.insert ``Array.emptyWithCapacity
    |>.insert ``Array.mk
    |>.insert ``Array.mkArray0 |>.insert ``Array.mkArray1 |>.insert ``Array.mkArray2
    |>.insert ``Array.mkArray3 |>.insert ``Array.mkArray4 |>.insert ``Array.mkArray5
    |>.insert ``Array.mkArray6 |>.insert ``Array.mkArray7 |>.insert ``Array.mkArray8
    |>.insert ``Array.push
    |>.insert ``Bind.bind
    |>.insert ``Bool |>.insert ``Bool.and |>.insert ``Bool.false |>.insert ``Bool.not
    |>.insert ``Bool.or |>.insert ``Bool.true
    |>.insert ``EStateM |>.insert ``EStateM.instMonad
    |>.insert ``EStateM.instMonadExceptOfOfBacktrackable |>.insert ``EStateM.nonBacktrackable
    |>.insert ``Eq
    |>.insert ``Lean.MacroScope
    |>.insert ``Lean.MonadQuotation.getContext
    |>.insert ``Lean.MonadQuotation.getCurrMacroScope
    |>.insert ``Lean.MonadQuotation.toMonadRef
    |>.insert ``Lean.MonadRef.mkInfoFromRefPos
    |>.insert ``Lean.Name |>.insert ``Lean.Name.anonymous
    |>.insert ``Lean.Name.mkNum |>.insert ``Lean.Name.mkSimple |>.insert ``Lean.Name.mkStr
    |>.insert ``Lean.Name.mkStr1 |>.insert ``Lean.Name.mkStr2 |>.insert ``Lean.Name.mkStr3
    |>.insert ``Lean.Name.mkStr4 |>.insert ``Lean.Name.mkStr5 |>.insert ``Lean.Name.mkStr6
    |>.insert ``Lean.Name.mkStr7 |>.insert ``Lean.Name.mkStr8
    |>.insert ``Lean.Name.num |>.insert ``Lean.Name.str
    |>.insert ``Lean.SourceInfo |>.insert ``Lean.SourceInfo.none |>.insert ``Lean.SourceInfo.synthetic
    |>.insert ``Lean.Syntax |>.insert ``Lean.Syntax.atom |>.insert ``Lean.Syntax.getArg
    |>.insert ``Lean.Syntax.isOfKind |>.insert ``Lean.Syntax.missing
    |>.insert ``Lean.Syntax.node |>.insert ``Lean.Syntax.node1 |>.insert ``Lean.Syntax.node2
    |>.insert ``Lean.Syntax.node3 |>.insert ``Lean.Syntax.node4 |>.insert ``Lean.Syntax.node5
    |>.insert ``Lean.Syntax.node6 |>.insert ``Lean.Syntax.node7 |>.insert ``Lean.Syntax.node8
    |>.insert ``Lean.SyntaxNodeKind
    |>.insert ``Lean.TSyntax |>.insert ``Lean.TSyntax.mk |>.insert ``Lean.TSyntax.raw
    |>.insert ``List |>.insert ``List.cons |>.insert ``List.nil |>.insert ``List.toArray
    |>.insert ``Monad.toBind |>.insert ``MonadExcept.throw
    |>.insert ``Nat |>.insert ``Nat.succ |>.insert ``Nat.zero |>.insert ``OfNat.ofNat
    |>.insert ``PUnit |>.insert ``PUnit.unit |>.insert ``Pure.pure
    |>.insert ``ReaderT.instApplicativeOfMonad |>.insert ``ReaderT.instMonad |>.insert ``ReaderT.instMonadExceptOf
    |>.insert ``String |>.insert ``String.Pos.Raw.mk |>.insert ``String.toRawSubstring' |>.insert ``Substring.Raw.mk
    |>.insert ``Unit |>.insert ``Unit.unit
    |>.insert ``cond |>.insert ``instDecidableEqBool |>.insert ``instMonadExceptOfMonadExceptOf
    |>.insert ``instOfNatNat |>.insert ``ite

private def allowedAutoMacroConsts : NameSet :=
  commonQuotSyntaxConsts
    |>.insert ``Lean.Macro.Context
    |>.insert ``Lean.Macro.Exception
    |>.insert ``Lean.Macro.Exception.unsupportedSyntax
    |>.insert ``Lean.Macro.State
    |>.insert ``Lean.Macro.instMonadQuotationMacroM
    |>.insert ``Lean.Macro.instMonadRefMacroM
    |>.insert ``Lean.MacroM
    |>.insert ``Lean.Syntax.Preresolved
    |>.insert ``Lean.Syntax.Preresolved.decl
    |>.insert ``Lean.Syntax.Preresolved.namespace
    |>.insert ``Lean.Syntax.ident
    |>.insert ``Lean.addMacroScope

private def allowedAutoUnexpanderConsts : NameSet :=
  commonQuotSyntaxConsts
    |>.insert ``Lean.PrettyPrinter.UnexpandM
    |>.insert ``Lean.PrettyPrinter.instMonadQuotationUnexpandM
    |>.insert ``Lean.Syntax.isNone
    |>.insert ``Lean.Syntax.matchesIdent
    |>.insert ``Lean.Syntax.matchesLit
    |>.insert ``Lean.Syntax.matchesNull
    |>.insert ``Lean.withRef

private def allowedAutoParamSyntaxConsts : NameSet :=
  ({} : NameSet)
    |>.insert ``Array |>.insert ``Array.empty |>.insert ``Array.emptyWithCapacity |>.insert ``Array.mk
    |>.insert ``Array.mkArray0 |>.insert ``Array.mkArray1 |>.insert ``Array.mkArray2
    |>.insert ``Array.mkArray3 |>.insert ``Array.mkArray4 |>.insert ``Array.mkArray5
    |>.insert ``Array.mkArray6 |>.insert ``Array.mkArray7 |>.insert ``Array.mkArray8
    |>.insert ``Array.push
    |>.insert ``Bool |>.insert ``Bool.false |>.insert ``Bool.true
    |>.insert ``Lean.Name |>.insert ``Lean.Name.anonymous
    |>.insert ``Lean.Name.mkNum |>.insert ``Lean.Name.mkSimple |>.insert ``Lean.Name.mkStr
    |>.insert ``Lean.Name.mkStr1 |>.insert ``Lean.Name.mkStr2 |>.insert ``Lean.Name.mkStr3
    |>.insert ``Lean.Name.mkStr4 |>.insert ``Lean.Name.mkStr5 |>.insert ``Lean.Name.mkStr6
    |>.insert ``Lean.Name.mkStr7 |>.insert ``Lean.Name.mkStr8
    |>.insert ``Lean.Name.num |>.insert ``Lean.Name.str
    |>.insert ``Lean.SourceInfo |>.insert ``Lean.SourceInfo.none |>.insert ``Lean.SourceInfo.synthetic
    |>.insert ``Lean.Syntax |>.insert ``Lean.Syntax.Preresolved
    |>.insert ``Lean.Syntax.Preresolved.decl |>.insert ``Lean.Syntax.Preresolved.namespace
    |>.insert ``Lean.Syntax.atom |>.insert ``Lean.Syntax.ident |>.insert ``Lean.Syntax.missing
    |>.insert ``Lean.Syntax.node |>.insert ``Lean.Syntax.node1 |>.insert ``Lean.Syntax.node2
    |>.insert ``Lean.Syntax.node3 |>.insert ``Lean.Syntax.node4 |>.insert ``Lean.Syntax.node5
    |>.insert ``Lean.Syntax.node6 |>.insert ``Lean.Syntax.node7 |>.insert ``Lean.Syntax.node8
    |>.insert ``Lean.mkAtom |>.insert ``Lean.mkIdent
    |>.insert ``List |>.insert ``List.cons |>.insert ``List.nil |>.insert ``List.toArray
    |>.insert ``Nat |>.insert ``Nat.succ |>.insert ``Nat.zero |>.insert ``OfNat.ofNat
    |>.insert ``String |>.insert ``String.Pos.Raw.mk |>.insert ``String.toRawSubstring |>.insert ``String.toRawSubstring' |>.insert ``Substring.Raw.mk
    |>.insert ``instOfNatNat

private def forbiddenMacroQuotedKinds : NameSet :=
  forbiddenAstKinds
    |>.insert ``Lean.Parser.Command.set_option
    |>.insert ``Lean.Parser.Term.set_option
    |>.insert ``Lean.Parser.Tactic.set_option
    |>.insert `Lean.Parser.Tactic.Grind.setOption
    |>.insert ``Lean.Parser.Term.byTactic
    |>.insert ``Lean.Parser.Term.byTactic'
    |>.insert ``Lean.Parser.Term.do
    |>.insert ``Lean.Parser.Term.doSeq
    |>.insert ``Lean.Parser.Term.doSeqIndent
    |>.insert ``Lean.Parser.Term.doSeqBracketed
    |>.insert ``Lean.Parser.Tactic.tacticSeq
    |>.insert interpolatedStrKind
    |>.insert interpolatedStrLitKind

private def forbiddenAutoParamKinds : NameSet :=
  forbiddenAstKinds
    |>.insert `Mathlib.Tactic.linarithArgsRest
    |>.insert ``Lean.Parser.Command.set_option
    |>.insert ``Lean.Parser.Term.set_option
    |>.insert ``Lean.Parser.Tactic.set_option
    |>.insert `Lean.Parser.Tactic.Grind.setOption
    |>.insert ``Lean.Parser.Term.do
    |>.insert interpolatedStrKind
    |>.insert interpolatedStrLitKind

private def isNameCtor (c : Name) : Bool :=
  c == ``Lean.Name.str || c == ``Lean.Name.mkStr ||
  c == ``Lean.Name.num || c == ``Lean.Name.mkNum ||
  c == ``Lean.Name.mkSimple ||
  c == ``Lean.Name.mkStr1 || c == ``Lean.Name.mkStr2 || c == ``Lean.Name.mkStr3 ||
  c == ``Lean.Name.mkStr4 || c == ``Lean.Name.mkStr5 || c == ``Lean.Name.mkStr6 ||
  c == ``Lean.Name.mkStr7 || c == ``Lean.Name.mkStr8

private def isSyntaxNodeCtor (c : Name) : Bool :=
  c == ``Lean.Syntax.node || c == ``Lean.Syntax.node1 || c == ``Lean.Syntax.node2 ||
  c == ``Lean.Syntax.node3 || c == ``Lean.Syntax.node4 || c == ``Lean.Syntax.node5 ||
  c == ``Lean.Syntax.node6 || c == ``Lean.Syntax.node7 || c == ``Lean.Syntax.node8

private partial def exprHasBinder (e : Expr) : Bool :=
  match e.consumeMData with
  | .lam _ _ _ _ | .forallE _ _ _ _ | .letE _ _ _ _ _ | .bvar _ => true
  | .app f a => exprHasBinder f || exprHasBinder a
  | .proj _ _ s => exprHasBinder s
  | _ => false

private partial def exprHasBadLiteral (forbKinds : NameSet) (forbidNativeWord : Bool) (e : Expr) : Option String :=
  let e := e.consumeMData
  match evalNameExpr? e with
  | some n =>
    if forbKinds.contains n || hasSubstr n.toString "SudoSet_option" then
      some s!"forbidden quoted kind '{n}'"
    else if isForbiddenOptionName n then
      some s!"forbidden option '{n}'"
    else if let some hit := checkNameForbidden n then
      some s!"forbidden name '{hit}' in '{n}'"
    else if forbidNativeWord && (n == `native || n == `config || n == `oracle || n == `preprocessors) then
      some s!"forbidden '{n}' config in autoParam"
    else
      none
  | none =>
    let (fn, args) := unwrapApp e
    if !args.isEmpty || fn.isConst then
      let headErr? : Option String :=
        match fn with
        | .const c _ =>
          if isNameCtor c then
            some s!"non-literal Name construction via '{c}'"
          else if isSyntaxNodeCtor c then
            if args.size >= 2 && (evalNameExpr? args[1]!).isSome then none
            else some s!"non-literal Syntax node kind in '{c}'"
          else if c == ``Lean.Syntax.ident then
            let valOk :=
              args.size == 4 &&
              let v := args[2]!.consumeMData
              (evalNameExpr? v).isSome ||
              (let (vfn, vargs) := unwrapApp v
               vfn == .const ``Lean.addMacroScope [] && vargs.size == 3 && (evalNameExpr? vargs[1]!).isSome)
            if valOk then none
            else some "non-literal Syntax.ident name"
          else if c == ``Lean.mkIdent then
            if args.size == 1 && (evalNameExpr? args[0]!).isSome then none
            else some "non-literal Name in 'Lean.mkIdent'"
          else if c == ``Lean.addMacroScope then
            if args.size == 3 && (evalNameExpr? args[1]!).isSome then none
            else some "non-literal Name in 'Lean.addMacroScope'"
          else if c == ``Lean.Syntax.Preresolved.decl then
            if args.size == 2 && (evalNameExpr? args[0]!).isSome then none
            else some "non-literal Name in 'Lean.Syntax.Preresolved.decl'"
          else if c == ``Lean.Syntax.Preresolved.namespace then
            if args.size == 1 && (evalNameExpr? args[0]!).isSome then none
            else some "non-literal Name in 'Lean.Syntax.Preresolved.namespace'"
          else none
        | _ => none
      if headErr?.isSome then headErr?
      else
        let fnErr? := if fn.isConst then none else exprHasBadLiteral forbKinds forbidNativeWord fn
        fnErr?.orElse fun _ => args.findSome? (exprHasBadLiteral forbKinds forbidNativeWord)
    else
      match e with
      | .lit (.strVal s) =>
        let t := s.trimAscii.toString
        if forbiddenTokens.contains t || hasForbiddenIdentWord s then
          some s!"forbidden token in string literal {repr s}"
        else if forbidNativeWord && (t == "native" || t == "config" || t == "oracle" || t == "preprocessors") then
          some s!"forbidden config token {repr s} in autoParam"
        else none
      | .lam _ t b _ =>
        (exprHasBadLiteral forbKinds forbidNativeWord t).orElse fun _ =>
          exprHasBadLiteral forbKinds forbidNativeWord b
      | .forallE _ t b _ =>
        (exprHasBadLiteral forbKinds forbidNativeWord t).orElse fun _ =>
          exprHasBadLiteral forbKinds forbidNativeWord b
      | .letE _ t v b _ =>
        (exprHasBadLiteral forbKinds forbidNativeWord t).orElse fun _ =>
          (exprHasBadLiteral forbKinds forbidNativeWord v).orElse fun _ =>
            exprHasBadLiteral forbKinds forbidNativeWord b
      | .proj _ _ s => exprHasBadLiteral forbKinds forbidNativeWord s
      | _ => none

private partial def collectConstructedNodeKinds (e : Expr) (acc : NameSet) : Except String NameSet := do
  let e := e.consumeMData
  let (fn, args) := unwrapApp e
  if !args.isEmpty || fn.isConst then
    let acc ←
      match fn with
      | .const c _ =>
        if isSyntaxNodeCtor c then
          if args.size >= 2 then
            match evalNameExpr? args[1]! with
            | some k => pure (acc.insert k)
            | none => throw s!"non-literal Syntax node kind in '{c}'"
          else
            throw s!"non-literal Syntax node kind in '{c}'"
        else pure acc
      | _ => pure acc
    let acc ← if fn.isConst then pure acc else collectConstructedNodeKinds fn acc
    args.foldlM (fun a arg => collectConstructedNodeKinds arg a) acc
  else
    match e with
    | .lam _ t b _ => collectConstructedNodeKinds b (← collectConstructedNodeKinds t acc)
    | .forallE _ t b _ => collectConstructedNodeKinds b (← collectConstructedNodeKinds t acc)
    | .letE _ t v b _ => collectConstructedNodeKinds b (← collectConstructedNodeKinds v (← collectConstructedNodeKinds t acc))
    | .proj _ _ s => collectConstructedNodeKinds s acc
    | _ => pure acc

private partial def extractPreresolvedDecls (e : Expr) (acc : Array Name) : Array Name :=
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  match fn with
  | .const c _ =>
    if c == ``Lean.Syntax.Preresolved.decl && args.size == 2 then
      match evalNameExpr? args[0]! with
      | some decl => acc.push decl
      | none => acc
    else args.foldl (fun a arg => extractPreresolvedDecls arg a) acc
  | _ =>
    match e with
    | .app f a => extractPreresolvedDecls a (extractPreresolvedDecls f acc)
    | _ => acc

private def extractHeadIdentTarget? (stxExpr : Expr) : Option Name :=
  let stxExpr := stxExpr.consumeMData
  let fn := stxExpr.getAppFn.consumeMData
  let args := stxExpr.getAppArgs
  match fn with
  | .const c [] =>
    if c == ``Lean.Syntax.ident && args.size == 4 then
      let decls := extractPreresolvedDecls args[3]! #[]
      if decls.size == 1 then some decls[0]! else none
    else if c == ``Lean.Syntax.node2 && args.size == 4 &&
            evalNameExpr? args[1]! == some ``Lean.Parser.Term.app then
      let head := args[2]!.consumeMData
      let hfn := head.getAppFn.consumeMData
      let hargs := head.getAppArgs
      if hfn == .const ``Lean.Syntax.ident [] && hargs.size == 4 then
        let decls := extractPreresolvedDecls hargs[3]! #[]
        if decls.size == 1 then some decls[0]! else none
      else none
    else none
  | _ => none

private partial def extractMacroHeadTarget? (e : Expr) : Option Name :=
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  if fn == .const ``Lean.TSyntax.mk [] && args.size == 2 then
    extractHeadIdentTarget? args[1]!
  else
    match e with
    | .app f a => (extractMacroHeadTarget? f).orElse fun _ => extractMacroHeadTarget? a
    | .lam _ _ b _ => extractMacroHeadTarget? b
    | .letE _ _ v b _ => (extractMacroHeadTarget? v).orElse fun _ => extractMacroHeadTarget? b
    | _ => none

private partial def collectAutoParamRefs (e : Expr) (acc : NameSet) : NameSet :=
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  let acc :=
    match fn with
    | .const c _ =>
      if c == ``autoParam && args.size >= 2 then
        let tacArg := args[1]!.consumeMData
        match tacArg with
        | .const tacName _ => acc.insert tacName
        | _ =>
          match evalNameExpr? tacArg with
          | some tacName => acc.insert tacName
          | none => tacArg.getUsedConstants.foldl (·.insert ·) acc
      else acc
    | _ => acc
  match e with
  | .app f a => collectAutoParamRefs a (collectAutoParamRefs f acc)
  | .lam _ t b _ => collectAutoParamRefs b (collectAutoParamRefs t acc)
  | .forallE _ t b _ => collectAutoParamRefs b (collectAutoParamRefs t acc)
  | .letE _ t v b _ => collectAutoParamRefs b (collectAutoParamRefs v (collectAutoParamRefs t acc))
  | .proj _ _ s => collectAutoParamRefs s acc
  | _ => acc

private def isAuxTailMatching (n : Name) (marker : String) : Bool :=
  match n with | .str _ tail => tail.startsWith "_aux_" && hasSubstr tail marker | _ => false

private def isAutoParamName (n : Name) : Bool :=
  match n with
  | .str _ tail => tail.startsWith "_auto_" || tail == "_autoParam"
  | _ => false

private def isDerivedMetaDecl (safeMeta : NameSet) (n : Name) : Bool :=
  if safeMeta.contains n then true
  else
    let rec go : Name → Bool
      | .anonymous => false
      | cur@(.str p s) =>
        if safeMeta.contains cur then true
        else if s.startsWith "_closed_" || s == "_boxed" || s == "_redArg" ||
                s.startsWith "_lam_" || s.startsWith "_jp_" || s.startsWith "_at_" ||
                s.startsWith "_cstage" then go p
        else false
      | .num p _ => go p
    go n

private def mergePartConstant (existing : ConstantInfo) (incoming : ConstantInfo) : Except String ConstantInfo :=
  if existing.name != incoming.name || existing.type != incoming.type || existing.levelParams != incoming.levelParams then
    .error s!"cross-part type/levelParams mismatch for '{existing.name}'"
  else
    match existing, incoming with
    | .defnInfo d1, .defnInfo d2 =>
      if d1.value == d2.value && d1.safety == d2.safety then .ok existing
      else .error s!"cross-part defn value mismatch for '{existing.name}'"
    | .thmInfo t1, .thmInfo t2 =>
      if t1.value == t2.value then .ok existing
      else .error s!"cross-part thm value mismatch for '{existing.name}'"
    | .opaqueInfo o1, .opaqueInfo o2 =>
      if o1.value == o2.value && o1.isUnsafe == o2.isUnsafe then .ok existing
      else .error s!"cross-part opaque value mismatch for '{existing.name}'"
    | .axiomInfo a1, .axiomInfo a2 =>
      if a1.isUnsafe == a2.isUnsafe then .ok existing
      else .error s!"cross-part axiom safety mismatch for '{existing.name}'"
    | .inductInfo i1, .inductInfo i2 =>
      if i1.numParams == i2.numParams && i1.numIndices == i2.numIndices &&
         i1.all == i2.all && i1.ctors == i2.ctors && i1.isUnsafe == i2.isUnsafe then .ok existing
      else .error s!"cross-part inductive mismatch for '{existing.name}'"
    | .ctorInfo c1, .ctorInfo c2 =>
      if c1 == c2 then .ok existing
      else .error s!"cross-part ctor mismatch for '{existing.name}'"
    | .recInfo r1, .recInfo r2 =>
      if r1 == r2 then .ok existing
      else .error s!"cross-part rec mismatch for '{existing.name}'"
    | .defnInfo _, .axiomInfo ax =>
      if !ax.isUnsafe then .ok existing
      else .error s!"cross-part unsafe axiom stub for '{existing.name}'"
    | .axiomInfo ax, .defnInfo _ =>
      if !ax.isUnsafe then .ok incoming
      else .error s!"cross-part unsafe axiom stub for '{existing.name}'"
    | .thmInfo _, .axiomInfo ax =>
      if !ax.isUnsafe then .ok existing
      else .error s!"cross-part unsafe axiom stub for '{existing.name}'"
    | .axiomInfo ax, .thmInfo _ =>
      if !ax.isUnsafe then .ok incoming
      else .error s!"cross-part unsafe axiom stub for '{existing.name}'"
    | .opaqueInfo op, .axiomInfo ax =>
      if !ax.isUnsafe && !op.isUnsafe then .ok existing
      else .error s!"cross-part unsafe opaque/axiom stub for '{existing.name}'"
    | .axiomInfo ax, .opaqueInfo op =>
      if !ax.isUnsafe && !op.isUnsafe then .ok incoming
      else .error s!"cross-part unsafe opaque/axiom stub for '{existing.name}'"
    | _, _ =>
      .error s!"inconsistent multi-part constant kinds for '{existing.name}'"

private unsafe def preCheckVisit
    (isTrustedLoc : Name → IO Bool)
    (tokTable : TokenTable)
    (modName : Name) : StateRefT PreCheckState IO Unit := do
  if (← get).visited.contains modName then return
  modify fun s => { s with visited := s.visited.insert modName }
  let trusted ← isTrustedLoc modName
  if trusted then return
  let (_, allParts, regs) ← readModDataAll modName
  modify fun s => { s with keptRegions := s.keptRegions ++ regs }

  -- Pass 1A: inspect ALL parts for corruptness/unsafe/raw-parser and merge `constMap`
  -- (resolving Lean 4.32 `module` `.axiomInfo`/`.opaqueInfo` exported stubs to `.olean.private` `.defnInfo`).
  let mut constMap : Std.HashMap Name ConstantInfo := {}
  let mut autoParamRefs : NameSet := {}
  for part in allParts do
    if part.constNames.size != part.constants.size then
      modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' has corrupt .olean" }
    for cinfo in part.constants do
      if cinfo.isUnsafe then
        modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' contains unsafe declaration '{cinfo.name}'" }
      if isRawParserCodomain cinfo.type then
        modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' declares raw parser/category constant '{cinfo.name}'" }
      if cinfo.type.getUsedConstants.contains ``autoParam then
        autoParamRefs := collectAutoParamRefs cinfo.type autoParamRefs
      if let some val := cinfo.value? (allowOpaque := true) then
        if val.getUsedConstants.contains ``autoParam then
          autoParamRefs := collectAutoParamRefs val autoParamRefs
      match constMap.get? cinfo.name with
      | none => constMap := constMap.insert cinfo.name cinfo
      | some prev =>
        match mergePartConstant prev cinfo with
        | .ok merged => constMap := constMap.insert cinfo.name merged
        | .error err => modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}': {err}" }

  -- Pass 1B: build closed per-module whitelists for pure-term-notation `ParserDescr`s
  -- and safe `autoParam` `Lean.Syntax` constants.
  let mut safeTermParserDecls : NameSet := {}
  let mut safeTermParserKinds : NameSet := {}
  let mut safeAutoParamDecls : NameSet := {}
  for (_, cinfo) in constMap.toArray do
    if isParserDescrCodomain cinfo.type then
      if !isStrictParserDescrType cinfo.type then
        modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' declares non-closed ParserDescr function '{cinfo.name}'" }
      else
        match cinfo with
        | .defnInfo d =>
          if !d.levelParams.isEmpty || d.safety != .safe then
            modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' declares invalid ParserDescr definition '{cinfo.name}'" }
          else
            match isSafeTermNotationParserDescrExpr tokTable d.value with
            | some nodeKind =>
              safeTermParserDecls := safeTermParserDecls.insert cinfo.name
              safeTermParserKinds := safeTermParserKinds.insert nodeKind
            | none =>
              modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' contains disallowed non-term-notation ParserDescr '{cinfo.name}'" }
        | _ =>
          modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' declares non-definition ParserDescr '{cinfo.name}'" }
    else if getCodomainHead cinfo.type == .const ``Lean.Syntax [] then
      match cinfo with
      | .defnInfo d =>
        let constsOk := d.value.getUsedConstants.all fun c =>
          !constMap.contains c && allowedAutoParamSyntaxConsts.contains c
        let noBinders := !exprHasBinder d.value
        let litErr? := exprHasBadLiteral forbiddenAutoParamKinds (forbidNativeWord := true) d.value
        if d.levelParams.isEmpty && d.safety == .safe &&
           d.type.consumeMData == .const ``Lean.Syntax [] &&
           isAutoParamName cinfo.name && constsOk && noBinders && litErr?.isNone then
          safeAutoParamDecls := safeAutoParamDecls.insert cinfo.name
        else
          let why :=
            if !noBinders then "binders disallowed in autoParam Lean.Syntax"
            else litErr?.getD "non-whitelisted Lean.Syntax definition"
          modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' declares disallowed Lean.Syntax constant '{cinfo.name}' ({why})" }
      | _ =>
        modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' declares non-definition Lean.Syntax constant '{cinfo.name}'" }

  for tacName in autoParamRefs do
    if constMap.contains tacName && !safeAutoParamDecls.contains tacName then
      modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' uses non-whitelisted local autoParam target '{tacName}'" }

  -- Pass 2A: CLOSED POSITIVE WHITELIST on every non-empty persistent extension in `allParts`;
  -- structurally audit `parserExtension` & `macroAttribute` first, collect `appUnexpanderAttribute` / `metaExt` / `declMetaExt`.
  let mut seenMacrosByKind : Std.HashMap Name Name := {}
  let mut macroTargetsByKind : Std.HashMap Name Name := {}
  let mut verifiedMacroDecls : NameSet := {}
  let mut unexpEntries : Array KeyedDeclsAttribute.OLeanEntry := #[]
  let mut metaEntries : Array Name := #[]
  let mut declMetaEntries : Array Name := #[]

  for part in allParts do
    for (extName, entries) in part.entries do
      if entries.isEmpty then continue
      if allowedUntrustedPassiveExtSet.contains extName then
        continue
      else if extName == ``Lean.Parser.parserExtension then
        for e in entries do
          let se : ScopedEnvExtension.Entry Parser.ParserExtension.OLeanEntry := unsafeCast e
          let oe := match se with | .global oe => oe | .scoped _ oe => oe
          match oe with
          | .token tk =>
            if !isSafeNotationAtom tokTable tk then
              modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' registers unsafe parser token {repr tk}" }
          | .kind k =>
            if !safeTermParserKinds.contains k then
              modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' registers unwhitelisted syntax kind '{k}'" }
          | .category catName _ _ =>
            modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' declares syntax category '{catName}'" }
          | .parser catName declName _ =>
            if catName != `term || !safeTermParserDecls.contains declName then
              modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' registers disallowed parser '{declName}' in category '{catName}'" }
      else if extName == ``Lean.Elab.macroAttribute then
        for e in entries do
          let se : ScopedEnvExtension.Entry KeyedDeclsAttribute.OLeanEntry := unsafeCast e
          let oe := match se with | .global oe => oe | .scoped _ oe => oe
          if !safeTermParserKinds.contains oe.key then
            modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' registers macro '{oe.declName}' for non-whitelisted kind '{oe.key}'" }
          else
            match seenMacrosByKind.get? oe.key with
            | some prevDecl =>
              if prevDecl != oe.declName then
                modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' registers multiple macros ('{prevDecl}', '{oe.declName}') for kind '{oe.key}'" }
            | none =>
              seenMacrosByKind := seenMacrosByKind.insert oe.key oe.declName
              match constMap.get? oe.declName with
              | some (.defnInfo d) =>
                let badConsts := d.value.getUsedConstants.filter fun c =>
                  constMap.contains c || !allowedAutoMacroConsts.contains c
                let litErr? := exprHasBadLiteral forbiddenMacroQuotedKinds (forbidNativeWord := false) d.value
                if !d.levelParams.isEmpty || d.safety != .safe ||
                   d.type.consumeMData != .const ``Lean.Macro [] ||
                   !d.value.consumeMData.isLambda ||
                   !isAuxTailMatching oe.declName "___macroRules_" then
                  modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' registers non-auto-generated macro '{oe.declName}' for '{oe.key}'" }
                else if !badConsts.isEmpty then
                  modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' macro '{oe.declName}' references non-whitelisted constants {badConsts.extract 0 4}" }
                else if let some why := litErr? then
                  modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' macro '{oe.declName}' contains {why}" }
                else
                  verifiedMacroDecls := verifiedMacroDecls.insert oe.declName
                  if let some tgt := extractMacroHeadTarget? d.value then
                    macroTargetsByKind := macroTargetsByKind.insert oe.key tgt
              | _ =>
                modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' macro '{oe.declName}' missing or non-definition" }
      else if extName == ``Lean.PrettyPrinter.Delaborator.appUnexpanderAttribute then
        for e in entries do
          let se : ScopedEnvExtension.Entry KeyedDeclsAttribute.OLeanEntry := unsafeCast e
          let oe := match se with | .global oe => oe | .scoped _ oe => oe
          unexpEntries := unexpEntries.push oe
      else if extName == metaExtName then
        for e in entries do
          metaEntries := metaEntries.push (unsafeCast e : Name)
      else if extName == declMetaExtName then
        for e in entries do
          declMetaEntries := declMetaEntries.push (unsafeCast e : Name)
      else
        modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' contains non-whitelisted extension '{extName}'" }

  -- Pass 2B: audit `appUnexpanderAttribute` against `allowedAutoUnexpanderConsts` and exact 1-to-1 `(kind, headTarget)` coupling
  let mut seenUnexpByKind : Std.HashMap Name Name := {}
  let mut verifiedUnexpDecls : NameSet := {}
  for oe in unexpEntries do
    match constMap.get? oe.declName with
    | some (.defnInfo d) =>
      let badConsts := d.value.getUsedConstants.filter fun c =>
        constMap.contains c || !allowedAutoUnexpanderConsts.contains c
      let litErr? := exprHasBadLiteral forbiddenMacroQuotedKinds (forbidNativeWord := false) d.value
      let builtKindsRes := collectConstructedNodeKinds d.value {}
      if !d.levelParams.isEmpty || d.safety != .safe ||
         d.type.consumeMData != .const ``Lean.PrettyPrinter.Unexpander [] ||
         !d.value.consumeMData.isLambda ||
         !isAuxTailMatching oe.declName "___unexpand_" then
        modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' registers disallowed @[app_unexpander] '{oe.declName}' for '{oe.key}'" }
      else if !badConsts.isEmpty then
        modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' @[app_unexpander] '{oe.declName}' references non-whitelisted constants {badConsts.extract 0 4}" }
      else if let some why := litErr? then
        modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' @[app_unexpander] '{oe.declName}' contains {why}" }
      else
        match builtKindsRes with
        | .error why =>
          modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' @[app_unexpander] '{oe.declName}' contains {why}" }
        | .ok builtKindSet =>
          let builtKinds := builtKindSet.toArray.filter safeTermParserKinds.contains
          if builtKinds.size != 1 then
            modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' @[app_unexpander] '{oe.declName}' must construct exactly 1 whitelisted notation kind" }
          else
            let k := builtKinds[0]!
            if macroTargetsByKind.get? k != some oe.key then
              modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' @[app_unexpander] '{oe.declName}' key '{oe.key}' mismatches macro target for '{k}'" }
            else
              match seenUnexpByKind.get? k with
              | some prevDecl =>
                if prevDecl != oe.declName then
                  modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' registers multiple @[app_unexpander]s ('{prevDecl}', '{oe.declName}') for kind '{k}'" }
              | none =>
                seenUnexpByKind := seenUnexpByKind.insert k oe.declName
                verifiedUnexpDecls := verifiedUnexpDecls.insert oe.declName
    | _ =>
      modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' @[app_unexpander] '{oe.declName}' missing or non-definition" }

  -- Pass 2C: audit `metaExt` and `declMetaExt` against the closed set of verified meta declarations
  let safeMetaDecls : NameSet :=
    safeTermParserDecls.foldl (·.insert ·)
      (verifiedMacroDecls.foldl (·.insert ·)
        (verifiedUnexpDecls.foldl (·.insert ·) safeAutoParamDecls))
  for n in metaEntries do
    if !safeMetaDecls.contains n then
      modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' marks non-whitelisted declaration '{n}' as meta" }
  for n in declMetaEntries do
    if !isDerivedMetaDecl safeMetaDecls n then
      modify fun s => { s with errors := s.errors.push s!"untrusted imported module '{modName}' exports non-whitelisted meta IR declaration '{n}'" }

  for part in allParts do
    for imp in part.imports do
      preCheckVisit isTrustedLoc tokTable imp.module

private def mkIsTrustedLoc (repoRootStr : String) : IO (Name → IO Bool) := do
  let sysroot ← Lean.findSysroot
  let sysrootLibReal ← IO.FS.realPath (← Lean.getLibDir sysroot)
  let repoRoot : System.FilePath := repoRootStr
  let packagesDir := repoRoot / ".lake" / "packages"
  let packagesDirReal? ←
    if (← packagesDir.pathExists) then some <$> IO.FS.realPath packagesDir else pure none
  return fun modName => do
    let oleanPath ← Lean.findOLean modName
    let oleanReal ← IO.FS.realPath oleanPath
    return pathIsUnder oleanReal sysrootLibReal ||
      (match packagesDirReal? with
       | some pkgReal => pathIsUnder oleanReal pkgReal
       | none => false)

private unsafe def preCheckImports (isTrustedLoc : Name → IO Bool) (imports : Array Import) : IO (Except String Unit) := do
  try
    let btt ← Lean.Parser.builtinTokenTable.get
    let (_, st) ← (for imp in imports do preCheckVisit isTrustedLoc btt imp.module).run {}
    let _ := st.keptRegions.size
    if !st.errors.isEmpty then
      return .error (String.intercalate "; " st.errors.toList)
    return .ok ()
  catch ex =>
    return .error ex.toString

-- Defense-in-depth: strip ALL untrusted-module entries (both active `stateStack` and
-- `scopedEntries`) from executable `KeyedDeclsAttribute`s while preserving
-- `Lean.Parser.parserExtension` and `namespacesExt` intact for whitelisted notations like `⊠`.
private def isDeclTrusted (env : Environment) (trustedMods : NameSet) (declName : Name) : Bool :=
  match env.getModuleIdxFor? declName with
  | none => false
  | some modIdx =>
    match env.header.moduleNames[modIdx.toNat]? with
    | some modName => trustedMods.contains modName
    | none => false

private def filterKeyedAttr {γ : Type} (attr : KeyedDeclsAttribute γ)
    (trustedMods : NameSet) (env : Environment) : Environment :=
  let keep (e : KeyedDeclsAttribute.AttributeEntry γ) : Bool :=
    e.isBuiltin || isDeclTrusted env trustedMods e.declName
  let filterTable (t : KeyedDeclsAttribute.Table γ) : KeyedDeclsAttribute.Table γ :=
    t.fold (init := {}) fun acc k es =>
      let es' := es.filter keep
      if es'.isEmpty then acc else acc.insert k es'
  let filterExtState (es : KeyedDeclsAttribute.ExtensionState γ) : KeyedDeclsAttribute.ExtensionState γ :=
    let table' := filterTable es.table
    let declNames' := table'.fold (init := {}) fun s _ entries =>
      entries.foldl (init := s) fun s e => s.insert e.declName
    { es with
      table := table'
      declNames := declNames'
      newEntries := es.newEntries.filter fun oe => isDeclTrusted env trustedMods oe.declName }
  attr.ext.ext.modifyState env fun stack =>
    let stateStack' := stack.stateStack.map fun st =>
      { st with state := filterExtState st.state }
    let scopedMap' := stack.scopedEntries.map.fold (init := {}) fun acc ns arr =>
      let arr' := arr.toArray.filter keep
      if arr'.isEmpty then acc else acc.insert ns (arr'.foldl PersistentArray.push {})
    { stack with
      stateStack := stateStack'
      scopedEntries := { map := scopedMap' } }

private def sanitizeImportedEnv (isTrustedLoc : Name → IO Bool) (env : Environment) : IO Environment := do
  let mut trustedMods : NameSet := {}
  for modName in env.header.moduleNames do
    let ok ← try isTrustedLoc modName catch _ => pure false
    if ok then
      trustedMods := trustedMods.insert modName
  let env := filterKeyedAttr Lean.Elab.macroAttribute trustedMods env
  let env := filterKeyedAttr Lean.Elab.Command.commandElabAttribute trustedMods env
  let env := filterKeyedAttr Lean.Elab.Term.termElabAttribute trustedMods env
  let env := filterKeyedAttr Lean.Elab.Tactic.tacticElabAttribute trustedMods env
  let env := filterKeyedAttr Lean.PrettyPrinter.Delaborator.appUnexpanderAttribute trustedMods env
  let env := filterKeyedAttr Lean.PrettyPrinter.Delaborator.delabAttribute trustedMods env
  let env := filterKeyedAttr Lean.Elab.Do.doElemElabAttribute trustedMods env
  let env := filterKeyedAttr Lean.Elab.Do.controlInfoElemAttribute trustedMods env
  let env := filterKeyedAttr Lean.Elab.Tactic.Grind.grindTacElabAttribute trustedMods env
  let env := filterKeyedAttr Lean.Elab.Tactic.Grind.symSimprocElabAttribute trustedMods env
  let env := filterKeyedAttr Lean.Elab.Tactic.Grind.symDSimprocElabAttribute trustedMods env
  let env := filterKeyedAttr Lean.Elab.Tactic.Grind.symDischargerElabAttribute trustedMods env
  let env := filterKeyedAttr Lean.Elab.Tactic.Try.tryTacticElabAttribute trustedMods env
  return env

-- Closed Pure-Math Top-Level Command Whitelist
private def allowedLeafCommandKinds : NameSet :=
  ({} : NameSet)
    -- Declarations
    |>.insert ``Lean.Parser.Command.declaration
    |>.insert ``Lean.Parser.Command.deriving
    |>.insert ``Lean.Parser.Command.classAbbrev
    |>.insert `lemma
    |>.insert `Batteries.Tactic.Lemma.lemmaCmd
    |>.insert `Batteries.Tactic.Alias.alias
    |>.insert `Batteries.Tactic.Alias.aliasLR
    -- Scopes / options / variables / attributes
    |>.insert ``Lean.Parser.Command.section
    |>.insert ``Lean.Parser.Command.namespace
    |>.insert ``Lean.Parser.Command.end
    |>.insert ``Lean.Parser.Command.open
    |>.insert ``Lean.Parser.Command.export
    |>.insert ``Lean.Parser.Command.variable
    |>.insert ``Lean.Parser.Command.universe
    |>.insert ``Lean.Parser.Command.include
    |>.insert ``Lean.Parser.Command.omit
    |>.insert ``Lean.Parser.Command.set_option
    |>.insert ``Lean.Parser.Command.unlock_limits
    |>.insert ``Lean.Parser.Command.attribute
    -- Declarative term notations
    |>.insert ``Lean.Parser.Command.notation
    |>.insert ``Lean.Parser.Command.mixfix
    -- Docs / metadata
    |>.insert ``Lean.Parser.Command.moduleDoc
    |>.insert ``Lean.Parser.Command.addDocString
    |>.insert ``Lean.Parser.Command.recommended_spelling
    |>.insert ``Lean.Parser.Command.deprecated_module
    |>.insert ``Lean.Parser.Command.deprecatedSyntax
    -- Pure diagnostics (zero meta-exec)
    |>.insert ``Lean.Parser.Command.print
    |>.insert ``Lean.Parser.Command.printSig
    |>.insert ``Lean.Parser.Command.printAxioms
    |>.insert ``Lean.Parser.Command.printEqns
    |>.insert ``Lean.Parser.Command.printTacTags
    |>.insert ``Lean.Parser.Command.check
    |>.insert ``Lean.Parser.Command.check_failure
    |>.insert ``Lean.Parser.Command.synth
    |>.insert ``Lean.Parser.Command.«where»
    |>.insert ``Lean.Parser.Command.version
    |>.insert ``Lean.Parser.Command.importPath
    |>.insert ``Lean.Parser.Command.assertNotExists
    |>.insert ``Lean.Parser.Command.assertNotImported
    |>.insert ``Lean.Parser.Command.checkAssertions
    |>.insert ``Lean.Parser.Command.showDeprecatedModules
    |>.insert ``Lean.reduceCmd
    |>.insert ``Lean.Parser.checkTactic
    |>.insert ``Lean.Parser.checkTacticFailure
    |>.insert ``Lean.Parser.checkSimp
    |>.insert ``Lean.Parser.checkSimpFailure
    |>.insert ``Lean.Parser.discrTreeKeyCmd
    |>.insert ``Lean.Parser.discrTreeSimpKeyCmd
    |>.insert ``Lean.Parser.Tactic.normCastAddElim
    |>.insert `Lean.Parser.commandSeal__
    |>.insert `Lean.Parser.commandUnseal__
    |>.insert ``Lean.Parser.Command.eoi

private partial def stxContainsAtom (stx : Syntax) (target : String) : Bool :=
  match stx with
  | .atom _ val => val.trimAscii.toString == target
  | .node _ _ args => args.any fun c => stxContainsAtom c target
  | _ => false

private def guardMsgsMayHideError (stx : Syntax) : Bool :=
  let hasDoc := stx.getNumArgs >= 1 && !stx[0].isNone
  let docMayExpectError :=
    if hasDoc then
      let docStr := stx[0].reprint.getD ""
      hasSubstr docStr "error:" || hasSubstr docStr "error("
    else false
  let specDropsOrSubstrError :=
    if stx.getNumArgs >= 3 && !stx[2].isNone then
      (stxContainsAtom stx[2] "drop" &&
        (stxContainsAtom stx[2] "error" || stxContainsAtom stx[2] "all")) ||
      stxContainsAtom stx[2] "substring"
    else false
  docMayExpectError || specDropsOrSubstrError

private def isDeclCmdKind (k : Name) : Bool :=
  k == ``Lean.Parser.Command.declaration ||
  k == ``Lean.Parser.Command.classAbbrev ||
  k == `lemma ||
  k == `Batteries.Tactic.Lemma.lemmaCmd ||
  k == `Batteries.Tactic.Alias.alias ||
  k == `Batteries.Tactic.Alias.aliasLR

private partial def hasDisallowedGuardedCmd (inScopedIn : Bool) (forbidDecls : Bool) (stx : Syntax) : Bool :=
  let k := stx.getKind
  if k == choiceKind then
    stx.getArgs.any (hasDisallowedGuardedCmd inScopedIn forbidDecls)
  else if k == ``Lean.Parser.Command.withExporting then
    stx.getNumArgs >= 2 && hasDisallowedGuardedCmd inScopedIn forbidDecls stx[1]
  else if k == ``Lean.Parser.timeCmd then
    stx.getNumArgs == 2 && hasDisallowedGuardedCmd inScopedIn forbidDecls stx[1]
  else if k == ``Lean.Parser.Command.mutual then
    stx.getNumArgs >= 2 && stx[1].getArgs.any (hasDisallowedGuardedCmd inScopedIn forbidDecls)
  else if k == ``Lean.Parser.Command.in then
    stx.getNumArgs != 3 ||
    hasDisallowedGuardedCmd true forbidDecls stx[0] ||
    hasDisallowedGuardedCmd true forbidDecls stx[2]
  else if k == ``Lean.Parser.Command.notation ||
          k == ``Lean.Parser.Command.mixfix ||
          k == ``Lean.Parser.Command.namespace ||
          k == ``Lean.Parser.Command.section ||
          k == ``Lean.Parser.Command.end ||
          k == ``Lean.Parser.Command.withWeakNamespace ||
          k == `Lean.Elab.Command.commandWith_weak_namespace__ ||
          k == `Mathlib.Tactic.scopedNS then
    true
  else if forbidDecls && isDeclCmdKind k then
    true
  else if !inScopedIn && (
          k == ``Lean.Parser.Command.open ||
          k == ``Lean.Parser.Command.set_option ||
          k == ``Lean.Parser.Command.unlock_limits) then
    true
  else
    false

private partial def checkAllowedCommand (stx : Syntax) : Option String :=
  let k := stx.getKind
  if k == choiceKind then
    let args := stx.getArgs
    if args.isEmpty then some "empty choice command"
    else args.findSome? checkAllowedCommand
  else if k == ``Lean.Parser.Command.in then
    if stx.getNumArgs == 3 then
      (checkAllowedCommand stx[0]).orElse fun _ => checkAllowedCommand stx[2]
    else some s!"malformed Command.in ({stx.getNumArgs} args)"
  else if k == ``Lean.Parser.Command.withWeakNamespace ||
          k == `Lean.Elab.Command.commandWith_weak_namespace__ then
    if stx.getNumArgs == 3 && stx[1].isIdent then checkAllowedCommand stx[2]
    else some s!"malformed with_weak_namespace ({stx.getNumArgs} args)"
  else if k == `Mathlib.Tactic.scopedNS then
    if stx.getNumArgs == 7 && stx[4].isIdent then
      let inner := stx[6]
      let innerK := inner.getKind
      if innerK == ``Lean.Parser.Command.notation ||
         innerK == ``Lean.Parser.Command.mixfix ||
         innerK == ``Lean.Parser.Command.attribute then
        none
      else
        some s!"scoped[NS] wrapping disallowed command '{innerK}'"
    else some s!"malformed scoped[NS] ({stx.getNumArgs} args)"
  else if k == ``Lean.Parser.Command.withExporting then
    if stx.getNumArgs >= 2 then checkAllowedCommand stx[1]
    else some "malformed with_exporting"
  else if k == ``Lean.Parser.timeCmd then
    if stx.getNumArgs == 2 then checkAllowedCommand stx[1]
    else some "malformed #time"
  else if k == ``Lean.guardMsgsCmd then
    if stx.getNumArgs == 5 then
      let forbidDecls := guardMsgsMayHideError stx
      (checkAllowedCommand stx[4]).orElse fun _ =>
        if hasDisallowedGuardedCmd false forbidDecls stx[4] then
          some "disallowed scope/notation/error-guarded declaration inside '#guard_msgs'"
        else none
    else some "malformed #guard_msgs"
  else if k == ``Lean.guardPanicCmd then
    if stx.getNumArgs == 3 then
      (checkAllowedCommand stx[2]).orElse fun _ =>
        if hasDisallowedGuardedCmd false true stx[2] then
          some "disallowed scope/notation/declaration inside '#guard_panic'"
        else none
    else some "malformed wrapper '#guard_panic'"
  else if k == ``Lean.infoTreesCmd then
    if stx.getNumArgs == 3 then
      (checkAllowedCommand stx[2]).orElse fun _ =>
        if hasDisallowedGuardedCmd false false stx[2] then
          some "disallowed scope/notation mutation inside '#info_trees'"
        else none
    else some "malformed wrapper '#info_trees'"
  else if k == ``Lean.Parser.Command.mutual then
    if stx.getNumArgs >= 2 then
      stx[1].getArgs.findSome? checkAllowedCommand
    else some "malformed mutual block"
  else if k == ``Lean.Parser.Command.section then
    if stx.getNumArgs == 3 && stx[0].getNumArgs == 4 then
      if stx[0][3].isNone then none
      else some "disallowed 'meta section'"
    else some "malformed section command"
  else if allowedLeafCommandKinds.contains k then
    none
  else
    some s!"disallowed command kind '{k}'"

-- Closed Positive Whitelist of Pure-Math Attributes (FAIL-CLOSED on ALL unlisted attributes).
-- Every whitelisted attribute is source-audited across Lean v4.32.2 / Batteries / Mathlib to have
-- ZERO evalConst / evalConstCheck / evalExpr / evalTerm / FFI / IO / Aesop / metaprogramming exec.
-- Nested `(attr := ...)` in `to_additive`/`to_dual`/`to_fun`/`elementwise`/`reassoc`/`to_app`
-- parses via `Parser.Term.attrInstance,*` and is recursively audited by `findViolations`.
private def allowedSimpleAttrNames : NameSet :=
  ({} : NameSet)
    -- Reducibility (5)
    |>.insert `reducible
    |>.insert `irreducible
    |>.insert `semireducible
    |>.insert `implicit_reducible
    |>.insert `instance_reducible
    -- Compiler inlining / specialization hints (6; pure hints, zero FFI/evalConst)
    |>.insert `inline
    |>.insert `noinline
    |>.insert `always_inline
    |>.insert `inline_if_reduce
    |>.insert `nospecialize
    |>.insert `weak_specialize
    -- Visibility / docs / pretty printing (5)
    |>.insert `expose
    |>.insert `no_expose
    |>.insert `inherit_doc
    |>.insert `pp_nodot
    |>.insert `pp_using_anonymous_constructor
    -- Pure-math elaboration / matching / coercions / eliminators (8)
    |>.insert `match_pattern
    |>.insert `coe_decl
    |>.insert `elab_as_elim
    |>.insert `elab_without_expected_type
    |>.insert `induction_eliminator
    |>.insert `cases_eliminator
    |>.insert `unification_hint
    |>.insert `partial_fixpoint_monotone
    -- Pure-math tactic theorem databases (9; zero evalConst)
    |>.insert `refl
    |>.insert `symm
    |>.insert `trans
    |>.insert `congr
    |>.insert `defeq
    |>.insert `push_cast
    |>.insert `bool_to_prop
    |>.insert `fun_prop
    |>.insert `field_simps

private def allowedAttrSyntaxKinds : NameSet :=
  ({} : NameSet)
    -- Core Lean v4.32.2 pure-math custom-syntax attributes (17)
    |>.insert ``Lean.Parser.Attr.simp
    |>.insert ``Lean.Parser.Attr.ext
    |>.insert ``Lean.Parser.Attr.class
    |>.insert ``Lean.Parser.Attr.instance
    |>.insert ``Lean.Parser.Attr.default_instance
    |>.insert ``Lean.Parser.Attr.specialize
    |>.insert ``Lean.Parser.Attr.recursor
    |>.insert ``Lean.Parser.Attr.norm_cast
    |>.insert ``Lean.Parser.Attr.grind
    |>.insert ``Lean.Parser.Attr.«grind!»
    |>.insert ``Lean.Parser.Attr.«grind?»
    |>.insert ``Lean.Parser.Attr.«grind!?»
    |>.insert `Lean.Attr.coe
    |>.insert `Lean.deprecated
    |>.insert `Lean.deprecated_arg
    |>.insert `Lean.univ_out_params
    |>.insert `Lean.suggest_for
    -- Batteries pure-math attributes (1)
    |>.insert `Batteries.Tactic.Lint.nolint
    -- Mathlib pure-math attributes (22; zero evalConst, zero Aesop, zero Simps)
    |>.insert `Mathlib.Tactic.GCongr.gcongrAttr
    |>.insert `Mathlib.Tactic.Push.pushAttr
    |>.insert `Mathlib.Tactic.Monotonicity.Attr.mono
    |>.insert `Mathlib.PPWithUniv.ppWithUnivAttr
    |>.insert `Mathlib.Tactic.ToAdditive.to_additive
    |>.insert `Mathlib.Tactic.ToAdditive.«attrTo_additive?_»
    |>.insert `Mathlib.Tactic.ToAdditive.to_additive_ignore_args
    |>.insert `Mathlib.Tactic.ToAdditive.to_additive_do_translate
    |>.insert `Mathlib.Tactic.ToAdditive.to_additive_dont_translate
    |>.insert `Mathlib.Tactic.ToDual.to_dual
    |>.insert `Mathlib.Tactic.ToDual.«attrTo_dual?_»
    |>.insert `Mathlib.Tactic.ToDual.to_dual_ignore_args
    |>.insert `Mathlib.Tactic.ToDual.to_dual_do_translate
    |>.insert `Mathlib.Tactic.ToDual.to_dual_dont_translate
    |>.insert `eqns
    |>.insert `Mathlib.Tactic.MkIff.mkIff
    |>.insert `Lean.Parser.Attr.higherOrder
    |>.insert `Mathlib.Tactic.to_fun
    |>.insert `Mathlib.Tactic.Elementwise.elementwise
    |>.insert `Mathlib.Tactic.Reassoc.reassoc
    |>.insert `Mathlib.Tactic.CategoryTheory.ToApp.to_app
    |>.insert `aliasIn
    -- Mathlib `register_simp_attr` pure theorem sets (17)
    |>.insert `Parser.Attr.mfld_simps
    |>.insert `Parser.Attr.zify_simps
    |>.insert `Parser.Attr.qify_simps
    |>.insert `Parser.Attr.rify_simps
    |>.insert `Parser.Attr.parity_simps
    |>.insert `Parser.Attr.functor_norm
    |>.insert `Parser.Attr.monad_norm
    |>.insert `Parser.Attr.nontriviality
    |>.insert `Parser.Attr.fin_omega
    |>.insert `Parser.Attr.enat_to_nat_coe
    |>.insert `Parser.Attr.enat_to_nat_top
    |>.insert `Parser.Attr.pnat_to_nat_coe
    |>.insert `Parser.Attr.rclike_simps
    |>.insert `Parser.Attr.integral_simps
    |>.insert `Parser.Attr.ghost_simps
    |>.insert `Parser.Attr.mon_tauto
    |>.insert `Parser.Attr.coassoc_simps

private def allowedEraseAttrNames : NameSet :=
  allowedSimpleAttrNames
    |>.insert `simp
    |>.insert `ext
    |>.insert `class
    |>.insert `instance
    |>.insert `default_instance
    |>.insert `specialize
    |>.insert `recursor
    |>.insert `norm_cast
    |>.insert `grind
    |>.insert `coe
    |>.insert `deprecated
    |>.insert `deprecated_arg
    |>.insert `univ_out_params
    |>.insert `suggest_for
    |>.insert `nolint
    |>.insert `gcongr
    |>.insert `push
    |>.insert `mono
    |>.insert `pp_with_univ
    |>.insert `eqns
    |>.insert `mfld_simps
    |>.insert `zify_simps
    |>.insert `qify_simps
    |>.insert `rify_simps
    |>.insert `parity_simps
    |>.insert `functor_norm
    |>.insert `monad_norm
    |>.insert `nontriviality
    |>.insert `fin_omega
    |>.insert `enat_to_nat_coe
    |>.insert `enat_to_nat_top
    |>.insert `pnat_to_nat_coe
    |>.insert `rclike_simps
    |>.insert `integral_simps
    |>.insert `ghost_simps
    |>.insert `mon_tauto
    |>.insert `coassoc_simps

private def checkAttrInstance (stx : Syntax) : Option String :=
  if stx.getNumArgs != 2 || stx[0].getKind != ``Lean.Parser.Term.attrKind then
    some "malformed @[...]"
  else
    let attrStx := stx[1]
    let ak := attrStx.getKind
    if ak == ``Lean.Parser.Attr.simple then
      if attrStx.getNumArgs >= 1 && attrStx[0].isIdent then
        let id := attrStx[0].getId.eraseMacroScopes
        if allowedSimpleAttrNames.contains id then none
        else some s!"@[ {id} ]"
      else
        some "malformed @[ simple ]"
    else if allowedAttrSyntaxKinds.contains ak then
      none
    else
      some s!"@[ {ak} ]"

private def checkEraseAttr (stx : Syntax) : Option String :=
  if stx.getNumArgs != 2 || !stx[1].isIdent then
    some "malformed attribute [-...]"
  else
    let id := stx[1].getId.eraseMacroScopes
    if allowedEraseAttrNames.contains id then none
    else some s!"attribute [-{id}]"

-- Positive whitelist for `decide` config items (allows ONLY kernel/revert and -native; fails closed).
private def checkDecideConfig (stx : Syntax) : Option String :=
  if stx.getNumArgs < 2 then none
  else
    let optCfg := stx[1]
    if optCfg.getNumArgs < 1 then none
    else
      optCfg[0].getArgs.findSome? fun item =>
        let ci := if item.getKind == ``Lean.Parser.Tactic.configItem && item.getNumArgs >= 1 then item[0] else item
        let ck := ci.getKind
        if ck == ``Lean.Parser.Tactic.negConfigItem && ci.getNumArgs >= 2 then
          let nm := ci[1].getId.eraseMacroScopes
          if nm == `native || nm == `kernel || nm == `revert then none
          else some s!"decide -{nm}"
        else if ck == ``Lean.Parser.Tactic.posConfigItem && ci.getNumArgs >= 2 then
          let nm := ci[1].getId.eraseMacroScopes
          if nm == `kernel || nm == `revert then none
          else some s!"decide +{nm}"
        else if ck == ``Lean.Parser.Tactic.valConfigItem && ci.getNumArgs >= 2 then
          let nm := ci[1].getId.eraseMacroScopes
          if nm == `kernel || nm == `revert then none
          else some s!"decide ({nm} := ...)"
        else
          some s!"decide malformed config item '{ck}'"

-- Positive whitelist for `linarith`/`linarith!`/`linarith?`/`linarith?!`/`nlinarith`/`nlinarith!`
-- config items on `Mathlib.Tactic.linarithArgsRest`. Blocks `Meta.evalExpr'` RCE via
-- `(oracle := ...)`, `(preprocessors := ...)`, `(config := ...)` while allowing all pure syntactic options.
private def allowedLinarithConfigFields : NameSet :=
  ({} : NameSet)
    |>.insert `discharger
    |>.insert `exfalso
    |>.insert `transparency
    |>.insert `splitHypotheses
    |>.insert `splitNe
    |>.insert `minimize

private def checkLinarithConfig (stx : Syntax) : Option String :=
  if stx.getNumArgs < 1 then none
  else
    let optCfg := stx[0]
    if optCfg.getNumArgs < 1 then none
    else
      optCfg[0].getArgs.findSome? fun item =>
        let ci := if item.getKind == ``Lean.Parser.Tactic.configItem && item.getNumArgs >= 1 then item[0] else item
        let ck := ci.getKind
        if (ck == ``Lean.Parser.Tactic.posConfigItem ||
            ck == ``Lean.Parser.Tactic.negConfigItem ||
            ck == ``Lean.Parser.Tactic.valConfigItem) && ci.getNumArgs >= 2 then
          let nm := ci[1].getId.eraseMacroScopes
          if allowedLinarithConfigFields.contains nm then none
          else some s!"linarith ({nm} := ...)"
        else
          some s!"linarith malformed config item '{ck}'"

private def isGenuineSkippedLeaf (stx : Syntax) : Bool :=
  match stx with
  | .node _ k #[.atom _ val] =>
    if k == strLitKind then
      (val.startsWith "\"" && val.endsWith "\"") ||
      (val.startsWith "r\"" && val.endsWith "\"") ||
      (val.startsWith "r#" && val.endsWith "#")
    else if k == charLitKind then
      val.startsWith "'" && val.endsWith "'"
    else if k == interpolatedStrLitKind then
      (val.startsWith "\"" || val.startsWith "}") &&
      (val.endsWith "\"" || val.endsWith "{")
    else
      false
  | .node _ k #[.atom _ openTok, .atom _ bodyTok] =>
    if k == ``Lean.Parser.Command.docComment then
      openTok == "/--" && bodyTok.endsWith "-/"
    else if k == ``Lean.Parser.Command.moduleDoc then
      openTok == "/-!" && bodyTok.endsWith "-/"
    else
      false
  | _ => false

private def stxLine (stx : Syntax) (fmap : FileMap) : Nat :=
  match stx.getPos? with
  | some p => (fmap.toPosition p).line
  | none => 0

private partial def findFirstIdent? (stx : Syntax) : Option Name :=
  match stx with
  | .ident _ _ id _ => some id.eraseMacroScopes
  | .node _ _ args => args.findSome? findFirstIdent?
  | _ => none

private def extractSetOptionName (stx : Syntax) : Name :=
  if stx.getNumArgs < 2 then Name.anonymous
  else
    let optStx := stx[1]
    let base :=
      if optStx.isIdent then optStx.getId
      else if optStx.getNumArgs >= 1 && optStx[0].isIdent then optStx[0].getId
      else Name.anonymous
    -- Handle `Lean.Parser.Tactic.Grind.setOption` optional `(noWs "." noWs ident)?` at arg[2]
    if stx.getKind == `Lean.Parser.Tactic.Grind.setOption && stx.getNumArgs >= 3 && !stx[2].isNone then
      match findFirstIdent? stx[2] with
      | some extId => base ++ extId
      | none => base
    else base

private def checkSetOption (stx : Syntax) : Option String :=
  let optName := extractSetOptionName stx
  if optName.isAnonymous then
    some "malformed set_option"
  else if isForbiddenOptionName optName then
    some s!"set_option {optName.eraseMacroScopes}"
  else
    none

partial def findViolations (stx : Syntax) (fmap : FileMap) (acc : Array (Nat × String)) :
    Array (Nat × String) :=
  if isGenuineSkippedLeaf stx then
    acc
  else if stx.getKind == nameLitKind then
    match stx.isNameLit? with
    | some n =>
      match checkNameForbidden n with
      | some hit => acc.push (stxLine stx fmap, hit)
      | none => acc
    | none =>
      stx.getArgs.foldl (fun a arg => findViolations arg fmap a) acc
  else
    match stx with
    | .ident _ _ val _ =>
      match checkNameForbidden val with
      | some hit => acc.push (stxLine stx fmap, hit)
      | none => acc
    | .atom _ val =>
      let trimmed := val.trimAscii.toString
      if forbiddenTokens.contains trimmed then
        acc.push (stxLine stx fmap, trimmed)
      else
        acc
    | .node _ k args =>
      let acc :=
        if forbiddenAstKinds.contains k || hasSubstr k.toString "SudoSet_option" then
          acc.push (stxLine stx fmap, s!"syntax:{k}")
        else acc
      let acc :=
        if k == ``Lean.Parser.Tactic.decide then
          match checkDecideConfig stx with
          | some hit => acc.push (stxLine stx fmap, hit)
          | none => acc
        else if k == `Mathlib.Tactic.linarithArgsRest then
          match checkLinarithConfig stx with
          | some hit => acc.push (stxLine stx fmap, hit)
          | none => acc
        else if k == ``Lean.Parser.Command.set_option ||
                k == ``Lean.Parser.Term.set_option ||
                k == ``Lean.Parser.Tactic.set_option ||
                k == `Lean.Parser.Tactic.Grind.setOption then
          match checkSetOption stx with
          | some hit => acc.push (stxLine stx fmap, hit)
          | none => acc
        else if k == ``Lean.Parser.Term.attrInstance then
          match checkAttrInstance stx with
          | some hit => acc.push (stxLine stx fmap, hit)
          | none => acc
        else if k == ``Lean.Parser.Command.eraseAttr then
          match checkEraseAttr stx with
          | some hit => acc.push (stxLine stx fmap, hit)
          | none => acc
        else acc
      args.foldl (fun a arg => findViolations arg fmap a) acc
    | .missing => acc

-- Exact Built-In Scope / Option / Declarative-Notation State Transition (ZERO user macro exec)
private def resolveNamespaceRelative (ns : Name) : Name → Name
  | `_root_ => Name.anonymous
  | Name.str n s .. => Name.mkStr (resolveNamespaceRelative ns n) s
  | Name.num n i .. => Name.mkNum (resolveNamespaceRelative ns n) i
  | Name.anonymous => ns

private def registerNamespaceWithPrefixes (env : Environment) (ns : Name) : Environment :=
  let rec go (env : Environment) : Name → Environment
    | .anonymous => env
    | n@(.str p _) => go (env.registerNamespace n) p
    | .num p _ => go env p
  go env ns

private def withWeakNamespaceStage1 {α : Type} (ns : Name) (m : CommandElabM α) : CommandElabM α := do
  let old ← getCurrNamespace
  let ns := resolveNamespaceRelative old ns
  modify fun s => { s with env := registerNamespaceWithPrefixes s.env ns }
  modifyScope ({ · with currNamespace := ns })
  try m finally modifyScope ({ · with currNamespace := old })

private def resolveNsStage1? (nsStx : Ident) : OpenDecl.M (m := CommandElabM) (Option (List Name)) := do
  try
    let nss ← resolveNamespace nsStx
    return some nss
  catch _ =>
    return none

private def elabOpenStage1 (stx : Syntax) : CommandElabM Unit := do
  match stx with
  | `(Lean.Parser.Command.open| open $decl:openDecl) =>
    let openDecls ← StateRefT'.run'
      (s := { openDecls := (← getOpenDecls), currNamespace := (← getCurrNamespace) }) do
      match decl with
      | `(Lean.Parser.Command.openDecl| $nss*) =>
        for ns in nss do
          match ← resolveNsStage1? ns with
          | some rnsList =>
            for rns in rnsList do
              modify fun s => { s with openDecls := OpenDecl.simple rns [] :: s.openDecls }
              activateScoped rns
          | none =>
            let fallback := resolveNamespaceRelative (← getCurrNamespace) ns.getId
            modify fun s => { s with openDecls := OpenDecl.simple fallback [] :: s.openDecls }
      | `(Lean.Parser.Command.openDecl| scoped $nss*) =>
        for ns in nss do
          if let some rnsList ← resolveNsStage1? ns then
            for rns in rnsList do
              activateScoped rns
      | `(Lean.Parser.Command.openDecl| $ns ($ids*)) =>
        let currNs ← getCurrNamespace
        let rns := match ← resolveNsStage1? ns with
          | some (h :: _) => h
          | _ => resolveNamespaceRelative currNs ns.getId
        for idStx in ids do
          modify fun s => { s with openDecls := OpenDecl.explicit idStx.getId (rns ++ idStx.getId) :: s.openDecls }
      | `(Lean.Parser.Command.openDecl| $ns hiding $ids*) =>
        let hideList := ids.map (·.getId) |>.toList
        match ← resolveNsStage1? ns with
        | some rnsList =>
          for rns in rnsList do
            activateScoped rns
            modify fun s => { s with openDecls := OpenDecl.simple rns hideList :: s.openDecls }
        | none =>
          let fallback := resolveNamespaceRelative (← getCurrNamespace) ns.getId
          modify fun s => { s with openDecls := OpenDecl.simple fallback hideList :: s.openDecls }
      | `(Lean.Parser.Command.openDecl| $ns renaming $[$froms -> $tos],*) =>
        let currNs ← getCurrNamespace
        let rns := match ← resolveNsStage1? ns with
          | some (h :: _) => h
          | _ => resolveNamespaceRelative currNs ns.getId
        for («from», to) in froms.zip tos do
          modify fun s => { s with openDecls := OpenDecl.explicit to.getId (rns ++ «from».getId) :: s.openDecls }
      | _ => throwUnsupportedSyntax
      return (← get).openDecls
    modifyScope fun scope => { scope with openDecls := openDecls }
  | _ => throwUnsupportedSyntax

private def checkNotationNameSafe (name? : Option (TSyntax `ident)) : CommandElabM Unit := do
  if let some n := name? then
    let rawId := n.getId.eraseMacroScopes
    let fullId := resolveNamespaceRelative (← getCurrNamespace) rawId
    if rawId.isAnonymous ||
       forbiddenNotationKinds.contains rawId || forbiddenNotationKinds.contains fullId ||
       forbiddenAstKinds.contains rawId || forbiddenAstKinds.contains fullId then
      throwError "disallowed notation kind name '{rawId}'"

private def checkNotationItemSafe (tokTable : TokenTable) (item : Syntax) : CommandElabM Bool := do
  let k := item.getKind
  if k == ``Lean.Parser.Command.identPrec then
    return false
  else if k == strLitKind then
    match item.isStrLit? with
    | some s =>
      if !isSafeNotationAtom tokTable s then
        throwError "disallowed notation symbol {repr s}"
      return true
    | none =>
      throwError "malformed notation symbol"
  else if k == ``Lean.Parser.Syntax.unicodeAtom && item.getNumArgs >= 4 then
    match item[1].isStrLit?, item[3].isStrLit? with
    | some s1, some s2 =>
      if !(isSafeNotationAtom tokTable s1 && isSafeNotationAtom tokTable s2) then
        throwError "disallowed unicode notation symbol"
      return true
    | _, _ =>
      throwError "malformed unicode notation symbol"
  else
    throwError "unsupported notation item kind '{k}'"

private def elabNotationStage1 (tokTable : TokenTable) (stx : Syntax) (forceScoped : Bool := false) : CommandElabM Unit := do
  match stx with
  | ref@`($[$_doc?:docComment]? $[@[$_attrs?,*]]? $attrKind:attrKind
      notation $[: $prec?]? $[(name := $name?)]? $[(priority := $prio?)]? $items* => $_rhs) =>
    if items.isEmpty then
      throwError "empty notation items"
    checkNotationNameSafe name?
    let mut hasAtom := false
    for item in items do
      if ← checkNotationItemSafe tokTable item.raw then
        hasAtom := true
    if !hasAtom then
      throwError "notation must contain at least one symbolic atom"
    let ak ← if forceScoped then `(Lean.Parser.Term.attrKind| scoped) else pure attrKind
    let prio ← liftMacroM <| evalOptPrio prio?
    let stxParts ← liftMacroM <| items.mapM expandNotationItemIntoSyntaxItem
    let cat := mkIdentFrom ref `term
    let cmd ← `($ak:attrKind
      syntax $[: $prec?]? $[(name := $name?)]? (priority := $(quote prio):num) $[$stxParts]* : $cat)
    discard <| Lean.Elab.Command.elabSyntax cmd.raw
  | _ =>
    throwError "unsupported notation command form"

private def elabMixfixStage1 (tokTable : TokenTable) (stx : Syntax) (forceScoped : Bool := false) : CommandElabM Unit := do
  if stx.getNumArgs < 3 then
    throwError "malformed mixfix command"
  let origAttrKind : TSyntax ``Lean.Parser.Term.attrKind := ⟨stx[2]⟩
  let ak ← if forceScoped then `(Lean.Parser.Term.attrKind| scoped) else pure origAttrKind
  let stxGlobal := stx.setArg 2 (Unhygienic.run `(Lean.Parser.Term.attrKind| ))
  match stxGlobal with
  | `($[$_doc?:docComment]? $[@[$_attrs?,*]]? infixl:$prec $[(name := $name?)]? $[(priority := $prio?)]? $op => $_f) =>
    checkNotationNameSafe name?
    if !(← checkNotationItemSafe tokTable op.raw) then
      throwError "mixfix operator must be a symbolic atom"
    let p ← liftMacroM <| evalPrec prec
    let p1 := quote (p + 1)
    let prio ← liftMacroM <| evalOptPrio prio?
    let opStx ← liftMacroM <| expandNotationItemIntoSyntaxItem op
    let cmd ← `($ak:attrKind
      syntax:$prec $[(name := $name?)]? (priority := $(quote prio):num) term:$prec $opStx term:$p1 : term)
    discard <| Lean.Elab.Command.elabSyntax cmd.raw
  | `($[$_doc?:docComment]? $[@[$_attrs?,*]]? infix:$prec $[(name := $name?)]? $[(priority := $prio?)]? $op => $_f) =>
    checkNotationNameSafe name?
    if !(← checkNotationItemSafe tokTable op.raw) then
      throwError "mixfix operator must be a symbolic atom"
    let p ← liftMacroM <| evalPrec prec
    let p1 := quote (p + 1)
    let prio ← liftMacroM <| evalOptPrio prio?
    let opStx ← liftMacroM <| expandNotationItemIntoSyntaxItem op
    let cmd ← `($ak:attrKind
      syntax:$prec $[(name := $name?)]? (priority := $(quote prio):num) term:$p1 $opStx term:$p1 : term)
    discard <| Lean.Elab.Command.elabSyntax cmd.raw
  | `($[$_doc?:docComment]? $[@[$_attrs?,*]]? infixr:$prec $[(name := $name?)]? $[(priority := $prio?)]? $op => $_f) =>
    checkNotationNameSafe name?
    if !(← checkNotationItemSafe tokTable op.raw) then
      throwError "mixfix operator must be a symbolic atom"
    let p ← liftMacroM <| evalPrec prec
    let p1 := quote (p + 1)
    let prio ← liftMacroM <| evalOptPrio prio?
    let opStx ← liftMacroM <| expandNotationItemIntoSyntaxItem op
    let cmd ← `($ak:attrKind
      syntax:$prec $[(name := $name?)]? (priority := $(quote prio):num) term:$p1 $opStx term:$prec : term)
    discard <| Lean.Elab.Command.elabSyntax cmd.raw
  | `($[$_doc?:docComment]? $[@[$_attrs?,*]]? prefix:$prec $[(name := $name?)]? $[(priority := $prio?)]? $op => $_f) =>
    checkNotationNameSafe name?
    if !(← checkNotationItemSafe tokTable op.raw) then
      throwError "mixfix operator must be a symbolic atom"
    let prio ← liftMacroM <| evalOptPrio prio?
    let opStx ← liftMacroM <| expandNotationItemIntoSyntaxItem op
    let cmd ← `($ak:attrKind
      syntax:$prec $[(name := $name?)]? (priority := $(quote prio):num) $opStx term:$prec : term)
    discard <| Lean.Elab.Command.elabSyntax cmd.raw
  | `($[$_doc?:docComment]? $[@[$_attrs?,*]]? postfix:$prec $[(name := $name?)]? $[(priority := $prio?)]? $op => $_f) =>
    checkNotationNameSafe name?
    if !(← checkNotationItemSafe tokTable op.raw) then
      throwError "mixfix operator must be a symbolic atom"
    let prio ← liftMacroM <| evalOptPrio prio?
    let opStx ← liftMacroM <| expandNotationItemIntoSyntaxItem op
    let cmd ← `($ak:attrKind
      syntax:$prec $[(name := $name?)]? (priority := $(quote prio):num) term:$prec $opStx : term)
    discard <| Lean.Elab.Command.elabSyntax cmd.raw
  | _ =>
    throwError "unsupported mixfix command form"

private def extractDeclId? (stx : Syntax) : Option Name :=
  if stx.getKind == ``Lean.Parser.Command.declId && stx.getNumArgs >= 1 && stx[0].isIdent then
    some stx[0].getId.eraseMacroScopes
  else if stx.isIdent then
    some stx.getId.eraseMacroScopes
  else
    none

private def hasWhereDeclsInVal (valStx : Syntax) : Bool :=
  let vk := valStx.getKind
  if vk == ``Lean.Parser.Command.declValSimple && valStx.getNumArgs >= 4 then
    !valStx[3].isNone
  else if vk == ``Lean.Parser.Command.declValEqns && valStx.getNumArgs >= 1 then
    let ma := valStx[0]
    ma.getKind == ``Lean.Parser.Term.matchAltsWhereDecls && ma.getNumArgs >= 3 && !ma[2].isNone
  else if vk == ``Lean.Parser.Command.whereStructInst && valStx.getNumArgs >= 3 then
    !valStx[2].isNone
  else
    false

private def selfNsAuxKinds : NameSet :=
  ({} : NameSet)
    |>.insert ``Lean.Parser.Term.whereDecls
    |>.insert ``Lean.Parser.Tactic.match
    |>.insert ``Lean.Parser.Term.nomatch
    |>.insert ``Lean.Parser.Term.nofun
    |>.insert ``Lean.Parser.Term.letrec
    |>.insert ``Lean.Parser.Term.doLetRec
    |>.insert ``Lean.Parser.Term.doLetElse
    |>.insert ``Lean.Parser.Term.doMatch
    |>.insert ``Lean.Parser.Term.doIfLet
    |>.insert `termIfLet

private def isNonVarPatternIdent (env : Environment) (opts : Options) (currNs : Name) (openDecls : List OpenDecl) (id : Name) : Bool :=
  let resolved := Lean.ResolveName.resolveGlobalName env opts currNs openDecls id
  resolved.any fun (full, fields) =>
    fields.isEmpty &&
    match env.find? full with
    | some (.ctorInfo _) => true
    | some _ => Lean.hasMatchPatternAttribute env full
    | none => false

private partial def isUnitPattern (env : Environment) (opts : Options) (currNs : Name) (openDecls : List OpenDecl) (stx : Syntax) : Bool :=
  if stx.getKind == ``Lean.Parser.Term.paren && stx.getNumArgs == 3 then
    isUnitPattern env opts currNs openDecls stx[1]
  else if stx.getKind == ``Lean.Parser.Term.tuple && stx.getNumArgs == 3 && stx[1].isNone then
    true
  else if stx.isIdent then
    let n := stx.getId.eraseMacroScopes
    n == `Unit.unit || n == `PUnit.unit ||
    (Lean.ResolveName.resolveGlobalName env opts currNs openDecls n).any fun (full, fields) =>
      fields.isEmpty && (full == `Unit.unit || full == `PUnit.unit)
  else false

private def isPlainVarPattern (env : Environment) (opts : Options) (currNs : Name) (openDecls : List OpenDecl) (stx : Syntax) : Bool :=
  stx.isIdent &&
  let id := stx.getId.eraseMacroScopes
  id.isAtomic && !isNonVarPatternIdent env opts currNs openDecls id

-- Exact match to Lean v4.32.2 `Match.lean`:
--   `expandSimpleMatch` (`| x => rhs` for a single plain pattern variable `x`)
--   and `isMatchUnit?` (`| () => rhs` for a single `PUnit.unit`/`Unit.unit` pattern).
-- Returns `some (optBoundVar, rhs)` iff this `matchAlts` does NOT synthesize `match_1`.
private def extractTrivialMatchAlt? (env : Environment) (opts : Options) (currNs : Name) (openDecls : List OpenDecl)
    (matchAltsStx : Syntax) : Option (Option Name × Syntax) :=
  if matchAltsStx.getKind == ``Lean.Parser.Term.matchAlts && matchAltsStx.getNumArgs >= 1 then
    let alts := matchAltsStx[0].getArgs
    if alts.size == 1 then
      let alt := alts[0]!
      if alt.getKind == ``Lean.Parser.Term.matchAlt && alt.getNumArgs >= 4 then
        let patRows := alt[1].getSepArgs
        if patRows.size == 1 then
          let pats := patRows[0]!.getSepArgs
          if pats.size == 1 then
            let pat := pats[0]!
            let rhs := alt[3]
            if isUnitPattern env opts currNs openDecls pat then
              some (none, rhs)
            else if isPlainVarPattern env opts currNs openDecls pat then
              some (some pat.getId.eraseMacroScopes, rhs)
            else none
          else none
        else none
      else none
    else none
  else none

private def collectBracketedBinderNames (b : Syntax) (acc : NameSet) : NameSet :=
  let k := b.getKind
  if b.isIdent then
    acc.insert b.getId.eraseMacroScopes
  else if (k == ``Lean.Parser.Term.explicitBinder ||
           k == ``Lean.Parser.Term.implicitBinder ||
           k == ``Lean.Parser.Term.strictImplicitBinder) && b.getNumArgs >= 2 then
    b[1].getArgs.foldl (fun s a => if a.isIdent then s.insert a.getId.eraseMacroScopes else s) acc
  else if k == ``Lean.Parser.Term.instBinder && b.getNumArgs >= 2 then
    if b[1].getNumArgs >= 1 && b[1][0].isIdent then
      acc.insert b[1][0].getId.eraseMacroScopes
    else acc
  else acc

private def extractFunBinderIdents? (term : Syntax) : Option (Array Name) :=
  if term.isIdent then
    some #[term.getId.eraseMacroScopes]
  else if term.getKind == ``Lean.Parser.Term.hole then
    some #[]
  else if term.getKind == ``Lean.Parser.Term.app && term.getNumArgs == 2 then
    let fn := term[0]
    let args := term[1].getArgs
    let init? : Option (Array Name) :=
      if fn.isIdent then some #[fn.getId.eraseMacroScopes]
      else if fn.getKind == ``Lean.Parser.Term.hole then some #[]
      else none
    init?.bind fun arr =>
      args.foldlM (init := arr) fun a arg =>
        if arg.isIdent then some (a.push arg.getId.eraseMacroScopes)
        else if arg.getKind == ``Lean.Parser.Term.hole then some a
        else none
  else none

private def collectDeclSigBinderNames (sigStx : Syntax) (acc : NameSet) : NameSet :=
  if sigStx.getNumArgs >= 1 then
    sigStx[0].getArgs.foldl (fun s b => collectBracketedBinderNames b s) acc
  else acc

private partial def valCreatesSelfNamespace
    (env : Environment) (opts : Options) (currNs : Name) (openDecls : List OpenDecl)
    (recTargets : NameSet) (bound : NameSet) (stx : Syntax) : Bool :=
  if isGenuineSkippedLeaf stx then false
  else
    match stx with
    | .ident _ _ id _ =>
      let clean := id.eraseMacroScopes
      if clean.isAtomic && bound.contains clean then false
      else
        recTargets.contains clean ||
        (match clean with | .str _ tail => recTargets.contains (Name.mkSimple tail) | _ => false)
    | .node _ k args =>
      if k == ``Lean.Parser.Term.binderTactic then
        false
      else if selfNsAuxKinds.contains k then
        true
      else if k == ``Lean.Parser.Command.declValEqns && args.size >= 1 then
        let ma := args[0]!
        if ma.getKind == ``Lean.Parser.Term.matchAltsWhereDecls && ma.getNumArgs >= 3 then
          if !ma[2].isNone then true
          else
            match extractTrivialMatchAlt? env opts currNs openDecls ma[0] with
            | some (bVar?, rhs) =>
              let bound' := match bVar? with | some v => bound.insert v | none => bound
              valCreatesSelfNamespace env opts currNs openDecls recTargets bound ma[1] ||
              valCreatesSelfNamespace env opts currNs openDecls recTargets bound' rhs
            | none => true
        else true
      else if k == ``Lean.Parser.Term.match && args.size >= 6 then
        let discrs := args[3]!.getSepArgs
        let simpleDiscr :=
          args[1]!.isNone && args[2]!.isNone && discrs.size == 1 &&
          discrs[0]!.getNumArgs >= 2 && discrs[0]![0].isNone
        if simpleDiscr then
          match extractTrivialMatchAlt? env opts currNs openDecls args[5]! with
          | some (bVar?, rhs) =>
            let bound' := match bVar? with | some v => bound.insert v | none => bound
            valCreatesSelfNamespace env opts currNs openDecls recTargets bound discrs[0]![1] ||
            valCreatesSelfNamespace env opts currNs openDecls recTargets bound' rhs
          | none => true
        else true
      else if k == ``Lean.Parser.Term.matchAlts then
        match extractTrivialMatchAlt? env opts currNs openDecls stx with
        | some (bVar?, rhs) =>
          let bound' := match bVar? with | some v => bound.insert v | none => bound
          valCreatesSelfNamespace env opts currNs openDecls recTargets bound' rhs
        | none => true
      else if k == ``Lean.Parser.Term.fun && args.size >= 2 then
        let funBody := args[1]!
        if funBody.getKind == ``Lean.Parser.Term.matchAlts then
          match extractTrivialMatchAlt? env opts currNs openDecls funBody with
          | some (bVar?, rhs) =>
            let bound' := match bVar? with | some v => bound.insert v | none => bound
            valCreatesSelfNamespace env opts currNs openDecls recTargets bound' rhs
          | none => true
        else if funBody.getKind == ``Lean.Parser.Term.basicFun && funBody.getNumArgs >= 4 then Id.run do
          let mut funBound := bound
          for b in funBody[0].getArgs do
            let bk := b.getKind
            if b.isIdent then
              funBound := funBound.insert b.getId.eraseMacroScopes
            else if bk == ``Lean.Parser.Term.hole then
              pure ()
            else if bk == ``Lean.Parser.Term.explicitBinder ||
                    bk == ``Lean.Parser.Term.implicitBinder ||
                    bk == ``Lean.Parser.Term.strictImplicitBinder then
              if b.getNumArgs >= 3 && valCreatesSelfNamespace env opts currNs openDecls recTargets funBound b[2] then
                return true
              if b.getNumArgs >= 4 && valCreatesSelfNamespace env opts currNs openDecls recTargets funBound b[3] then
                return true
              funBound := collectBracketedBinderNames b funBound
            else if bk == ``Lean.Parser.Term.instBinder then
              if b.getNumArgs >= 3 && valCreatesSelfNamespace env opts currNs openDecls recTargets funBound b[2] then
                return true
              funBound := collectBracketedBinderNames b funBound
            else if bk == ``Lean.Parser.Term.paren && b.getNumArgs == 3 then
              match extractFunBinderIdents? b[1] with
              | some ids =>
                if ids.any (isNonVarPatternIdent env opts currNs openDecls) then
                  return true
                funBound := ids.foldl (·.insert ·) funBound
              | none =>
                if !isUnitPattern env opts currNs openDecls b[1] then
                  return true
            else if bk == ``Lean.Parser.Term.typeAscription && b.getNumArgs >= 4 then
              if valCreatesSelfNamespace env opts currNs openDecls recTargets funBound b[3] then
                return true
              match extractFunBinderIdents? b[1] with
              | some ids =>
                funBound := ids.foldl (·.insert ·) funBound
              | none =>
                if !isUnitPattern env opts currNs openDecls b[1] then
                  return true
            else if isUnitPattern env opts currNs openDecls b then
              pure ()
            else
              -- Pattern-destructuring lambda binder (e.g. `fun (a, b) => ...`) synthesizes `match_1`.
              return true
          return valCreatesSelfNamespace env opts currNs openDecls recTargets funBound funBody[1] ||
                 valCreatesSelfNamespace env opts currNs openDecls recTargets funBound funBody[3]
        else
          args.any (valCreatesSelfNamespace env opts currNs openDecls recTargets bound)
      else if (k == ``Lean.Parser.Term.let || k == ``Lean.Parser.Term.have) && args.size >= 5 then
        let letDeclNode := args[2]!
        let body := args[4]!
        let decl :=
          if letDeclNode.getKind == ``Lean.Parser.Term.letDecl &&
             letDeclNode.getNumArgs >= 1 then letDeclNode[0]
          else letDeclNode
        let dk := decl.getKind
        if dk == ``Lean.Parser.Term.letIdDecl && decl.getNumArgs >= 5 then
          let letName? : Option Name :=
            if decl[0].getKind == ``Lean.Parser.Term.letId && decl[0].getNumArgs >= 1 && decl[0][0].isIdent then
              some decl[0][0].getId.eraseMacroScopes
            else if decl[0].isIdent then
              some decl[0].getId.eraseMacroScopes
            else none
          let bBound := decl[1].getArgs.foldl (fun s b => collectBracketedBinderNames b s) bound
          let rhsHit :=
            valCreatesSelfNamespace env opts currNs openDecls recTargets bound decl[1] ||
            valCreatesSelfNamespace env opts currNs openDecls recTargets bBound decl[2] ||
            valCreatesSelfNamespace env opts currNs openDecls recTargets bBound decl[4]
          let bodyBound := match letName? with | some nm => bound.insert nm | none => bound
          rhsHit || valCreatesSelfNamespace env opts currNs openDecls recTargets bodyBound body
        else if dk == ``Lean.Parser.Term.letPatDecl && decl.getNumArgs >= 5 then
          let pat := decl[0]
          if isUnitPattern env opts currNs openDecls pat then
            valCreatesSelfNamespace env opts currNs openDecls recTargets bound decl[1] ||
            valCreatesSelfNamespace env opts currNs openDecls recTargets bound decl[2] ||
            valCreatesSelfNamespace env opts currNs openDecls recTargets bound decl[4] ||
            valCreatesSelfNamespace env opts currNs openDecls recTargets bound body
          else if isPlainVarPattern env opts currNs openDecls pat then
            let bodyBound := bound.insert pat.getId.eraseMacroScopes
            valCreatesSelfNamespace env opts currNs openDecls recTargets bound decl[1] ||
            valCreatesSelfNamespace env opts currNs openDecls recTargets bound decl[2] ||
            valCreatesSelfNamespace env opts currNs openDecls recTargets bound decl[4] ||
            valCreatesSelfNamespace env opts currNs openDecls recTargets bodyBound body
          else true
        else if dk == ``Lean.Parser.Term.letEqnsDecl && decl.getNumArgs >= 4 then
          match extractTrivialMatchAlt? env opts currNs openDecls decl[3] with
          | some (bVar?, rhs) =>
            let letName? : Option Name :=
              if decl[0].getKind == ``Lean.Parser.Term.letId && decl[0].getNumArgs >= 1 && decl[0][0].isIdent then
                some decl[0][0].getId.eraseMacroScopes
              else none
            let bBound := decl[1].getArgs.foldl (fun s b => collectBracketedBinderNames b s) bound
            let rhsBound := match bVar? with | some v => bBound.insert v | none => bBound
            let bodyBound := match letName? with | some nm => bound.insert nm | none => bound
            valCreatesSelfNamespace env opts currNs openDecls recTargets bound decl[1] ||
            valCreatesSelfNamespace env opts currNs openDecls recTargets bBound decl[2] ||
            valCreatesSelfNamespace env opts currNs openDecls recTargets rhsBound rhs ||
            valCreatesSelfNamespace env opts currNs openDecls recTargets bodyBound body
          | none => true
        else
          args.any (valCreatesSelfNamespace env opts currNs openDecls recTargets bound)
      else if k == ``Lean.Parser.Term.letPatDecl && args.size >= 1 then
        let pat := args[0]!
        if isUnitPattern env opts currNs openDecls pat || isPlainVarPattern env opts currNs openDecls pat then
          args.extract 1 args.size |>.any (valCreatesSelfNamespace env opts currNs openDecls recTargets bound)
        else true
      else if k == ``Lean.Parser.Term.depArrow && args.size >= 3 then
        let b := args[0]!
        let bBound := collectBracketedBinderNames b bound
        let typeHit :=
          if (b.getKind == ``Lean.Parser.Term.explicitBinder ||
              b.getKind == ``Lean.Parser.Term.implicitBinder ||
              b.getKind == ``Lean.Parser.Term.strictImplicitBinder ||
              b.getKind == ``Lean.Parser.Term.instBinder) && b.getNumArgs >= 3 then
            valCreatesSelfNamespace env opts currNs openDecls recTargets bound b[2]
          else false
        typeHit || valCreatesSelfNamespace env opts currNs openDecls recTargets bBound args[2]!
      else if k == ``Lean.Parser.Term.forall && args.size >= 4 then Id.run do
        let mut fBound := bound
        for b in args[1]!.getArgs do
          if (b.getKind == ``Lean.Parser.Term.explicitBinder ||
              b.getKind == ``Lean.Parser.Term.implicitBinder ||
              b.getKind == ``Lean.Parser.Term.strictImplicitBinder ||
              b.getKind == ``Lean.Parser.Term.instBinder) && b.getNumArgs >= 3 then
            if valCreatesSelfNamespace env opts currNs openDecls recTargets fBound b[2] then
              return true
          fBound := collectBracketedBinderNames b fBound
        return valCreatesSelfNamespace env opts currNs openDecls recTargets fBound args[3]!
      else
        args.any (valCreatesSelfNamespace env opts currNs openDecls recTargets bound)
    | _ => false

private def sigCreatesSelfNamespace
    (env : Environment) (opts : Options) (currNs : Name) (openDecls : List OpenDecl)
    (sigStx : Syntax) : Bool :=
  valCreatesSelfNamespace env opts currNs openDecls {} {} sigStx

private def declRegistersSelfNamespace
    (env : Environment) (opts : Options) (currNs : Name) (openDecls : List OpenDecl)
    (recTargets : NameSet) (sigBound : NameSet) (valStx : Syntax) : Bool :=
  hasWhereDeclsInVal valStx ||
  valCreatesSelfNamespace env opts currNs openDecls recTargets sigBound valStx

private def collectDeclShortName? (stx : Syntax) : Option Name :=
  let k := stx.getKind
  if k == ``Lean.Parser.Command.declaration && stx.getNumArgs >= 2 then
    let inner := stx[1]
    let ik := inner.getKind
    if (ik == ``Lean.Parser.Command.definition ||
        ik == ``Lean.Parser.Command.theorem ||
        ik == ``Lean.Parser.Command.abbrev ||
        ik == ``Lean.Parser.Command.opaque) && inner.getNumArgs >= 2 then
      extractDeclId? inner[1]
    else if ik == ``Lean.Parser.Command.instance && inner.getNumArgs >= 4 && inner[3].getNumArgs >= 1 then
      extractDeclId? inner[3][0]
    else none
  else if (k == `lemma || k == `Batteries.Tactic.Lemma.lemmaCmd) && stx.getNumArgs >= 2 && stx[1].getNumArgs >= 2 then
    extractDeclId? stx[1][1]
  else none

private def addRecTargets (base : NameSet) (currNs rawId : Name) : NameSet :=
  let full := resolveNamespaceRelative currNs rawId.eraseMacroScopes
  let s := base.insert rawId.eraseMacroScopes |>.insert full
  match rawId.eraseMacroScopes with
  | .str _ tail => s.insert (Name.mkSimple tail)
  | _ => s

private def registerDeclName (rawId : Name) (includeSelf : Bool) : CommandElabM Unit := do
  let currNs ← getCurrNamespace
  let fullName := resolveNamespaceRelative currNs rawId.eraseMacroScopes
  let nsToReg := if includeSelf then fullName else fullName.getPrefix
  if !nsToReg.isAnonymous then
    modify fun s => { s with env := registerNamespaceWithPrefixes s.env nsToReg }

private def registerDeclNamespaces (stx : Syntax) (mutualRecTargets : NameSet := {}) : CommandElabM Unit := do
  let k := stx.getKind
  let env ← getEnv
  let opts ← getOptions
  let currNs ← getCurrNamespace
  let openDecls ← getOpenDecls
  let elabAsync := opts.getBool `Elab.async true
  if k == ``Lean.Parser.Command.declaration && stx.getNumArgs >= 2 then
    let inner := stx[1]
    let ik := inner.getKind
    if (ik == ``Lean.Parser.Command.structure ||
        ik == ``Lean.Parser.Command.inductive ||
        ik == ``Lean.Parser.Command.coinductive ||
        ik == ``Lean.Parser.Command.classInductive) && inner.getNumArgs >= 2 then
      if let some id := extractDeclId? inner[1] then
        registerDeclName id (includeSelf := true)
    else if (ik == ``Lean.Parser.Command.definition ||
             ik == ``Lean.Parser.Command.abbrev ||
             ik == ``Lean.Parser.Command.opaque) && inner.getNumArgs >= 2 then
      if let some id := extractDeclId? inner[1] then
        let targets := addRecTargets mutualRecTargets currNs id
        let sigSelfNs := inner.getNumArgs >= 3 && sigCreatesSelfNamespace env opts currNs openDecls inner[2]
        let sigBound := if inner.getNumArgs >= 3 then collectDeclSigBinderNames inner[2] {} else {}
        let valSelfNs := inner.getNumArgs >= 4 && declRegistersSelfNamespace env opts currNs openDecls targets sigBound inner[3]
        registerDeclName id (includeSelf := sigSelfNs || valSelfNs)
    else if ik == ``Lean.Parser.Command.theorem && inner.getNumArgs >= 2 then
      if let some id := extractDeclId? inner[1] then
        let targets := addRecTargets mutualRecTargets currNs id
        let sigSelfNs := inner.getNumArgs >= 3 && sigCreatesSelfNamespace env opts currNs openDecls inner[2]
        let sigBound := if inner.getNumArgs >= 3 then collectDeclSigBinderNames inner[2] {} else {}
        let valSelfNs := !elabAsync && inner.getNumArgs >= 4 && declRegistersSelfNamespace env opts currNs openDecls targets sigBound inner[3]
        registerDeclName id (includeSelf := sigSelfNs || valSelfNs)
    else if ik == ``Lean.Parser.Command.axiom && inner.getNumArgs >= 2 then
      if let some id := extractDeclId? inner[1] then
        let sigSelfNs := inner.getNumArgs >= 3 && sigCreatesSelfNamespace env opts currNs openDecls inner[2]
        registerDeclName id (includeSelf := sigSelfNs)
    else if ik == ``Lean.Parser.Command.instance && inner.getNumArgs >= 4 then
      let optDeclId := inner[3]
      if optDeclId.getNumArgs >= 1 then
        if let some id := extractDeclId? optDeclId[0] then
          let targets := addRecTargets mutualRecTargets currNs id
          let sigSelfNs := inner.getNumArgs >= 5 && sigCreatesSelfNamespace env opts currNs openDecls inner[4]
          let sigBound := if inner.getNumArgs >= 5 then collectDeclSigBinderNames inner[4] {} else {}
          let valSelfNs := inner.getNumArgs >= 6 && declRegistersSelfNamespace env opts currNs openDecls targets sigBound inner[5]
          registerDeclName id (includeSelf := sigSelfNs || valSelfNs)
  else if k == ``Lean.Parser.Command.classAbbrev && stx.getNumArgs >= 4 then
    if let some id := extractDeclId? stx[3] then
      registerDeclName id (includeSelf := true)
  else if (k == `lemma || k == `Batteries.Tactic.Lemma.lemmaCmd) && stx.getNumArgs >= 2 then
    let grp := stx[1]
    if grp.getNumArgs >= 2 then
      if let some id := extractDeclId? grp[1] then
        let targets := addRecTargets mutualRecTargets currNs id
        let sigSelfNs := grp.getNumArgs >= 3 && sigCreatesSelfNamespace env opts currNs openDecls grp[2]
        let sigBound := if grp.getNumArgs >= 3 then collectDeclSigBinderNames grp[2] {} else {}
        let valSelfNs := !elabAsync && grp.getNumArgs >= 4 && declRegistersSelfNamespace env opts currNs openDecls targets sigBound grp[3]
        registerDeclName id (includeSelf := sigSelfNs || valSelfNs)
  else if k == `Batteries.Tactic.Alias.alias && stx.getNumArgs >= 3 then
    if let some id := extractDeclId? stx[2] then
      registerDeclName id (includeSelf := false)
  else if k == `Batteries.Tactic.Alias.aliasLR && stx.getNumArgs >= 6 then
    for b in #[stx[3], stx[5]] do
      if b.getKind == ``Lean.binderIdent && b.getNumArgs >= 1 && b[0].isIdent then
        registerDeclName b[0].getId (includeSelf := false)

private partial def registerGuardedDeclNamespaces (stx : Syntax) : CommandElabM Unit := do
  let k := stx.getKind
  if k == choiceKind then
    if let some first := stx.getArgs[0]? then
      registerGuardedDeclNamespaces first
  else if isDeclCmdKind k then
    registerDeclNamespaces stx
  else if k == ``Lean.Parser.Command.withExporting then
    if stx.getNumArgs >= 2 then registerGuardedDeclNamespaces stx[1]
  else if k == ``Lean.Parser.timeCmd then
    if stx.getNumArgs == 2 then registerGuardedDeclNamespaces stx[1]
  else if k == ``Lean.Parser.Command.in then
    if stx.getNumArgs == 3 then
      if stx[0].getKind == ``Lean.Parser.Command.set_option then
        let secCmd ← `(Lean.Parser.Command.section| section)
        let endCmd ← `(Lean.Parser.Command.end| end)
        Lean.Elab.Command.elabSection secCmd.raw
        try
          Lean.Elab.Command.elabSetOption stx[0]
          registerGuardedDeclNamespaces stx[2]
        finally
          Lean.Elab.Command.elabEnd endCmd.raw
      else
        registerGuardedDeclNamespaces stx[0]
        registerGuardedDeclNamespaces stx[2]
  else if k == ``Lean.Parser.Command.mutual then
    if stx.getNumArgs >= 2 then
      let currNs ← getCurrNamespace
      let mut mTargets : NameSet := {}
      for child in stx[1].getArgs do
        if let some nm := collectDeclShortName? child then
          mTargets := addRecTargets mTargets currNs nm
      for child in stx[1].getArgs do
        registerDeclNamespaces child mTargets
  else
    pure ()

private partial def elabStage1CmdCore (baseTokTable : TokenTable) (stx : Syntax) : CommandElabM Unit := do
  let k := stx.getKind
  withRef stx <| withIncRecDepth <| withFreshMacroScope do
    if k == choiceKind then
      if let some builtinAlt := stx.getArgs.find? (·.getKind == ``Lean.Parser.Command.withWeakNamespace) then
        elabStage1CmdCore baseTokTable builtinAlt
      else if let some first := stx.getArgs[0]? then
        elabStage1CmdCore baseTokTable first
    else if k == ``Lean.Parser.Command.namespace then
      Lean.Elab.Command.elabNamespace stx
    else if k == ``Lean.Parser.Command.section then
      Lean.Elab.Command.elabSection stx
    else if k == ``Lean.Parser.Command.end then
      Lean.Elab.Command.elabEnd stx
    else if k == ``Lean.Parser.Command.open then
      elabOpenStage1 stx
    else if k == ``Lean.Parser.Command.set_option then
      Lean.Elab.Command.elabSetOption stx
    else if k == ``Lean.Parser.Command.unlock_limits then
      Lean.Elab.Command.elabUnlockLimits stx
    else if k == ``Lean.Parser.Command.notation then
      elabNotationStage1 baseTokTable stx
    else if k == ``Lean.Parser.Command.mixfix then
      elabMixfixStage1 baseTokTable stx
    else if isDeclCmdKind k then
      registerDeclNamespaces stx
    else if k == ``Lean.Parser.Command.mutual then
      if stx.getNumArgs >= 2 then
        let currNs ← getCurrNamespace
        let mut mTargets : NameSet := {}
        for child in stx[1].getArgs do
          if let some nm := collectDeclShortName? child then
            mTargets := addRecTargets mTargets currNs nm
        for child in stx[1].getArgs do
          if isDeclCmdKind child.getKind then
            registerDeclNamespaces child mTargets
          else
            elabStage1CmdCore baseTokTable child
    else if k == ``Lean.Parser.Command.in then
      if stx.getNumArgs == 3 then
        let secCmd ← `(Lean.Parser.Command.section| section)
        let endCmd ← `(Lean.Parser.Command.end| end)
        Lean.Elab.Command.elabSection secCmd.raw
        try
          elabStage1CmdCore baseTokTable stx[0]
          Lean.setDelimitsLocal 1
          elabStage1CmdCore baseTokTable stx[2]
        finally
          Lean.Elab.Command.elabEnd endCmd.raw
    else if k == ``Lean.Parser.Command.withWeakNamespace ||
            k == `Lean.Elab.Command.commandWith_weak_namespace__ then
      if stx.getNumArgs == 3 then
        withWeakNamespaceStage1 stx[1].getId (elabStage1CmdCore baseTokTable stx[2])
    else if k == `Mathlib.Tactic.scopedNS then
      if stx.getNumArgs == 7 then
        let ns := rootNamespace ++ stx[4].getId
        let inner := stx[6]
        let innerK := inner.getKind
        if innerK == ``Lean.Parser.Command.notation then
          withWeakNamespaceStage1 ns (elabNotationStage1 baseTokTable inner (forceScoped := true))
        else if innerK == ``Lean.Parser.Command.mixfix then
          withWeakNamespaceStage1 ns (elabMixfixStage1 baseTokTable inner (forceScoped := true))
        else if innerK == ``Lean.Parser.Command.attribute then
          withWeakNamespaceStage1 ns (pure ())
    else if k == ``Lean.Parser.Command.withExporting then
      if stx.getNumArgs >= 2 then elabStage1CmdCore baseTokTable stx[1]
    else if k == ``Lean.Parser.timeCmd then
      if stx.getNumArgs == 2 then elabStage1CmdCore baseTokTable stx[1]
    else if k == ``Lean.guardMsgsCmd then
      if stx.getNumArgs == 5 && !guardMsgsMayHideError stx then
        registerGuardedDeclNamespaces stx[4]
    else if k == ``Lean.infoTreesCmd then
      if stx.getNumArgs == 3 then
        registerGuardedDeclNamespaces stx[2]
    else
      -- `#guard_panic` and pure diagnostics MUST NOT mutate Stage 1 scope/notation/namespace state.
      pure ()

def scanFile (filePath : String) (baseEnv : Environment) : IO (Array String) := do
  let baseTokTable := Lean.Parser.getTokenTable baseEnv
  let input ← IO.FS.readFile filePath
  let inputCtx := Parser.mkInputContext input filePath
  let lines := (inputCtx.inputString.splitOn "\n").toArray
  let (_, parserState, headerMsgs) ← Parser.parseHeader inputCtx
  let mut violations : Array String := #[]
  for m in headerMsgs.toList do
    if m.severity == MessageSeverity.error then
      violations := violations.push s!"  {filePath}: parse error (header): {(← m.toString).trimAscii.toString}"
  if !violations.isEmpty then
    return violations
  let cmdCtx : Command.Context := {
    fileName := filePath
    fileMap := inputCtx.fileMap
    snap? := none
    cancelTk? := none
  }
  let mut cmdState := Command.mkState baseEnv MessageLog.empty {}
  let mut st := parserState
  let mut done := false
  while !done do
    let scope := cmdState.scopes.head!
    let pmctx : ParserModuleContext := {
      env := cmdState.env
      options := scope.opts
      currNamespace := scope.currNamespace
      openDecls := scope.openDecls
    }
    let (stx, st', msgs') := Parser.parseCommand inputCtx pmctx st MessageLog.empty
    for m in msgs'.toList do
      if m.severity == MessageSeverity.error then
        violations := violations.push s!"  {filePath}: parse error: {(← m.toString).trimAscii.toString}"
    let prevPos := st.pos
    st := st'
    -- Break cleanly ONLY on true EOI; `#exit` and mid-file `import` fall through and fail closed.
    if stx.getKind == ``Lean.Parser.Command.eoi then
      done := true
    else if st.pos == prevPos then
      let pos := inputCtx.fileMap.toPosition st.pos
      violations := violations.push s!"  {filePath}:{pos.line}: parse error: parser made no progress"
      done := true
    else
      let cmdLine := stxLine stx inputCtx.fileMap
      let snippet := if cmdLine > 0 && cmdLine - 1 < lines.size then (lines[cmdLine - 1]!).trimAscii.toString else ""
      let cmdErr? := checkAllowedCommand stx
      if let some err := cmdErr? then
        violations := violations.push s!"  {filePath}:{cmdLine}: {err}: {snippet}"
      let hits := findViolations stx inputCtx.fileMap #[]
      for (line, tok) in hits do
        let hitSnippet := if line > 0 && line - 1 < lines.size then (lines[line - 1]!).trimAscii.toString else ""
        violations := violations.push s!"  {filePath}:{line}: forbidden token '{tok}': {hitSnippet}"
      if cmdErr?.isNone && hits.isEmpty then
        let (elabRes, cmdState') ←
          match ← ((elabStage1CmdCore baseTokTable stx).run cmdCtx |>.run cmdState).toBaseIO with
          | .ok ((), st') =>
            if st'.messages.hasErrors then
              let mut errStrs : Array String := #[]
              for m in st'.messages.toList do
                if m.severity == MessageSeverity.error then
                  errStrs := errStrs.push (← m.toString).trimAscii.toString
              pure (Except.error (String.intercalate "; " errStrs.toList), { st' with messages := MessageLog.empty })
            else
              pure (Except.ok (), { st' with messages := MessageLog.empty })
          | .error ex =>
            let msg ← ex.toMessageData.toString
            pure (Except.error msg.trimAscii.toString, cmdState)
        cmdState := cmdState'
        if let .error err := elabRes then
          violations := violations.push s!"  {filePath}:{cmdLine}: stage 1 scope/notation error: {err}"
  if st.pos < inputCtx.inputString.rawEndPos && violations.isEmpty then
    let pos := inputCtx.fileMap.toPosition st.pos
    violations := violations.push s!"  {filePath}:{pos.line}: parse error: unconsumed trailing input"
  return violations

private def impKey (imp : Import) : String :=
  s!"{imp.module}|{imp.importAll}|{imp.isExported}|{imp.isMeta}"

private def canonicalizeImports (imps : Array Import) : String × Array Import := Id.run do
  let sorted := imps.qsort fun a b => impKey a < impKey b
  let mut dedup : Array Import := #[]
  let mut lastKey := ""
  for imp in sorted do
    let k := impKey imp
    if k != lastKey then
      dedup := dedup.push imp
      lastKey := k
  let key := String.intercalate ";" (dedup.map impKey).toList
  return (key, dedup)

unsafe def importEnvFor (repoRootStr : String) (imports : Array Import) : IO (Except String Environment) := do
  -- Guard untrusted local .oleans BEFORE enabling initializers or calling importModules!
  let isTrustedLoc ← mkIsTrustedLoc repoRootStr
  match ← preCheckImports isTrustedLoc imports with
  | .error err => return .error err
  | .ok () =>
    Lean.enableInitializersExecution
    try
      let e ← Lean.importModules imports {} (loadExts := true)
      -- Defense-in-depth: strip all untrusted-module entries from macro/elab KeyedDeclsAttributes.
      let e ← sanitizeImportedEnv isTrustedLoc e
      return .ok e
    catch ex =>
      return .error ex.toString

unsafe def scanBucket (repoRootStr : String) (imports : Array Import) (files : Array String) :
    IO (Array String) := do
  if files.isEmpty then return #[]
  match ← importEnvFor repoRootStr imports with
  | .error err =>
    return files.map fun f => s!"  {f}: import error: {err}"
  | .ok env =>
    let mut vs : Array String := #[]
    for f in files do
      vs := vs ++ (← scanFile f env)
    return vs

-- Hard output-path guard: refuse to write ANY file ending in `.lean` (case-insensitive),
-- any symlink / directory, or any path resolving to or inside `repoRootReal`.
private def assertSafeOutputPath (repoRootReal : System.FilePath) (rawPath : String) : IO Unit := do
  let trimmed := rawPath.trimAscii.toString
  if trimmed.isEmpty then
    throw <| IO.userError "refusing to write empty output path"
  if trimmed.toLower.endsWith ".lean" then
    throw <| IO.userError s!"refusing to write .lean output path: {rawPath}"
  let fp : System.FilePath := rawPath
  let metaOpt : Option IO.FS.Metadata ← try
    some <$> fp.symlinkMetadata
  catch _ =>
    pure none
  if let some md := metaOpt then
    if md.type == .symlink then
      throw <| IO.userError s!"refusing to write through symlink output path: {rawPath}"
    if md.type == .dir then
      throw <| IO.userError s!"refusing to write to directory output path: {rawPath}"
  let resolved : System.FilePath ←
    if metaOpt.isSome then
      IO.FS.realPath fp
    else
      match fp.fileName with
      | none =>
        throw <| IO.userError s!"refusing to write output path without filename: {rawPath}"
      | some fname =>
        if fname.isEmpty || fname == "." || fname == ".." || fname.toLower.endsWith ".lean" then
          throw <| IO.userError s!"refusing to write unsafe output filename: {rawPath}"
        let parent := fp.parent.getD "."
        let parentReal ← IO.FS.realPath parent
        pure (parentReal / fname)
  if resolved.toString.toLower.endsWith ".lean" then
    throw <| IO.userError s!"refusing to write resolved .lean output path: {resolved}"
  if resolved == repoRootReal || pathIsUnder resolved repoRootReal then
    throw <| IO.userError s!"refusing to write output path inside repository root ({repoRootReal}): {resolved}"

private def writeLines (repoRootReal : System.FilePath) (path : String) (lines : Array String) : IO Unit := do
  assertSafeOutputPath repoRootReal path
  if lines.isEmpty then
    IO.FS.writeFile path ""
  else
    IO.FS.writeFile path (String.intercalate "\n" lines.toList ++ "\n")

private def writeSentinel (repoRootReal : System.FilePath) (path : String) : IO Unit := do
  assertSafeOutputPath repoRootReal path
  IO.FS.writeFile path "OK\n"

private inductive CliCmd where
  | plan (repoRoot planOut violOut sentinel : String) (files : List String)
  | bucket (repoRoot violOut sentinel : String) (files : List String)

private def parseCliArgs (args : List String) : Except String CliCmd := do
  let (isPlan, rest) ← match args with
    | "--plan" :: r => pure (true, r)
    | "--bucket" :: r => pure (false, r)
    | _ => throw "expected --plan or --bucket"
  let mut repoRoot? : Option String := none
  let mut planOut? : Option String := none
  let mut violOut? : Option String := none
  let mut sentinel? : Option String := none
  let mut cur := rest
  let mut files? : Option (List String) := none
  while !cur.isEmpty && files?.isNone do
    match cur with
    | "--" :: fs =>
      files? := some fs
      cur := []
    | "--repo-root" :: v :: r =>
      if repoRoot?.isSome then throw "duplicate --repo-root"
      repoRoot? := some v
      cur := r
    | "--plan-out" :: v :: r =>
      if !isPlan then throw "--plan-out is only valid with --plan"
      if planOut?.isSome then throw "duplicate --plan-out"
      planOut? := some v
      cur := r
    | "--viol-out" :: v :: r =>
      if violOut?.isSome then throw "duplicate --viol-out"
      violOut? := some v
      cur := r
    | "--sentinel" :: v :: r =>
      if sentinel?.isSome then throw "duplicate --sentinel"
      sentinel? := some v
      cur := r
    | flag :: _ =>
      throw s!"unknown or incomplete option: {flag}"
    | [] => cur := []
  let some files := files? | throw "missing '-- <files...>' separator"
  if files.isEmpty then throw "empty file list after '--'"
  let some repoRoot := repoRoot? | throw "missing required --repo-root"
  let some violOut := violOut? | throw "missing required --viol-out"
  let some sentinel := sentinel? | throw "missing required --sentinel"
  if isPlan then
    let some planOut := planOut? | throw "missing required --plan-out"
    return .plan repoRoot planOut violOut sentinel files
  else
    return .bucket repoRoot violOut sentinel files

private def usageMsg : String :=
  "Usage:\n" ++
  "  Stage1Audit.lean --plan --repo-root <dir> --plan-out <path> --viol-out <path> --sentinel <path> -- <files...>\n" ++
  "  Stage1Audit.lean --bucket --repo-root <dir> --viol-out <path> --sentinel <path> -- <files...>"

unsafe def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  if let some s1DirStr ← IO.getEnv "VERIFY_AXIOMS_S1_MOD_DIR" then
    if !s1DirStr.isEmpty then
      let s1Real? ← try some <$> IO.FS.realPath s1DirStr catch _ => pure none
      let sp ← Lean.searchPathRef.get
      let mut filtered : SearchPath := []
      for p in sp do
        let pReal? ← try some <$> IO.FS.realPath p catch _ => pure none
        let isMatch :=
          p.toString == s1DirStr ||
          (match s1Real?, pReal? with | some a, some b => a == b | _, _ => false)
        if !isMatch then
          filtered := filtered ++ [p]
      Lean.searchPathRef.set filtered
  checkAllowedCoreExtsRegistered
  let cmd ← match parseCliArgs args with
    | .ok c => pure c
    | .error err =>
      IO.eprintln s!"Stage1Audit CLI error: {err}\n{usageMsg}"
      return 2
  match cmd with
  | .plan repoRootStr bucketsPath violationsPath sentinelPath files =>
    let repoRootReal ← try
      IO.FS.realPath repoRootStr
    catch ex =>
      IO.eprintln s!"Stage1Audit invalid --repo-root: {ex}"
      return 2
    try
      assertSafeOutputPath repoRootReal bucketsPath
      assertSafeOutputPath repoRootReal violationsPath
      assertSafeOutputPath repoRootReal sentinelPath
    catch ex =>
      IO.eprintln s!"Stage1Audit output path guard error: {ex}"
      return 2
    let mut buckets : Array (Array Import × Array Nat × Array String) := #[]
    let mut keyIdx : Std.HashMap String Nat := {}
    let mut violations : Array String := #[]
    let mut idx : Nat := 0
    for f in files do
      let input ← IO.FS.readFile f
      let inputCtx := Parser.mkInputContext input f
      let (header, _, msgs) ← Parser.parseHeader inputCtx
      let mut hdrErr := false
      for m in msgs.toList do
        if m.severity == MessageSeverity.error then
          hdrErr := true
          violations := violations.push s!"  {f}: parse error (header): {(← m.toString).trimAscii.toString}"
      if !hdrErr then
        let (key, normImps) := canonicalizeImports (Elab.headerToImports header)
        match keyIdx[key]? with
        | some bIdx =>
          let (imps, idxs, fs) := buckets[bIdx]!
          buckets := buckets.set! bIdx (imps, idxs.push idx, fs.push f)
        | none =>
          keyIdx := keyIdx.insert key buckets.size
          buckets := buckets.push (normImps, #[idx], #[f])
      idx := idx + 1
    if buckets.size <= 1 then
      -- Fast path: 0 or 1 unique import bucket runs inline with zero extra process startup.
      if h : buckets.size = 1 then
        let (normImps, _, fs) := buckets[0]
        violations := violations ++ (← scanBucket repoRootStr normImps fs)
      writeLines repoRootReal bucketsPath #[]
      writeLines repoRootReal violationsPath violations
      writeSentinel repoRootReal sentinelPath
      return if violations.isEmpty then 0 else 1
    else
      -- Multi-bucket path: emit 0-based index lines so each bucket runs in a fresh OS process
      -- (keeps peak RSS bounded <= 4.2 GiB regardless of bucket count and prevents UAF/OOM).
      let bucketLines := buckets.map fun (_, idxs, _) =>
        String.intercalate " " (idxs.map toString).toList
      writeLines repoRootReal bucketsPath bucketLines
      writeLines repoRootReal violationsPath violations
      writeSentinel repoRootReal sentinelPath
      return 0
  | .bucket repoRootStr violationsPath sentinelPath files =>
    let repoRootReal ← try
      IO.FS.realPath repoRootStr
    catch ex =>
      IO.eprintln s!"Stage1Audit invalid --repo-root: {ex}"
      return 2
    try
      assertSafeOutputPath repoRootReal violationsPath
      assertSafeOutputPath repoRootReal sentinelPath
    catch ex =>
      IO.eprintln s!"Stage1Audit output path guard error: {ex}"
      return 2
    let mut violations : Array String := #[]
    let mut expectedKey? : Option (String × Array Import) := none
    let mut validFiles : Array String := #[]
    for f in files do
      let input ← IO.FS.readFile f
      let inputCtx := Parser.mkInputContext input f
      let (header, _, msgs) ← Parser.parseHeader inputCtx
      let mut hdrErr := false
      for m in msgs.toList do
        if m.severity == MessageSeverity.error then
          hdrErr := true
          violations := violations.push s!"  {f}: parse error (header): {(← m.toString).trimAscii.toString}"
      if !hdrErr then
        let (key, normImps) := canonicalizeImports (Elab.headerToImports header)
        match expectedKey? with
        | none =>
          expectedKey? := some (key, normImps)
          validFiles := validFiles.push f
        | some (ek, _) =>
          if key != ek then
            violations := violations.push s!"  {f}: internal error: mismatched bucket import set"
          else
            validFiles := validFiles.push f
    if let some (_, normImps) := expectedKey? then
      violations := violations ++ (← scanBucket repoRootStr normImps validFiles)
    writeLines repoRootReal violationsPath violations
    writeSentinel repoRootReal sentinelPath
    return if violations.isEmpty then 0 else 1
STAGE1_LEAN

STAGE1_RUNNER="$TMP_DIR/run_stage1.sh"
cat > "$STAGE1_RUNNER" <<'STAGE1_SH'
#!/usr/bin/env bash
set -euo pipefail

STAGE1_FILE="$1"
REPO_ROOT_REAL="$2"
WORK_DIR="$3"
shift 3
FILES=("$@")

BUCKETS_FILE="$WORK_DIR/stage1_buckets.txt"
VIOL_FILE="$WORK_DIR/stage1_violations.txt"
PLAN_SENTINEL="$WORK_DIR/stage1_plan.sentinel"
: > "$BUCKETS_FILE"
: > "$VIOL_FILE"
rm -f "$PLAN_SENTINEL"

STAGE1_RUN_FILE="$STAGE1_FILE"
if [ "${#FILES[@]}" -gt 1 ]; then
  S1_MOD_DIR="$WORK_DIR/s1mod"
  S1_MOD_NAME="__VerifyAxiomsStage1Internal_$$"
  mkdir -p "$S1_MOD_DIR"
  cp "$STAGE1_FILE" "$S1_MOD_DIR/${S1_MOD_NAME}.lean"
  lean -R "$S1_MOD_DIR" -o "$S1_MOD_DIR/${S1_MOD_NAME}.olean" \
    "$S1_MOD_DIR/${S1_MOD_NAME}.lean"
  printf 'import %s\n' "$S1_MOD_NAME" > "$WORK_DIR/Stage1Driver.lean"
  export LEAN_PATH="$S1_MOD_DIR${LEAN_PATH:+:$LEAN_PATH}"
  export VERIFY_AXIOMS_S1_MOD_DIR="$S1_MOD_DIR"
  STAGE1_RUN_FILE="$WORK_DIR/Stage1Driver.lean"
fi

plan_rc=0
lean --run "$STAGE1_RUN_FILE" --plan \
  --repo-root "$REPO_ROOT_REAL" \
  --plan-out "$BUCKETS_FILE" \
  --viol-out "$VIOL_FILE" \
  --sentinel "$PLAN_SENTINEL" \
  -- "${FILES[@]}" || plan_rc=$?

if [ ! -f "$PLAN_SENTINEL" ] || [ "$(cat "$PLAN_SENTINEL")" != "OK" ]; then
  : > "$BUCKETS_FILE"
  echo "STATIC HYGIENE INTERNAL ERROR: Stage 1 exited without completion sentinel (plan, exit code $plan_rc)" >&2
  exit 1
fi

if [ "$plan_rc" -ne 0 ]; then
  : > "$BUCKETS_FILE"
  if [ ! -s "$VIOL_FILE" ]; then
    echo "  (stage1-plan): internal Stage 1 error (exit code $plan_rc)" >> "$VIOL_FILE"
  fi
fi

bidx=0
while IFS= read -r line; do
  [ -z "$line" ] && continue
  bidx=$((bidx + 1))
  bfiles=()
  for idx in $line; do
    bfiles+=("${FILES[$idx]}")
  done
  berr="$WORK_DIR/stage1_bucket_${bidx}.err"
  bsent="$WORK_DIR/stage1_bucket_${bidx}.sentinel"
  : > "$berr"
  rm -f "$bsent"
  brc=0
  lean --run "$STAGE1_RUN_FILE" --bucket \
    --repo-root "$REPO_ROOT_REAL" \
    --viol-out "$berr" \
    --sentinel "$bsent" \
    -- "${bfiles[@]}" || brc=$?
  if [ ! -f "$bsent" ] || [ "$(cat "$bsent")" != "OK" ]; then
    echo "STATIC HYGIENE INTERNAL ERROR: Stage 1 exited without completion sentinel (bucket ${bidx}, exit code $brc)" >&2
    exit 1
  fi
  if [ -s "$berr" ]; then
    cat "$berr" >> "$VIOL_FILE"
  elif [ "$brc" -ne 0 ]; then
    echo "  (stage1-bucket-${bidx}): internal Stage 1 error (exit code $brc)" >> "$VIOL_FILE"
  fi
done < "$BUCKETS_FILE"

if [ -s "$VIOL_FILE" ]; then
  echo "STATIC HYGIENE CHECK FAILED:" >&2
  cat "$VIOL_FILE" >&2
  exit 1
fi

echo "STATIC HYGIENE PASSED: 0 forbidden tokens across ${#FILES[@]} file(s)."
STAGE1_SH

LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" lake env bash "$STAGE1_RUNNER" "$STAGE1_FILE" "$REPO_ROOT_REAL" "$TMP_DIR" "${FILES[@]}"

if [ "${#EXTERNAL_FILES[@]}" -gt 0 ]; then
  for ef in "${EXTERNAL_FILES[@]}"; do
    echo "ERROR: File is outside repository root ($REPO_ROOT): $ef" >&2
  done
  exit 1
fi

echo "=== [2/3] Verifying compiled .olean freshness ==="
if ! LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" lake build --no-build "${MODS[@]}"; then
  echo "ERROR: One or more target modules are missing or stale .oleans." >&2
  echo "Run 'lake build ${MODS[*]}' first (or re-run with --build)." >&2
  exit 1
fi

echo "=== [3/3] True Lean 4 kernel replay & axiom audit (${#MODS[@]} module(s)) ==="
STAGE3A_FILE="$TMP_DIR/Stage3Replay.lean"
STAGE3B_FILE="$TMP_DIR/Stage3Partial.lean"
PARTIAL_MANIFEST="$TMP_DIR/partial_manifest.txt"
SUMMARY_FILE="$TMP_DIR/stage3_summary.txt"

cat > "$STAGE3A_FILE" <<'STAGE3A_LEAN'
import Lean
import Lean.Replay

open Lean

private def pathIsUnder (child parent : System.FilePath) : Bool :=
  let c := child.toString
  let p := parent.toString
  let pSlash := if p.endsWith "/" then p else p ++ "/"
  c.startsWith pSlash

private def parseModName (s : String) : Name :=
  s.splitOn "." |>.foldl (init := Name.anonymous) fun acc part =>
    Name.mkStr acc part

private def readModDataAll (modName : Name) : IO (ModuleData × Array ModuleData × Array CompactedRegion) := do
  let mFile ← Lean.findOLean modName
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {modName} does not exist"
  let (mainData, mainReg) ← Lean.readModuleData mFile
  if !mainData.isModule then
    let mut allParts := #[mainData]
    let mut allRegs := #[mainReg]
    let irFile := mFile.withExtension "ir"
    if (← irFile.pathExists) then
      let (irData, irReg) ← Lean.readModuleData irFile
      allParts := allParts.push irData
      allRegs := allRegs.push irReg
    return (mainData, allParts, allRegs)
  let sFile := OLeanLevel.server.adjustFileName mFile
  let pFile := OLeanLevel.private.adjustFileName mFile
  let parts ← Lean.readModuleDataParts #[mFile, sFile, pFile]
  let mut allParts := parts.map (·.1)
  let mut allRegs := parts.map (·.2)
  let irFile := mFile.withExtension "ir"
  if (← irFile.pathExists) then
    let (irData, irReg) ← Lean.readModuleData irFile
    allParts := allParts.push irData
    allRegs := allRegs.push irReg
  match parts[2]? with
  | some (privData, _) => return (privData, allParts, allRegs)
  | none => throw <| IO.userError s!"missing .olean.private part for module {modName}"

private structure AxiomCache where
  cache : Std.HashMap Name (Array Name) := {}

private partial def collectAxiomsDFS
    (kenv : Kernel.Environment)
    (c : Name)
    (depth : Nat)
    (visiting : Std.HashMap Name Nat) : StateRefT AxiomCache IO (Array Name × Nat) := do
  if let some axs := (← get).cache[c]? then
    return (axs, depth + 1)
  if let some ancDepth := visiting[c]? then
    return (#[], ancDepth)
  let visiting' := visiting.insert c depth
  let mut accSet : NameSet := {}
  let mut minD : Nat := depth + 1
  let visitExpr (e : Expr) (acc0 : NameSet) (m0 : Nat) : StateRefT AxiomCache IO (NameSet × Nat) := do
    let mut acc := acc0
    let mut m := m0
    for dep in e.getUsedConstants do
      let (dAxs, dMin) ← collectAxiomsDFS kenv dep (depth + 1) visiting'
      for ax in dAxs do
        acc := acc.insert ax
      if dMin < m then m := dMin
    return (acc, m)
  match kenv.find? c with
  | some (.axiomInfo v) =>
    accSet := accSet.insert c
    let (a1, m1) ← visitExpr v.type accSet minD
    accSet := a1; minD := m1
  | some (.defnInfo v) =>
    let (a1, m1) ← visitExpr v.type accSet minD
    let (a2, m2) ← visitExpr v.value a1 m1
    accSet := a2; minD := m2
  | some (.thmInfo v) =>
    let (a1, m1) ← visitExpr v.type accSet minD
    let (a2, m2) ← visitExpr v.value a1 m1
    accSet := a2; minD := m2
  | some (.opaqueInfo v) =>
    let (a1, m1) ← visitExpr v.type accSet minD
    let (a2, m2) ← visitExpr v.value a1 m1
    accSet := a2; minD := m2
  | some (.quotInfo _) => pure ()
  | some (.ctorInfo v) =>
    let (a1, m1) ← visitExpr v.type accSet minD
    accSet := a1; minD := m1
  | some (.recInfo v) =>
    let (a1, m1) ← visitExpr v.type accSet minD
    accSet := a1; minD := m1
  | some (.inductInfo v) =>
    let (a1, m1) ← visitExpr v.type accSet minD
    accSet := a1; minD := m1
    for ctor in v.ctors do
      let (dAxs, dMin) ← collectAxiomsDFS kenv ctor (depth + 1) visiting'
      for ax in dAxs do accSet := accSet.insert ax
      if dMin < minD then minD := dMin
  | none => pure ()
  let resArr := accSet.toArray.qsort Name.lt
  if minD >= depth then
    modify fun s => { s with cache := s.cache.insert c resArr }
  return (resArr, minD)

private def collectExprAxioms
    (kenv : Kernel.Environment) (e : Expr) : StateRefT AxiomCache IO (Array Name) := do
  let mut accSet : NameSet := {}
  for dep in e.getUsedConstants do
    let (dAxs, _) ← collectAxiomsDFS kenv dep 0 {}
    for ax in dAxs do
      accSet := accSet.insert ax
  return accSet.toArray.qsort Name.lt

private def isBRecNameKernel (kenv : Kernel.Environment) (u : Name) : Bool :=
  match u with
  | .str ind s =>
    (s == "brecOn" || s.startsWith "brecOn_" ||
     s == "below" || s.startsWith "below_" ||
     s == "binductionOn") &&
    (kenv.find? ind matches some (.inductInfo _))
  | _ => false

private def isKernelRecConst (kenv : Kernel.Environment) (u : Name) : Bool :=
  u == ``WellFounded.fix || u == ``WellFounded.fixF ||
  u == ``WellFounded.Nat.fix ||
  u == ``Lean.Order.fix || u == ``Lean.Order.lfp_monotone ||
  isBRecNameKernel kenv u

private def hasKernelRecCombinator
    (kenv : Kernel.Environment)
    (modConsts : NameSet)
    (rootVal : Expr) : Bool := Id.run do
  let mut queue := rootVal.getUsedConstants
  let mut seen : NameSet := {}
  for _ in [:4] do
    let mut nextQ : Array Name := #[]
    for u in queue do
      if !seen.contains u then
        seen := seen.insert u
        match kenv.find? u with
        | some (.recInfo _) => return true
        | some (.defnInfo du) =>
          if isKernelRecConst kenv u then
            return true
          else if modConsts.contains u then
            nextQ := nextQ ++ du.value.getUsedConstants
        | some (.thmInfo tu) =>
          if isKernelRecConst kenv u then
            return true
          else if modConsts.contains u then
            nextQ := nextQ ++ tu.value.getUsedConstants
        | _ => pure ()
    queue := nextQ
  return false

private def constInfoEq (a b : ConstantInfo) : Bool :=
  match a, b with
  | .axiomInfo x, .axiomInfo y =>
    x.name == y.name && x.levelParams == y.levelParams && x.type == y.type && x.isUnsafe == y.isUnsafe
  | .defnInfo x, .defnInfo y =>
    x.name == y.name && x.levelParams == y.levelParams && x.type == y.type &&
    x.value == y.value && x.hints == y.hints && x.safety == y.safety && x.all == y.all
  | .thmInfo x, .thmInfo y =>
    x.name == y.name && x.levelParams == y.levelParams && x.type == y.type &&
    x.value == y.value && x.all == y.all
  | .opaqueInfo x, .opaqueInfo y =>
    x.name == y.name && x.levelParams == y.levelParams && x.type == y.type &&
    x.value == y.value && x.isUnsafe == y.isUnsafe && x.all == y.all
  | .quotInfo x, .quotInfo y =>
    x.name == y.name && x.levelParams == y.levelParams && x.type == y.type &&
    (match x.kind, y.kind with
     | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
     | _, _ => false)
  | .inductInfo x, .inductInfo y =>
    x.name == y.name && x.levelParams == y.levelParams && x.type == y.type &&
    x.numParams == y.numParams && x.numIndices == y.numIndices &&
    x.all == y.all && x.ctors == y.ctors && x.numNested == y.numNested &&
    x.isRec == y.isRec && x.isUnsafe == y.isUnsafe && x.isReflexive == y.isReflexive
  | .ctorInfo x, .ctorInfo y => x == y
  | .recInfo x, .recInfo y => x == y
  | _, _ => false

private def exportPartConsistent (partMap : Std.HashMap Name ConstantInfo) (pinfo privInfo : ConstantInfo) : Bool :=
  if constInfoEq pinfo privInfo then
    true
  else
    match pinfo with
    | .axiomInfo ax =>
      !ax.isUnsafe &&
      !Lean.isPrivateName ax.name &&
      ax.name == privInfo.name &&
      ax.levelParams == privInfo.levelParams &&
      ax.type == privInfo.type &&
      match privInfo with
      | .thmInfo _ => true
      | .defnInfo d =>
        if d.safety == .safe then true
        else if d.safety == .partial then
          match Lean.Compiler.isUnsafeRecName? d.name with
          | some base =>
            -- Lean v4.32.2 (AddDecl.lean:116-120) legitimately exports non-@[expose] public recursive
            -- `._unsafe_rec` helpers as `.axiomInfo` in parts[0]/parts[1] iff `base` itself is also
            -- exported as a non-unsafe `.axiomInfo` (non-exposed) in the same part.
            match partMap[base]? with
            | some (.axiomInfo bax) => !bax.isUnsafe
            | _ => false
          | none => false
        else false
      | .opaqueInfo op => !op.isUnsafe
      | _ => false
    | _ => false

private def hasNonEmptyExtEntry (parts : Array ModuleData) (extName : Name) : Bool :=
  parts.any fun md =>
    md.entries.any fun (n, arr) => n == extName && !arr.isEmpty

private partial def mkFreshAuditName (kenv : Kernel.Environment) (base : Name) (tag : String) : Name :=
  go (Name.mkStr base tag)
where
  go (cand : Name) : Name :=
    if (kenv.find? cand).isSome then
      go (Name.mkStr cand "_x")
    else
      cand

private structure BFSState where
  visited : NameSet := {}
  replaySet : NameSet := {}
  replayDataMap : Std.HashMap Name ModuleData := {}
  replayAllParts : Std.HashMap Name (Array ModuleData) := {}
  replayOrder : Array Name := #[]
  baseImportSet : NameSet := {}
  baseImports : Array Import := #[]
  keptRegions : Array CompactedRegion := #[]

private partial def bfsVisit
    (targetSet : NameSet)
    (isTrustedLoc : Name → IO Bool)
    (modName : Name) : StateRefT BFSState IO Unit := do
  if (← get).visited.contains modName then return
  modify fun s => { s with visited := s.visited.insert modName }
  let trusted ← isTrustedLoc modName
  if targetSet.contains modName || !trusted then
    modify fun s => { s with replaySet := s.replaySet.insert modName }
    let (modData, allParts, regs) ← readModDataAll modName
    modify fun s => { s with keptRegions := s.keptRegions ++ regs }
    for imp in modData.imports do
      bfsVisit targetSet isTrustedLoc imp.module
    modify fun s => { s with
      replayDataMap := s.replayDataMap.insert modName modData
      replayAllParts := s.replayAllParts.insert modName allParts
      replayOrder := s.replayOrder.push modName
    }
  else
    if !(← get).baseImportSet.contains modName then
      modify fun s => { s with
        baseImportSet := s.baseImportSet.insert modName
        baseImports := s.baseImports.push { module := modName }
      }

private def getBaseSafeInfo (kenv : Kernel.Environment) (base : Name) :
    Option (List Name × Expr × Expr × List Name) :=
  match kenv.find? base with
  | some (.defnInfo d) =>
    if d.safety == .safe then some (d.levelParams, d.type, d.value, d.all) else none
  | some (.thmInfo t) =>
    some (t.levelParams, t.type, t.value, t.all)
  | _ => none

private def runPhase3A (args : List String) : IO Unit := do
  let sysroot ← Lean.findSysroot
  Lean.initSearchPath sysroot
  let sysrootLibReal ← IO.FS.realPath (← Lean.getLibDir sysroot)

  let (repoRootStr, verbose, manifestPath, summaryPath, modStrs) ←
    match args with
    | r :: v :: mf :: sf :: ms => pure (r, v == "1" || v == "true", mf, sf, ms)
    | _ => throw <| IO.userError "Usage: Stage3Replay.lean <repoRoot> <verbose:0|1> <manifest> <summary> <mod>..."
  if modStrs.isEmpty then
    throw <| IO.userError "AXIOM AUDIT FAILED: no target modules provided"

  let repoRoot : System.FilePath := repoRootStr
  let packagesDir := repoRoot / ".lake" / "packages"
  let packagesDirReal? ←
    if (← packagesDir.pathExists) then some <$> IO.FS.realPath packagesDir else pure none

  let targetMods := modStrs.toArray.map parseModName
  let targetSet : NameSet := targetMods.foldl (init := {}) fun s m => s.insert m
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

  let isTrustedLoc (modName : Name) : IO Bool := do
    let oleanPath ← Lean.findOLean modName
    let oleanReal ← IO.FS.realPath oleanPath
    return pathIsUnder oleanReal sysrootLibReal ||
      (match packagesDirReal? with
       | some pkgReal => pathIsUnder oleanReal pkgReal
       | none => false)

  let (_, bfs) ← (for m in targetMods do bfsVisit targetSet isTrustedLoc m).run {}

  let baseEnv ←
    if bfs.baseImports.isEmpty then
      Lean.mkEmptyEnvironment (trustLevel := 0)
    else
      Lean.importModules bfs.baseImports {} (trustLevel := 0) (loadExts := false)

  for idx in [:baseEnv.header.modules.size] do
    let bMod := baseEnv.header.modules[idx]!.module
    if bfs.replaySet.contains bMod then
      throw <| IO.userError s!"AXIOM AUDIT FAILED: replay module '{bMod}' leaked into trusted base environment"
    if !(← isTrustedLoc bMod) then
      throw <| IO.userError s!"AXIOM AUDIT FAILED: untrusted module '{bMod}' found in base environment"

  let mut replayMap : Std.HashMap Name ConstantInfo := {}
  let mut dupTheorems : Array (Name × TheoremVal) := #[]
  let mut violations : Array String := #[]

  for m in bfs.replayOrder do
    let md : ModuleData := bfs.replayDataMap[m]!
    let allParts := bfs.replayAllParts[m]!
    if md.constNames.size != md.constants.size then
      violations := violations.push s!"[{m}] corrupt .olean: constNames.size ({md.constNames.size}) != constants.size ({md.constants.size})"
    if hasNonEmptyExtEntry allParts `Lean.Compiler.implementedByAttr then
      violations := violations.push s!"[{m}] module contains @[implemented_by] attribute"
    if hasNonEmptyExtEntry allParts `Lean.externAttr then
      violations := violations.push s!"[{m}] module contains @[extern] attribute"
    if hasNonEmptyExtEntry allParts `Lean.regularInitAttr ||
       hasNonEmptyExtEntry allParts `Lean.builtinInitAttr then
      violations := violations.push s!"[{m}] module contains @[init] / initialize hook"
    let mut modPrivMap : Std.HashMap Name ConstantInfo := {}
    for cname in md.constNames, cinfo in md.constants do
      modPrivMap := modPrivMap.insert cname cinfo
    for partIdx in [:allParts.size] do
      let part := allParts[partIdx]!
      if part.constNames.size != part.constants.size then
        violations := violations.push s!"[{m}] corrupt module part #{partIdx}: constNames.size ({part.constNames.size}) != constants.size ({part.constants.size})"
      for imp in part.imports do
        if !md.imports.any (fun pi => pi.module == imp.module) then
          violations := violations.push s!"[{m}] module part #{partIdx} has import '{imp.module}' absent from private/main part"
      let mut partMap : Std.HashMap Name ConstantInfo := {}
      let mut seenPartConsts : NameSet := {}
      for pcname in part.constNames, pinfo in part.constants do
        if seenPartConsts.contains pcname then
          violations := violations.push s!"[{m}] corrupt module part #{partIdx}: duplicate constant '{pcname}'"
        seenPartConsts := seenPartConsts.insert pcname
        partMap := partMap.insert pcname pinfo
      for pcname in part.constNames, pinfo in part.constants do
        if pcname != pinfo.name then
          violations := violations.push s!"[{m}] corrupt module part #{partIdx}: constName '{pcname}' != cinfo.name '{pinfo.name}'"
        match modPrivMap[pcname]? with
        | none =>
          violations := violations.push s!"[{m}] module part #{partIdx} exports constant '{pcname}' absent from private/main part"
        | some privInfo =>
          if !exportPartConsistent partMap pinfo privInfo then
            violations := violations.push s!"[{m}] module part #{partIdx} constant '{pcname}' inconsistent with private/main part"
    for cname in md.constNames, cinfo in md.constants do
      if cname != cinfo.name then
        violations := violations.push s!"[{m}] corrupt .olean: constName '{cname}' != cinfo.name '{cinfo.name}'"
      if cinfo.isUnsafe then
        violations := violations.push s!"[{m}] unsafe declaration: {cname}"
      match cinfo with
      | .axiomInfo _ =>
        violations := violations.push s!"[{m}] custom axiom declared: {cname}"
      | .quotInfo _ =>
        violations := violations.push s!"[{m}] illegal quotient declaration: {cname}"
      | _ => pure ()
      if let some prev := replayMap[cname]? then
        match prev, cinfo with
        | .thmInfo t1, .thmInfo t2 =>
          if t1.name == t2.name && t1.levelParams == t2.levelParams &&
             t1.type == t2.type && t1.all == t2.all then
            dupTheorems := dupTheorems.push (m, t2)
          else
            violations := violations.push s!"[{m}] conflicting duplicate declaration: {cname}"
        | _, _ =>
          violations := violations.push s!"[{m}] duplicate non-theorem declaration: {cname}"
      else
        replayMap := replayMap.insert cname cinfo

  for (cname, cinfo) in replayMap.toList do
    if let .inductInfo iv := cinfo then
      if iv.all.isEmpty then
        violations := violations.push s!"malformed inductive '{cname}': empty 'all' list"
      for al in iv.all do
        match replayMap[al]? with
        | some (.inductInfo aiv) =>
          for ctor in aiv.ctors do
            match replayMap[ctor]? with
            | some (.ctorInfo _) => pure ()
            | _ => violations := violations.push s!"malformed inductive '{cname}': missing ctor '{ctor}'"
        | _ => violations := violations.push s!"malformed inductive '{cname}': missing mutual inductive '{al}'"

  if !violations.isEmpty then
    let msg := String.intercalate "\n" violations.toList
    throw <| IO.userError s!"AXIOM AUDIT FAILED ({violations.size} pre-replay violation(s)):\n{msg}"

  let replayedEnv ←
    try
      Lean.Environment.replay replayMap baseEnv
    catch ex =>
      throw <| IO.userError s!"AXIOM AUDIT FAILED (Lean kernel replay rejected declaration):\n  {ex}"

  let kenv := replayedEnv.toKernelEnv

  let ((checkedCount, publicThmCount, partialModStrs, expectedPartialCount, postViolations), _) ←
    StateRefT'.run (s := ({} : AxiomCache)) do
      let mut checkedCount : Nat := 0
      let mut publicThmCount : Nat := 0
      let mut partialModSet : Std.HashSet String := {}
      let mut partialModStrs : Array String := #[]
      let mut expectedPartialCount : Nat := 0
      let mut postViolations : Array String := #[]

      for (m, t2) in dupTheorems do
        let verifyDecl := Declaration.thmDecl { t2 with name := mkFreshAuditName kenv t2.name "_audit_dup_verify" }
        match kenv.addDeclCore 0 verifyDecl none with
        | .error ex =>
          let exStr ← (ex.toMessageData {}).toString
          postViolations := postViolations.push s!"[{m}] duplicate theorem '{t2.name}' failed kernel check: {exStr}"
        | .ok _ => pure ()
        let valAxs ← collectExprAxioms kenv t2.value
        let bad := valAxs.filter fun ax => !allowed.contains ax
        if !bad.isEmpty then
          postViolations := postViolations.push s!"[{m}] duplicate theorem '{t2.name}' uses disallowed axioms: {bad.toList}"

      for m in bfs.replayOrder do
        let md : ModuleData := bfs.replayDataMap[m]!
        let allParts := bfs.replayAllParts[m]!
        let isTarget := targetSet.contains m
        let modConsts : NameSet := md.constNames.foldl (init := {}) fun s n => s.insert n
        let modHasRecExt := hasNonEmptyExtEntry allParts `recExt

        for cname in md.constNames, cinfo in md.constants do
          if isTarget then
            checkedCount := checkedCount + 1
          if cinfo.isPartial then
            let mut partialOk := false
            let mut reason := "not a compiler-generated recursive helper"
            match cinfo, Lean.Compiler.isUnsafeRecName? cname with
            | .defnInfo u, some base =>
              if u.safety != .partial then
                reason := s!"unexpected safety on '{cname}'"
              else if !(u.hints matches .opaque) then
                reason := s!"reducibility hints on '{cname}' must be opaque"
              else if !modConsts.contains base then
                reason := s!"base '{base}' not declared in same module '{m}'"
              else if !modHasRecExt then
                reason := s!"module '{m}' has no recursive definitions in recExt"
              else
                match getBaseSafeInfo kenv base with
                | none =>
                  reason := s!"base '{base}' is not a safe kernel definition/theorem (likely a `partial def`)"
                | some (bLevels, bType, bVal, bAll) =>
                  if bAll.isEmpty || !bAll.contains base || !u.all.contains cname then
                    reason := s!"invalid mutual clique membership for '{cname}' / '{base}'"
                  else if u.all != bAll.map Lean.Compiler.mkUnsafeRecName then
                    reason := s!"mutual block mismatch: u.all = {u.all} vs base.all = {bAll}"
                  else if u.levelParams != bLevels then
                    reason := s!"levelParams mismatch between '{cname}' and '{base}'"
                  else if !(match Lean.Kernel.isDefEq replayedEnv {} u.type bType with | .ok true => true | _ => false) then
                    reason := s!"type mismatch between '{cname}' and '{base}'"
                  else if !u.all.any (fun a => u.value.getUsedConstants.contains a) then
                    reason := s!"body of '{cname}' makes no recursive call to {u.all}"
                  else if !hasKernelRecCombinator kenv modConsts bVal then
                    reason := s!"base '{base}' body contains no kernel recursion combinator"
                  else
                    let mut allValid := true
                    let mut substMap : Std.HashMap Name Name := {}
                    for alBase in bAll do
                      if modConsts.contains alBase && (getBaseSafeInfo kenv alBase).isSome then
                        substMap := substMap.insert (Lean.Compiler.mkUnsafeRecName alBase) alBase
                      else
                        allValid := false
                    if !allValid then
                      reason := s!"invalid mutual base clique bAll = {bAll}"
                    else
                      let uValSubst := u.value.replace fun e =>
                        match e with
                        | .const n ls => (substMap[n]?).map (mkConst · ls)
                        | _ => none
                      let mut hasBadRef := false
                      for used in u.type.getUsedConstants ++ uValSubst.getUsedConstants do
                        if let some uinfo := replayMap[used]? then
                          if uinfo.isPartial || uinfo.isUnsafe then
                            hasBadRef := true
                      if hasBadRef then
                        reason := s!"type or substituted body references partial/unsafe constant"
                      else
                        let checkDecl := Declaration.defnDecl {
                          name := mkFreshAuditName kenv cname "_audit_verify"
                          levelParams := u.levelParams
                          type := u.type
                          value := uValSubst
                          hints := .opaque
                          safety := .safe
                        }
                        match kenv.addDeclCore 0 checkDecl none with
                        | .error ex =>
                          let exStr ← (ex.toMessageData {}).toString
                          reason := s!"substituted body failed kernel typecheck: {exStr}"
                        | .ok _ =>
                          let tAxs ← collectExprAxioms kenv u.type
                          let uAxs ← collectExprAxioms kenv uValSubst
                          let bad := (tAxs ++ uAxs).filter fun ax => !allowed.contains ax
                          if !bad.isEmpty then
                            reason := s!"type or body depends on disallowed axioms: {bad.toList}"
                          else
                            partialOk := true
            | _, _ => pure ()
            if !partialOk then
              postViolations := postViolations.push s!"[{m}] partial declaration '{cname}': {reason}"
            else
              expectedPartialCount := expectedPartialCount + 1
              let mStr := m.toString
              if !partialModSet.contains mStr then
                partialModSet := partialModSet.insert mStr
                partialModStrs := partialModStrs.push mStr
          else
            match kenv.find? cname with
            | none =>
              postViolations := postViolations.push s!"[{m}] constant missing after kernel replay: {cname}"
            | some rinfo =>
              if rinfo.name != cinfo.name || rinfo.levelParams != cinfo.levelParams || rinfo.type != cinfo.type then
                postViolations := postViolations.push s!"[{m}] replayed signature mismatch on: {cname}"
              if let some (.thmInfo _) := baseEnv.toKernelEnv.find? cname then
                if let .thmInfo tinfo := cinfo then
                  let checkDecl := Declaration.thmDecl { tinfo with name := mkFreshAuditName kenv cname "_audit_basedup_verify" }
                  match kenv.addDeclCore 0 checkDecl none with
                  | .error ex =>
                    let exStr ← (ex.toMessageData {}).toString
                    postViolations := postViolations.push s!"[{m}] base-duplicate theorem '{cname}' failed kernel check: {exStr}"
                  | .ok _ =>
                    let valAxs ← collectExprAxioms kenv tinfo.value
                    let bad := valAxs.filter fun ax => !allowed.contains ax
                    if !bad.isEmpty then
                      postViolations := postViolations.push s!"[{m}] base-duplicate theorem '{cname}' uses disallowed axioms: {bad.toList}"
              let (axs, _) ← collectAxiomsDFS kenv cname 0 {}
              let disallowed := axs.filter fun ax => !allowed.contains ax
              if !disallowed.isEmpty then
                postViolations := postViolations.push s!"[{m}] {cname} depends on disallowed axioms: {disallowed.toList}"
              if isTarget && !cname.isInternalDetail then
                if let .thmInfo _ := rinfo then
                  publicThmCount := publicThmCount + 1
                  if verbose then
                    IO.println s!"  '{cname}' depends on axioms: {axs.toList}"
      return (checkedCount, publicThmCount, partialModStrs, expectedPartialCount, postViolations)

  let _ := bfs.keptRegions.size
  if checkedCount == 0 then
    throw <| IO.userError "AXIOM AUDIT FAILED: 0 declarations audited!"
  if !postViolations.isEmpty then
    let msg := String.intercalate "\n" postViolations.toList
    throw <| IO.userError s!"AXIOM AUDIT FAILED ({postViolations.size} violation(s) across {checkedCount} target declarations):\n{msg}"

  let manifestLines := #[toString expectedPartialCount] ++ partialModStrs
  IO.FS.writeFile manifestPath (String.intercalate "\n" manifestLines.toList ++ "\n")

  let replayNote :=
    if bfs.replayOrder.size > targetMods.size then
      s!" (replayed {bfs.replayOrder.size} local module(s), {replayMap.size} constants)"
    else
      s!" (kernel-replayed {replayMap.size} constants)"
  let summary := s!"AXIOM AUDIT PASSED: {checkedCount} total declarations ({publicThmCount} public theorems) across {targetMods.size} module(s){replayNote}; axioms ⊆ {allowed.toList}"
  IO.FS.writeFile summaryPath (summary ++ "\n")

def main (args : List String) : IO Unit := do
  try
    runPhase3A args
  catch ex =>
    IO.eprintln (toString ex)
    IO.Process.exit 1
STAGE3A_LEAN

LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" lake env lean --run "$STAGE3A_FILE" "$REPO_ROOT_REAL" "$VERBOSE" "$PARTIAL_MANIFEST" "$SUMMARY_FILE" "${MODS[@]}"

EXPECTED_PARTIALS="$(head -n 1 "$PARTIAL_MANIFEST")"
if [ "$EXPECTED_PARTIALS" -gt 0 ]; then
  mapfile -t PARTIAL_MODS < <(tail -n +2 "$PARTIAL_MANIFEST")
  cat > "$STAGE3B_FILE" <<'STAGE3B_LEAN'
import Lean

open Lean Meta

private def parseModName (s : String) : Name :=
  s.splitOn "." |>.foldl (init := Name.anonymous) fun acc part =>
    Name.mkStr acc part

private def checkStructuralRecompile
    (privateEnv : Environment)
    (base : Name)
    (binfo : ConstantInfo)
    (checkKernelDefEq : Bool) : MetaM (Except String Unit) := do
  withoutModifyingEnv do
    let mut freshMap : Std.HashMap Name Name := {}
    for g in binfo.all do
      freshMap := freshMap.insert (Lean.Compiler.mkUnsafeRecName g) (g ++ `_audit_srec_tmp)
    let mut preDefs : Array Lean.Elab.PreDefinition := #[]
    let mut termMeasures : Array (Option Lean.Elab.TerminationMeasure) := #[]
    for g in binfo.all do
      let uName := Lean.Compiler.mkUnsafeRecName g
      let some (.defnInfo gd) := privateEnv.find? uName
        | return .error s!"missing partial helper '{uName}' during structural re-check"
      let some ginfo := privateEnv.find? g
        | return .error s!"missing base '{g}' during structural re-check"
      let fName := freshMap[uName]!
      let val := gd.value.replace fun sub =>
        match sub with
        | .const n us => (freshMap[n]?).map (mkConst · us)
        | _ => none
      let tm? ←
        if let some gei := Lean.Elab.Structural.eqnInfoExt.find? privateEnv g then
          lambdaTelescope val fun xs _ => do
            if h : gei.recArgPos < xs.size then
              let fn ← mkLambdaFVars xs xs[gei.recArgPos]
              pure (some { ref := Syntax.missing, structural := true, fn : Lean.Elab.TerminationMeasure })
            else
              pure none
        else
          pure none
      termMeasures := termMeasures.push tm?
      preDefs := preDefs.push {
        ref := Syntax.missing
        kind := if ginfo.isTheorem then .theorem else .def
        levelParams := gd.levelParams
        modifiers := { computeKind := .noncomputable }
        declName := fName
        binders := Syntax.missing
        type := gd.type
        value := val
        termination := default
      }
    try
      let termAction : Lean.Elab.TermElabM Unit :=
        Lean.Elab.Structural.structuralRecursion (← getLCtx, ← getLocalInstances) preDefs termMeasures
      let _ ← termAction.run'
      if checkKernelDefEq then
        let env' ← getEnv
        let us := binfo.levelParams.map mkLevelParam
        let fName := base ++ `_audit_srec_tmp
        match Lean.Kernel.isDefEq env' {} (mkConst fName us) (mkConst base us) with
        | .ok true => return .ok ()
        | .ok false =>
          return .error s!"recompiled structural '{base}' is not kernel-defEq to '{base}'"
        | .error ex =>
          return .error s!"kernel isDefEq failed for structural '{base}': {← (ex.toMessageData {}).toString}"
      else
        return .ok ()
    catch ex =>
      return .error s!"structural recursion re-verification failed for '{base}': {← ex.toMessageData.toString}"

private def findWFFunctional? (e : Expr) : Option Expr :=
  (e.find? fun sub =>
    (sub.isAppOf ``WellFounded.fix && sub.getAppNumArgs >= 5) ||
    ((sub.isAppOf ``WellFounded.Nat.fix || sub.isAppOf ``WellFounded.fixF) && sub.getAppNumArgs >= 4)).bind fun sub =>
      if sub.isAppOf ``WellFounded.fix then sub.getAppArgs[4]?
      else sub.getAppArgs[3]?

private partial def usesIHAsCall (ihFVar : FVarId) (e : Expr) : MetaM Bool := do
  let e ← Core.betaReduce e
  go e
where
  go (e : Expr) : MetaM Bool := do
    let e := e.consumeMData
    if e.isApp && e.getAppFn == .fvar ihFVar then
      return true
    if let some matcherApp ← matchMatcherApp? e (alsoCasesOn := true) then
      if let some remIdx := matcherApp.remaining.findIdx? (·.consumeMData == .fvar ihFVar) then
        for alt in matcherApp.alts, altNumParams in matcherApp.altNumParams do
          let ok ← lambdaBoundedTelescope alt (altNumParams + remIdx + 1) fun ys altBody => do
            if h : altNumParams + remIdx < ys.size then
              usesIHAsCall ys[altNumParams + remIdx].fvarId! altBody
            else
              return false
          if ok then return true
    if e.isAppOf ``PSum.rec || e.isAppOf ``PSigma.rec then
      let args := e.getAppArgs
      let (altIdxs, remStart) :=
        if e.isAppOf ``PSum.rec then (#[(3, 1), (4, 1)], 6)
        else (#[(3, 2)], 5)
      if args.size > remStart then
        let rem := args[remStart...*].toArray
        if let some remIdx := rem.findIdx? (·.consumeMData == .fvar ihFVar) then
          for (altIdx, nParams) in altIdxs do
            if hAlt : altIdx < args.size then
              let ok ← lambdaBoundedTelescope args[altIdx] (nParams + remIdx + 1) fun ys altBody => do
                if h : nParams + remIdx < ys.size then
                  usesIHAsCall ys[nParams + remIdx].fvarId! altBody
                else
                  return false
              if ok then return true
    match e with
    | .app f a =>
      if (← go f) then return true
      go a
    | .lam n t b bi =>
      withLocalDecl n bi t fun fv => go (b.instantiate1 fv)
    | .forallE n t b bi =>
      if (← go t) then return true
      withLocalDecl n bi t fun fv => go (b.instantiate1 fv)
    | .letE _ _ v b _ =>
      if (← go v) then return true
      usesIHAsCall ihFVar (b.instantiate1 v)
    | .proj _ _ s => go s
    | _ => return false

private def unfoldConstApp? (privateEnv : Environment) (e : Expr) : Option Expr :=
  match e.getAppFn with
  | .const n ls =>
    match privateEnv.find? n with
    | some ci =>
      match ci.value? (allowOpaque := true) with
      | some v =>
        if ci.levelParams.length == ls.length then
          some ((v.instantiateLevelParams ci.levelParams ls).beta e.getAppArgs)
        else none
      | none => none
    | none => none
  | _ => none

private partial def unfoldConstsRec (privateEnv : Environment) (pred : Name → Bool) (e : Expr) : MetaM Expr := do
  Meta.transform e (pre := fun sub => do
    if let .const n _ := sub.getAppFn then
      if pred n then
        if let some u := unfoldConstApp? privateEnv sub then
          return .visit (← Core.betaReduce u)
    return .continue)

private partial def isBareSelfCallAux
    (privateEnv : Environment) (clique : List Name) (body : Expr)
    (idx : Nat) (acc : Std.HashMap Name Expr) (fvs : Array FVarId) : MetaM Bool := do
  if h : idx < clique.length then
    let g := clique[idx]
    let gTy := match privateEnv.find? g with | some ci => ci.type | none => mkSort 0
    withLocalDeclD (Name.mkNum `_audit_clique idx) gTy fun fv =>
      isBareSelfCallAux privateEnv clique body (idx + 1) (acc.insert g fv) (fvs.push fv.fvarId!)
  else
    let bodyOpaque := body.replace fun sub =>
      match sub with
      | .const n _ => acc[n]?
      | _ => none
    let bodyDef ← withTransparency .default <| whnf bodyOpaque
    return match bodyDef.getAppFn with
      | .fvar fid => fvs.contains fid
      | _ => false

private def isBareSelfCall (privateEnv : Environment) (clique : List Name) (rhs : Expr) : MetaM Bool := do
  lambdaTelescope rhs fun _ body => do
    let body := body.consumeMData
    if let .const fn _ := body.getAppFn then
      if clique.contains fn then return true
    let bodyRed ← withTransparency .reducible <| whnf body
    if let .const fn _ := bodyRed.getAppFn then
      if clique.contains fn then return true
    isBareSelfCallAux privateEnv clique body 0 {} #[]

private def verifyUnfoldEqnType (base : Name) (binfo : ConstantInfo) (rhs : Expr) (eqThm : Name) : MetaM Bool := do
  let env ← getEnv
  let some (.thmInfo ti) := env.find? eqThm | return false
  unless ti.levelParams.length == binfo.levelParams.length do return false
  let us := binfo.levelParams.map mkLevelParam
  let eqType := ti.type.instantiateLevelParams ti.levelParams us
  forallTelescopeReducing eqType fun xs body => do
    let some (_, lhs, eqRhs) := body.eq? | return false
    let expLhs := mkAppN (mkConst base us) xs
    let expRhs := rhs.beta xs
    unless (← withTransparency .reducible <| Meta.isDefEq lhs expLhs) do return false
    withTransparency .reducible <| Meta.isDefEq eqRhs expRhs

private partial def propRecSkeletonEq (recTargets : NameSet) (e1 e2 : Expr) : MetaM Bool := do
  let e1 := e1.consumeMData
  let e2 := e2.consumeMData
  let hasRec1 := e1.getUsedConstants.any recTargets.contains
  let hasRec2 := e2.getUsedConstants.any recTargets.contains
  if !hasRec1 && !hasRec2 && !e1.hasLooseBVars && !e2.hasLooseBVars then
    let t1 ← inferType e1
    let t2 ← inferType e2
    if (← Meta.isProp t1) && (← Meta.isProp t2) then
      return ← Meta.isDefEq t1 t2
  match e1, e2 with
  | .bvar i, .bvar j => return i == j
  | .fvar i, .fvar j => return i == j
  | .sort _, .sort _ => return true
  | .const n1 _, .const n2 _ => return n1 == n2
  | .lit l1, .lit l2 => return l1 == l2
  | .proj s1 i1 x1, .proj s2 i2 x2 =>
    if s1 == s2 && i1 == i2 then propRecSkeletonEq recTargets x1 x2 else return false
  | .app f1 a1, .app f2 a2 =>
    if (← propRecSkeletonEq recTargets f1 f2) then propRecSkeletonEq recTargets a1 a2 else return false
  | .lam n1 t1 b1 bi1, .lam _ t2 b2 _ =>
    if !(← Meta.isDefEq t1 t2) then return false
    withLocalDecl n1 bi1 t1 fun fv =>
      propRecSkeletonEq recTargets (b1.instantiate1 fv) (b2.instantiate1 fv)
  | .forallE n1 t1 b1 bi1, .forallE _ t2 b2 _ =>
    if !(← Meta.isDefEq t1 t2) then return false
    withLocalDecl n1 bi1 t1 fun fv =>
      propRecSkeletonEq recTargets (b1.instantiate1 fv) (b2.instantiate1 fv)
  | .letE n1 t1 v1 b1 _, .letE _ t2 v2 b2 _ =>
    if !(← Meta.isDefEq t1 t2) then return false
    if !(← propRecSkeletonEq recTargets v1 v2) then return false
    withLetDecl n1 t1 v1 fun fv =>
      propRecSkeletonEq recTargets (b1.instantiate1 fv) (b2.instantiate1 fv)
  | _, _ => return false

private def isFixFnLam (e : Expr) : Bool :=
  e.isLambda && e.bindingBody!.isLambda && e.bindingBody!.bindingBody!.isApp &&
  !e.bindingBody!.bindingBody!.hasLooseBVar 0 &&
  e.bindingBody!.bindingBody!.appArg! == .bvar 1 &&
  !e.bindingBody!.bindingBody!.appFn!.hasLooseBVar 1

private partial def normalizeWFUnfolded (e : Expr) : MetaM Expr := do
  Meta.transform e (post := fun sub => do
    let sub := sub.headBeta
    if sub.isAppOf ``PSum.casesOn || sub.isAppOf ``PSum.rec ||
       sub.isAppOf ``PSigma.casesOn || sub.isAppOf ``PSigma.rec then
      if let some r ← reduceRecMatcher? sub then
        return .visit (← Core.betaReduce r)
    if sub.isProj then
      if let some r ← reduceProj? sub then
        return .visit (← Core.betaReduce r)
    if let some matcherApp ← matchMatcherApp? sub (alsoCasesOn := true) then
      if let some fArg := matcherApp.remaining[0]? then
        if isFixFnLam fArg then
          let newMotive? ← lambdaBoundedTelescope matcherApp.motive matcherApp.discrs.size fun xs t => do
            if xs.size == matcherApp.discrs.size && t.isForall && !t.bindingBody!.hasLooseBVar 0 then
              return some (← mkLambdaFVars xs t.bindingBody!)
            else
              return none
          if let some newMotive := newMotive? then
            let newAlts ← (matcherApp.alts.zip matcherApp.altNumParams).mapM fun (alt, nParams) =>
              lambdaBoundedTelescope alt nParams fun ys altBody => do
                let altBody' := mkApp altBody fArg
                mkLambdaFVars ys (← Core.betaReduce altBody')
            let uElim ← lambdaBoundedTelescope newMotive matcherApp.discrs.size fun _ mb => getLevel mb
            let newLevels := match matcherApp.uElimPos? with
              | none => matcherApp.matcherLevels
              | some pos => matcherApp.matcherLevels.set! pos uElim
            let newApp : MatcherApp := { matcherApp with
              matcherLevels := newLevels
              motive := newMotive
              alts := newAlts
              remaining := matcherApp.remaining[1...*].toArray
            }
            return .visit (← Core.betaReduce newApp.toExpr)
    return .done sub)

private def verifyWFUnfoldDirect
    (privateEnv : Environment) (base nonRecName : Name) (binfo : ConstantInfo)
    (rhs : Expr) (isPropTy : Bool) : MetaM (Except String Unit) := do
  withoutModifyingEnv do
    let us := binfo.levelParams.map mkLevelParam
    lambdaTelescope rhs fun xs body => do
      let lhs := mkAppN (mkConst base us) xs
      let lhs1 ← if base != nonRecName then unfoldConstsRec privateEnv (· == base) lhs else pure lhs
      let some lhs' := unfoldConstApp? privateEnv lhs1
        | return .error s!"WF base '{base}' could not unfold '{nonRecName}'"
      let fn := lhs'.getAppFn
      let args := lhs'.getAppArgs
      let (F, x, extraArgs) ←
        if fn.isConstOf ``WellFounded.fix && args.size >= 6 then
          pure (args[4]!, args[5]!, args[6...*].toArray)
        else if (fn.isConstOf ``WellFounded.Nat.fix || fn.isConstOf ``WellFounded.fixF) && args.size >= 5 then
          pure (args[3]!, args[4]!, args[5...*].toArray)
        else
          return .error s!"WF base '{base}' does not unfold to WellFounded.fix/Nat.fix/fixF"
      let nonVac ← lambdaBoundedTelescope F 2 fun fxs fbody => do
        if fxs.size == 2 then usesIHAsCall fxs[1]!.fvarId! fbody else return false
      unless nonVac do
        return .error s!"WF base '{base}' has vacuous WellFounded functional (IH never applied)"
      let lhs1Args := lhs1.getAppArgs
      unless lhs1Args.size >= extraArgs.size + 1 do
        return .error s!"WF base '{base}' arity mismatch during fixpoint unfolding"
      let keepArgs := lhs1Args.size - extraArgs.size - 1
      let lhsBaseFn := mkAppN lhs1.getAppFn (lhs1Args[*...keepArgs].toArray)
      let fxTy ← whnf (← inferType (mkApp F x))
      unless fxTy.isForall do
        return .error s!"WF base '{base}' functional type is not a function"
      let ftype := fxTy.bindingDomain!
      let some ihSubst ← forallBoundedTelescope ftype (some 2) fun ys _ => do
        if ys.size == 2 then
          some <$> mkLambdaFVars ys (.app lhsBaseFn ys[0]!)
        else
          return none
        | return .error s!"WF base '{base}' IH parameter type mismatch"
      let unfolded0 := mkAppN (mkApp2 F x ihSubst) extraArgs
      let unfolded ← normalizeWFUnfolded (← Core.betaReduce unfolded0)
      let body' ← if base != nonRecName then unfoldConstsRec privateEnv (fun n => binfo.all.contains n) body else pure body
      let body' ← normalizeWFUnfolded (← Core.betaReduce body')
      if isPropTy then
        let recTargets : NameSet := (binfo.all.foldl (init := {}) NameSet.insert).insert nonRecName
        if (← propRecSkeletonEq recTargets unfolded body') then
          return .ok ()
        else
          let preRes ← Lean.Elab.WF.preprocess rhs
          let bodyPre := preRes.expr.beta xs
          let bodyPre' ← if base != nonRecName then unfoldConstsRec privateEnv (fun n => binfo.all.contains n) bodyPre else pure bodyPre
          let bodyPre' ← normalizeWFUnfolded (← Core.betaReduce bodyPre')
          if (← propRecSkeletonEq recTargets unfolded bodyPre') then
            return .ok ()
          else
            return .error s!"Prop-valued WF base '{base}' functional does not match recursive body"
      else
        let ok ← withAtLeastTransparency .all <|
          withOptions (Lean.Meta.smartUnfolding.set · false) <|
            Meta.isDefEq unfolded body'
        if ok then
          return .ok ()
        else
          let preRes ← Lean.Elab.WF.preprocess rhs
          let bodyPre := preRes.expr.beta xs
          let bodyPre' ← if base != nonRecName then unfoldConstsRec privateEnv (fun n => binfo.all.contains n) bodyPre else pure bodyPre
          let bodyPre' ← normalizeWFUnfolded (← Core.betaReduce bodyPre')
          let ok2 ← withAtLeastTransparency .all <|
            withOptions (Lean.Meta.smartUnfolding.set · false) <|
              Meta.isDefEq unfolded bodyPre'
          if ok2 then
            return .ok ()
          else
            return .error s!"WF 1-step fixpoint unfolding of '{base}' is not defEq to recursive body"

private partial def rwPFUnder (lhs : Expr) : MetaM (Option Expr) := do
  if lhs.isAppOfArity ``Lean.Order.fix 4 then
    return some (mkAppN (mkConst ``Lean.Order.fix_eq lhs.getAppFn.constLevels!) lhs.getAppArgs)
  else if lhs.isAppOfArity ``Lean.Order.lfp_monotone 4 then
    return some (mkAppN (mkConst ``Lean.Order.lfp_monotone_fix lhs.getAppFn.constLevels!) lhs.getAppArgs)
  else if lhs.isApp then
    let some h ← rwPFUnder lhs.appFn! | return none
    return some (← mkAppM ``congrFun #[h, lhs.appArg!])
  else if lhs.isProj then
    let f := mkLambda `p .default (← inferType lhs.projExpr!) (lhs.updateProj! (.bvar 0))
    let some h ← rwPFUnder lhs.projExpr! | return none
    return some (← mkAppM ``congrArg #[f, h])
  else
    return none

private def verifyPFUnfoldDirect
    (privateEnv : Environment) (base declNameNonRec : Name) (binfo : ConstantInfo)
    (rhs : Expr) : MetaM (Except String Unit) := do
  withoutModifyingEnv do
    let us := binfo.levelParams.map mkLevelParam
    lambdaTelescope rhs fun xs body => do
      let lhs := mkAppN (mkConst base us) xs
      let lhs' ← unfoldConstsRec privateEnv (fun n => n == base || n == declNameNonRec) lhs
      let some h ← rwPFUnder lhs'
        | return .error s!"PartialFixpoint base '{base}' does not unfold to Lean.Order.fix/lfp_monotone"
      let some (_, _, lhsNew) := (← inferType h).eq?
        | return .error s!"PartialFixpoint fixpoint rewrite for '{base}' did not produce equality"
      let ok ← withAtLeastTransparency .all <|
        withOptions (Lean.Meta.smartUnfolding.set · false) <|
          Meta.isDefEq lhsNew body
      if ok then return .ok ()
      else return .error s!"PartialFixpoint 1-step unfolding of '{base}' is not defEq to recursive body"

private partial def unfoldPropPFApp? (e : Expr) : MetaM (Option Expr) := do
  if e.isAppOfArity ``Lean.Order.fix 4 || e.isAppOfArity ``Lean.Order.lfp_monotone 4 then
    let F := e.getAppArgs[2]!
    return some (mkApp F e)
  else if e.isApp then
    let some f' ← unfoldPropPFApp? e.appFn! | return none
    return some (mkApp f' e.appArg!)
  else if e.isProj then
    let some s' ← unfoldPropPFApp? e.projExpr! | return none
    return some (e.updateProj! s')
  else
    return none

private def verifyPropPFUnfold
    (privateEnv : Environment) (modIdx : ModuleIdx) (base : Name) (binfo : ConstantInfo)
    (rhs : Expr) : MetaM (Except String Unit) := do
  withoutModifyingEnv do
    let us := binfo.levelParams.map mkLevelParam
    let some bval := binfo.value? (allowOpaque := true) | return .error s!"base '{base}' has no value"
    let isPF (n : Name) : Bool := n == ``Lean.Order.fix || n == ``Lean.Order.lfp_monotone
    let nonRecName : Name :=
      if bval.getUsedConstants.any isPF then base
      else
        let cands := bval.getUsedConstants.filter fun n =>
          privateEnv.getModuleIdxFor? n == some modIdx &&
          match privateEnv.find? n with
          | some ci => (ci.value? (allowOpaque := true)).any (fun v => v.getUsedConstants.any isPF)
          | none => false
        cands[0]?.getD base
    lambdaTelescope rhs fun xs body => do
      let lhs := mkAppN (mkConst base us) xs
      let lhs' ← unfoldConstsRec privateEnv (fun n => n == base || n == nonRecName) lhs
      let some unfolded0 ← unfoldPropPFApp? lhs'
        | return .error s!"Prop-valued PartialFixpoint base '{base}' does not unfold to Lean.Order.fix/lfp_monotone"
      let reduceProjs (e : Expr) : MetaM Expr := do
        Meta.transform (← Core.betaReduce e) (post := fun sub => do
          if sub.isProj then
            if let some r ← reduceProj? sub then return .visit (← Core.betaReduce r)
          return .done sub)
      let unfolded ← reduceProjs unfolded0
      let body' ← reduceProjs (← unfoldConstsRec privateEnv (fun n => binfo.all.contains n || n == nonRecName) body)
      let recTargets : NameSet :=
        (binfo.all.foldl (init := {}) NameSet.insert)
          |>.insert nonRecName |>.insert ``Lean.Order.fix |>.insert ``Lean.Order.lfp_monotone
      if (← propRecSkeletonEq recTargets unfolded body') then
        return .ok ()
      else
        return .error s!"Prop-valued PartialFixpoint base '{base}' functional does not match recursive body"

private def checkPartialMeta
    (privateEnv : Environment)
    (modIdx : ModuleIdx)
    (c : Name)
    (info : ConstantInfo) : MetaM (Except String Unit) := do
  -- 1. Shape & same-module check
  let .defnInfo d := info | return .error "not a defnInfo"
  unless d.safety == Lean.DefinitionSafety.partial do return .error "not partial safety"
  unless d.hints matches .opaque do return .error "hints must be opaque"
  let some base := Lean.Compiler.isUnsafeRecName? c | return .error "name does not end in ._unsafe_rec"

  -- 2. Base constant and entire mutual clique: same module, computable, safe def or class-codomain thm
  let isValidBase (n : Name) (ci : ConstantInfo) : MetaM Bool := do
    unless privateEnv.getModuleIdxFor? n == some modIdx do return false
    if Lean.isNoncomputable privateEnv n then return false
    match ci with
    | .defnInfo bd => return bd.safety == Lean.DefinitionSafety.safe
    | .thmInfo bt =>
      -- In Lean v4.32.2 (PreDefinition/Basic.lean:135,213), the ONLY `thmInfo` that emits
      -- `_unsafe_rec` is a recursive `Prop`-valued `instance` (codomain head is a `class`).
      Meta.forallTelescopeReducing bt.type fun _ body =>
        pure (match body.getAppFn with | .const fn _ => Lean.isClass privateEnv fn | _ => false)
    | _ => return false

  let some binfo := privateEnv.find? base | return .error s!"base '{base}' missing in extEnv"
  unless (← isValidBase base binfo) do
    return .error s!"base '{base}' is noncomputable, non-safe, wrong module, or non-class theorem"

  -- 3. Mutual clique (`all`), universe params, and kernel type consistency
  if binfo.all.isEmpty || !binfo.all.contains base || !d.all.contains c then
    return .error s!"invalid mutual clique for '{c}' / '{base}'"
  unless d.all == binfo.all.map Lean.Compiler.mkUnsafeRecName do
    return .error s!"mutual clique mismatch d.all={d.all} vs binfo.all={binfo.all}"
  for g in binfo.all do
    let some ginfo := privateEnv.find? g | return .error s!"mutual member '{g}' missing"
    unless (← isValidBase g ginfo) do
      return .error s!"mutual member '{g}' failed computable/safe/class check"
  unless d.levelParams == binfo.levelParams do
    return .error s!"levelParams mismatch between '{c}' and '{base}'"
  match Lean.Kernel.isDefEq privateEnv {} d.type binfo.type with
  | .ok true => pure ()
  | _ => return .error s!"kernel type mismatch between '{c}' and '{base}'"

  -- 4. Genuine recursion in both `d.value` and per-constant `Lean.Meta.recExt`
  unless d.all.any (fun a => d.value.getUsedConstants.contains a) do
    return .error s!"body makes no recursive call to {d.all}"
  unless Lean.Meta.recExt.isTagged privateEnv base do
    return .error s!"base '{base}' is not tagged in Lean.Meta.recExt"

  -- 5. Safe substituted RHS (already C++ kernel-checked in Phase 3A via addDeclCore)
  let rhs : Expr := d.value.replace fun sub =>
    match sub with
    | .const n us =>
      match Lean.Compiler.isUnsafeRecName? n with
      | some b => if binfo.all.contains b then some (.const b us) else none
      | none => none
    | _ => none
  for used in rhs.getUsedConstants do
    if let some uinfo := privateEnv.find? used then
      if uinfo.isPartial || uinfo.isUnsafe then
        return .error s!"substituted body references partial/unsafe constant '{used}'"

  -- 6. Kernel recursion combinator + equational consistency
  let some bval := binfo.value? (allowOpaque := true) | return .error s!"base '{base}' has no value"
  let isBRec (n : Name) : Bool :=
    Lean.isBRecOnRecursor privateEnv n ||
    match n with
    | .str ind s =>
      (s == "brecOn" || s.startsWith "brecOn_") &&
      (privateEnv.find? ind matches some (.inductInfo _))
    | _ => false
  let isWF (n : Name) : Bool :=
    n == ``WellFounded.fix || n == ``WellFounded.fixF || n == `WellFounded.Nat.fix
  let isPF (n : Name) : Bool :=
    n == ``Lean.Order.fix || n == ``Lean.Order.lfp_monotone
  let hasComb (pred : Name → Bool) (v : Expr) : Bool :=
    v.getUsedConstants.any pred ||
    v.getUsedConstants.any fun n =>
      privateEnv.getModuleIdxFor? n == some modIdx &&
      match privateEnv.find? n with
      | some (.defnInfo hd) => hd.value.getUsedConstants.any pred
      | some (.thmInfo ht) => ht.value.getUsedConstants.any pred
      | _ => false
  let hasCombNonProp (pred : Name → Bool) (v : Expr) : MetaM Bool := do
    if v.getUsedConstants.any pred then return true
    for n in v.getUsedConstants do
      if privateEnv.getModuleIdxFor? n == some modIdx then
        if let some (.defnInfo hd) := privateEnv.find? n then
          if hd.safety == Lean.DefinitionSafety.safe && !(← Meta.isProp hd.type) then
            if hd.value.getUsedConstants.any pred then
              return true
    return false

  let isPropType ← Meta.isProp binfo.type
  if isPropType then
    -- Prop-valued recursive instances / defs skip `eqnInfoExt` in Lean v4.32.2; verify genuine recursion!
    if hasComb isBRec bval then
      if (← isBareSelfCall privateEnv binfo.all rhs) then
        return .error s!"Prop-valued recursive body of '{c}' is a bare self-loop"
      return ← checkStructuralRecompile privateEnv base binfo (checkKernelDefEq := false)
    else if hasComb isWF bval then
      if (← isBareSelfCall privateEnv binfo.all rhs) then
        return .error s!"Prop-valued recursive body of '{c}' is a bare self-loop"
      let nonRecName : Name :=
        if (findWFFunctional? bval).isSome then base
        else
          let cands := bval.getUsedConstants.filter fun n =>
            privateEnv.getModuleIdxFor? n == some modIdx &&
            match privateEnv.find? n with
            | some ci => (ci.value? (allowOpaque := true)).any (fun v => (findWFFunctional? v).isSome)
            | none => false
          cands[0]?.getD base
      return ← verifyWFUnfoldDirect privateEnv base nonRecName binfo rhs (isPropTy := true)
    else if hasComb isPF bval then
      return ← verifyPropPFUnfold privateEnv modIdx base binfo rhs
    else
      return .error s!"Prop-valued recursive base '{base}' lacks kernel recursion combinator"

  -- Non-Prop recursive defs MUST match one of Lean v4.32.2's three recursion compilers:
  if let some ei := Lean.Elab.Structural.eqnInfoExt.find? privateEnv base then
    unless (← hasCombNonProp isBRec bval) do
      return .error s!"Structural eqnInfoExt present for '{base}' but no non-Prop brecOn combinator"
    let fName := base ++ `_f
    unless privateEnv.getModuleIdxFor? fName == some modIdx && bval.getUsedConstants.contains fName do
      return .error s!"Structural recursive base '{base}' missing same-module '{fName}'"
    let some (.defnInfo fd) := privateEnv.find? fName |
      return .error s!"'{fName}' is not a defnInfo"
    unless fd.safety == Lean.DefinitionSafety.safe && (fd.hints matches .abbrev) && !(← Meta.isProp fd.type) do
      return .error s!"'{fName}' must be a safe non-Prop abbrev definition"
    let sunfoldName := Lean.Meta.mkSmartUnfoldingNameFor base
    unless privateEnv.getModuleIdxFor? sunfoldName == some modIdx do
      return .error s!"Structural recursive base '{base}' missing same-module '{sunfoldName}'"
    let some (.defnInfo sf) := privateEnv.find? sunfoldName |
      return .error s!"'{sunfoldName}' is not a defnInfo"
    unless sf.safety == Lean.DefinitionSafety.safe do
      return .error s!"'{sunfoldName}' is not safe"
    if (← isBareSelfCall privateEnv binfo.all rhs) then
      return .error s!"structural body of '{c}' is a bare self-loop"
    if let .error err := (← checkStructuralRecompile privateEnv base binfo (checkKernelDefEq := true)) then
      return .error err
    withoutModifyingEnv do
      unless (← withTransparency .reducible <| Meta.isDefEq rhs ei.value) do
        return .error s!"rhs not reducibly defEq to Structural eqnInfoExt value for '{base}'"
      unless (← withTransparency .reducible <| Meta.isDefEq rhs sf.value) do
        return .error s!"rhs not reducibly defEq to '{sunfoldName}' for '{base}'"
      if !(← Lean.isIrreducible base) then
        try
          match (← Meta.getUnfoldEqnFor? base) with
          | none =>
            return .error s!"Meta.getUnfoldEqnFor? returned none for structural '{base}'"
          | some eqThm =>
            unless (← verifyUnfoldEqnType base binfo rhs eqThm) do
              return .error s!"unfold theorem '{eqThm}' type mismatch for structural '{base}'"
        catch ex =>
          return .error s!"Meta.getUnfoldEqnFor? failed for structural '{base}': {← ex.toMessageData.toString}"
      return .ok ()
  else if let some ei := Lean.Elab.WF.eqnInfoExt.find? privateEnv base then
    unless (← hasCombNonProp isWF bval) do
      return .error s!"WF eqnInfoExt present for '{base}' but no non-Prop WellFounded.fix combinator"
    unless privateEnv.getModuleIdxFor? ei.declNameNonRec == some modIdx do
      return .error s!"WF declNameNonRec '{ei.declNameNonRec}' not in module"
    let some (.defnInfo nrec) := privateEnv.find? ei.declNameNonRec |
      return .error s!"WF declNameNonRec '{ei.declNameNonRec}' is not a defnInfo"
    unless nrec.safety == Lean.DefinitionSafety.safe && !(← Meta.isProp nrec.type) && nrec.value.getUsedConstants.any isWF do
      return .error s!"WF declNameNonRec '{ei.declNameNonRec}' is not a safe non-Prop WF definition"
    if ei.declNameNonRec != base && !bval.getUsedConstants.contains ei.declNameNonRec then
      return .error s!"WF base '{base}' does not reference '{ei.declNameNonRec}'"
    if (← isBareSelfCall privateEnv binfo.all rhs) then
      return .error s!"WF body of '{c}' is a bare self-loop"
    if let .error err := (← verifyWFUnfoldDirect privateEnv base ei.declNameNonRec binfo rhs (isPropTy := false)) then
      return .error err
    withoutModifyingEnv do
      unless (← withTransparency .reducible <| Meta.isDefEq rhs ei.value) do
        return .error s!"rhs not reducibly defEq to WF eqnInfoExt value for '{base}'"
      try
        match (← Meta.getUnfoldEqnFor? base) with
        | none =>
          return .error s!"Meta.getUnfoldEqnFor? returned none for WF '{base}'"
        | some eqThm =>
          unless (← verifyUnfoldEqnType base binfo rhs eqThm) do
            return .error s!"unfold theorem '{eqThm}' type mismatch for WF '{base}'"
          return .ok ()
      catch ex =>
        return .error s!"Meta.getUnfoldEqnFor? failed for WF '{base}': {← ex.toMessageData.toString}"
  else if let some ei := Lean.Elab.PartialFixpoint.eqnInfoExt.find? privateEnv base then
    unless (← hasCombNonProp isPF bval) do
      return .error s!"PartialFixpoint eqnInfoExt present for '{base}' but no non-Prop Lean.Order combinator"
    unless privateEnv.getModuleIdxFor? ei.declNameNonRec == some modIdx do
      return .error s!"PartialFixpoint declNameNonRec '{ei.declNameNonRec}' not in module"
    let some (.defnInfo nrec) := privateEnv.find? ei.declNameNonRec |
      return .error s!"PartialFixpoint declNameNonRec '{ei.declNameNonRec}' is not a defnInfo"
    unless nrec.safety == Lean.DefinitionSafety.safe && !(← Meta.isProp nrec.type) && nrec.value.getUsedConstants.any isPF do
      return .error s!"PartialFixpoint declNameNonRec '{ei.declNameNonRec}' is not a safe non-Prop PartialFixpoint definition"
    if ei.declNameNonRec != base && !bval.getUsedConstants.contains ei.declNameNonRec then
      return .error s!"PartialFixpoint base '{base}' does not reference '{ei.declNameNonRec}'"
    if let .error err := (← verifyPFUnfoldDirect privateEnv base ei.declNameNonRec binfo rhs) then
      return .error err
    withoutModifyingEnv do
      unless (← withTransparency .reducible <| Meta.isDefEq rhs ei.value) do
        return .error s!"rhs not reducibly defEq to PartialFixpoint eqnInfoExt value for '{base}'"
      try
        match (← Meta.getUnfoldEqnFor? base) with
        | none =>
          return .error s!"Meta.getUnfoldEqnFor? returned none for PartialFixpoint '{base}'"
        | some eqThm =>
          unless (← verifyUnfoldEqnType base binfo rhs eqThm) do
            return .error s!"unfold theorem '{eqThm}' type mismatch for PartialFixpoint '{base}'"
          return .ok ()
      catch ex =>
        return .error s!"Meta.getUnfoldEqnFor? failed for PartialFixpoint '{base}': {← ex.toMessageData.toString}"
  else
    return .error s!"base '{base}' has no Structural/WF/PartialFixpoint eqnInfoExt entry"

private unsafe def runPhase3B (args : List String) : IO Unit := do
  let (expectedStr, modStrs) ←
    match args with
    | e :: ms => pure (e, ms)
    | _ => throw <| IO.userError "Usage: Stage3Partial.lean <expectedCount> <mod>..."
  let some expectedPartialCount := expectedStr.toNat? |
    throw <| IO.userError s!"AXIOM AUDIT FAILED: invalid expected partial count '{expectedStr}'"
  if modStrs.isEmpty then
    throw <| IO.userError "AXIOM AUDIT FAILED: no partial modules provided to Phase 3B"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let extImports := modStrs.toArray.map fun s => { module := parseModName s }
  let extEnv ← Lean.importModules extImports {} (trustLevel := 0) (loadExts := true)
  let privateEnv := extEnv.setExporting false
  let coreCtx : Core.Context := { fileName := "<stage3b>", fileMap := default, maxHeartbeats := 0 }
  let coreState : Core.State := { env := privateEnv }
  let action : MetaM (Nat × Array String) := withoutExporting do
    let mut verifiedCount : Nat := 0
    let mut metaViolations : Array String := #[]
    for modStr in modStrs do
      let modName := parseModName modStr
      match extEnv.getModuleIdx? modName with
      | none =>
        metaViolations := metaViolations.push s!"[{modName}] module missing in extension environment"
      | some modIdx =>
        let md := extEnv.header.moduleData[modIdx.toNat]!
        for c in md.constNames do
          if let some info := privateEnv.find? c then
            if info.isPartial then
              verifiedCount := verifiedCount + 1
              match ← checkPartialMeta privateEnv modIdx c info with
              | .ok () => pure ()
              | .error reason =>
                metaViolations := metaViolations.push s!"[{modName}] partial declaration '{c}': {reason}"
    return (verifiedCount, metaViolations)
  let ((verifiedCount, metaViolations), _) ← (action.run' {} {}).toIO coreCtx coreState
  if !metaViolations.isEmpty then
    let msg := String.intercalate "\n" metaViolations.toList
    throw <| IO.userError s!"AXIOM AUDIT FAILED ({metaViolations.size} partial-helper violation(s)):\n{msg}"
  if verifiedCount != expectedPartialCount then
    throw <| IO.userError s!"AXIOM AUDIT FAILED: partial helper count mismatch (Phase 3A saw {expectedPartialCount}, Phase 3B verified {verifiedCount})"

unsafe def main (args : List String) : IO Unit := do
  try
    runPhase3B args
  catch ex =>
    IO.eprintln (toString ex)
    IO.Process.exit 1
STAGE3B_LEAN

  LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" lake env lean --run "$STAGE3B_FILE" "$EXPECTED_PARTIALS" "${PARTIAL_MODS[@]}"
fi

cat "$SUMMARY_FILE"
