#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOOLCHAIN="leanprover/lean4:v4.32.2"
MATHLIB_CACHE_URL="https://cache.mathlib.org/mathlib4-master"

export PATH="$HOME/.elan/bin:/opt/pipx/bin:/opt/cargo/bin:$PATH"

echo "=== [1/5] Checking elan & Lean toolchain ($TOOLCHAIN) ==="
if ! command -v elan >/dev/null 2>&1; then
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain "$TOOLCHAIN"
  export PATH="$HOME/.elan/bin:$PATH"
fi

if ! elan toolchain list | grep -q "v4.32.2"; then
  elan toolchain install "$TOOLCHAIN"
fi

(
  cd "$REPO_ROOT"
  lean --version
  lake --version
)

echo "=== [2/5] Resolving Lake dependencies & fetching Mathlib cache ==="
(
  cd "$REPO_ROOT"
  if [ ! -f "$REPO_ROOT/lakefile.toml" ] || [ ! -f "$REPO_ROOT/lean-toolchain" ]; then
    echo "ERROR: lakefile.toml and lean-toolchain must exist in $REPO_ROOT" >&2
    exit 1
  fi

  export MATHLIB_CACHE_GET_URL="$MATHLIB_CACHE_URL"
  if [ ! -f "$REPO_ROOT/lake-manifest.json" ]; then
    lake update
  else
    lake resolve-deps
  fi

  MATHLIB_CACHE_GET_URL="$MATHLIB_CACHE_URL" lake exe cache get

  echo "Verifying Mathlib precompiled .olean cache (zero source compilation check)..."
  lake build --no-build \
    Mathlib.Combinatorics.SimpleGraph.Basic \
    Mathlib.Analysis.Subadditive \
    Mathlib.Data.ZMod.Basic
)

echo "=== [3/5] Provisioning Python 3.12 .venv via uv ==="
if ! command -v uv >/dev/null 2>&1; then
  echo "ERROR: uv not found on PATH ($PATH)" >&2
  exit 1
fi

if [ ! -x "$REPO_ROOT/.venv/bin/python" ]; then
  uv venv --python 3.12 "$REPO_ROOT/.venv"
fi

uv pip install --python "$REPO_ROOT/.venv/bin/python" \
  numpy scipy sympy mpmath ortools highspy python-sat cvxpy clarabel scs pytest

"$REPO_ROOT/.venv/bin/python" - <<'PY'
import numpy, scipy, sympy, mpmath, ortools, highspy, pysat, cvxpy, clarabel, scs, pytest
from ortools.sat.python import cp_model
from pysat.solvers import Solver
print(
    f"Python venv OK: numpy={numpy.__version__}, scipy={scipy.__version__}, "
    f"sympy={sympy.__version__}, cvxpy={cvxpy.__version__}, pytest={pytest.__version__}"
)
PY

echo "=== [4/5] Checking/installing Ubuntu APT solvers & libraries ==="
APT_PKGS=(coinor-cbc coinor-csdp cadical nauty cliquer libeigen3-dev zstd)
MISSING_PKGS=()
for pkg in "${APT_PKGS[@]}"; do
  if ! dpkg-query -W -f='${Status}\n' "$pkg" 2>/dev/null | grep -qx "install ok installed"; then
    MISSING_PKGS+=("$pkg")
  fi
done

if [ "${#MISSING_PKGS[@]}" -gt 0 ]; then
  echo "Installing missing APT packages: ${MISSING_PKGS[*]}"
  sudo apt-get update
  sudo apt-get install -y "${MISSING_PKGS[@]}"
else
  echo "All APT packages already installed: ${APT_PKGS[*]}"
fi

echo "=== [5/5] Verifying native toolchains & solvers ==="
for pkg in "${APT_PKGS[@]}"; do
  ver=$(dpkg-query -W -f='${Version}' "$pkg")
  echo "  apt $pkg = $ver"
done
echo "  g++   = $(g++ --version | head -n 1)"
echo "  cargo = $(cargo --version)"
echo "=== Environment setup complete ==="
