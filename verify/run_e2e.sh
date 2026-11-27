#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
DEFAULT_PROJECT_DIR="$(dirname -- "${SCRIPT_DIR}")"

# Dynamically prepend elan toolchain bin directory if installed (read-only)
ELAN_BIN="${ELAN_HOME:-${HOME:-/home/antigravity}/.elan}/bin"
if [ -d "${ELAN_BIN}" ]; then
    case ":${PATH}:" in
        *":${ELAN_BIN}:"*) ;;
        *) export PATH="${ELAN_BIN}:${PATH}" ;;
    esac
fi

# Prevent __pycache__ / .pyc creation inside verify/
export PYTHONDONTWRITEBYTECODE=1

exec python3 -B "${SCRIPT_DIR}/runner.py" \
    --default-project-dir "${DEFAULT_PROJECT_DIR}" \
    --verify-dir "${SCRIPT_DIR}" \
    "$@"
