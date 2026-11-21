#!/usr/bin/env bash
set -euo pipefail

repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
export PROJECT_DIR="$repo"
export ISABELLE_IDENTIFIER=utp-2026-patched

exec "$HOME/Applications/Isabelle2026-patched.app/bin/isabelle" pide_mcp "$@"
