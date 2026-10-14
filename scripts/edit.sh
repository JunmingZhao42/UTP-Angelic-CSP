#!/usr/bin/env bash
set -euo pipefail

repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
export PROJECT_DIR="$repo"
export ISABELLE_IDENTIFIER="${UTP_PROFILE:-utp-2025-2}"
editor=${1:-jedit}
if (( $# )); then shift; fi

case "$editor" in
  jedit)
    exec "${ISABELLE:-isabelle}" jedit -u -A UTP-Angelic-Designs -R UTP-Angelic-CSP \
      -d "$repo/deps" -d "$repo" "$@" "$repo/Angelic_CSP.thy" ;;
  vscode)
    exec "${ISABELLE:-isabelle}" vscode_server -A UTP-Angelic-Designs -R UTP-Angelic-CSP \
      -d "$repo/deps" -d "$repo" -o system_heaps=false "$@" ;;
  *)
    printf 'Usage: %s [jedit|vscode] [Isabelle options]\n' "$0" >&2
    exit 2 ;;
esac
