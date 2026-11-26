#!/usr/bin/env bash
set -euo pipefail

repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
export PROJECT_DIR="$repo"
export ISABELLE_IDENTIFIER="${UTP_PROFILE:-utp-2026-patched}"
editor=${1:-jedit}
if (( $# )); then shift; fi

case "$editor" in
  jedit)
    exec "${ISABELLE:-$HOME/Applications/Isabelle2026-patched.app/bin/isabelle}" jedit -u -A UTP-Angelic-Designs -R UTP-Angelic-CSP \
      -d "$repo/deps" -d "$repo" "$@" "$repo/angelic-processes/utp_ap.thy" ;;
  vscode)
    exec "${ISABELLE:-$HOME/Applications/Isabelle2026-patched.app/bin/isabelle}" vscode_server -A UTP-Angelic-Designs -R UTP-Angelic-CSP \
      -d "$repo/deps" -d "$repo" -o system_heaps=false "$@" ;;
  *)
    printf 'Usage: %s [jedit|vscode] [Isabelle options]\n' "$0" >&2
    exit 2 ;;
esac
