#!/usr/bin/env bash
set -euo pipefail

repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
export PROJECT_DIR="$repo"
export ISABELLE_IDENTIFIER="${UTP_PROFILE:-utp-2026-patched}"

exec "${ISABELLE:-$HOME/Applications/Isabelle2026-patched.app/bin/isabelle}" build -b -d "$repo/deps" -d "$repo" \
  -o system_heaps=false -o threads=4 "$@" UTP-Angelic-CSP
