#!/usr/bin/env bash
set -euo pipefail

repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
paper_dir=$(mktemp -d "${TMPDIR:-/tmp}/utp-paperbuild.XXXXXX")
trap 'rm -rf -- "$paper_dir"' EXIT

# The paper import graph needs its own ROOT and entry theories, not checkout edits.
for directory in . angelic-designs reactive-angelic-designs angelic-processes; do
  mkdir -p "$paper_dir/$directory"
  for source in "$repo/$directory"/*.thy; do
    case "${source##*/}" in
      utp_ades_parallel.thy|utp_rad_parallel.thy|utp_ap_parallel.thy|utp_rad_representation.thy)
        continue ;;
    esac
    cp "$source" "$paper_dir/$directory/"
  done
done

sed -E '/^[[:space:]]+(utp_ades_parallel|utp_rad_parallel|utp_rad_representation|"angelic-processes\/utp_ap_parallel")$/d' \
  "$repo/ROOT" > "$paper_dir/ROOT"

for entry in angelic-designs/utp_ades.thy reactive-angelic-designs/utp_rad.thy Angelic_CSP.thy; do
  sed '/^[[:space:]]*imports / {
    s/ utp_ades_parallel/ utp_ades_designs/g
    s/ utp_rad_parallel//g
    s/ "angelic-processes\/utp_ap_parallel"//g
  }' "$paper_dir/$entry" > "$paper_dir/$entry.tmp"
  mv "$paper_dir/$entry.tmp" "$paper_dir/$entry"
done

# A separate profile avoids loading the full project's ROOTS into the paper build.
export ISABELLE_IDENTIFIER="${UTP_PROFILE:-utp-2025-2}-paper"
export PROJECT_DIR="$paper_dir"
"${ISABELLE:-isabelle}" build -b -d "$repo/deps" -d "$paper_dir" \
  -o system_heaps=false -o threads=4 "$@" UTP-Angelic-CSP
