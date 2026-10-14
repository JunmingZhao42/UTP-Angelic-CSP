#!/usr/bin/env bash
# Run ./scripts/test-build-scripts.sh to check the build/edit helpers using a mock
# Isabelle command. Checks paper exclusions, unchanged proofs, cleanup, failure
# propagation and command routing; does not build proofs or open an editor.
set -euo pipefail

repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
test_dir=$(mktemp -d "${TMPDIR:-/tmp}/utp-build-tests.XXXXXX")
trap 'rm -rf -- "$test_dir"' EXIT

cat > "$test_dir/isabelle" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
[[ "$1" == "$TEST_COMMAND" ]]
printf '%s\n' "$PROJECT_DIR" > "$TEST_RECORD"
printf '%s\n' "$@" > "$TEST_RECORD.args"
grep -Fxq -- "$TEST_REPO/deps" "$TEST_RECORD.args"
if [[ "$ISABELLE_IDENTIFIER" == build-script-test-paper ]]; then
  [[ "$PROJECT_DIR" != "$TEST_REPO" ]]
  for directory in . angelic-designs reactive-angelic-designs angelic-processes; do
    for source in "$TEST_REPO/$directory"/*.thy; do
      name=${source##*/}
      case "$name" in
        utp_ades_parallel.thy|utp_rad_parallel.thy|utp_ap_parallel.thy|utp_rad_representation.thy)
          [[ ! -e "$PROJECT_DIR/$directory/$name" ]] ;;
        utp_ades.thy|utp_rad.thy|Angelic_CSP.thy) ;;
        *) cmp "$source" "$PROJECT_DIR/$directory/$name" ;;
      esac
    done
  done
  if grep -Eq 'utp_(ades_parallel|rad_parallel|ap_parallel|rad_representation)' \
    "$PROJECT_DIR/ROOT" "$PROJECT_DIR/angelic-designs/utp_ades.thy" \
    "$PROJECT_DIR/reactive-angelic-designs/utp_rad.thy" "$PROJECT_DIR/Angelic_CSP.thy"; then
    exit 1
  fi
  grep -q 'imports utp_ades_designs' "$PROJECT_DIR/angelic-designs/utp_ades.thy"
else
  [[ "$PROJECT_DIR" == "$TEST_REPO" ]]
  [[ "$ISABELLE_IDENTIFIER" == build-script-test ]]
fi
exit "${TEST_EXIT:-0}"
SH
chmod +x "$test_dir/isabelle"

export ISABELLE="$test_dir/isabelle" UTP_PROFILE=build-script-test
export TEST_REPO="$repo" TEST_RECORD="$test_dir/project" TEST_COMMAND=build
cd "$test_dir"

"$repo/scripts/fullbuild.sh" -n
grep -Fxq -- -n "$TEST_RECORD.args"
"$repo/scripts/paperbuild.sh"
[[ ! -e "$(cat "$TEST_RECORD")" ]]

if TEST_EXIT=7 "$repo/scripts/paperbuild.sh"; then
  printf 'Expected the build failure to propagate.\n' >&2
  exit 1
else
  [[ $? == 7 ]]
fi
[[ ! -e "$(cat "$TEST_RECORD")" ]]

TEST_COMMAND=jedit "$repo/scripts/edit.sh"
TEST_COMMAND=vscode_server "$repo/scripts/edit.sh" vscode

printf 'Build/edit forwarding, paper exclusions, unchanged proofs and cleanup passed.\n'
