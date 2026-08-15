#!/usr/bin/env bash

# Regenerate the Proximity Prize style baseline from the current tracked tree.

set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

raw="$(mktemp "${TMPDIR:-/tmp}/proximity-style-raw.XXXXXX")"
generated="$(mktemp "${TMPDIR:-/tmp}/proximity-style-generated.XXXXXX")"
backup="$(mktemp "${TMPDIR:-/tmp}/proximity-style-backup.XXXXXX")"
cleanup() {
  rm -f "$raw" "$generated" "$backup"
}
trap cleanup EXIT

cp scripts/style-exceptions.txt "$backup"
: > scripts/style-exceptions.txt

set +e
{
  printf '%s\n' ArkLib/Data/CodingTheory/ProximityGap.lean
  git ls-files 'ArkLib/Data/CodingTheory/ProximityGap/*.lean'
} | sort -u | xargs ./scripts/lint-style.py > "$raw"
lint_status=$?
set -e

if (( lint_status != 0 && lint_status != 1 && lint_status != 123 )); then
  cp "$backup" scripts/style-exceptions.txt
  echo "ERROR: style baseline generation failed with status $lint_status" >&2
  exit "$lint_status"
fi

# Exceptions are file-and-rule scoped (except the long-file watermark), so
# retain one representative line for each file/rule pair.
awk -F ' : ' '!seen[$1 FS $3]++' "$raw" | LC_ALL=C sort > "$generated"
mv "$generated" scripts/style-exceptions.txt

echo "Updated scripts/style-exceptions.txt with $(wc -l < scripts/style-exceptions.txt) entries."
