#!/usr/bin/env bash

# Recommended convenience wrapper for routine local validation in ArkLib.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

run_docs=0
run_site=0
run_axioms=0
run_legacy_lint=0

usage() {
  cat <<'EOF'
Usage: ./scripts/validate.sh [--lint] [--docs] [--site] [--axioms]

Default checks:
  - Python regression tests and downstream source honesty gates
  - ./scripts/lake-locked.sh build
  - ./scripts/lake-locked.sh test (ArkLibTest compile-time acceptance clients)
  - ./scripts/lake-locked.sh exe lint-style
  - ./scripts/test-lint-plugin.sh
  - ./scripts/lake-locked.sh exe toyproblem-runtime
  - ./scripts/lake-locked.sh exe hachi-runtime
  - ./scripts/lake-locked.sh exe sumcheck-runtime
  - ./scripts/lake-locked.sh exe fri-extractor-runtime
  - fail on non-`sorry` warnings in the canonical ArkLib inventory
  - ./scripts/test-retiredsweep.sh and ./scripts/lake-locked.sh exe retiredsweep --require-empty
  - ./scripts/check-imports.sh
  - ./scripts/test-build-timing-report.sh
  - python3 ./scripts/check-docs-integrity.py
  - python3 ./scripts/kb/check_generated.py
  - python3 ./scripts/kb/lint.py --strict-cited-pages

Optional checks:
  --lint    Also check the maintained style baseline for classic downstream modules
  --docs    Run DISABLE_EQUATIONS=1 ./scripts/lake-locked.sh build ArkLib:docs
  --site    Run ./scripts/build-web.sh (implies --docs)
  --axioms  Test the axiomsweep tool, then run the axiom/sorry regression gate
EOF
}

for arg in "$@"; do
  case "$arg" in
    --lint)
      run_legacy_lint=1
      ;;
    --docs)
      run_docs=1
      ;;
    --site)
      run_docs=1
      run_site=1
      ;;
    --axioms)
      run_axioms=1
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "ERROR: Unknown flag: $arg" >&2
      usage >&2
      exit 1
      ;;
  esac
done

build_log="$(mktemp "${TMPDIR:-/tmp}/arklib-validate-build.XXXXXX")"
cleanup() {
  rm -f "$build_log"
}
trap cleanup EXIT

echo "# Checking Python regressions"
python3 -m unittest discover -s scripts/tests

echo "# Checking canonical provenance and generated import surfaces"
./scripts/check-imports.sh

echo "# Checking downstream source honesty"
python3 scripts/forbidden_tokens.py
python3 scripts/sorry_census.py --fail-on-holes

echo "# Building project"
./scripts/lake-locked.sh build 2>&1 | tee "$build_log"

# The runtime acceptance clients link VCVio's FFI backends. Lake fetches the
# package, but not its Git submodules; initialize them before any native build.
if [ -e .lake/packages/VCVio/.git ]; then
  git -C .lake/packages/VCVio submodule update --init --recursive --quiet
fi

echo ""
echo "# Building compile-time acceptance clients"
./scripts/lake-locked.sh test 2>&1 | tee -a "$build_log"

echo ""
echo "# Checking ArkLibTest warning budget"
python3 ./scripts/check-warning-log.py "$build_log" \
  --path-prefix ArkLibTest/ \
  --label "ArkLibTest warnings (including admissions)"

echo ""
echo "# Checking ArkLib warning budget"
python3 ./scripts/check-warning-log.py "$build_log" \
  --source-inventory scripts/arklib-upstream.json \
  --exclude-substring 'declaration uses `sorry`' \
  --label 'ArkLib non-sorry warnings'

echo ""
echo "# Checking native probability retirement"
./scripts/test-retiredsweep.sh
./scripts/lake-locked.sh exe retiredsweep --require-empty

echo ""
echo "# Running Lean-native source-policy gate"
if [[ "${GITHUB_ACTIONS:-}" == "true" ]]; then
  ./scripts/lake-locked.sh exe lint-style --github
else
  ./scripts/lake-locked.sh exe lint-style
fi

echo ""
echo "# Testing build-time source-policy plugin"
./scripts/test-lint-plugin.sh

echo ""
echo "# Running toy-problem compiled runtime checks"
./scripts/lake-locked.sh exe toyproblem-runtime

echo ""
echo "# Running nonrecursive-Hachi compiled runtime checks"
# Default target only: the composed opening run (`--full`) is dominated by the honest sumcheck
# prover and is far too slow to gate on. See scripts/HachiRuntime.lean.
./scripts/lake-locked.sh exe hachi-runtime

echo ""
echo "# Running computable Sumcheck runtime checks"
./scripts/lake-locked.sh exe sumcheck-runtime

echo ""
echo "# Running measured FRI extractor runtime checks"
./scripts/lake-locked.sh exe fri-extractor-runtime

echo ""
echo "# Checking downstream flagship axioms"
awk '!/^([[:space:]]*(#|$))/ { print $1 }' scripts/flagship_axioms.txt \
  | LC_ALL=C sort -u | xargs ./scripts/lake-locked.sh build
python3 scripts/axiom_audit.py

echo ""
echo "# Testing build timing report fixtures"
./scripts/test-build-timing-report.sh

echo ""
echo "# Checking docs integrity"
python3 ./scripts/check-docs-integrity.py

echo ""
echo "# Checking knowledge base"
python3 ./scripts/kb/check_generated.py
python3 ./scripts/kb/lint.py --strict-cited-pages

if (( run_axioms )); then
  echo ""
  echo "# Testing the axiom sweep tool against its fixture matrix"
  ./scripts/test-axiomsweep.sh
  echo ""
  echo "# Checking axiom/sorry regression baseline"
  ./scripts/lake-locked.sh exe axiomsweep --check
fi

if (( run_legacy_lint )); then
  echo "# Checking classic downstream style baseline"
  ./scripts/lint-style.sh
fi

if (( run_docs )); then
  echo ""
  echo "# Building API docs"
  DISABLE_EQUATIONS=1 ./scripts/lake-locked.sh build ArkLib:docs
fi

if (( run_site )); then
  echo ""
  echo "# Building website and blueprint outputs"
  ./scripts/build-web.sh
fi

echo ""
echo "All requested validation checks passed."
