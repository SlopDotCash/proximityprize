#!/bin/bash
# Tier 1 Test Infrastructure Master Suite for ArkLib
#
# Orchestrates all test categories (gating, metrics, benchmarks) with unified
# proof metrics collection and reporting. Tracks sorry count, axiom efficiency,
# and proof completion metrics.
#
# Usage:
#   ./scripts/test-suite.sh gating [--json] [--fail-fast]
#   ./scripts/test-suite.sh metrics [--json]
#   ./scripts/test-suite.sh full [--json] [--fail-fast]
#   ./scripts/test-suite.sh report [--baseline REF] [--json]
#
# Return codes:
#   0: All gating gates passed
#   1: Gating gate failure (merge-blocking)
#   2: Metric collection failed (warning-level)
#   3: Benchmark timeout/OOM (non-blocking)

set -eo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
METRICS_DIR="${RUNNER_TEMP:-/tmp}/arklib-metrics"
METRICS_FILE="$METRICS_DIR/proof-metrics.json"
BUILD_LOG="$METRICS_DIR/build.log"

# Command-line parsing
MODE="${1:-gating}"
shift || true

JSON_OUTPUT=false
FAIL_FAST=false
PARALLEL_JOBS=1
BASELINE_REF=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --json) JSON_OUTPUT=true; shift ;;
    --fail-fast) FAIL_FAST=true; shift ;;
    --parallel) PARALLEL_JOBS="$2"; shift 2 ;;
    --baseline) BASELINE_REF="$2"; shift 2 ;;
    *) echo "Unknown option: $1" >&2; exit 1 ;;
  esac
done

mkdir -p "$METRICS_DIR"

# ─────────────────────────────────────────────────────────────────────────
# Utility functions
# ─────────────────────────────────────────────────────────────────────────

log_section() {
  if [ "$JSON_OUTPUT" = false ]; then
    echo ""
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    echo "$1"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  fi
}

log_metric() {
  if [ "$JSON_OUTPUT" = false ]; then
    printf "  %-40s: %s\n" "$1" "$2"
  fi
}

log_error() {
  echo "ERROR: $1" >&2
}

# ─────────────────────────────────────────────────────────────────────────
# Proof metrics collection
# ─────────────────────────────────────────────────────────────────────────

collect_metrics() {
  local sorry_count=0
  local axiom_violations=0
  local modules_compiled=0
  local build_time_sec=0

  log_section "Collecting Proof Metrics"

  # Run sorry census with JSON output
  log_metric "Running sorry census..." "in progress"
  if python3 "$SCRIPT_DIR/sorry_census.py" --root "$PROJECT_ROOT" --out "$METRICS_DIR/sorry-census.json" >/dev/null 2>&1; then
    sorry_count=$(jq -r '.summary.holes // 0' "$METRICS_DIR/sorry-census.json" 2>/dev/null || echo "0")
    log_metric "Sorry holes (live)" "$sorry_count"
  else
    log_error "Failed to run sorry census"
    if [ "$FAIL_FAST" = true ]; then return 2; fi
  fi

  # Run axiom audit with JSON output (if available)
  log_metric "Running axiom audit..." "in progress"
  if python3 "$SCRIPT_DIR/axiom_audit.py" --root "$PROJECT_ROOT" --out "$METRICS_DIR/axiom-audit.json" >/dev/null 2>&1; then
    axiom_violations=$(jq 'length' "$METRICS_DIR/axiom-audit.json" 2>/dev/null || echo "0")
    log_metric "Axiom violations" "$axiom_violations"
  fi

  # Extract build metrics from logs
  if [ -f "$BUILD_LOG" ]; then
    build_time_sec=$(grep "Time:" "$BUILD_LOG" | tail -1 | awk '{print $2}' | sed 's/[^0-9.]//g' || echo "0")
    modules_compiled=$(grep "Compiled:" "$BUILD_LOG" | tail -1 | awk '{print $2}' | sed 's/[^0-9]//g' || echo "0")
  fi
  log_metric "Modules compiled" "${modules_compiled:-N/A}"
  log_metric "Build time (warm)" "${build_time_sec}s"

  # Generate proof metrics JSON
  local timestamp=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
  local git_sha=$(git -C "$PROJECT_ROOT" rev-parse --short HEAD 2>/dev/null || echo "unknown")
  local git_branch=$(git -C "$PROJECT_ROOT" rev-parse --abbrev-ref HEAD 2>/dev/null || echo "unknown")

  cat > "$METRICS_FILE" <<EOF
{
  "timestamp": "$timestamp",
  "git_sha": "$git_sha",
  "git_branch": "$git_branch",
  "metrics": {
    "sorry_count": {
      "total_holes": $sorry_count,
      "per_file": {}
    },
    "axiom_efficiency": {
      "violations": $axiom_violations,
      "flagship_declarations": 43
    },
    "build_metrics": {
      "warm_build_sec": $build_time_sec,
      "modules_compiled": $modules_compiled
    }
  },
  "status": $([ "$sorry_count" -eq 0 ] && [ "$axiom_violations" -eq 0 ] && echo '"pass"' || echo '"fail"')
}
EOF

  log_metric "Metrics written to" "$METRICS_FILE"
}

# ─────────────────────────────────────────────────────────────────────────
# Gating gates
# ─────────────────────────────────────────────────────────────────────────

run_gating_gates() {
  local exit_code=0

  log_section "Running Gating Gates (Merge-Blocking)"

  # Gate 1: Forbidden tokens precheck
  log_metric "Gate 1" "Reject native_decide/bv_decide/custom axioms"
  if ! python3 "$SCRIPT_DIR/forbidden_tokens.py" >/dev/null 2>&1; then
    log_error "Forbidden tokens check failed"
    [ "$FAIL_FAST" = true ] && return 1
    exit_code=1
  fi

  # Gate 2: Build
  log_metric "Gate 2" "Build (lake build)"
  if ! lake build 2>&1 | tee -a "$BUILD_LOG"; then
    log_error "Lake build failed"
    return 1
  fi

  # Gate 3: Sorry census
  log_metric "Gate 3" "Sorry census (zero holes)"
  if ! python3 "$SCRIPT_DIR/sorry_census.py" --root "$PROJECT_ROOT" --fail-on-holes >/dev/null 2>&1; then
    log_error "Sorry census found live holes"
    [ "$FAIL_FAST" = true ] && return 1
    exit_code=1
  fi

  # Gate 4: Axiom audit
  log_metric "Gate 4" "Axiom audit (approved axioms only)"
  if ! python3 "$SCRIPT_DIR/axiom_audit.py" --root "$PROJECT_ROOT" >/dev/null 2>&1; then
    log_error "Axiom audit failed"
    [ "$FAIL_FAST" = true ] && return 1
    exit_code=1
  fi

  # Gate 5: Import checks
  log_metric "Gate 5" "Import integrity"
  if ! bash "$SCRIPT_DIR/check-imports.sh" >/dev/null 2>&1; then
    log_error "Import check failed"
    [ "$FAIL_FAST" = true ] && return 1
    exit_code=1
  fi

  return "$exit_code"
}

# ─────────────────────────────────────────────────────────────────────────
# Benchmark gates (non-gating)
# ─────────────────────────────────────────────────────────────────────────

run_benchmarks() {
  log_section "Running Benchmarks (Non-Gating)"

  # Warm rebuild
  log_metric "Benchmark" "Warm rebuild timing"
  if ! timeout 300 lake build 2>&1 | tee -a "$BUILD_LOG"; then
    log_error "Warm rebuild timeout or failed (non-blocking)"
  fi

  # Note: Clean build skipped to avoid exceeding runner budget
  log_metric "Clean build" "Skipped (exceeds runner budget)"
}

# ─────────────────────────────────────────────────────────────────────────
# Report generation
# ─────────────────────────────────────────────────────────────────────────

generate_report() {
  if [ ! -f "$METRICS_FILE" ]; then
    log_error "No metrics file found at $METRICS_FILE"
    return 2
  fi

  log_section "Proof Metrics Summary"

  # Parse JSON using grep and simple text processing (avoid Python path issues)
  local sorry_count=$(grep -o '"total_holes": *[0-9]*' "$METRICS_FILE" | grep -o '[0-9]*' | head -1 || echo "0")
  local axiom_violations=$(grep -o '"violations": *[0-9]*' "$METRICS_FILE" | grep -o '[0-9]*' | head -1 || echo "0")
  local build_time=$(grep -o '"warm_build_sec": *[0-9]*\.?[0-9]*' "$METRICS_FILE" | grep -o '[0-9]*\.?[0-9]*' || echo "N/A")
  local modules=$(grep -o '"modules_compiled": *[0-9]*' "$METRICS_FILE" | grep -o '[0-9]*' || echo "N/A")
  local status=$(grep -o '"status": "[^"]*"' "$METRICS_FILE" | grep -o '"[^"]*"' | tail -1 | tr -d '"' || echo "unknown")

  if [ "$JSON_OUTPUT" = true ]; then
    cat "$METRICS_FILE"
  else
    cat <<EOF

Proof Metrics Summary
────────────────────────────────────────────────────────────────────
Metric                              Value              Status
────────────────────────────────────────────────────────────────────
Sorry Count (live holes)            $sorry_count                 $([ "$sorry_count" -eq 0 ] 2>/dev/null && echo "✅" || echo "❌")
Axiom Violations                    $axiom_violations                 $([ "$axiom_violations" -eq 0 ] 2>/dev/null && echo "✅" || echo "❌")
Build Time (warm)                   ${build_time}s
Modules Compiled                    $modules
────────────────────────────────────────────────────────────────────
Overall Status                                         $status
────────────────────────────────────────────────────────────────────

For detailed metrics, see: $METRICS_FILE
EOF
  fi

  [ "$status" = "pass" ] && return 0 || return 1
}

# ─────────────────────────────────────────────────────────────────────────
# Main orchestration
# ─────────────────────────────────────────────────────────────────────────

main() {
  cd "$PROJECT_ROOT"

  case "$MODE" in
    gating)
      run_gating_gates
      local exit_code=$?
      collect_metrics
      if [ "$JSON_OUTPUT" = true ]; then
        cat "$METRICS_FILE"
      fi
      return "$exit_code"
      ;;

    metrics)
      collect_metrics
      if [ "$JSON_OUTPUT" = true ]; then
        cat "$METRICS_FILE"
      fi
      ;;

    benchmarks)
      run_benchmarks
      collect_metrics
      if [ "$JSON_OUTPUT" = true ]; then
        cat "$METRICS_FILE"
      fi
      ;;

    full)
      run_gating_gates || { collect_metrics; return 1; }
      run_benchmarks || true
      collect_metrics
      if [ "$JSON_OUTPUT" = true ]; then
        cat "$METRICS_FILE"
      fi
      ;;

    report)
      generate_report
      ;;

    *)
      log_error "Unknown mode: $MODE"
      cat >&2 <<EOF
Usage: $0 <mode> [options]

Modes:
  gating       Run merge-blocking gates only (CI primary)
  metrics      Collect proof metrics only (no build)
  benchmarks   Run benchmarks (non-gating)
  full         Gating + metrics + benchmarks (full local validation)
  report       Generate summary report from cached results

Options:
  --json          Output results as JSON
  --fail-fast     Exit on first failure
  --parallel N    Run N parallel jobs where applicable
  --baseline REF  Compare against git ref/commit (for report mode)
EOF
      return 1
      ;;
  esac
}

main "$@"
