#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

fixture_tmp="$(mktemp -d)"
trap 'rm -rf "$fixture_tmp"' EXIT

./scripts/lake-locked.sh exe lint-style --self-test

plugin_path="$(./scripts/lake-locked.sh query ArkLibLintPlugin:shared)"
allowed="scripts/LintStyleFixtures/PluginAllowed.lean"
rejected="scripts/LintStyleFixtures/PluginRejected.lean"
guard_rejected="scripts/LintStyleFixtures/PluginGuardRejected.lean"

lake env lean --plugin="$plugin_path" "$allowed"

if lake env lean --plugin="$plugin_path" "$rejected" >"$fixture_tmp/rejected.log" 2>&1; then
  echo "ERROR: source-policy plugin accepted forbidden suppression fixtures" >&2
  exit 1
fi

for root in linter pp profiler trace; do
  grep -Fq "Forbidden \`set_option ${root}.*\`" "$fixture_tmp/rejected.log"
done
grep -Fq "\`@[nolint]\` suppressions are forbidden" "$fixture_tmp/rejected.log"
if [[ "$(grep -Fc '`@[nolint]` suppressions are forbidden' "$fixture_tmp/rejected.log")" -ne 2 ]]; then
  echo "ERROR: source-policy plugin did not reject both nolint attribute forms" >&2
  exit 1
fi

if lake env lean --plugin="$plugin_path" "$guard_rejected" >"$fixture_tmp/guard-rejected.log" 2>&1; then
  echo "ERROR: source-policy plugin errors were discarded by #guard_msgs" >&2
  exit 1
fi

grep -Fq 'Forbidden `set_option linter.*`' "$fixture_tmp/guard-rejected.log"
grep -Fq "\`@[nolint]\` suppressions are forbidden" "$fixture_tmp/guard-rejected.log"

if lake env lean --plugin="$plugin_path" scripts/LintStyleFixtures/PluginProbabilityRejected.lean \
    >"$fixture_tmp/probability-rejected.log" 2>&1; then
  echo "ERROR: source-policy plugin accepted retired probability notation" >&2
  exit 1
fi
for token in '$ᵖ' 'Pr_{' 'Pr[' '𝒮['; do
  grep -Fq "Retired probability notation \`$token\`" "$fixture_tmp/probability-rejected.log"
done

stop_plugin_path="$(./scripts/lake-locked.sh query StopTacticPlugin:shared)"
stop_rejected="scripts/LintStyleFixtures/StopTacticRejected.lean"
lake env lean --plugin="$stop_plugin_path" scripts/LintStyleFixtures/StopTacticAllowed.lean

if ! lake env lean "$stop_rejected" >"$fixture_tmp/stop-compiler.log" 2>&1; then
  cat "$fixture_tmp/stop-compiler.log" >&2
  echo "ERROR: the stop fixture must compile without the source-policy plugin" >&2
  exit 1
fi

if lake env lean --plugin="$stop_plugin_path" "$stop_rejected" \
    >"$fixture_tmp/stop-rejected.log" 2>&1; then
  echo "ERROR: source-policy plugin accepted the stop tactic" >&2
  exit 1
fi

if [[ "$(grep -Fc 'error: The `stop` tactic admits open goals.' "$fixture_tmp/stop-rejected.log")" -ne 13 ]]; then
  cat "$fixture_tmp/stop-rejected.log" >&2
  echo "ERROR: source-policy plugin did not reject all 13 stop tactic occurrences" >&2
  exit 1
fi

echo "ArkLib source-policy plugin fixtures passed"
