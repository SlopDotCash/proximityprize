#!/usr/bin/env bash
# pg-warm.sh — pre-build the Proximity Gap (#334) SUBSTRATE oleans ONCE, so every agent's
# `pg-iterate.sh` (lake env lean) starts hot and never stalls on a missing olean.
#
# Run this ONCE per machine (or after a mathlib bump). Do NOT run it per-iteration. It takes
# the build lock, so run it while no agent is mid-`./scripts/lake-locked.sh build`. After it finishes, all agents
# iterate lock-free in parallel via `scripts/pg-iterate.sh`.
#
# It builds only the substrate the Frontier lanes consume — NOT the full 808-file cone.
set -euo pipefail
MODS=(
  ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
  ArkLib.Data.CodingTheory.ProximityGap.KKH26WitnessSpread
  ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman
  ArkLib.Data.CodingTheory.ProximityGap.KKH26PolyFieldCeiling
  ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread
  ArkLib.Data.CodingTheory.ProximityGap.JohnsonListBound
  ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityMCA
  ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityMCAP
  ArkLib.Data.CodingTheory.Connections.ListDecodingAndCA
)
echo "Warming ${#MODS[@]} substrate modules (one-time, holds the build lock)…"
# one lake invocation builds them in parallel across all cores (shared dependency graph)
warm_log="$(mktemp "${TMPDIR:-/tmp}/pg-warm.XXXXXX")"
trap 'rm -f "$warm_log"' EXIT
if "$(dirname "$0")/lake-locked.sh" build "${MODS[@]}" >"$warm_log" 2>&1; then
  tail -n 2 "$warm_log"
else
  warm_status=$?
  cat "$warm_log" >&2 || true
  exit "$warm_status"
fi
echo "Done. Agents may now iterate lock-free with scripts/pg-iterate.sh."
