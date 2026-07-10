#!/usr/bin/env bash
# pg-warm.sh — pre-build the Proximity Gap (#334) SUBSTRATE oleans ONCE, so every agent's
# `pg-iterate.sh` (lake env lean) starts hot and never stalls on a missing olean.
#
# Run this ONCE per machine (or after a mathlib bump). Do NOT run it per-iteration. It takes
# the build lock, so run it while no agent is mid-`lake build`. After it finishes, all agents
# iterate lock-free in parallel via `scripts/pg-iterate.sh`.
#
# It builds only the substrate the Frontier lanes consume — NOT the full 808-file cone.
set -uo pipefail
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
"$(dirname "$0")/lake-locked.sh" build "${MODS[@]}" 2>&1 | tail -2
echo "Done. Agents may now iterate lock-free with scripts/pg-iterate.sh."
