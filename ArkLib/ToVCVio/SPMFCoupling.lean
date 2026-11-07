/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ProximityPrize.Compatibility.CompletedPMFCoupling

/-!
# Completed-distribution coupling compatibility

The former SPMF-specific facts now live in
`ProximityPrize.Compatibility.CompletedPMFCoupling` over explicit `PMF (Option α)`
distributions. They retain arbitrary countable support and the `none` failure mass, while
canonical measure total variation owns the metric. The exact API mapping is recorded in
`scripts/integration/probability-api-migration.json`.
-/
