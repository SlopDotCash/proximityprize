/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WeilRegimeClosure

/-!
# A high-excess concrete Garcia–Voloch instance: `μ_20 ⊆ F_41` (#389)

The opposite extreme from the exactly-Sidon instances (`μ_4/μ_6/μ_18`): `μ_20 ⊆ F_41` (the 20th
roots of unity, `⟨8⟩`) sits in a field so small relative to its order (`n²/p = 400/41 ≈ 9.8`) that it
is *far* from Sidon-modulo-negation — additive energy `E = 4020` versus the Sidon value
`3·20² − 3·20 = 1140`, so `energyExcess = 2880 = 7.2·20²`, requiring `C = 8`:

> **`mu20_F41_gvRepBound`** — `GVRepBound (μ_20 ⊆ F_41) 15` (`(3+8)·20 = 220 ≤ 15² = 225`,
> `15³ = 3375 ≤ 64·20² = 25600`).

This is the largest-excess point in the concrete sequence (`μ_4:0, μ_6:0, μ_8:32, μ_10:120/0,
μ_12:288, μ_14:168, μ_18:0, μ_20:2880`), illustrating the full range of the `n²/p` Sidon-defect
phenomenon: a *large* field makes `μ_n` exactly Sidon (`C=0`), a *small* one makes it far from it
(`C=8`).  Every hypothesis (including `E = 4020`, a sum of `20⁴` indicator terms) is discharged by
`decide` (8M heartbeats, ~29 s); axiom-clean.
-/

open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg

instance prime41FactMu20 : Fact (Nat.Prime 41) := ⟨by norm_num⟩

/-- `μ_20 ⊆ F_41`, the 20th roots of unity (`⟨8⟩`). -/
def mu20_F41 : Finset (ZMod 41) :=
  {1, 2, 4, 5, 8, 9, 10, 16, 18, 20, 21, 23, 25, 31, 32, 33, 36, 37, 39, 40}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 8000000 in
/-- **Residual-free Garcia–Voloch bound for `μ_20 ⊆ F_41`** (high excess, `C = 8`).  `μ_20` has
`E = 4020`, `energyExcess = 2880 ≤ 8·20²`, so the `C = 8` branch yields `GVRepBound (μ_20) 15`. -/
theorem mu20_F41_gvRepBound : GVRepBound mu20_F41 15 :=
  gvRepBound_of_energyExcess_quadratic (G := mu20_F41) (n := 20) (C := 8) (M := 15)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
