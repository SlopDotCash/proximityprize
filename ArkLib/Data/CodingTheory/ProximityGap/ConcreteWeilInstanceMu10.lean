/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WeilRegimeClosure

/-!
# A residual-free Garcia–Voloch instance at `n = 10`: `μ_10 ⊆ F_31` (#389)

Fills the order-10 entry of the concrete residual-free sequence (`μ_4 ⊆ F_13`, `μ_6 ⊆ F_37`,
`μ_8 ⊆ F_41`, `μ_10 ⊆ F_31`, `μ_12 ⊆ F_37`, `μ_14 ⊆ F_239`).  `μ_10 ⊆ F_31` (the 10th roots of
unity, `−2` a primitive 10th root since `(−2)^5 = −1`) has additive energy `E = 390`; the
Sidon-modulo-negation value is `3·10² − 3·10 = 270`, so `energyExcess = 120` and (since
`120 ≤ 2·10²`) the general `C = 2` branch of `gvRepBound_of_energyExcess_quadratic` fires:

> **`mu10_F31_gvRepBound`** — `GVRepBound (μ_10 ⊆ F_31) 8`: every nonzero `t` has at most `8`
> additive representations (`(3+2)·10 = 50 ≤ 8² = 64`, `8³ = 512 ≤ 64·10² = 6400`).

The concrete excess sequence is now `μ_4:0, μ_6:0, μ_8:32 (C=1), μ_10:120 (C=2), μ_12:288 (C=2),
μ_14:168 (C=1)`.  Every hypothesis (including the energy `E = 390`) is discharged by `decide`;
axiom-clean.
-/

open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg

instance prime31FactMu10 : Fact (Nat.Prime 31) := ⟨by norm_num⟩

/-- `μ_10 ⊆ F_31`, the 10th roots of unity `{1, 2, 4, 8, 15, 16, 23, 27, 29, 30}`
(`−2 = 29` is a primitive 10th root: `(−2)^5 = −1 = 30`). -/
def mu10_F31 : Finset (ZMod 31) := {1, 2, 4, 8, 15, 16, 23, 27, 29, 30}

set_option maxRecDepth 400000 in
/-- **Residual-free Garcia–Voloch bound for `μ_10 ⊆ F_31`** (excess `C = 2`).  `μ_10` has `E = 390`,
`energyExcess = 120 ≤ 2·10²`, so the `C = 2` branch yields `GVRepBound (μ_10) 8`. -/
theorem mu10_F31_gvRepBound : GVRepBound mu10_F31 8 :=
  gvRepBound_of_energyExcess_quadratic (G := mu10_F31) (n := 10) (C := 2) (M := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
