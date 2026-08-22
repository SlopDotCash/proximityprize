/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WeilRegimeClosure

/-!
# A residual-free Garcia–Voloch instance at `n = 12`: `μ_12 ⊆ F_37` (#389)

Extends the concrete residual-free sequence (`μ_4 ⊆ F_13`, `μ_6 ⊆ F_37`, `μ_8 ⊆ F_41`,
`μ_14 ⊆ F_239`) to order 12 with the **largest excess seen so far**.  `μ_12 ⊆ F_37` (the 12th roots
of unity, `8` a primitive 12th root since `8^6 = −1`) has additive energy `E = 684`; the
Sidon-modulo-negation value is `3·12² − 3·12 = 396`, so `energyExcess = 288 = 2·12²` and the general
`C = 2` branch of `gvRepBound_of_energyExcess_quadratic` fires:

> **`mu12_F37_gvRepBound`** — `GVRepBound (μ_12 ⊆ F_37) 8`: every nonzero `t` has at most `8`
> additive representations (`(3+2)·12 = 60 ≤ 8² = 64`, `8³ = 512 ≤ 64·12² = 9216`; minimal `M` for
> excess `288`).

The concrete excess sequence is now `μ_4: 0, μ_6: 0, μ_8: 32 (C=1), μ_12: 288 (C=2), μ_14: 168
(C=1)` — illustrating the `energyExcess ≈ |G|²` growth the quadratic branch is built for.  Every
hypothesis (including the energy `E = 684`) is discharged by `decide`; axiom-clean.
-/

open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg

instance prime37FactMu12 : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- `μ_12 ⊆ F_37`, the 12th roots of unity `{1, 6, 8, 10, 11, 14, 23, 26, 27, 29, 31, 36}`
(`8` is a primitive 12th root: `8^6 = 36 = −1`). -/
def mu12_F37 : Finset (ZMod 37) := {1, 6, 8, 10, 11, 14, 23, 26, 27, 29, 31, 36}

set_option maxRecDepth 400000 in
/-- **Residual-free Garcia–Voloch bound for `μ_12 ⊆ F_37`** (excess `C = 2`).  `μ_12` has `E = 684`,
`energyExcess = 288 = 2·12²`, so the `C = 2` branch yields `GVRepBound (μ_12) 8`. -/
theorem mu12_F37_gvRepBound : GVRepBound mu12_F37 8 :=
  gvRepBound_of_energyExcess_quadratic (G := mu12_F37) (n := 12) (C := 2) (M := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
