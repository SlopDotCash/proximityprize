/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WeilRegimeClosure

/-!
# A residual-free Garcia–Voloch instance with nonzero excess: `μ_8 ⊆ F_41` (#389)

Companion to `ConcreteWeilInstance` / `ConcreteWeilInstanceMu4`.  `μ_8 ⊆ F_41` (the 8th roots of
unity `{1, 3, 9, 14, 27, 32, 38, 40}`, with `3` a primitive 8th root) is **not** exactly
Sidon-modulo-negation: its additive energy is `E = 200`, giving `energyExcess = 32 = E − (3·8²−3·8)`,
so `energyExcess ≤ 1·8²` and the general `C = 1` branch of `gvRepBound_of_energyExcess_quadratic`
fires:

> **`mu8_F41_gvRepBound`** — `GVRepBound (μ_8 ⊆ F_41) 6`: every nonzero `t` has at most `6` additive
> representations (`6³ = 216 ≤ 64·64`; the minimal `M` for excess `32`).

This validates the closure on a non-exactly-Sidon subgroup at a fresh field, complementing the
exactly-Sidon `μ_4`/`μ_6` instances and the `C = 1` `μ_14 ⊆ F_239` instance.  Every hypothesis
(including the energy) is discharged by `decide`; axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg

instance prime41FactMu8 : Fact (Nat.Prime 41) := ⟨by norm_num⟩

/-- `μ_8 ⊆ F_41`, the 8th roots of unity `{1, 3, 9, 14, 27, 32, 38, 40}` (`3` is a primitive
8th root: `3^4 = 40 = −1`). -/
def mu8_F41 : Finset (ZMod 41) := {1, 3, 9, 14, 27, 32, 38, 40}

set_option maxRecDepth 200000 in
/-- **Residual-free Garcia–Voloch bound for `μ_8 ⊆ F_41`** (nonzero excess `C = 1`).  `μ_8` has
`E = 200`, `energyExcess = 32 ≤ 1·8²`, so the `C = 1` branch yields `GVRepBound (μ_8) 6`. -/
theorem mu8_F41_gvRepBound : GVRepBound mu8_F41 6 :=
  gvRepBound_of_energyExcess_quadratic (G := mu8_F41) (n := 8) (C := 1) (M := 6)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
