/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WeilRegimeClosure

/-!
# A residual-free Garcia–Voloch instance: `μ_4 ⊆ F_13` (#389)

Companion to `ConcreteWeilInstance` (`μ_6 ⊆ F_37`, `μ_14 ⊆ F_239`).  `μ_4 ⊆ F_13` (the 4th roots of
unity `{1, 5, 8, 12}`, with `5` a primitive 4th root) is exactly Sidon-modulo-negation: its additive
energy is `E = 36 = 3·4² − 3·4`, so `energyExcess = 0`.  Feeding `C = 0` into
`gvRepBound_of_energyExcess_quadratic` gives, with no residual,

> **`mu4_F13_gvRepBound`** — `GVRepBound (μ_4 ⊆ F_13) 4`: every nonzero `t` has at most `4` additive
> representations.

This is the smallest untried even order, in the fastest field, extending the in-tree
`n⁴/p`-energy-scaling sequence of concrete residual-free instances.  Every hypothesis (including the
energy) is discharged by `decide`; axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg

instance prime13FactMu4 : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- `μ_4 ⊆ F_13`, the 4th roots of unity `{1, 5, 8, 12}` (`5` is a primitive 4th root). -/
def mu4_F13 : Finset (ZMod 13) := {1, 5, 8, 12}

/-- **Residual-free Garcia–Voloch bound for `μ_4 ⊆ F_13`.**  `μ_4` is exactly Sidon-modulo-negation
(`E = 36 = 3·4²−3·4`, `energyExcess = 0`), so the `C = 0` branch fires with no residual: every
nonzero `t` has at most `4` additive representations. -/
theorem mu4_F13_gvRepBound : GVRepBound mu4_F13 4 :=
  gvRepBound_of_energyExcess_quadratic (G := mu4_F13) (n := 4) (C := 0) (M := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
