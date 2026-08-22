/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WeilRegimeClosure

/-!
# A RESIDUAL-FREE end-to-end instance (#389)

The general wall closure (`wall_closes_in_weil_regime`) is conditional on the standard
Weil energy bound.  This file discharges that bound *by computation* for a concrete
deployed-shape instance, giving a **fully residual-free** end-to-end Garcia–Voloch
representation bound — every hypothesis decided, no open input.

`G = μ_6 ⊆ F_37` (the 6th roots of unity, `{1,10,11,26,27,36}`): its additive energy is
`E = 90 = 3·6²−3·6`, so `energyExcess G = 0` — `μ_6` is *exactly* Sidon-modulo-negation
(matching the `n²/p → 0` prediction).  Feeding `energyExcess = 0` (i.e. `C = 0`) into
`gvRepBound_of_energyExcess_quadratic` yields, with no residual:

> **`mu6_F37_gvRepBound`** — `GVRepBound (μ_6 ⊆ F_37) 5`: every nonzero `t` has at most
> `5` additive representations, the optimal `√(3·6) ≈ 4.2` scale.

This is the complete supply-wall closure realised end-to-end on a concrete subgroup,
demonstrating that the `δ*`-pinning machinery is residual-free once the energy is known.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg

instance prime37Fact : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- `μ_6 ⊆ F_37`, the 6th roots of unity. -/
def mu6 : Finset (ZMod 37) := {1, 10, 11, 26, 27, 36}

/-- **Residual-free end-to-end Garcia–Voloch bound for `μ_6 ⊆ F_37`.**  Every hypothesis
— including the energy (excess `= 0`) — is discharged by `decide`; no open input. -/
theorem mu6_F37_gvRepBound : GVRepBound mu6 5 :=
  gvRepBound_of_energyExcess_quadratic (G := mu6) (n := 6) (C := 0) (M := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

instance prime239Fact : Fact (Nat.Prime 239) := ⟨by norm_num⟩

/-- `μ_14 ⊆ F_239`, the 14th roots of unity. -/
def mu14 : Finset (ZMod 239) :=
  {1, 10, 24, 38, 44, 98, 100, 139, 141, 195, 201, 215, 229, 238}

-- **Residual-free instance with NONZERO excess (C = 1).**  μ_14 ⊆ F_239 has
-- energyExcess = 168 ≤ 1·14², so the general C > 0 branch fires: GVRepBound mu14 8,
-- every hypothesis (including the energy) decided — no residual, even off exactly-Sidon.
set_option maxRecDepth 100000 in
theorem mu14_F239_gvRepBound : GVRepBound mu14 8 :=
  gvRepBound_of_energyExcess_quadratic (G := mu14) (n := 14) (C := 1) (M := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms mu6_F37_gvRepBound
#print axioms mu14_F239_gvRepBound
