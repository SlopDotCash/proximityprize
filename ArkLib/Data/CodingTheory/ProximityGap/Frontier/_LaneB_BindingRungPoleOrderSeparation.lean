/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._OffBGK_UnionGrowthGeneratingFn

/-!
# Lane B binding-rung pole-order separation substrate (#444)

This file supplies the small wiring substrate consumed by
`_AvL12_BindingDiagonalOrbitCountConstant`: the binding-diagonal orbit count is the orbit-count
family sampled on the binding rung `rstar n`, and a constant diagonal orbit count discharges the
Off-BGK distinct-γ union growth law via the existing simple-pole theorem
`unionFloor_of_pole_le_one`.

Honest scope: this proves only the conditional reduction. It does **not** prove the measured
constant orbit-count persistence, and it does not touch the BGK/Paley signed-sum core.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Filter

namespace ArkLib.ProximityGap.LaneBBindingRungPole

open ArkLib.ProximityGap.SpecF8
open ArkLib.ProximityGap.OffBGK.UnionGrowthGF

/-- The binding-diagonal orbit count: sample the two-parameter orbit-count table `O` on the
binding rung `rstar n` at tower index `n`. -/
def diagonalOrbitCount (O : ℕ → ℕ → ℕ) (rstar : ℕ → ℕ) : ℕ → ℕ :=
  fun n => O (rstar n) n

/-- **Binding-rung simple-pole discharge.** If the binding-diagonal orbit count is constant `c`,
`U` decomposes as that count times a fixed orbit size, and the budget eventually dominates
`c·orbitSize`, then the Off-BGK distinct-γ union growth law holds. This is just the Lane-B
specialization of `_OffBGK_UnionGrowthGeneratingFn.unionFloor_of_pole_le_one` to the diagonal
`n ↦ O (rstar n) n`. -/
theorem unionFloor_of_binding_orbit_collapse
    (U budget : ℕ → ℕ) (O : ℕ → ℕ → ℕ) (rstar : ℕ → ℕ) (orbitSize c : ℕ)
    (hpole : PoleOrderOne (diagonalOrbitCount O rstar) c)
    (hdecomp : ∀ n, U n = diagonalOrbitCount O rstar n * orbitSize)
    (hbudget : ∀ᶠ n in atTop, c * orbitSize ≤ budget n) :
    DistinctGammaUnionGrowthLaw U budget :=
  unionFloor_of_pole_le_one U budget (diagonalOrbitCount O rstar) orbitSize c
    hpole hdecomp hbudget

/-- The `c = 1` consumer used by the measured AvL12 diagonal-pole file: if the diagonal orbit count
is persistently one and the budget eventually dominates one orbit, the union growth law holds. -/
theorem unionFloor_of_binding_orbit_one
    (U budget : ℕ → ℕ) (O : ℕ → ℕ → ℕ) (rstar : ℕ → ℕ) (orbitSize : ℕ)
    (hpole : PoleOrderOne (diagonalOrbitCount O rstar) 1)
    (hdecomp : ∀ n, U n = diagonalOrbitCount O rstar n * orbitSize)
    (hbudget : ∀ᶠ n in atTop, orbitSize ≤ budget n) :
    DistinctGammaUnionGrowthLaw U budget := by
  refine unionFloor_of_binding_orbit_collapse U budget O rstar orbitSize 1 hpole hdecomp ?_
  simpa using hbudget

end ArkLib.ProximityGap.LaneBBindingRungPole

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.LaneBBindingRungPole.diagonalOrbitCount
#print axioms ArkLib.ProximityGap.LaneBBindingRungPole.unionFloor_of_binding_orbit_collapse
#print axioms ArkLib.ProximityGap.LaneBBindingRungPole.unionFloor_of_binding_orbit_one
