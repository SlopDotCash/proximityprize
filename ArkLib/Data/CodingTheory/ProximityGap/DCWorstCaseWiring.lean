/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCOptimized
import ArkLib.Data.CodingTheory.ProximityGap.InteriorWorstCaseIncompleteSum

/-!
# Wiring the corrected DC reduction into the interior-δ* consumer (#407)

The interior δ* consumer chain (`InteriorWorstCaseIncompleteSum`) consumes the named Prop
`WorstCaseIncompleteSumBound ψ G M := ∀ b ≠ 0, ‖η_b‖² ≤ M`. The in-tree
`GaussPeriodMomentBound.worstCaseIncompleteSumBound_of_energyBound` discharges it from
`GaussianEnergyBound` — **vacuous at the prize** (its `E_r ≤ Wick` hypothesis is false for `n ≥ 64`).
This file discharges it from the **corrected** DC-subtracted hypothesis (true at the prize):

> **`worstCaseBound_of_dcEnergyBound`** — `DCEnergyBound G r` at `r ≥ max(1, ln q)` ⟹
> `WorstCaseIncompleteSumBound ψ G (2e·|G|·r)`.

So the corrected chain `DCEnergyBound ⟹ M ≤ √(2e·n·ln q) ⟹ WorstCaseIncompleteSumBound ⟹ interior δ*`
is non-vacuous end-to-end at the prize parameters; the sole open input is `A_r ≤ Wick` (BGK).

Issue #407.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.DCEnergyCorrection ArkLib.ProximityGap.DCOptimized
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum

namespace ArkLib.ProximityGap.DCWorstCaseWiring

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The corrected reduction feeds the δ* consumer.** From the DC-subtracted energy bound at order
`r ≥ max(1, ln q)`, the worst-case incomplete-sum bound holds at scale `M = 2e·|G|·r` — non-vacuously
at the prize, unlike the in-tree `GaussianEnergyBound` route. -/
theorem worstCaseBound_of_dcEnergyBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ}
    (hr : 1 ≤ r) (hrq : Real.log (Fintype.card F) ≤ r) (h : DCEnergyBound G r) :
    WorstCaseIncompleteSumBound ψ G (2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ)) :=
  fun b hb => eta_sq_le_dcOptimized hψ hr hrq h hb

end ArkLib.ProximityGap.DCWorstCaseWiring
#print axioms ArkLib.ProximityGap.DCWorstCaseWiring.worstCaseBound_of_dcEnergyBound
