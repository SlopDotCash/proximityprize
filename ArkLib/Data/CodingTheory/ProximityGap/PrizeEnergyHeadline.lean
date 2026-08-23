/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCWorstCaseWiring

/-!
# The corrected prize energy headline — front door (#407)

A single capstone chaining the **corrected** DC reduction into the in-tree additive-energy consumer:

> **`prize_addEnergy_of_dcEnergyBound`** — from `DCEnergyBound G r` at `r ≥ max(1, ln q)` and the
> deployed regime `q ≥ |G|²`, the additive energy is `E(G) ≤ |G|² + 2e·|G|²·r`.

At `r = ⌈ln q⌉` this is `E(G) = O(n² log q)`. The whole corrected chain in one statement:
`DCEnergyBound ⟹ M ≤ √(2e·n·ln q)` (`worstCaseBound_of_dcEnergyBound`, non-vacuous at the prize —
unlike the in-tree DC-included `GaussianEnergyBound`, which is vacuous, see `DCEnergyCorrection`)
`⟹ WorstCaseIncompleteSumBound ⟹ E(G) = O(n² log q)` (`addEnergy_le_div`). The sole open input is
`DCEnergyBound` at `r ≈ ln q` — the BGK/anomaly-suppression core (`A_r ≤ Wick`).

Issue #407.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.DCWorstCaseWiring
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum

namespace ArkLib.ProximityGap.PrizeEnergyHeadline

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Corrected prize energy headline.** From the corrected DC-subtracted energy bound at the
optimal `r ≈ ln q` and the deployed regime `q ≥ |G|²`, the additive energy is `O(n² log q)`. The
full corrected chain `DCEnergyBound ⟹ M ⟹ WorstCaseIncompleteSumBound ⟹ E(G)` in one front door. -/
theorem prize_addEnergy_of_dcEnergyBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    {r : ℕ} (hr : 1 ≤ r) (hrq : Real.log (Fintype.card F) ≤ r) (hdc : DCEnergyBound G r)
    (hq : (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) (hqpos : 0 < Fintype.card F) :
    (addEnergy G : ℝ)
      ≤ (G.card : ℝ) ^ 2 + (2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ)) * (G.card : ℝ) := by
  have hwc := worstCaseBound_of_dcEnergyBound hψ hr hrq hdc
  have hM0 : (0 : ℝ) ≤ 2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ) := by positivity
  exact addEnergy_le_div hψ G hM0 hwc hq hqpos

end ArkLib.ProximityGap.PrizeEnergyHeadline
#print axioms ArkLib.ProximityGap.PrizeEnergyHeadline.prize_addEnergy_of_dcEnergyBound
