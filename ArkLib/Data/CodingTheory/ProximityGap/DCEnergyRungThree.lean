/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussianEnergyThreeRepThree
import ArkLib.Data.CodingTheory.ProximityGap.EnergyBoundImplication

/-!
# The r = 3 corrected DC rung, modulo `RepThree` (#407)

Composes the in-tree r=3 reducer (`gaussianEnergyBound_three_of_repThree`: `RepThree G ⟹
GaussianEnergyBound G 3`) with the corrected-hypothesis implication (`dcEnergyBound_of_gaussianEnergyBound`):

> **`dcEnergyBound_three_of_repThree`** — `RepThree G ⟹ DCEnergyBound G 3` (negation-closed `G`).

So the **entire corrected reduction** (`DCEnergyBound ⟹ M ⟹ E(G) = O(n² log q)`, via `PrizeEnergyHeadline`)
works at `r = 3` the instant `RepThree(μ_{2^m})` is discharged in char-`p`. `RepThree` is **true in char-0**
(verified: zero non-antipodal zero-sum sextuples of `μ₄,μ₈,μ₁₆`); the open part is the char-`p` transfer
at a prime threshold — the exact r=3 analog of the landed r=2 `sidonModNeg_rootsOfUnity_improved`.

Issue #407.
-/

open ArkLib.ProximityGap.GaussianEnergyThreeRepThree
open ArkLib.ProximityGap.EnergyBoundImplication
open ArkLib.ProximityGap.DCEnergyCorrection

namespace ArkLib.ProximityGap.DCEnergyRungThree

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The r = 3 corrected DC rung from `RepThree`.** For negation-closed `G` with a primitive additive
character, the order-6 antipodal-pairing residual `RepThree G` discharges the corrected
`DCEnergyBound G 3`. Slots into `PrizeEnergyHeadline` to give the full reduction at `r = 3`. -/
theorem dcEnergyBound_three_of_repThree {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} (hG : ∀ x ∈ G, -x ∈ G) (hrep : RepThree G) :
    DCEnergyBound G 3 :=
  dcEnergyBound_of_gaussianEnergyBound (gaussianEnergyBound_three_of_repThree hψ hG hrep)

end ArkLib.ProximityGap.DCEnergyRungThree
#print axioms ArkLib.ProximityGap.DCEnergyRungThree.dcEnergyBound_three_of_repThree
