/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# The DC-subtracted energy bound holds unconditionally at `r = 1` (#407)

The corrected prize hypothesis `DCEnergyBound G r` (`A_r ≤ Wick`) holds **unconditionally and exactly at
`r = 1`** — the anchor of the moment ladder. First, `E_1(G) = |G|` (only the diagonal contributes); this
follows by comparing the two Parseval identities `∑_b ‖η_b‖² = q·E_1` and `∑_b ‖η_b‖² = q·|G|`. Then
`DCEnergyBound G 1` reduces to `q·|G| − |G|² ≤ q·|G|`, i.e. `−|G|² ≤ 0`.

> **`rEnergy_one`** — `E_1(G) = |G|`.
> **`dcEnergyBound_one`** — `DCEnergyBound G 1` (unconditional).

So the corrected `A_r ≤ Wick` ladder is *anchored* for free at `r = 1`; the open content is `r ≥ 2`
(where the char-`p` additive-energy anomaly = BGK enters).

Issue #407.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCEnergyCorrection

namespace ArkLib.ProximityGap.DCEnergyBaseCase

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **First additive energy is the cardinality**, via Parseval: from `q·E_1 = ∑_b ‖η_b‖² = q·|G|`. -/
theorem rEnergy_one {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    (rEnergy G 1 : ℝ) = (G.card : ℝ) := by
  have h1 : ∑ b : F, ‖eta ψ G b‖ ^ (2 * 1) = (Fintype.card F : ℝ) * (rEnergy G 1 : ℝ) :=
    subgroup_gaussSum_moment hψ G 1
  have h2 : ∑ b : F, ‖eta ψ G b‖ ^ 2 = (Fintype.card F : ℝ) * (G.card : ℝ) :=
    subgroup_gaussSum_secondMoment hψ G
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have : (Fintype.card F : ℝ) * (rEnergy G 1 : ℝ) = (Fintype.card F : ℝ) * (G.card : ℝ) := by
    rw [← h1]; simpa using h2
  exact mul_left_cancel₀ (ne_of_gt hq) this

/-- **The corrected hypothesis is free at `r = 1`.** `DCEnergyBound G 1` holds unconditionally:
it reduces to `q·|G| − |G|² ≤ q·|G|`, i.e. `−|G|² ≤ 0`. -/
theorem dcEnergyBound_one {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    DCEnergyBound G 1 := by
  unfold DCEnergyBound
  rw [rEnergy_one hψ G]
  have : (Nat.doubleFactorial (2 * 1 - 1) : ℝ) = 1 := by norm_num [Nat.doubleFactorial]
  rw [this]
  have hsq : (0 : ℝ) ≤ (G.card : ℝ) ^ (2 * 1) := by positivity
  nlinarith [hsq]

end ArkLib.ProximityGap.DCEnergyBaseCase

#print axioms ArkLib.ProximityGap.DCEnergyBaseCase.dcEnergyBound_one
