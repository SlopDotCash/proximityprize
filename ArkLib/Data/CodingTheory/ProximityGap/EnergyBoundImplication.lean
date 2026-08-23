/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection

/-!
# `GaussianEnergyBound ⟹ DCEnergyBound` — the corrected hypothesis is weaker (#407)

The in-tree `GaussianEnergyBound G r` (`E_r ≤ Wick`) is strictly STRONGER than the corrected
DC-subtracted `DCEnergyBound G r` (`q·E_r − |G|^{2r} ≤ q·Wick`, i.e. `A_r ≤ Wick`): subtracting the
non-negative DC mass `|G|^{2r}` only weakens the inequality.

> **`dcEnergyBound_of_gaussianEnergyBound`** — `GaussianEnergyBound G r ⟹ DCEnergyBound G r`.

Consequence: any proof of the in-tree bound (e.g. in the proven regime `q > (2r)^{|G|/2}` via
Lam–Leung + `EffectiveTransfer`, where `E_r = E_r^{(0)} ≤ Wick`) automatically yields `DCEnergyBound`,
hence the corrected non-vacuous reduction. And the prize needs only the WEAKER `DCEnergyBound` — which
remains true where `GaussianEnergyBound` is false (the prize regime). So the DC subtraction strictly
enlarges the regime in which the reduction is valid.

Issue #407.
-/

open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound ArkLib.ProximityGap.DCEnergyCorrection

namespace ArkLib.ProximityGap.EnergyBoundImplication

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The corrected hypothesis is weaker.** `GaussianEnergyBound G r ⟹ DCEnergyBound G r`: the
DC-subtracted bound is implied by the raw one (subtracting `|G|^{2r} ≥ 0` weakens the inequality). -/
theorem dcEnergyBound_of_gaussianEnergyBound {G : Finset F} {r : ℕ}
    (h : GaussianEnergyBound G r) : DCEnergyBound G r := by
  unfold GaussianEnergyBound at h
  unfold DCEnergyBound
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have hd : (0 : ℝ) ≤ (G.card : ℝ) ^ (2 * r) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h hq, hd]

end ArkLib.ProximityGap.EnergyBoundImplication
#print axioms ArkLib.ProximityGap.EnergyBoundImplication.dcEnergyBound_of_gaussianEnergyBound
