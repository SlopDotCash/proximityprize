/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment

/-!
# The sub-Gaussian fourth moment of the Gauss period (#407)

The `r = 2` instance of the corrected DC-subtracted energy bound is the **sub-Gaussian fourth moment**
— the kurtosis input of the period central limit theorem (C14). From `DCEnergyBound G 2` and the
DC-subtracted moment identity `∑_{b≠0}‖η_b‖^4 = q·E_2 − |G|^4`:

> **`fourth_moment_le_of_dc`** — `DCEnergyBound G 2 ⟹ ∑_{b≠0}‖η_b‖^4 ≤ 3·q·|G|²`.

Together with the exact second moment `∑_{b≠0}‖η_b‖² = q·|G| − |G|²` this gives the period kurtosis
`≤ 3·(1+o(1))` — the **Gaussian** value, i.e. the period is sub-Gaussian at the 4th moment (the
provable instance of the CLT; `E_2 = 3|G|²−3|G|` for `q > 2^{|G|}`). The full CLT (all moments,
`r ≈ ln q`) is `A_r ≤ Wick` = BGK.

Issue #407.
-/

open Finset ArkLib.ProximityGap.SubgroupGaussSumSecondMoment ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCEnergyCorrection ArkLib.ProximityGap.DCSubtractedMoment

namespace ArkLib.ProximityGap.FourthMomentCLT

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Sub-Gaussian fourth moment.** Under `DCEnergyBound G 2`, the DC-subtracted fourth moment is at most
the Gaussian value: `∑_{b≠0}‖η_b‖^4 ≤ 3·q·|G|²`. This is the kurtosis input of the period CLT. -/
theorem fourth_moment_le_of_dc {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (h : DCEnergyBound G 2) :
    ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ 4
      ≤ 3 * (Fintype.card F : ℝ) * (G.card : ℝ) ^ 2 := by
  have hmom : ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * 2)
      = (Fintype.card F : ℝ) * (rEnergy G 2 : ℝ) - (G.card : ℝ) ^ (2 * 2) :=
    sum_nonzero_moment hψ G 2
  unfold DCEnergyBound at h
  have hdf : (Nat.doubleFactorial (2 * 2 - 1) : ℝ) = 3 := by norm_num [Nat.doubleFactorial]
  rw [hdf] at h
  -- h : q·E_2 − |G|^4 ≤ q·(3·|G|^2);  ∑ ‖η‖^4 = q·E_2 − |G|^4
  have h44 : (4 : ℕ) = 2 * 2 := by norm_num
  calc ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ 4
      = ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * 2) := by rw [h44]
    _ = (Fintype.card F : ℝ) * (rEnergy G 2 : ℝ) - (G.card : ℝ) ^ (2 * 2) := hmom
    _ ≤ (Fintype.card F : ℝ) * (3 * (G.card : ℝ) ^ 2) := h
    _ = 3 * (Fintype.card F : ℝ) * (G.card : ℝ) ^ 2 := by ring

end ArkLib.ProximityGap.FourthMomentCLT
#print axioms ArkLib.ProximityGap.FourthMomentCLT.fourth_moment_le_of_dc
