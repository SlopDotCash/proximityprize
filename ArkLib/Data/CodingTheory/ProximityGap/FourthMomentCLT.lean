/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment

/-!
# A Gaussian-comparison fourth-moment bound for the Gauss periods (#407)

The `r = 2` instance of the corrected DC-subtracted energy bound is a **Gaussian-comparison
fourth-moment upper bound** for the Gauss periods. From the explicit assumption
`DCEnergyBound G 2` and the DC-subtracted moment identity `∑_{b≠0}‖η_b‖^4 = q·E_2 − |G|^4`:

> **`fourth_moment_le_of_dc`** — `DCEnergyBound G 2 ⟹ ∑_{b≠0}‖η_b‖^4 ≤ 3·q·|G|²`.

Together with the exact second moment `∑_{b≠0}‖η_b‖² = q·|G| − |G|²` this bounds the normalized
fourth moment (kurtosis) of the periods over `b ≠ 0` by `3·q(q−1)/(q−|G|)²`, i.e. by the real
Gaussian value `3` up to a `1 + O(|G|/q)` factor. `DCEnergyBound G 2` is a hypothesis here; it holds
e.g. when `E_2 = 3|G|² − 3|G|` (Sidon mod negation, proved for `G = μ_n` with `n = 2^m`, `p > 2^n`
in `SidonModNegEnergyEquality.lean`).

**This is not a central limit theorem.** An upper bound on one moment (or even on all moments,
`A_r ≤ Wick`) does not give distributional convergence to a Gaussian: that needs a normalization
and convergence (not mere domination) of moments or distributions. For instance a fixed Rademacher
`±1` variable has every even moment `1 ≤ (2r−1)!!` and is not Gaussian. The all-moment
inequalities `A_r ≤ Wick` up to `r ≈ ln q` (the BGK-type target) would give high-order tail
bounds; a period CLT would be a separate statement with its own hypotheses and conclusion, and is
not formalized here.

Issue #407.
-/

open Finset ArkLib.ProximityGap.SubgroupGaussSumSecondMoment ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCEnergyCorrection ArkLib.ProximityGap.DCSubtractedMoment

namespace ArkLib.ProximityGap.FourthMomentCLT

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Gaussian-comparison fourth-moment bound.** Under the explicit assumption
`DCEnergyBound G 2`, the DC-subtracted fourth moment is at most the Gaussian-comparison value:
`∑_{b≠0}‖η_b‖^4 ≤ 3·q·|G|²`. An upper bound only; it does not by itself give a CLT. -/
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
