/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound

/-!
# The sharp DC-subtracted per-frequency moment bound (#407)

`GaussPeriodMomentBound.eta_pow_le_of_energyBound` gives `‖η_b‖^{2r} ≤ q·(2r−1)‼·|G|^r` by bounding a
single term of the FULL moment `∑_b ‖η_b‖^{2r} = q·E_r`. But for `b ≠ 0` we may subtract the DC term
`‖η_0‖^{2r} = |G|^{2r}` first (`sum_nonzero_moment`), giving the strictly sharper bound:

> **`eta_pow_le_dc`** — for `b ≠ 0`, `‖η_b‖^{2r} ≤ q·E_r(G) − |G|^{2r}`.
> **`eta_pow_le_dc_of_energyBound`** — under `GaussianEnergyBound G r`, `‖η_b‖^{2r} ≤ q·(2r−1)‼·|G|^r − |G|^{2r}`.

The `−|G|^{2r}` is exactly the principal-character mass removed; it is the right object for the moment
method, since `M(n) = max_{b≠0}‖η_b‖` excludes `b=0`.

Issue #407.
-/

open Finset ArkLib.ProximityGap.SubgroupGaussSumSecondMoment ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound ArkLib.ProximityGap.DCSubtractedMoment

namespace ArkLib.ProximityGap.DCMomentSupBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Sharp DC-subtracted per-frequency bound.** For every non-trivial frequency `b ≠ 0`,
`‖η_b‖^{2r} ≤ q·E_r(G) − |G|^{2r}` — a single non-DC term is at most the DC-subtracted total moment. -/
theorem eta_pow_le_dc {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) {b : F}
    (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) := by
  rw [← sum_nonzero_moment hψ G r]
  apply Finset.single_le_sum (f := fun b => ‖eta ψ G b‖ ^ (2 * r))
  · intro i _; positivity
  · exact Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩

/-- **Sharp DC-subtracted bound under the energy hypothesis.** Combining `eta_pow_le_dc` with
`GaussianEnergyBound G r` (`E_r ≤ (2r−1)‼·|G|^r`): for `b ≠ 0`,
`‖η_b‖^{2r} ≤ q·(2r−1)‼·|G|^r − |G|^{2r}`. Strictly sharper than the non-DC `eta_pow_le_of_energyBound`. -/
theorem eta_pow_le_dc_of_energyBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ}
    (h : GaussianEnergyBound G r) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
        - (G.card : ℝ) ^ (2 * r) := by
  refine (eta_pow_le_dc hψ G r hb).trans ?_
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left h hq
  linarith [this]

end ArkLib.ProximityGap.DCMomentSupBound

#print axioms ArkLib.ProximityGap.DCMomentSupBound.eta_pow_le_dc
#print axioms ArkLib.ProximityGap.DCMomentSupBound.eta_pow_le_dc_of_energyBound
