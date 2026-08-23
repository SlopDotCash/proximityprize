/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceSpectralVariance

/-!
# A one-step spectral cap leaves only cap-slack variance (#407 / #444)

Door (iv)'s localized object is the one-step kernel spectrum
`w_k = ‖K̂(k)‖²`.  The already-proven mean identity gives
`∑_k w_k = m (m - 1)`, and the variance identity gives
`T 2 - (m - 1)^2 = (1 / m) ∑_k (w_k - (m - 1))^2`.

This leaf records the sharp elementary consumer between a **uniform squared-spectrum cap** and the
r=2 spread:

* if `w_k ≤ B` for every frequency, then `T 2 ≤ (m - 1) B`;
* therefore the variance budget obeys
  `T 2 - (m - 1)^2 ≤ (m - 1)(B - (m - 1))`.

So a cap barely above the Parseval floor leaves only the corresponding cap-slack for the depth-two
agreement excess.  This is only bookkeeping: it proves no cap and gives no CORE cancellation
theorem. The open content remains the arithmetic anti-concentration bound on the actual worst
frequency.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open Finset ZMod
open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- **Uniform squared cap controls the depth-two resonance moment by mean times cap.**
For `w_k = ‖K̂(k)‖²`, the pointwise cap `w_k ≤ B` gives `w_k² ≤ B w_k`; summing and using the
spectral mean `∑ w_k = m(m-1)` plus the Parseval bridge at `r = 2` yields
`T 2 ≤ (m - 1) B`. -/
theorem resonanceMoment_two_le_mean_mul_cap (u : ZMod m → ℂ)
    (hu : ∀ l : ZMod m, ‖u l‖ = 1) {B : ℝ}
    (hB : ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 ≤ B) :
    resonanceMoment u 2 ≤ ((m : ℝ) - 1) * B := by
  classical
  set w : ZMod m → ℝ := fun k => ‖kernelSpectrum (dftChar k) u‖ ^ 2 with hw
  have hmpos_nat : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos_nat
  have hbridge : (m : ℝ) * resonanceMoment u 2 = ∑ k : ZMod m, (w k) ^ 2 := by
    have h := resonanceMoment_eq_spectral_powerMean u 2
    rw [hw]
    rw [h]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← pow_mul]
  have hmean : (∑ k : ZMod m, w k) = (m : ℝ) * ((m : ℝ) - 1) := by
    rw [hw]
    exact sum_normSq_kernelSpectrum_eq u hu
  have hsq_le : (∑ k : ZMod m, (w k) ^ 2) ≤ ∑ k : ZMod m, B * w k := by
    refine Finset.sum_le_sum ?_
    intro k _hk
    have hw_nonneg : 0 ≤ w k := by
      rw [hw]
      positivity
    have hkB : w k ≤ B := by
      rw [hw]
      exact hB k
    calc (w k) ^ 2 = w k * w k := by ring
      _ ≤ B * w k := mul_le_mul_of_nonneg_right hkB hw_nonneg
  have hcap : (∑ k : ZMod m, B * w k) = B * ((m : ℝ) * ((m : ℝ) - 1)) := by
    rw [← Finset.mul_sum, hmean]
  have hmul : (m : ℝ) * resonanceMoment u 2 ≤ (m : ℝ) * (((m : ℝ) - 1) * B) := by
    calc (m : ℝ) * resonanceMoment u 2
        = ∑ k : ZMod m, (w k) ^ 2 := hbridge
      _ ≤ ∑ k : ZMod m, B * w k := hsq_le
      _ = B * ((m : ℝ) * ((m : ℝ) - 1)) := hcap
      _ = (m : ℝ) * (((m : ℝ) - 1) * B) := by ring
  exact le_of_mul_le_mul_left hmul hmpos

/-- **Cap-slack bounds the depth-two spectral variance budget.**  Under the same pointwise cap,
`T 2 - (m - 1)^2 ≤ (m - 1) · (B - (m - 1))`.  Thus near-Parseval one-step caps leave only
near-zero depth-two spread; no such cap is proved here. -/
theorem resonanceMoment_two_sub_floor_le_capSlack (u : ZMod m → ℂ)
    (hu : ∀ l : ZMod m, ‖u l‖ = 1) {B : ℝ}
    (hB : ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 ≤ B) :
    resonanceMoment u 2 - ((m : ℝ) - 1) ^ 2 ≤
      ((m : ℝ) - 1) * (B - ((m : ℝ) - 1)) := by
  have h := resonanceMoment_two_le_mean_mul_cap u hu hB
  nlinarith

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_two_le_mean_mul_cap
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_two_sub_floor_le_capSlack
