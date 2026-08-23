/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceSpikeVarianceCost
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceAgreementSpectralVariance

/-!
# Spectral spikes are paid by the depth-two agreement off-diagonal (#444 door-(iv))

This leaf composes the existing single-spike Cantelli obstruction with the newer exact
identification of the depth-two agreement off-diagonal:

`∑_k (‖K̂(k)‖² - (m-1))² = m · Re Off(2)`.

Thus a frequency whose squared one-step spectrum is `d` above the Parseval mean forces
`d² ≤ m · Re Off(2)`, and the whole set of `d`-spikes has size at most `m · Re Off(2) / d²`.

This is a constraint lemma only. It does not upper-bound the worst frequency, prove cancellation, or
claim CORE. It says any such spike is exactly paid by the named depth-two agreement budget, so a
selector or spike-count route is still consuming the localized off-diagonal object rather than
bypassing it.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open Finset ZMod
open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- A squared-spectrum spike of height `d` above the mean costs `d²` of the depth-two agreement
off-diagonal budget: `d² ≤ m · Re Off(2)`. -/
theorem spike_cost_le_offDiag_two_re
    (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (d : ℝ) (hd : 0 < d)
    (hspike : ∃ k : ZMod m, ((m : ℝ) - 1) + d ≤ ‖kernelSpectrum (dftChar k) u‖ ^ 2) :
    d ^ 2 ≤ (m : ℝ) * (resonanceOffDiag u 2).re := by
  have h := spike_cost_le_variance u hu d hd hspike
  have hoff := resonanceOffDiag_re_eq_moment_sub_floor u 2 hu
  rw [hoff]
  exact h

/-- Normalized form: a spike of height `d` forces `Re Off(2) ≥ d² / m`. -/
theorem offDiag_two_re_ge_spike_sq_div
    (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (d : ℝ) (hd : 0 < d)
    (hspike : ∃ k : ZMod m, ((m : ℝ) - 1) + d ≤ ‖kernelSpectrum (dftChar k) u‖ ^ 2) :
    d ^ 2 / (m : ℝ) ≤ (resonanceOffDiag u 2).re := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : (0 : ℕ) < m := Nat.pos_of_ne_zero (NeZero.ne m)
    exact_mod_cast this
  rw [div_le_iff₀ hmpos]
  have h := spike_cost_le_offDiag_two_re u hu d hd hspike
  linarith [h]

/-- Count form: at most `m · Re Off(2) / d²` frequencies can lie `d` above the mean. -/
theorem spike_count_le_offDiag_two_re_div
    (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (d : ℝ) (hd : 0 < d) :
    (((Finset.univ : Finset (ZMod m)).filter
        (fun k => ((m : ℝ) - 1) + d ≤ ‖kernelSpectrum (dftChar k) u‖ ^ 2)).card : ℝ)
      ≤ (m : ℝ) * (resonanceOffDiag u 2).re / d ^ 2 := by
  have h := spike_count_le_variance_div u hu d hd
  have hoff := resonanceOffDiag_re_eq_moment_sub_floor u 2 hu
  have hdiff : resonanceMoment u 2 - ((m : ℝ) - 1) ^ 2 = (resonanceOffDiag u 2).re := by
    linarith [hoff]
  rwa [hdiff] at h

/-- Contrapositive count form: if the depth-two agreement budget is below `d²`, then no frequency
can spike `d` above the Parseval mean. -/
theorem spike_count_eq_zero_of_offDiag_two_re_lt_sq
    (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (d : ℝ) (hd : 0 < d)
    (hsmall : (m : ℝ) * (resonanceOffDiag u 2).re < d ^ 2) :
    ((Finset.univ : Finset (ZMod m)).filter
        (fun k => ((m : ℝ) - 1) + d ≤ ‖kernelSpectrum (dftChar k) u‖ ^ 2)).card = 0 := by
  classical
  have hzero :=
    _root_.ProximityGap.Frontier.DoorIVWorstBSpikeMomentBound.threshold_count_eq_zero_of_sndMoment_lt_sq
      (fun k => ‖kernelSpectrum (dftChar k) u‖ ^ 2) (Finset.univ : Finset (ZMod m))
      ((m : ℝ) - 1) d hd
  have hvar :
      (∑ k : ZMod m, (‖kernelSpectrum (dftChar k) u‖ ^ 2 - ((m : ℝ) - 1)) ^ 2)
        < d ^ 2 := by
    rw [sum_sq_centered_kernelSpectrum_eq_card_mul_offDiag_two_re u hu]
    exact hsmall
  exact hzero hvar

/-- Downward deviations from the Parseval mean are also paid by the same depth-two agreement budget.
If some frequency lies at least `d` *below* the mean, then `d² ≤ m · Re Off(2)`.

This is the two-sided companion to the spike-cost lemma.  It is a constraint only: a near-flatness
argument must control both upward spikes and downward holes, and either kind of deviation consumes
the same named agreement off-diagonal budget. -/
theorem dip_cost_le_offDiag_two_re
    (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (d : ℝ) (hd : 0 < d)
    (hdip : ∃ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 + d ≤ ((m : ℝ) - 1)) :
    d ^ 2 ≤ (m : ℝ) * (resonanceOffDiag u 2).re := by
  classical
  obtain ⟨k, hk⟩ := hdip
  let a : ℝ := ‖kernelSpectrum (dftChar k) u‖ ^ 2 - ((m : ℝ) - 1)
  have hdev : d ≤ -a := by
    dsimp [a]
    linarith
  have hsq : d ^ 2 ≤ a ^ 2 := by
    have hnonneg : 0 ≤ d := le_of_lt hd
    have hs := pow_le_pow_left₀ hnonneg hdev 2
    simpa [sq] using hs
  have hbudget := centeredKernelSpectrum_sq_le_card_mul_offDiag_two_re u hu k
  dsimp [a] at hsq
  exact le_trans hsq hbudget

/-- Contrapositive downward-deviation guard: if the depth-two agreement budget is below `d²`, then
no frequency can lie `d` below the Parseval mean.  Together with the upward spike guard, this states
that a sub-`d²` agreement budget forces the one-step squared spectrum into the two-sided window
`m-1-d < ‖K̂(k)‖² < m-1+d`. -/
theorem dip_count_eq_zero_of_offDiag_two_re_lt_sq
    (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (d : ℝ) (hd : 0 < d)
    (hsmall : (m : ℝ) * (resonanceOffDiag u 2).re < d ^ 2) :
    ((Finset.univ : Finset (ZMod m)).filter
        (fun k => ‖kernelSpectrum (dftChar k) u‖ ^ 2 + d ≤ ((m : ℝ) - 1))).card = 0 := by
  classical
  by_contra hne
  have hpos : 0 < ((Finset.univ : Finset (ZMod m)).filter
      (fun k => ‖kernelSpectrum (dftChar k) u‖ ^ 2 + d ≤ ((m : ℝ) - 1))).card :=
    Nat.pos_of_ne_zero hne
  rcases Finset.card_pos.mp hpos with ⟨k, hkT⟩
  have hk := (Finset.mem_filter.mp hkT).2
  have hcost := dip_cost_le_offDiag_two_re u hu d hd ⟨k, hk⟩
  linarith

end ArkLib.ProximityGap.GaussPhaseResonance

#print axioms ArkLib.ProximityGap.GaussPhaseResonance.spike_cost_le_offDiag_two_re
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.offDiag_two_re_ge_spike_sq_div
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.spike_count_le_offDiag_two_re_div
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.spike_count_eq_zero_of_offDiag_two_re_lt_sq
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.dip_cost_le_offDiag_two_re
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.dip_count_eq_zero_of_offDiag_two_re_lt_sq
