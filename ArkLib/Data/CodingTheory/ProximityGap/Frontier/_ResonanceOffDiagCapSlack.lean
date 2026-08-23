/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceAgreementFlatnessCriterion
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceAgreementSpectralVariance
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceCapVarianceBudget

/-!
# Cap slack bounds the depth-two agreement off-diagonal (#407 / #444)

The previous leaves identify three views of the same depth-two budget:

* `T 2 - (m - 1)^2`, the resonance floor excess;
* `(resonanceOffDiag u 2).re`, the real depth-two agreement off-diagonal;
* the centered variance of the one-step squared spectrum.

This file wires the one-step cap consumer directly to the named agreement object. If every squared
frequency obeys `‖K̂(k)‖² ≤ B`, then the agreement excess is at most
`(m - 1) · (B - (m - 1))`.

Honest scope: this proves no cap and no cancellation. It only says that any future arithmetic
anti-spike theorem immediately shrinks the exact off-diagonal object by its cap slack.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

variable {m : ℕ} [NeZero m]

/-- **A one-step spectral cap bounds the depth-two agreement excess by cap slack.**  The theorem
composes the exact identity `Re Off(2) = T 2 - (m - 1)^2` with the cap-slack variance consumer.
It is a consumer/constraint only: the hard door-(iv) input is still the cap itself. -/
theorem resonanceOffDiag_two_re_le_capSlack (u : ZMod m → ℂ)
    (hu : ∀ l : ZMod m, ‖u l‖ = 1) {B : ℝ}
    (hB : ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 ≤ B) :
    (resonanceOffDiag u 2).re ≤ ((m : ℝ) - 1) * (B - ((m : ℝ) - 1)) := by
  rw [resonanceOffDiag_re_eq_moment_sub_floor u 2 hu]
  exact resonanceMoment_two_sub_floor_le_capSlack u hu hB

/-- **Parseval-floor cap forces zero depth-two agreement excess.**  If the whole squared spectrum
is capped at its mean `m - 1`, then the nonnegative agreement off-diagonal at depth two must vanish.
This is the exact no-slack endpoint; it does not prove such a cap for the thin Gauss-period
kernel. -/
theorem resonanceOffDiag_two_re_eq_zero_of_cap_at_mean (u : ZMod m → ℂ)
    (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hcap : ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 ≤ (m : ℝ) - 1) :
    (resonanceOffDiag u 2).re = 0 := by
  have hle := resonanceOffDiag_two_re_le_capSlack (u := u) hu hcap
  have hnonneg := resonanceOffDiag_re_nonneg u 2 hu
  have hzero : ((m : ℝ) - 1) * (((m : ℝ) - 1) - ((m : ℝ) - 1)) = 0 := by ring
  rw [hzero] at hle
  exact le_antisymm hle hnonneg

/-- **Zero agreement excess iff no frequency rises above the Parseval mean.**  At depth two, the
threshold cap `‖K̂(k)‖² ≤ m - 1` is equivalent to zero real off-diagonal.  One direction is the
cap-slack endpoint; the other uses the flatness criterion. -/
theorem resonanceOffDiag_two_re_eq_zero_iff_cap_at_mean (u : ZMod m → ℂ)
    (hu : ∀ l : ZMod m, ‖u l‖ = 1) :
    (resonanceOffDiag u 2).re = 0 ↔
      ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 ≤ (m : ℝ) - 1 := by
  constructor
  · intro hzero k
    have hflat := (resonanceOffDiag_two_re_eq_zero_iff_flat u hu).mp hzero
    rw [hflat k]
  · intro hcap
    exact resonanceOffDiag_two_re_eq_zero_of_cap_at_mean u hu hcap

/-- **Positive depth-two agreement excess iff some one-step frequency spikes above the mean.**
The named off-diagonal is strictly positive exactly when the squared one-step spectrum violates the
Parseval-floor cap at at least one frequency.  This is an exact localization of the depth-two
obstruction, not a proof that such spikes are small for the thin Gauss-period kernel. -/
theorem resonanceOffDiag_two_re_pos_iff_exists_above_mean (u : ZMod m → ℂ)
    (hu : ∀ l : ZMod m, ‖u l‖ = 1) :
    0 < (resonanceOffDiag u 2).re ↔
      ∃ k : ZMod m, (m : ℝ) - 1 < ‖kernelSpectrum (dftChar k) u‖ ^ 2 := by
  constructor
  · intro hpos
    by_contra hno
    have hcap : ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 ≤ (m : ℝ) - 1 := by
      intro k
      exact le_of_not_gt fun hk => hno ⟨k, hk⟩
    have hzero := (resonanceOffDiag_two_re_eq_zero_iff_cap_at_mean u hu).mpr hcap
    linarith
  · rintro ⟨k, hk⟩
    have hnonneg := resonanceOffDiag_re_nonneg u 2 hu
    have hne : (resonanceOffDiag u 2).re ≠ 0 := by
      intro hzero
      have hcap := (resonanceOffDiag_two_re_eq_zero_iff_cap_at_mean u hu).mp hzero
      exact not_le_of_gt hk (hcap k)
    exact lt_of_le_of_ne' hnonneg hne

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceOffDiag_two_re_le_capSlack
#print axioms
  ArkLib.ProximityGap.GaussPhaseResonance.resonanceOffDiag_two_re_eq_zero_of_cap_at_mean
#print axioms
  ArkLib.ProximityGap.GaussPhaseResonance.resonanceOffDiag_two_re_eq_zero_iff_cap_at_mean
#print axioms
  ArkLib.ProximityGap.GaussPhaseResonance.resonanceOffDiag_two_re_pos_iff_exists_above_mean
