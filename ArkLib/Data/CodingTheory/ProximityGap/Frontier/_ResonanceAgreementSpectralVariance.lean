/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceAgreementOffDiagCorridor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceSpectralVariance

/-!
# The depth-two agreement excess is the spectral variance budget (#407 / #444)

At depth two, the agreement off-diagonal real excess has an exact spectral meaning.  The variance
identity says

`∑ k, (‖K̂(k)‖² - (m - 1))² = m · (T 2 - (m - 1)²)`,

while the agreement corridor says

`Re Off(2) = T 2 - (m - 1)²`.

Composing the two identifies the named agreement object with the one-step spectral variance:

`∑ k, (‖K̂(k)‖² - (m - 1))² = m · Re Off(2)`.

Honest scope: this is an exact localization/constraint, not an upper bound.  It says the depth-two
off-diagonal is precisely the variance budget of the one-step spectrum.  Proving the prize still
requires new anti-spike / near-flat control of that spectrum for the actual thin
Gauss-period kernel.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open Finset ZMod
open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- **Depth-two agreement excess is spectral variance.**  For unit-modulus phases, the centered
second moment of the one-step squared kernel spectrum is exactly `m` times the real agreement
off-diagonal at depth two.  Thus the `r = 2` agreement excess is not a new mysterious object: it is
precisely the spectral variance budget. -/
theorem sum_sq_centered_kernelSpectrum_eq_card_mul_offDiag_two_re (u : ZMod m → ℂ)
    (hu : ∀ a : ZMod m, ‖u a‖ = 1) :
    (∑ k : ZMod m, (‖kernelSpectrum (dftChar k) u‖ ^ 2 - ((m : ℝ) - 1)) ^ 2)
      = (m : ℝ) * (resonanceOffDiag u 2).re := by
  have hvar := sum_sq_centered_kernelSpectrum_eq u hu
  have hoff := resonanceOffDiag_re_eq_moment_sub_floor u 2 hu
  rw [hvar, hoff]

/-- **Flat variance iff zero agreement budget, sum-of-squares form.**  The centered spectral
variance vanishes iff the depth-two agreement off-diagonal has zero real excess.  This is the
sum-of-squares companion to `_ResonanceAgreementFlatnessCriterion`. -/
theorem centeredKernelSpectrum_zero_iff_offDiag_two_re_zero (u : ZMod m → ℂ)
    (hu : ∀ a : ZMod m, ‖u a‖ = 1) :
    (∑ k : ZMod m, (‖kernelSpectrum (dftChar k) u‖ ^ 2 - ((m : ℝ) - 1)) ^ 2) = 0
      ↔ (resonanceOffDiag u 2).re = 0 := by
  rw [sum_sq_centered_kernelSpectrum_eq_card_mul_offDiag_two_re u hu]
  have hm : (m : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (m : ℝ) := by
      have : (0 : ℕ) < m := Nat.pos_of_ne_zero (NeZero.ne m)
      exact_mod_cast this
    exact ne_of_gt hpos
  exact mul_eq_zero.trans (or_iff_right hm)

/-- **Every individual spectral deviation is paid by the agreement variance budget.**  Since the
centered spectrum sum of squares is exactly `m · Re Off(2)`, each single squared deviation from the
Parseval mean is bounded by that same budget.  Thus a large spike cannot hide from the named
depth-two agreement object. -/
theorem centeredKernelSpectrum_sq_le_card_mul_offDiag_two_re (u : ZMod m → ℂ)
    (hu : ∀ a : ZMod m, ‖u a‖ = 1) (k : ZMod m) :
    (‖kernelSpectrum (dftChar k) u‖ ^ 2 - ((m : ℝ) - 1)) ^ 2
      ≤ (m : ℝ) * (resonanceOffDiag u 2).re := by
  classical
  have hnonneg : ∀ x ∈ (Finset.univ : Finset (ZMod m)),
      0 ≤ (‖kernelSpectrum (dftChar x) u‖ ^ 2 - ((m : ℝ) - 1)) ^ 2 := by
    intro x hx
    positivity
  have hle := Finset.single_le_sum hnonneg (Finset.mem_univ k)
  calc
    (‖kernelSpectrum (dftChar k) u‖ ^ 2 - ((m : ℝ) - 1)) ^ 2
        ≤ ∑ x : ZMod m, (‖kernelSpectrum (dftChar x) u‖ ^ 2 - ((m : ℝ) - 1)) ^ 2 := hle
    _ = (m : ℝ) * (resonanceOffDiag u 2).re :=
        sum_sq_centered_kernelSpectrum_eq_card_mul_offDiag_two_re u hu

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms
  ArkLib.ProximityGap.GaussPhaseResonance.sum_sq_centered_kernelSpectrum_eq_card_mul_offDiag_two_re
#print axioms
  ArkLib.ProximityGap.GaussPhaseResonance.centeredKernelSpectrum_zero_iff_offDiag_two_re_zero
#print axioms
  ArkLib.ProximityGap.GaussPhaseResonance.centeredKernelSpectrum_sq_le_card_mul_offDiag_two_re
