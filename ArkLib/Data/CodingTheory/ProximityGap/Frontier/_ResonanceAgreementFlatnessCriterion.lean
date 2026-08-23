/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceAgreementOffDiagNonneg
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceFlatnessCriterion

/-!
# Zero agreement excess at depth two is exactly spectral flatness (#407 / #444)

The door-(iv) resonance campaign has two exact views of the same floor-saturation event:

* `_ResonanceAgreementOffDiagNonneg` pins
  `T r = (m - 1)^r + Re Off(r)`, so at `r = 2` the Wick floor is saturated iff the
  agreement off-diagonal has zero real excess.
* `_ResonanceFlatnessCriterion` pins `T 2 = (m - 1)^2` iff the one-step kernel spectrum is
  flat: `‖K̂(k)‖^2 = m - 1` for every frequency `k`.

This leaf composes those two already-proven characterizations.  It is a constraint/capstone, not an
upper bound: the agreement off-diagonal at depth two vanishes exactly in the Ramanujan-flat spectral
case, and any non-flat spectrum forces strictly positive agreement excess.

Honest scope: no CORE bound, no cancellation theorem, no completion, no moment-as-prize claim.  The
open content remains proving near-flat / anti-spike control for the actual thin Gauss-period kernel.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

variable {m : ℕ} [NeZero m]

/-- **Depth-two zero agreement excess iff flat spectrum.**  The real agreement off-diagonal at
`r = 2` vanishes exactly when the one-step squared kernel spectrum is flat at its mean `m - 1`.
This names the zero-slack / Ramanujan case for the single localized door-(iv) object. -/
theorem resonanceOffDiag_two_re_eq_zero_iff_flat (u : ZMod m → ℂ)
    (hu : ∀ a : ZMod m, ‖u a‖ = 1) :
    (resonanceOffDiag u 2).re = 0 ↔
      ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 = (m : ℝ) - 1 := by
  have hoff := resonanceMoment_eq_floor_iff_offDiag_re_eq_zero u 2 hu
  have hflat := resonanceMoment_two_eq_sq_iff_flat u hu
  exact hoff.symm.trans hflat

/-- **Non-flat spectrum forces positive agreement excess.**  At depth two, once the spectrum is not
flat at the mean, the nonnegative agreement off-diagonal is in fact strictly positive.  This is a
constraint only: it does not upper-bound the excess or prove flatness for any
Gauss-period kernel. -/
theorem resonanceOffDiag_two_re_pos_of_not_flat (u : ZMod m → ℂ)
    (hu : ∀ a : ZMod m, ‖u a‖ = 1)
    (hnotflat :
      ¬ ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 = (m : ℝ) - 1) :
    0 < (resonanceOffDiag u 2).re := by
  have hnonneg := resonanceOffDiag_re_nonneg u 2 hu
  have hne : (resonanceOffDiag u 2).re ≠ 0 := by
    intro hzero
    exact hnotflat ((resonanceOffDiag_two_re_eq_zero_iff_flat u hu).mp hzero)
  exact lt_of_le_of_ne' hnonneg hne

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceOffDiag_two_re_eq_zero_iff_flat
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceOffDiag_two_re_pos_of_not_flat
