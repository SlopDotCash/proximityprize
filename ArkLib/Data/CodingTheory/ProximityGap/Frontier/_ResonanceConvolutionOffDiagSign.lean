/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceConvolutionDiagExtraction

/-!
# The off-diagonal sign is exactly the resonance-moment monotonicity gap (#444)

`_ResonanceConvolutionDiagExtraction` proved the exact convolution-diagonal split

`(T (r+1) : ℂ) = (m−1) · (T r : ℂ) + convOffDiag u r`.

The prose there identified the missing lower-bound content as `Re(convOffDiag u r) ≥ 0`.
If true, the empirical spectral-Chebyshev monotonicity `T(r+1) ≥ (m−1)T(r)` follows.
This file kernel-checks that bookkeeping equivalence and names the *exact* real gap:

* `resonanceMoment_succ_sub_diag_eq_re_convOffDiag`:
  `T(r+1) − (m−1)T(r) = Re Off(r)`.
* `resonanceMoment_succ_ge_diag_iff_re_convOffDiag_nonneg`:
  `(m−1)T(r) ≤ T(r+1) ↔ 0 ≤ Re Off(r)`.

Honest scope: this proves no positivity.  It pins the open door-(iv) input to a single named real
quantity, the sign of the convolution off-diagonal cross-correlation.  CORE remains open.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- **The real monotonicity gap is exactly the real part of the convolution off-diagonal.**
The exact diagonal extraction
`(T (r+1) : ℂ) = (m−1)·(T r : ℂ) + Off(r)` becomes, after taking real parts,
`T(r+1) − (m−1)T(r) = Re Off(r)`.  This is pure bookkeeping:
no sign or cancellation is asserted. -/
theorem resonanceMoment_succ_sub_diag_eq_re_convOffDiag
    (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (r : ℕ) :
    resonanceMoment u (r + 1)
        - (((m : ℕ) - 1 : ℕ) : ℝ) * resonanceMoment u r
      = (convOffDiag u r).re := by
  have h := congrArg Complex.re (resonanceMoment_succ_eq_diag_add_offdiag u hu r)
  simp only [Complex.add_re, Complex.ofReal_re] at h
  have hmul :
      ((((((m : ℕ) - 1 : ℕ) : ℂ) * (resonanceMoment u r : ℂ))).re)
      = ((((m : ℕ) - 1 : ℕ) : ℝ) * resonanceMoment u r) := by
    simp
  rw [hmul] at h
  linarith

/-- **The diagonal lower bound is equivalent to nonnegative off-diagonal real part.**
Thus the empirical/prospective lower recurrence `T(r+1) ≥ (m−1)T(r)` contains exactly the
sign input `0 ≤ Re(convOffDiag u r)`.  This theorem deliberately does *not* prove the sign;
it isolates the open Door-IV cross-correlation obligation. -/
theorem resonanceMoment_succ_ge_diag_iff_re_convOffDiag_nonneg
    (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (r : ℕ) :
    (((m : ℕ) - 1 : ℕ) : ℝ) * resonanceMoment u r ≤ resonanceMoment u (r + 1)
      ↔ 0 ≤ (convOffDiag u r).re := by
  rw [← resonanceMoment_succ_sub_diag_eq_re_convOffDiag u hu r]
  constructor <;> intro h <;> linarith

/-- **Positive off-diagonal real part gives the strict monotonicity gap.**
A strict Door-IV cross-correlation surplus is exactly enough to make the diagonal recurrence
strict. -/
theorem resonanceMoment_succ_gt_diag_of_re_convOffDiag_pos
    (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (r : ℕ)
    (hoff : 0 < (convOffDiag u r).re) :
    (((m : ℕ) - 1 : ℕ) : ℝ) * resonanceMoment u r < resonanceMoment u (r + 1) := by
  have hgap := resonanceMoment_succ_sub_diag_eq_re_convOffDiag u hu r
  linarith

end ArkLib.ProximityGap.GaussPhaseResonance

#print axioms
  ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_succ_sub_diag_eq_re_convOffDiag
#print axioms
  ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_succ_ge_diag_iff_re_convOffDiag_nonneg
#print axioms
  ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_succ_gt_diag_of_re_convOffDiag_pos
