/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith

/-!
# G76: every higher distinct-generator moment misses the unique-root stratum

R385 shows that the second distinct-generator factorial moment is blind to endpoints incident to
exactly one primitive generator.  Taking more distinct generators cannot repair this: every
factorial moment of order at least two agrees on incidence counts zero and one.

This file packages the resulting information-theoretic obstruction.  No function of the entire
infinite hierarchy of higher distinct-generator moments can recover the centered coefficient
`q * Z - t` when `q != 0`, because that hierarchy identifies `Z = 0` with `Z = 1` while their
centered coefficients differ by exactly `q`.

The theorem rules out only higher *distinct*-generator statistics used without first-incidence
information.  Repeated-generator moments and arithmetic cancellation between endpoints remain out
of scope.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.G76HigherGeneratorMomentBlindSpot

/-- The centered contribution of an endpoint incident to `Z` generators. -/
def centeredCoeff (q t : ℝ) (Z : ℕ) : ℝ := q * Z - t

/-- All ordered distinct-generator counts of orders `2, 3, ...`. -/
def higherDistinctSignature (Z : ℕ) : ℕ → ℕ :=
  fun j => Z.descFactorial (j + 2)

/-- Incidence zero and incidence one have the same complete hierarchy of distinct-generator
moments of order at least two. -/
theorem higherDistinctSignature_zero_eq_one :
    higherDistinctSignature 0 = higherDistinctSignature 1 := by
  funext j
  simp [higherDistinctSignature, Nat.descFactorial_eq_factorial_mul_choose]

/-- The centered coefficients on the two indistinguishable strata differ by exactly `q`. -/
theorem centeredCoeff_one_sub_zero (q t : ℝ) :
    centeredCoeff q t 1 - centeredCoeff q t 0 = q := by
  simp [centeredCoeff]

/-- **All-higher-moments no-go.**  If `q` is nonzero, the centered incidence coefficient cannot
factor through even the entire infinite hierarchy of distinct-generator factorial moments of
orders at least two.  Any such method must add first-incidence information, which is the original
signed relation wall. -/
theorem no_factorization_through_higherDistinctSignature
    (q t : ℝ) (hq : q ≠ 0) :
    ¬ ∃ Φ : (ℕ → ℕ) → ℝ,
        ∀ Z : ℕ, centeredCoeff q t Z = Φ (higherDistinctSignature Z) := by
  rintro ⟨Φ, hΦ⟩
  have h0 := hΦ 0
  have h1 := hΦ 1
  rw [higherDistinctSignature_zero_eq_one] at h0
  have heq : centeredCoeff q t 1 = centeredCoeff q t 0 := h1.trans h0.symm
  have : q = 0 := by
    linarith [centeredCoeff_one_sub_zero q t]
  exact hq this

end ArkLib.ProximityGap.Frontier.G76HigherGeneratorMomentBlindSpot

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G76HigherGeneratorMomentBlindSpot.no_factorization_through_higherDistinctSignature
