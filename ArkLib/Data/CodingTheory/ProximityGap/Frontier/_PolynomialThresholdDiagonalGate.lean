/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FixedParameterLimitTransferGate
import Mathlib.Tactic

/-!
# Polynomial threshold exponents for fixed-parameter diagonal transfer

`_FixedParameterLimitTransferGate` records the qualitative obstruction: a theorem that is eventual
in `p` for each fixed `n` does not imply a statement at the prize diagonal `p = scale n` unless the
effective threshold `P0 n` is known to be below `scale n`.

This file records the elementary exponent contract in the polynomial case.  Using the harmless
offset base `(n+2)`, a threshold `(n+2)^theta` lies below a diagonal scale `(n+2)^beta` for every
`n` exactly when

`theta <= beta`.

Thus a vertical/equidistribution theorem with an effective threshold exponent above the prize field
exponent still misses the prize diagonal, even though it is true for each fixed `n` eventually.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.PolynomialThresholdDiagonalGate

open ArkLib.ProximityGap.Frontier.FixedParameterLimitTransferGate

/-- Polynomial scale with base shifted away from `0` and `1`, so exponent comparison is faithful
for every natural `n`. -/
def polynomialScale (e : Nat) : Nat -> Nat :=
  fun n => (n + 2) ^ e

/-- If the threshold exponent is at most the diagonal exponent, the threshold is below the scale
at every `n`. -/
theorem thresholdBelowScale_polynomial_of_exponent_le {theta beta : Nat}
    (h : theta <= beta) :
    ThresholdBelowScale (polynomialScale theta) (polynomialScale beta) := by
  intro n
  unfold polynomialScale
  exact Nat.pow_le_pow_right (by omega : 1 <= n + 2) h

/-- If the threshold exponent is strictly larger than the diagonal exponent, the threshold-below-scale
contract already fails at the base point `n = 0`, where the shifted base is `2`. -/
theorem not_thresholdBelowScale_polynomial_of_exponent_gt {theta beta : Nat}
    (h : beta < theta) :
    ¬ ThresholdBelowScale (polynomialScale theta) (polynomialScale beta) := by
  intro hBelow
  have h0 := hBelow 0
  have hpow : (2 : Nat) ^ beta < 2 ^ theta :=
    Nat.pow_lt_pow_right (by norm_num : 1 < (2 : Nat)) h
  unfold polynomialScale at h0
  norm_num at h0
  exact not_lt_of_ge h0 hpow

/-- Exact polynomial threshold contract: universal diagonal transfer for polynomial threshold
`(n+2)^theta` and polynomial scale `(n+2)^beta` is possible exactly when `theta <= beta`. -/
theorem thresholdBelowScale_polynomial_iff (theta beta : Nat) :
    ThresholdBelowScale (polynomialScale theta) (polynomialScale beta) <-> theta <= beta := by
  constructor
  · intro hBelow
    by_contra hnot
    have hgt : beta < theta := Nat.lt_of_not_ge hnot
    exact not_thresholdBelowScale_polynomial_of_exponent_gt hgt hBelow
  · intro h
    exact thresholdBelowScale_polynomial_of_exponent_le h

/-- Explicit mismatch witness: if the fixed-parameter theorem only starts at polynomial exponent
`theta > beta`, then there is a property which is true above that threshold but false on the
`beta`-diagonal.  Thus exponent comparison is not cosmetic bookkeeping; it is exactly the condition
needed before a fixed-parameter theorem can touch the prize field scale. -/
theorem exists_polynomial_eventual_not_diagonal_of_exponent_gt {theta beta : Nat}
    (h : beta < theta) :
    ∃ Good : Nat -> Nat -> Prop,
      EventualWithThreshold Good (polynomialScale theta) ∧
        ¬ PrizeDiagonalGood Good (polynomialScale beta) := by
  refine ⟨fun n p => polynomialScale theta n <= p, ?_, ?_⟩
  · intro n p hp
    exact hp
  · intro hDiagonal
    have hBelow : ThresholdBelowScale (polynomialScale theta) (polynomialScale beta) := by
      intro n
      exact hDiagonal n
    exact not_thresholdBelowScale_polynomial_of_exponent_gt h hBelow

/-- Consumer form: an eventual theorem with polynomial threshold exponent `theta` transfers to a
polynomial prize diagonal of exponent `beta` if `theta <= beta`. -/
theorem prizeDiagonalGood_of_polynomial_eventual_le {Good : Nat -> Nat -> Prop}
    {theta beta : Nat}
    (hTheta : theta <= beta)
    (hEventually : EventualWithThreshold Good (polynomialScale theta)) :
    PrizeDiagonalGood Good (polynomialScale beta) :=
  prizeDiagonalGood_of_eventualWithThreshold hEventually
    (thresholdBelowScale_polynomial_of_exponent_le hTheta)

/-- Countermodel specialized to a polynomial diagonal: the property is true only strictly above
`(n+2)^beta`. -/
def afterPolynomialScaleGood (beta : Nat) : Nat -> Nat -> Prop :=
  afterScaleGood (polynomialScale beta)

/-- For every fixed `n`, the polynomial countermodel is eventually true. -/
theorem pointwiseEventually_afterPolynomialScaleGood (beta : Nat) :
    PointwiseEventuallyGood (afterPolynomialScaleGood beta) :=
  afterScaleGood_pointwiseEventually (polynomialScale beta)

/-- Pointwise eventual truth alone still cannot prove a polynomial diagonal statement. -/
theorem pointwiseEventually_not_enough_for_polynomial_scale (beta : Nat) :
    ¬ (forall Good : Nat -> Nat -> Prop,
        PointwiseEventuallyGood Good -> PrizeDiagonalGood Good (polynomialScale beta)) :=
  pointwiseEventually_not_enough_for_any_scale (polynomialScale beta)

/-! ## Axiom audit -/
#print axioms polynomialScale
#print axioms thresholdBelowScale_polynomial_of_exponent_le
#print axioms not_thresholdBelowScale_polynomial_of_exponent_gt
#print axioms thresholdBelowScale_polynomial_iff
#print axioms exists_polynomial_eventual_not_diagonal_of_exponent_gt
#print axioms prizeDiagonalGood_of_polynomial_eventual_le
#print axioms afterPolynomialScaleGood
#print axioms pointwiseEventually_afterPolynomialScaleGood
#print axioms pointwiseEventually_not_enough_for_polynomial_scale

end ArkLib.ProximityGap.Frontier.PolynomialThresholdDiagonalGate
