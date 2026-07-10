/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterDeterminantCollapse

/-!
# Polynomial-line Plucker syzygies

Four decoded polynomial lines are not independent set-system labels.  Their
oriented determinants obey the affine cocycle identity, and three difference
vectors obey the two-dimensional Plucker syzygy.  Evaluating the latter gives
a local propagation rule: if two determinant pencils vanish at a coordinate,
then the third vanishes whenever one component of the remaining reference
difference is nonzero there.

This is an algebraic anti-sunflower constraint for the saturated rate-quarter
half-predecessor problem.
-/

set_option autoImplicit false

open Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse

namespace ArkLib.ProximityGap.Frontier.R396PolynomialLinePluckerSyzygy

variable {F : Type} [Field F]

/-- The four oriented affine areas form a simplicial cocycle. -/
theorem lineDeterminant_cocycle
    (line0 line1 line2 line3 : PolynomialLine F) :
    lineDeterminant line0 line1 line2 -
        lineDeterminant line0 line1 line3 +
        lineDeterminant line0 line2 line3 -
        lineDeterminant line1 line2 line3 = 0 := by
  simp only [lineDeterminant]
  ring

/-- First component of the two-dimensional Plucker syzygy. -/
theorem lineDeterminant_firstComponent_syzygy
    (line0 line1 line2 line3 : PolynomialLine F) :
    lineDeterminant line0 line1 line2 * (line3.1 - line0.1) -
        lineDeterminant line0 line1 line3 * (line2.1 - line0.1) +
        lineDeterminant line0 line2 line3 * (line1.1 - line0.1) = 0 := by
  simp only [lineDeterminant]
  ring

/-- Second component of the two-dimensional Plucker syzygy. -/
theorem lineDeterminant_secondComponent_syzygy
    (line0 line1 line2 line3 : PolynomialLine F) :
    lineDeterminant line0 line1 line2 * (line3.2 - line0.2) -
        lineDeterminant line0 line1 line3 * (line2.2 - line0.2) +
        lineDeterminant line0 line2 line3 * (line1.2 - line0.2) = 0 := by
  simp only [lineDeterminant]
  ring

/-- Vanishing of two determinant pencils propagates to the third at any point
where the first component of the remaining reference difference is nonzero. -/
theorem eval_lineDeterminant_eq_zero_of_two_eq_zero_of_firstComponent_ne
    (line0 line1 line2 line3 : PolynomialLine F) (x : F)
    (h12 : (lineDeterminant line0 line1 line2).eval x = 0)
    (h13 : (lineDeterminant line0 line1 line3).eval x = 0)
    (href : (line1.1 - line0.1).eval x ≠ 0) :
    (lineDeterminant line0 line2 line3).eval x = 0 := by
  have h := congrArg (Polynomial.eval x)
    (lineDeterminant_firstComponent_syzygy line0 line1 line2 line3)
  simp only [eval_add, eval_sub, eval_mul, eval_zero, h12, h13,
    zero_mul, zero_sub, neg_zero, zero_add] at h
  have href' : line1.1.eval x - line0.1.eval x ≠ 0 := by
    simpa only [eval_sub] using href
  exact (mul_eq_zero.mp h).resolve_right href'

/-- The symmetric propagation rule using the slope component. -/
theorem eval_lineDeterminant_eq_zero_of_two_eq_zero_of_secondComponent_ne
    (line0 line1 line2 line3 : PolynomialLine F) (x : F)
    (h12 : (lineDeterminant line0 line1 line2).eval x = 0)
    (h13 : (lineDeterminant line0 line1 line3).eval x = 0)
    (href : (line1.2 - line0.2).eval x ≠ 0) :
    (lineDeterminant line0 line2 line3).eval x = 0 := by
  have h := congrArg (Polynomial.eval x)
    (lineDeterminant_secondComponent_syzygy line0 line1 line2 line3)
  simp only [eval_add, eval_sub, eval_mul, eval_zero, h12, h13,
    zero_mul, zero_sub, neg_zero, zero_add] at h
  have href' : line1.2.eval x - line0.2.eval x ≠ 0 := by
    simpa only [eval_sub] using href
  exact (mul_eq_zero.mp h).resolve_right href'

#print axioms lineDeterminant_cocycle
#print axioms lineDeterminant_firstComponent_syzygy
#print axioms lineDeterminant_secondComponent_syzygy
#print axioms eval_lineDeterminant_eq_zero_of_two_eq_zero_of_firstComponent_ne
#print axioms eval_lineDeterminant_eq_zero_of_two_eq_zero_of_secondComponent_ne

end ArkLib.ProximityGap.Frontier.R396PolynomialLinePluckerSyzygy
