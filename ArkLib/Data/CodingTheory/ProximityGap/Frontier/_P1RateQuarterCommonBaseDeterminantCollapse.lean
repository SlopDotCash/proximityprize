/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterDeterminantCollapse
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorSecantLines

/-!
# Common-base secants collapse without a counting threshold

Every canonical secant through the same lifted point `(gamma0,q gamma0)` has
parameter `(q gamma0 - gamma0*r, r)`.  Consequently all such polynomial
parameter pairs lie on one affine line, and every three-line Pluecker
determinant vanishes identically.  Unlike the multiplicity consumer, this
collapse costs no core-cardinality budget.
-/

set_option autoImplicit false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterCommonBaseDeterminantCollapse

open HalfPredecessorBadEventRichPointBridge
open HalfPredecessorSecantLines
open HalfPredecessorRateQuarterDeterminantCollapse

/-- Any three polynomial-line parameters passing through the same scalar
lifted polynomial point have zero line determinant. -/
theorem lineDeterminant_eq_zero_of_common_lift
    {F : Type} [Field F]
    (gamma0 : F) (q0 : F[X])
    (line1 line2 line3 : PolynomialLine F)
    (hline1 : q0 = line1.1 + C gamma0 * line1.2)
    (hline2 : q0 = line2.1 + C gamma0 * line2.2)
    (hline3 : q0 = line3.1 + C gamma0 * line3.2) :
    lineDeterminant line1 line2 line3 = 0 := by
  have ha1 : line1.1 = q0 - C gamma0 * line1.2 := by
    linear_combination -hline1
  have ha2 : line2.1 = q0 - C gamma0 * line2.2 := by
    linear_combination -hline2
  have ha3 : line3.1 = q0 - C gamma0 * line3.2 := by
    linear_combination -hline3
  rw [lineDeterminant, ha1, ha2, ha3]
  ring

/-- **Threshold-free common-base collapse.**  Three canonical secants sharing
their first endpoint have identically zero determinant, for arbitrary other
endpoints (no distinctness or agreement-size assumptions are needed). -/
theorem three_commonBase_secants_lineDeterminant_eq_zero
    {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    {dom : iota ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (gamma0 beta1 beta2 beta3 : F) :
    lineDeterminant
        (secantParameter family gamma0 beta1)
        (secantParameter family gamma0 beta2)
        (secantParameter family gamma0 beta3) = 0 := by
  apply lineDeterminant_eq_zero_of_common_lift gamma0 (family.q gamma0)
  all_goals simp only [secantParameter]
  all_goals ring

end ArkLib.ProximityGap.Frontier.P1RateQuarterCommonBaseDeterminantCollapse

open ArkLib.ProximityGap.Frontier.P1RateQuarterCommonBaseDeterminantCollapse

#print axioms lineDeterminant_eq_zero_of_common_lift
#print axioms three_commonBase_secants_lineDeterminant_eq_zero
