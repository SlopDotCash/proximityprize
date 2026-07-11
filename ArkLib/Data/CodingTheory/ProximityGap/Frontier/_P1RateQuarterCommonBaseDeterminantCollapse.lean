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
open HalfPredecessorLineCoreGeometry
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

/-- All canonical secants through one base endpoint form a collapsed cluster
relative to any two fixed members of that common-base family. -/
theorem commonBase_secants_form_collapsed_cluster
    {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    {dom : iota ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (gamma0 beta0 beta1 : F) :
    ∀ beta : F,
      lineDeterminant
          (secantParameter family gamma0 beta0)
          (secantParameter family gamma0 beta1)
          (secantParameter family gamma0 beta) = 0 := by
  intro beta
  exact three_commonBase_secants_lineDeterminant_eq_zero
    family gamma0 beta0 beta1 beta

/-! ## Pointwise transversality -/

/-- **Common-base secant slopes separate at a base mismatch.**  If two
partner polynomials agree with their respective received affine combinations
at `x`, while the shared base polynomial misses there, then their canonical
common-base secant slopes have different evaluations at `x`. -/
theorem commonBase_secantSlope_eval_ne_of_baseMismatch
    {F : Type} [Field F]
    {gamma0 beta beta' : F}
    (hbeta : gamma0 ≠ beta) (hbeta' : gamma0 ≠ beta')
    (hbb' : beta ≠ beta')
    (q0 q q' : F[X]) (u0 u1 x : F)
    (hq : q.eval x = u0 + beta * u1)
    (hq' : q'.eval x = u0 + beta' * u1)
    (hmiss : q0.eval x ≠ u0 + gamma0 * u1) :
    (slopePolynomial gamma0 beta q0 q).eval x ≠
      (slopePolynomial gamma0 beta' q0 q').eval x := by
  intro heq
  simp only [slopePolynomial, eval_mul, eval_C, eval_sub] at heq
  rw [hq, hq'] at heq
  have hd : q0.eval x - (u0 + gamma0 * u1) ≠ 0 :=
    sub_ne_zero.mpr hmiss
  have hb : gamma0 - beta ≠ 0 := sub_ne_zero.mpr hbeta
  have hb' : gamma0 - beta' ≠ 0 := sub_ne_zero.mpr hbeta'
  have hfactor :
      (beta - beta') * (q0.eval x - (u0 + gamma0 * u1)) = 0 := by
    field_simp [hb, hb'] at heq
    linear_combination heq
  exact (mul_ne_zero (sub_ne_zero.mpr hbb') hd) hfactor

/-- Family-facing `href` adapter for the collapsed-cluster injection.  Two
distinct common-base canonical secants are pointwise transverse at every
coordinate where both partner codewords agree and the base codeword misses. -/
theorem commonBase_secantDirection_sub_eval_ne_zero
    {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    [Field F] [Fintype F] [DecidableEq F]
    {dom : iota ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    {gamma0 beta beta' : F}
    (hbeta : gamma0 ≠ beta) (hbeta' : gamma0 ≠ beta')
    (hbb' : beta ≠ beta') (i : iota)
    (hagree : (family.q beta).eval (dom i) = u 0 i + beta * u 1 i)
    (hagree' : (family.q beta').eval (dom i) = u 0 i + beta' * u 1 i)
    (hmiss : (family.q gamma0).eval (dom i) ≠
      u 0 i + gamma0 * u 1 i) :
    (((secantParameter family gamma0 beta).2 -
        (secantParameter family gamma0 beta').2).eval (dom i)) ≠ 0 := by
  rw [eval_sub, sub_ne_zero]
  simpa only [secantParameter] using
    commonBase_secantSlope_eval_ne_of_baseMismatch
      hbeta hbeta' hbb' (family.q gamma0) (family.q beta)
        (family.q beta') (u 0 i) (u 1 i) (dom i) hagree hagree' hmiss

/-! ## Degenerate-cluster injection no-go -/

/-- In a common-lift cluster, a pair equation for a scalar different from the
common base forces the two line directions to agree at that coordinate.  Thus
the transverse-petal premise of the generic collapsed-cluster injection is
incompatible with using two common-base lines as source and target for a
nonbase scalar. -/
theorem commonLift_pairEquation_forces_direction_eval_eq
    {F : Type} [Field F]
    (gamma0 gamma x : F) (q0 : F[X])
    (source target : PolynomialLine F)
    (hgamma : gamma ≠ gamma0)
    (hsource : q0 = source.1 + C gamma0 * source.2)
    (htarget : q0 = target.1 + C gamma0 * target.2)
    (hequation :
      (source.1 - target.1).eval x +
        gamma * (source.2 - target.2).eval x = 0) :
    (source.2 - target.2).eval x = 0 := by
  have ha : source.1 - target.1 =
      -C gamma0 * (source.2 - target.2) := by
    linear_combination -hsource + htarget
  rw [ha, eval_mul, eval_neg, eval_C] at hequation
  have hfactor : (gamma - gamma0) *
      (source.2 - target.2).eval x = 0 := by
    linear_combination hequation
  exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hgamma)

/-- Explicit contradiction form: no nonbase scalar can have a transverse pair
equation between two members of one common-base collapsed cluster. -/
theorem commonLift_no_transverse_pairEquation
    {F : Type} [Field F]
    (gamma0 gamma x : F) (q0 : F[X])
    (source target : PolynomialLine F)
    (hgamma : gamma ≠ gamma0)
    (hsource : q0 = source.1 + C gamma0 * source.2)
    (htarget : q0 = target.1 + C gamma0 * target.2)
    (htrans : (source.2 - target.2).eval x ≠ 0) :
    (source.1 - target.1).eval x +
        gamma * (source.2 - target.2).eval x ≠ 0 := by
  intro hequation
  exact htrans (commonLift_pairEquation_forces_direction_eval_eq
    gamma0 gamma x q0 source target hgamma hsource htarget hequation)

/-! ## Direct Möbius-label charge no-go -/

/-- Direction value carried at one common-base mismatch coordinate. -/
noncomputable def mobiusDirectionValue
    {F : Type} [Field F] (gamma0 u1 mismatch gamma : F) : F :=
  u1 + (gamma - gamma0)⁻¹ * mismatch

/-- At a nonzero base mismatch, the direction value at one fixed coordinate
is injective in the nonbase rider.  Consequently a coordinate can carry many
different riders with distinct direction labels; forgetting the label cannot
give a coordinate-only injection. -/
theorem mobiusDirectionValue_injOn_nonbase
    {F : Type} [Field F] (gamma0 u1 mismatch : F)
    (hmismatch : mismatch ≠ 0) :
    Set.InjOn (mobiusDirectionValue gamma0 u1 mismatch)
      {gamma : F | gamma ≠ gamma0} := by
  intro gamma hgamma beta hbeta heq
  simp only [Set.mem_setOf_eq] at hgamma hbeta
  simp only [mobiusDirectionValue] at heq
  have hinv : (gamma - gamma0)⁻¹ = (beta - gamma0)⁻¹ := by
    apply mul_right_cancel₀ hmismatch
    linear_combination heq
  have hsub : gamma - gamma0 = beta - gamma0 := inv_injective hinv
  linear_combination hsub

/-! ## External-line determinant factorization -/

/-- **External defect factorization.**  Relative to two lines through the
same lifted point `(gamma0,q0)`, the three-line determinant is the product of
their direction difference and the polynomial defect measuring whether the
external line also passes through that lifted point. -/
theorem lineDeterminant_commonLift_factorization
    {F : Type} [Field F]
    (gamma0 : F) (q0 : F[X])
    (line0 line1 external : PolynomialLine F)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2)
    (hline1 : q0 = line1.1 + C gamma0 * line1.2) :
    lineDeterminant line0 line1 external =
      (line1.2 - line0.2) *
        (q0 - (external.1 + C gamma0 * external.2)) := by
  have ha0 : line0.1 = q0 - C gamma0 * line0.2 := by
    linear_combination -hline0
  have ha1 : line1.1 = q0 - C gamma0 * line1.2 := by
    linear_combination -hline1
  rw [lineDeterminant, ha0, ha1]
  ring

/-- Two distinct lines through one lifted point necessarily have distinct
direction polynomials. -/
theorem direction_ne_of_commonLift_line_ne
    {F : Type} [Field F]
    (gamma0 : F) (q0 : F[X])
    (line0 line1 : PolynomialLine F)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2)
    (hline1 : q0 = line1.1 + C gamma0 * line1.2)
    (hne : line0 ≠ line1) : line1.2 ≠ line0.2 := by
  intro hdir
  apply hne
  apply Prod.ext
  · linear_combination -hline0 + hline1 + C gamma0 * hdir
  · exact hdir.symm

/-- **Maximality of a nondegenerate common-lift cluster.**  If the two
reference directions are distinct, an external line determinant-collapses
with them exactly only if it passes through the same lifted base point. -/
theorem external_commonLift_of_lineDeterminant_eq_zero
    {F : Type} [Field F]
    (gamma0 : F) (q0 : F[X])
    (line0 line1 external : PolynomialLine F)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2)
    (hline1 : q0 = line1.1 + C gamma0 * line1.2)
    (hdirection : line1.2 ≠ line0.2)
    (hdet : lineDeterminant line0 line1 external = 0) :
    q0 = external.1 + C gamma0 * external.2 := by
  rw [lineDeterminant_commonLift_factorization
    gamma0 q0 line0 line1 external hline0 hline1] at hdet
  have hdir : line1.2 - line0.2 ≠ 0 := sub_ne_zero.mpr hdirection
  exact sub_eq_zero.mp ((mul_eq_zero.mp hdet).resolve_left hdir)

/-- Distinct-reference form of common-lift maximality. -/
theorem external_commonLift_of_distinct_commonLift_determinant_zero
    {F : Type} [Field F]
    (gamma0 : F) (q0 : F[X])
    (line0 line1 external : PolynomialLine F)
    (hline0 : q0 = line0.1 + C gamma0 * line0.2)
    (hline1 : q0 = line1.1 + C gamma0 * line1.2)
    (hne : line0 ≠ line1)
    (hdet : lineDeterminant line0 line1 external = 0) :
    q0 = external.1 + C gamma0 * external.2 := by
  exact external_commonLift_of_lineDeterminant_eq_zero
    gamma0 q0 line0 line1 external hline0 hline1
      (direction_ne_of_commonLift_line_ne
        gamma0 q0 line0 line1 hline0 hline1 hne) hdet

/-- The external common-lift defect retains the original degree bound `<k`;
the factorization therefore exposes two separate one-degree budgets rather
than one opaque determinant budget of size `2(k-1)`. -/
theorem commonLift_externalDefect_natDegree_lt
    {F : Type} [Field F] {k : Nat}
    (gamma0 : F) (q0 : F[X]) (external : PolynomialLine F)
    (hq0 : q0.natDegree < k)
    (ha : external.1.natDegree < k)
    (hr : external.2.natDegree < k) :
    (q0 - (external.1 + C gamma0 * external.2)).natDegree < k := by
  have hCmul : (C gamma0 * external.2).natDegree ≤
      external.2.natDegree := by
    calc
      _ ≤ (C gamma0).natDegree + external.2.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ external.2.natDegree := by simp
  have hadd : (external.1 + C gamma0 * external.2).natDegree < k := by
    exact lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
      (max_lt ha (hCmul.trans_lt hr))
  exact lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
    (max_lt hq0 hadd)

end ArkLib.ProximityGap.Frontier.P1RateQuarterCommonBaseDeterminantCollapse

open ArkLib.ProximityGap.Frontier.P1RateQuarterCommonBaseDeterminantCollapse

#print axioms lineDeterminant_eq_zero_of_common_lift
#print axioms three_commonBase_secants_lineDeterminant_eq_zero
#print axioms commonBase_secants_form_collapsed_cluster
#print axioms commonBase_secantSlope_eval_ne_of_baseMismatch
#print axioms commonBase_secantDirection_sub_eval_ne_zero
#print axioms commonLift_pairEquation_forces_direction_eval_eq
#print axioms commonLift_no_transverse_pairEquation
#print axioms mobiusDirectionValue_injOn_nonbase
#print axioms lineDeterminant_commonLift_factorization
#print axioms direction_ne_of_commonLift_line_ne
#print axioms external_commonLift_of_lineDeterminant_eq_zero
#print axioms external_commonLift_of_distinct_commonLift_determinant_zero
#print axioms commonLift_externalDefect_natDegree_lt
