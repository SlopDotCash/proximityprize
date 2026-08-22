/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterCollapsedClusterInjection
import Mathlib.RingTheory.EuclideanDomain

/-!
# Primitive-direction injection for a collapsed rate-quarter cluster

The raw difference of two reference polynomial lines can have a common
polynomial factor.  At a root of that factor both reference components vanish,
so a pointwise argument with the raw reference pair needs a separate
``avoid the reference-slope roots'' hypothesis.

This file removes that artificial loss.  Divide both reference differences by
their polynomial gcd and write the resulting primitive direction as `(A,R)`.
Then `A` and `R` are coprime, hence never vanish simultaneously at a field
coordinate.  Determinant collapse cancels the gcd and gives

```text
A * (r_i-r_j) = R * (a_i-a_j)
```

for every two lines in the cluster.  Therefore a transverse cross-core petal
automatically has `R(x) != 0` and reads the scalar `-A(x)/R(x)`.  Distinct
scalars assigned to the same coordinate coincide, giving an injection into
the evaluation domain with no extra root-avoidance condition.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCollapsedClusterInjection

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveDirection

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- The common polynomial content of the two components of a reference-line
difference. -/
noncomputable def referenceContent
    (line0 line1 : PolynomialLine F) : F[X] :=
  GCDMonoid.gcd (line1.1 - line0.1) (line1.2 - line0.2)

/-- The reference intercept difference after removing its common content. -/
noncomputable def primitiveIntercept
    (line0 line1 : PolynomialLine F) : F[X] :=
  (line1.1 - line0.1) / referenceContent line0 line1

/-- The reference slope difference after removing its common content. -/
noncomputable def primitiveSlope
    (line0 line1 : PolynomialLine F) : F[X] :=
  (line1.2 - line0.2) / referenceContent line0 line1

/-- Two distinct reference lines have nonzero common content. -/
theorem referenceContent_ne_zero_of_ne
    {line0 line1 : PolynomialLine F} (hne : line0 ≠ line1) :
    referenceContent line0 line1 ≠ 0 := by
  intro hzero
  have hz := (gcd_eq_zero_iff
    (line1.1 - line0.1) (line1.2 - line0.2)).mp hzero
  apply hne
  exact Prod.ext (sub_eq_zero.mp hz.1).symm (sub_eq_zero.mp hz.2).symm

/-- The raw intercept difference is its content times the primitive
intercept direction. -/
theorem referenceIntercept_eq_content_mul_primitive
    {line0 line1 : PolynomialLine F} (hne : line0 ≠ line1) :
    line1.1 - line0.1 =
      referenceContent line0 line1 * primitiveIntercept line0 line1 := by
  symm
  exact EuclideanDomain.mul_div_cancel'
    (referenceContent_ne_zero_of_ne hne)
    (GCDMonoid.gcd_dvd_left
      (line1.1 - line0.1) (line1.2 - line0.2))

/-- The raw slope difference is its content times the primitive slope
direction. -/
theorem referenceSlope_eq_content_mul_primitive
    {line0 line1 : PolynomialLine F} (hne : line0 ≠ line1) :
    line1.2 - line0.2 =
      referenceContent line0 line1 * primitiveSlope line0 line1 := by
  symm
  exact EuclideanDomain.mul_div_cancel'
    (referenceContent_ne_zero_of_ne hne)
    (GCDMonoid.gcd_dvd_right
      (line1.1 - line0.1) (line1.2 - line0.2))

/-- Removing the gcd makes the direction components coprime. -/
theorem primitiveDirection_isCoprime
    {line0 line1 : PolynomialLine F} (hne : line0 ≠ line1) :
    IsCoprime (primitiveIntercept line0 line1)
      (primitiveSlope line0 line1) := by
  exact isCoprime_div_gcd_div_gcd_of_gcd_ne_zero
    (referenceContent_ne_zero_of_ne hne)

/-- A primitive polynomial direction has no simultaneous field-valued zero. -/
theorem primitiveDirection_eval_ne_zero
    {line0 line1 : PolynomialLine F} (hne : line0 ≠ line1) (x : F) :
    (primitiveIntercept line0 line1).eval x ≠ 0 \/
      (primitiveSlope line0 line1).eval x ≠ 0 := by
  rcases primitiveDirection_isCoprime hne with ⟨p, q, hpq⟩
  by_contra! hzero
  have heval := congrArg (fun f : F[X] => f.eval x) hpq
  simp only [eval_add, eval_mul, eval_one, hzero.1, hzero.2,
    mul_zero, add_zero, zero_ne_one] at heval

/-- Determinant collapse with the raw reference pair remains valid after
cancelling the common polynomial content. -/
theorem primitive_relation_of_lineDeterminant_eq_zero
    (line0 line1 line : PolynomialLine F)
    (hne : line0 ≠ line1)
    (hdet : lineDeterminant line0 line1 line = 0) :
    primitiveIntercept line0 line1 * (line.2 - line0.2) =
      primitiveSlope line0 line1 * (line.1 - line0.1) := by
  have hraw :
      (line1.1 - line0.1) * (line.2 - line0.2) =
        (line.1 - line0.1) * (line1.2 - line0.2) := by
    exact sub_eq_zero.mp (by simpa only [lineDeterminant] using hdet)
  rw [referenceIntercept_eq_content_mul_primitive hne,
    referenceSlope_eq_content_mul_primitive hne] at hraw
  apply mul_left_cancel₀ (referenceContent_ne_zero_of_ne hne)
  calc
    referenceContent line0 line1 *
        (primitiveIntercept line0 line1 * (line.2 - line0.2)) =
      (referenceContent line0 line1 * primitiveIntercept line0 line1) *
        (line.2 - line0.2) := by ring
    _ = (line.1 - line0.1) *
        (referenceContent line0 line1 * primitiveSlope line0 line1) := hraw
    _ = referenceContent line0 line1 *
        (primitiveSlope line0 line1 * (line.1 - line0.1)) := by ring

/-- **Polynomial affine-line collapse.**  The usual determinant-zero
conclusion is often described as collinearity over `F(X)`.  After removing
the gcd of one nonzero reference difference, coprimality strengthens this:
every polynomial line in the collapsed cluster differs from the base line by
an actual *polynomial* multiple of one common primitive direction. -/
theorem exists_polynomial_factor_of_lineDeterminant_eq_zero
    (line0 line1 line : PolynomialLine F)
    (hne : line0 ≠ line1)
    (hdet : lineDeterminant line0 line1 line = 0) :
    ∃ f : F[X],
      line.1 - line0.1 = primitiveIntercept line0 line1 * f ∧
      line.2 - line0.2 = primitiveSlope line0 line1 * f := by
  let A := primitiveIntercept line0 line1
  let R := primitiveSlope line0 line1
  let ea := line.1 - line0.1
  let er := line.2 - line0.2
  have hcop : IsCoprime A R := by
    simpa only [A, R] using primitiveDirection_isCoprime hne
  have hrel : A * er = R * ea := by
    simpa only [A, R, ea, er] using
      primitive_relation_of_lineDeterminant_eq_zero line0 line1 line hne hdet
  have hAdiv : A ∣ ea := hcop.dvd_of_dvd_mul_left ⟨er, hrel.symm⟩
  have hRdiv : R ∣ er := hcop.symm.dvd_of_dvd_mul_left ⟨ea, hrel⟩
  obtain ⟨f, hf⟩ := hAdiv
  obtain ⟨g, hg⟩ := hRdiv
  by_cases hA : A = 0
  · refine ⟨g, ?_, by simpa only [er, R] using hg⟩
    have heq : ea = A * g := by rw [hf, hA, zero_mul, zero_mul]
    simpa only [ea, A] using heq
  by_cases hR : R = 0
  · refine ⟨f, by simpa only [ea, A] using hf, ?_⟩
    have heq : er = R * f := by rw [hg, hR, zero_mul, zero_mul]
    simpa only [er, R] using heq
  have hgf : g = f := by
    apply mul_left_cancel₀ (mul_ne_zero hA hR)
    calc
      (A * R) * g = A * er := by rw [hg]; ring
      _ = R * ea := hrel
      _ = (A * R) * f := by rw [hf]; ring
  refine ⟨f, by simpa only [ea, A] using hf, ?_⟩
  have heq : er = R * f := by rw [hg, hgf]
  simpa only [er, R] using heq

/-- Every difference of two lines in the same collapsed cluster is parallel
to the primitive reference direction. -/
theorem pairDifference_primitive_relation
    (line0 line1 line2 line3 : PolynomialLine F)
    (hne : line0 ≠ line1)
    (hdet2 : lineDeterminant line0 line1 line2 = 0)
    (hdet3 : lineDeterminant line0 line1 line3 = 0) :
    primitiveIntercept line0 line1 * (line2.2 - line3.2) =
      primitiveSlope line0 line1 * (line2.1 - line3.1) := by
  have h2 := primitive_relation_of_lineDeterminant_eq_zero
    line0 line1 line2 hne hdet2
  have h3 := primitive_relation_of_lineDeterminant_eq_zero
    line0 line1 line3 hne hdet3
  linear_combination h2 - h3

/-- A transverse pair difference in a collapsed cluster automatically lies
in the primitive slope chart.  This is the key gain over the raw-reference
formulation. -/
theorem primitiveSlope_eval_ne_zero_of_pair_slope_eval_ne_zero
    (line0 line1 line2 line3 : PolynomialLine F) {x : F}
    (hne : line0 ≠ line1)
    (hdet2 : lineDeterminant line0 line1 line2 = 0)
    (hdet3 : lineDeterminant line0 line1 line3 = 0)
    (htrans : (line2.2 - line3.2).eval x ≠ 0) :
    (primitiveSlope line0 line1).eval x ≠ 0 := by
  have hrelation := congrArg (fun f : F[X] => f.eval x)
    (pairDifference_primitive_relation line0 line1 line2 line3
      hne hdet2 hdet3)
  simp only [eval_mul] at hrelation
  intro hR
  have hA : (primitiveIntercept line0 line1).eval x = 0 := by
    rw [hR, zero_mul] at hrelation
    exact (mul_eq_zero.mp hrelation).resolve_right htrans
  rcases primitiveDirection_eval_ne_zero hne x with hAne | hRne
  · exact hAne hA
  · exact hRne hR

/-- The coordinate scalar attached to the primitive cluster direction. -/
noncomputable def primitiveScalarAt
    (line0 line1 : PolynomialLine F) (x : F) : F :=
  -((primitiveIntercept line0 line1).eval x /
    (primitiveSlope line0 line1).eval x)

/-- Every transverse pair equation in a determinant-collapsed cluster reads
the primitive coordinate scalar. -/
theorem gamma_eq_primitiveScalarAt_of_pairEquation
    (line0 line1 line2 line3 : PolynomialLine F) {x gamma : F}
    (hne : line0 ≠ line1)
    (hdet2 : lineDeterminant line0 line1 line2 = 0)
    (hdet3 : lineDeterminant line0 line1 line3 = 0)
    (htrans : (line2.2 - line3.2).eval x ≠ 0)
    (hequation :
      (line2.1 - line3.1).eval x +
        gamma * (line2.2 - line3.2).eval x = 0) :
    gamma = primitiveScalarAt line0 line1 x := by
  have hrelation := congrArg (fun f : F[X] => f.eval x)
    (pairDifference_primitive_relation line0 line1 line2 line3
      hne hdet2 hdet3)
  simp only [eval_mul] at hrelation
  have hR := primitiveSlope_eval_ne_zero_of_pair_slope_eval_ne_zero
    line0 line1 line2 line3 hne hdet2 hdet3 htrans
  have hproduct :
      ((primitiveIntercept line0 line1).eval x +
          gamma * (primitiveSlope line0 line1).eval x) *
        (line2.2 - line3.2).eval x = 0 := by
    calc
      ((primitiveIntercept line0 line1).eval x +
            gamma * (primitiveSlope line0 line1).eval x) *
          (line2.2 - line3.2).eval x =
        (primitiveSlope line0 line1).eval x *
          ((line2.1 - line3.1).eval x +
            gamma * (line2.2 - line3.2).eval x) := by
              rw [add_mul, hrelation]
              ring
      _ = 0 := by rw [hequation, mul_zero]
  have hsum :
      (primitiveIntercept line0 line1).eval x +
        gamma * (primitiveSlope line0 line1).eval x = 0 :=
    (mul_eq_zero.mp hproduct).resolve_right htrans
  dsimp only [primitiveScalarAt]
  rw [← neg_div]
  apply (eq_div_iff hR).mpr
  linear_combination hsum

/-- **Primitive collapsed-cluster injection.**  Unlike the raw-reference
version, this theorem needs no hypothesis that chosen coordinates avoid the
roots of the reference slope difference.  Primitivity and pair transversality
prove that automatically. -/
theorem card_le_domain_of_primitive_collapsed_transverse_assignment
    (dom : I ↪ F) (G : Finset F)
    (line0 line1 : PolynomialLine F)
    (source target : F → PolynomialLine F) (coord : F → I)
    (hne : line0 ≠ line1)
    (hsource : ∀ gamma ∈ G,
      lineDeterminant line0 line1 (source gamma) = 0)
    (htarget : ∀ gamma ∈ G,
      lineDeterminant line0 line1 (target gamma) = 0)
    (htrans : ∀ gamma ∈ G,
      ((source gamma).2 - (target gamma).2).eval
        (dom (coord gamma)) ≠ 0)
    (hequation : ∀ gamma ∈ G,
      ((source gamma).1 - (target gamma).1).eval
          (dom (coord gamma)) +
        gamma * ((source gamma).2 - (target gamma).2).eval
          (dom (coord gamma)) = 0) :
    G.card ≤ Fintype.card I := by
  let f : {gamma // gamma ∈ G} → I := fun gamma => coord gamma.1
  have hf : Function.Injective f := by
    intro gamma beta heq
    have hcoord : coord gamma.1 = coord beta.1 := by
      simpa only [f] using heq
    have hgamma := gamma_eq_primitiveScalarAt_of_pairEquation
      line0 line1 (source gamma.1) (target gamma.1)
      hne (hsource gamma.1 gamma.2) (htarget gamma.1 gamma.2)
      (htrans gamma.1 gamma.2) (hequation gamma.1 gamma.2)
    have hbeta := gamma_eq_primitiveScalarAt_of_pairEquation
      line0 line1 (source beta.1) (target beta.1)
      hne (hsource beta.1 beta.2) (htarget beta.1 beta.2)
      (htrans beta.1 beta.2) (hequation beta.1 beta.2)
    apply Subtype.ext
    calc
      gamma.1 = primitiveScalarAt line0 line1 (dom (coord gamma.1)) := hgamma
      _ = primitiveScalarAt line0 line1 (dom (coord beta.1)) := by rw [hcoord]
      _ = beta.1 := hbeta.symm
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe] using hcard

/-- **Fresh-petal primitive injection.**  A genuine agreement coordinate in
another cluster line's core, outside the source core, supplies the transverse
pair equation.  Determinant collapse plus the primitive direction then bounds
the whole assigned cluster by the domain size, with no root-exception set. -/
theorem card_le_domain_of_primitive_collapsed_fresh_petals
    (dom : I ↪ F) (u0 u1 : I → F) (G : Finset F)
    (line0 line1 : PolynomialLine F)
    (source target : F → PolynomialLine F) (coord : F → I)
    (hne : line0 ≠ line1)
    (hsource : ∀ gamma ∈ G,
      lineDeterminant line0 line1 (source gamma) = 0)
    (htarget : ∀ gamma ∈ G,
      lineDeterminant line0 line1 (target gamma) = 0)
    (hagreement : ∀ gamma ∈ G,
      coord gamma ∈ fullAgreement dom u0 u1 gamma
        ((source gamma).1 + C gamma * (source gamma).2))
    (htargetCore : ∀ gamma ∈ G,
      coord gamma ∈ jointCore dom u0 u1
        (target gamma).1 (target gamma).2)
    (hfresh : ∀ gamma ∈ G,
      coord gamma ∉ jointCore dom u0 u1
        (source gamma).1 (source gamma).2) :
    G.card ≤ Fintype.card I := by
  apply card_le_domain_of_primitive_collapsed_transverse_assignment
    dom G line0 line1 source target coord hne hsource htarget
  · intro gamma hgamma
    exact transverse_of_mem_fullAgreement_mem_targetCore_not_mem_sourceCore
      dom u0 u1 (source gamma) (target gamma) gamma
        (hagreement gamma hgamma) (htargetCore gamma hgamma)
        (hfresh gamma hgamma)
  · intro gamma hgamma
    exact pairEquation_of_mem_fullAgreement_of_mem_jointCore
      dom u0 u1 (source gamma) (target gamma) gamma
        (hagreement gamma hgamma) (htargetCore gamma hgamma)

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveDirection

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveDirection
#print axioms primitiveDirection_isCoprime
#print axioms primitive_relation_of_lineDeterminant_eq_zero
#print axioms exists_polynomial_factor_of_lineDeterminant_eq_zero
#print axioms gamma_eq_primitiveScalarAt_of_pairEquation
#print axioms card_le_domain_of_primitive_collapsed_transverse_assignment
#print axioms card_le_domain_of_primitive_collapsed_fresh_petals
