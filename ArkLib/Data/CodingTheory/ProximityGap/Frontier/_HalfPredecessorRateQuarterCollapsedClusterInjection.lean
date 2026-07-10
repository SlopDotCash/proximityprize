/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterDeterminantCollapse

/-!
# Coordinate injection for a collapsed rate-quarter line cluster

Once the determinant of every decoded line with two reference lines vanishes,
all transverse pair equations read the same scalar from a coordinate.  Thus any
assignment of one transverse petal coordinate to every selected scalar is
injective and the cluster contributes at most the code length.

This is the incidence consequence of the determinant-collapse invariant.  The
remaining global rate-quarter task is to produce such a transverse coordinate
assignment, or to charge the points for which every available petal is
nontransverse.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCollapsedClusterInjection

attribute [local instance] Classical.propDecidable

variable {ι F : Type} [Fintype ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- The scalar read from a coordinate by two transverse reference lines. -/
noncomputable def referenceScalarAt (line0 line1 : PolynomialLine F) (x : F) : F :=
  -((line1.1 - line0.1).eval x / (line1.2 - line0.2).eval x)

/-- Determinant collapse makes every line difference a rational multiple of
the fixed reference-line difference, pointwise wherever the reference slope
difference is nonzero. -/
theorem lineDifference_eq_referenceRatio_mul
    (line0 line1 line : PolynomialLine F) {x : F}
    (hdet : lineDeterminant line0 line1 line = 0)
    (href : (line1.2 - line0.2).eval x ≠ 0) :
    (line.1 - line0.1).eval x =
      ((line1.1 - line0.1).eval x /
        (line1.2 - line0.2).eval x) *
      (line.2 - line0.2).eval x := by
  have hdetEval := congrArg (fun P : F[X] => P.eval x) hdet
  simp only [lineDeterminant, eval_sub, eval_mul, eval_zero] at hdetEval
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff href).2
  simpa only [eval_sub] using (sub_eq_zero.mp hdetEval).symm

/-- Two lines in the same collapsed cluster have the same pointwise
intercept-to-slope ratio as the reference pair. -/
theorem pairDifference_eq_referenceRatio_mul
    (line0 line1 line2 line3 : PolynomialLine F) {x : F}
    (hdet2 : lineDeterminant line0 line1 line2 = 0)
    (hdet3 : lineDeterminant line0 line1 line3 = 0)
    (href : (line1.2 - line0.2).eval x ≠ 0) :
    (line2.1 - line3.1).eval x =
      ((line1.1 - line0.1).eval x /
        (line1.2 - line0.2).eval x) *
      (line2.2 - line3.2).eval x := by
  have h2 := lineDifference_eq_referenceRatio_mul
    line0 line1 line2 hdet2 href
  have h3 := lineDifference_eq_referenceRatio_mul
    line0 line1 line3 hdet3 href
  simp only [eval_sub] at h2 h3 ⊢
  linear_combination h2 - h3

/-- A transverse equation between any two lines in a collapsed cluster reads
the reference scalar at that coordinate. -/
theorem gamma_eq_referenceScalarAt_of_pairEquation
    (line0 line1 line2 line3 : PolynomialLine F) {x gamma : F}
    (hdet2 : lineDeterminant line0 line1 line2 = 0)
    (hdet3 : lineDeterminant line0 line1 line3 = 0)
    (href : (line1.2 - line0.2).eval x ≠ 0)
    (htrans : (line2.2 - line3.2).eval x ≠ 0)
    (hequation :
      (line2.1 - line3.1).eval x +
        gamma * (line2.2 - line3.2).eval x = 0) :
    gamma = referenceScalarAt line0 line1 x := by
  have hratio := pairDifference_eq_referenceRatio_mul
    line0 line1 line2 line3 hdet2 hdet3 href
  have hzero :
      (((line1.1 - line0.1).eval x /
          (line1.2 - line0.2).eval x) + gamma) *
        (line2.2 - line3.2).eval x = 0 := by
    rw [add_mul, ← hratio]
    exact hequation
  have hsum :
      (line1.1 - line0.1).eval x /
          (line1.2 - line0.2).eval x + gamma = 0 :=
    (mul_eq_zero.mp hzero).resolve_right htrans
  dsimp only [referenceScalarAt]
  linear_combination hsum

/-- Agreement of a point on one decoded line at a coordinate in another
line's joint core is exactly the corresponding pair equation. -/
theorem pairEquation_of_mem_fullAgreement_of_mem_jointCore
    (dom : ι ↪ F) (u0 u1 : ι → F)
    (source target : PolynomialLine F) (gamma : F) {i : ι}
    (hagree : i ∈ fullAgreement dom u0 u1 gamma
      (source.1 + C gamma * source.2))
    (hcore : i ∈ jointCore dom u0 u1 target.1 target.2) :
    (source.1 - target.1).eval (dom i) +
      gamma * (source.2 - target.2).eval (dom i) = 0 := by
  simp only [fullAgreement, mem_filter, mem_univ, true_and,
    eval_add, eval_mul, eval_C] at hagree
  simp only [jointCore, mem_filter, mem_univ, true_and] at hcore
  simp only [eval_sub]
  linear_combination hagree - hcore.1 - gamma * hcore.2

/-- A petal coordinate carried by another decoded-line core is automatically
transverse unless it already belongs to the source line's own core. -/
theorem transverse_of_mem_fullAgreement_mem_targetCore_not_mem_sourceCore
    (dom : ι ↪ F) (u0 u1 : ι → F)
    (source target : PolynomialLine F) (gamma : F) {i : ι}
    (hagree : i ∈ fullAgreement dom u0 u1 gamma
      (source.1 + C gamma * source.2))
    (htarget : i ∈ jointCore dom u0 u1 target.1 target.2)
    (hfresh : i ∉ jointCore dom u0 u1 source.1 source.2) :
    (source.2 - target.2).eval (dom i) ≠ 0 := by
  have hequation := pairEquation_of_mem_fullAgreement_of_mem_jointCore
    dom u0 u1 source target gamma hagree htarget
  intro hzero
  have ha : (source.1 - target.1).eval (dom i) = 0 := by
    rw [hzero, mul_zero, add_zero] at hequation
    exact hequation
  apply hfresh
  simp only [jointCore, mem_filter, mem_univ, true_and] at htarget ⊢
  simp only [eval_sub] at ha hzero
  constructor
  · linear_combination ha + htarget.1
  · linear_combination hzero + htarget.2

/-- **Collapsed-cluster coordinate injection.**  Suppose every source and
target line belongs to one determinant-collapsed cluster with a fixed
reference pair.  If each scalar has a coordinate where its source-to-target
pair equation and both transversality conditions hold, then the coordinate
assignment is injective, so there are at most `|ι|` scalars. -/
theorem card_le_domain_of_collapsed_transverse_assignment
    (dom : ι ↪ F) (G : Finset F)
    (line0 line1 : PolynomialLine F)
    (source target : F → PolynomialLine F) (coord : F → ι)
    (hsource : ∀ gamma ∈ G,
      lineDeterminant line0 line1 (source gamma) = 0)
    (htarget : ∀ gamma ∈ G,
      lineDeterminant line0 line1 (target gamma) = 0)
    (href : ∀ gamma ∈ G,
      (line1.2 - line0.2).eval (dom (coord gamma)) ≠ 0)
    (htrans : ∀ gamma ∈ G,
      ((source gamma).2 - (target gamma).2).eval
        (dom (coord gamma)) ≠ 0)
    (hequation : ∀ gamma ∈ G,
      ((source gamma).1 - (target gamma).1).eval
          (dom (coord gamma)) +
        gamma * ((source gamma).2 - (target gamma).2).eval
          (dom (coord gamma)) = 0) :
    G.card ≤ Fintype.card ι := by
  let f : {gamma // gamma ∈ G} → ι := fun gamma => coord gamma.1
  have hf : Function.Injective f := by
    intro gamma beta heq
    have hcoord : coord gamma.1 = coord beta.1 := by
      simpa only [f] using heq
    have hgamma := gamma_eq_referenceScalarAt_of_pairEquation
      line0 line1 (source gamma.1) (target gamma.1)
      (hsource gamma.1 gamma.2) (htarget gamma.1 gamma.2)
      (href gamma.1 gamma.2) (htrans gamma.1 gamma.2)
      (hequation gamma.1 gamma.2)
    have hbeta := gamma_eq_referenceScalarAt_of_pairEquation
      line0 line1 (source beta.1) (target beta.1)
      (hsource beta.1 beta.2) (htarget beta.1 beta.2)
      (href beta.1 beta.2) (htrans beta.1 beta.2)
      (hequation beta.1 beta.2)
    apply Subtype.ext
    calc
      gamma.1 = referenceScalarAt line0 line1 (dom (coord gamma.1)) := hgamma
      _ = referenceScalarAt line0 line1 (dom (coord beta.1)) := by rw [hcoord]
      _ = beta.1 := hbeta.symm
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe] using hcard

/-- Geometric form of the collapsed-cluster injection.  The pair equation is
derived from a genuine agreement coordinate of the source line lying in the
target line's joint core. -/
theorem card_le_domain_of_collapsed_transverse_petals
    (dom : ι ↪ F) (u0 u1 : ι → F) (G : Finset F)
    (line0 line1 : PolynomialLine F)
    (source target : F → PolynomialLine F) (coord : F → ι)
    (hsource : ∀ gamma ∈ G,
      lineDeterminant line0 line1 (source gamma) = 0)
    (htarget : ∀ gamma ∈ G,
      lineDeterminant line0 line1 (target gamma) = 0)
    (href : ∀ gamma ∈ G,
      (line1.2 - line0.2).eval (dom (coord gamma)) ≠ 0)
    (htrans : ∀ gamma ∈ G,
      ((source gamma).2 - (target gamma).2).eval
        (dom (coord gamma)) ≠ 0)
    (hagreement : ∀ gamma ∈ G,
      coord gamma ∈ fullAgreement dom u0 u1 gamma
        ((source gamma).1 + C gamma * (source gamma).2))
    (hcore : ∀ gamma ∈ G,
      coord gamma ∈ jointCore dom u0 u1
        (target gamma).1 (target gamma).2) :
    G.card ≤ Fintype.card ι := by
  apply card_le_domain_of_collapsed_transverse_assignment
    dom G line0 line1 source target coord hsource htarget href htrans
  intro gamma hgamma
  exact pairEquation_of_mem_fullAgreement_of_mem_jointCore
    dom u0 u1 (source gamma) (target gamma) gamma
      (hagreement gamma hgamma) (hcore gamma hgamma)

/-- **Fresh-petal form of the collapsed-cluster injection.**  It is enough to
choose, for each scalar, an agreement coordinate carried by another line core
but not by the scalar's source-line core.  Transversality then follows from
the two membership statements. -/
theorem card_le_domain_of_collapsed_fresh_petals
    (dom : ι ↪ F) (u0 u1 : ι → F) (G : Finset F)
    (line0 line1 : PolynomialLine F)
    (source target : F → PolynomialLine F) (coord : F → ι)
    (hsource : ∀ gamma ∈ G,
      lineDeterminant line0 line1 (source gamma) = 0)
    (htarget : ∀ gamma ∈ G,
      lineDeterminant line0 line1 (target gamma) = 0)
    (href : ∀ gamma ∈ G,
      (line1.2 - line0.2).eval (dom (coord gamma)) ≠ 0)
    (hagreement : ∀ gamma ∈ G,
      coord gamma ∈ fullAgreement dom u0 u1 gamma
        ((source gamma).1 + C gamma * (source gamma).2))
    (htargetCore : ∀ gamma ∈ G,
      coord gamma ∈ jointCore dom u0 u1
        (target gamma).1 (target gamma).2)
    (hfresh : ∀ gamma ∈ G,
      coord gamma ∉ jointCore dom u0 u1
        (source gamma).1 (source gamma).2) :
    G.card ≤ Fintype.card ι := by
  apply card_le_domain_of_collapsed_transverse_petals
    dom u0 u1 G line0 line1 source target coord
      hsource htarget href
  · intro gamma hgamma
    exact transverse_of_mem_fullAgreement_mem_targetCore_not_mem_sourceCore
      dom u0 u1 (source gamma) (target gamma) gamma
        (hagreement gamma hgamma) (htargetCore gamma hgamma)
        (hfresh gamma hgamma)
  · exact hagreement
  · exact htargetCore

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCollapsedClusterInjection

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCollapsedClusterInjection
#print axioms gamma_eq_referenceScalarAt_of_pairEquation
#print axioms pairEquation_of_mem_fullAgreement_of_mem_jointCore
#print axioms transverse_of_mem_fullAgreement_mem_targetCore_not_mem_sourceCore
#print axioms card_le_domain_of_collapsed_transverse_assignment
#print axioms card_le_domain_of_collapsed_transverse_petals
#print axioms card_le_domain_of_collapsed_fresh_petals
