/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterPrimitiveDirection

/-!
# Lower-degree factor recursion inside a primitive collapsed cluster

Every determinant-collapsed polynomial line has the form

```text
c_f = c0 + f * (A,R)
```

for the common coprime primitive direction `(A,R)`.  This file records the
recursive Reed--Solomon geometry of the factor polynomials.  Because `A` and
`R` never vanish simultaneously, equality of two cluster lines at a field
coordinate is exactly equality of their factors there.  Hence intersections
of their received-word cores are bounded by the root count of `f-g`, and a
nonconstant primitive direction lowers the available factor degree.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveDirection

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveFactorRecursion

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Pointwise Bezout coordinates for a primitive two-vector.  The vector
`(vA,vR)` is the scalar multiple `f*(A,R)` iff it is collinear with `(A,R)`
and its Bezout coordinate is `f`. -/
theorem primitive_coordinates_iff
    {A R p q vA vR f : F} (hbezout : p * A + q * R = 1) :
    (vA = A * f ∧ vR = R * f) ↔
      (A * vR - R * vA = 0 ∧ f = p * vA + q * vR) := by
  constructor
  · rintro ⟨rfl, rfl⟩
    constructor
    · ring
    · calc
        f = 1 * f := by rw [one_mul]
        _ = (p * A + q * R) * f := by rw [hbezout]
        _ = p * (A * f) + q * (R * f) := by ring
  · rintro ⟨hcross, hfactor⟩
    have hcross' : A * vR = R * vA := sub_eq_zero.mp hcross
    constructor
    · calc
        vA = 1 * vA := by rw [one_mul]
        _ = (p * A + q * R) * vA := by rw [hbezout]
        _ = p * A * vA + q * R * vA := by ring
        _ = p * A * vA + q * A * vR := by
          linear_combination -q * hcross'
        _ = A * (p * vA + q * vR) := by ring
        _ = A * f := by rw [hfactor]
    · calc
        vR = 1 * vR := by rw [one_mul]
        _ = (p * A + q * R) * vR := by rw [hbezout]
        _ = p * A * vR + q * R * vR := by ring
        _ = p * R * vA + q * R * vR := by
          linear_combination p * hcross'
        _ = R * (p * vA + q * vR) := by ring
        _ = R * f := by rw [hfactor]

/-- Exact pointwise characterization of a cluster line's received-word core.
The first condition is a common mask, independent of `f`; the second says
that `f` agrees with one common scalar word obtained by Bezout projection. -/
theorem mem_jointCore_iff_primitive_factor_agrees
    (dom : I ↪ F) (u0 u1 : I → F)
    (line0 line1 lineF : PolynomialLine F)
    (f p q : F[X]) {i : I}
    (hFa : lineF.1 - line0.1 = primitiveIntercept line0 line1 * f)
    (hFr : lineF.2 - line0.2 = primitiveSlope line0 line1 * f)
    (hbezout :
      p * primitiveIntercept line0 line1 +
        q * primitiveSlope line0 line1 = 1) :
    i ∈ jointCore dom u0 u1 lineF.1 lineF.2 ↔
      (primitiveIntercept line0 line1).eval (dom i) *
            (u1 i - line0.2.eval (dom i)) -
          (primitiveSlope line0 line1).eval (dom i) *
            (u0 i - line0.1.eval (dom i)) = 0 ∧
        f.eval (dom i) =
          p.eval (dom i) * (u0 i - line0.1.eval (dom i)) +
            q.eval (dom i) * (u1 i - line0.2.eval (dom i)) := by
  have hFaEval := congrArg (fun z : F[X] ↦ z.eval (dom i)) hFa
  have hFrEval := congrArg (fun z : F[X] ↦ z.eval (dom i)) hFr
  have hbezoutEval := congrArg (fun z : F[X] ↦ z.eval (dom i)) hbezout
  simp only [eval_sub, eval_mul, eval_add, eval_one] at hFaEval hFrEval hbezoutEval
  simp only [jointCore, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ha, hr⟩
    apply (primitive_coordinates_iff hbezoutEval).mp
    constructor
    · calc
        u0 i - line0.1.eval (dom i) =
            lineF.1.eval (dom i) - line0.1.eval (dom i) := by rw [ha]
        _ = (primitiveIntercept line0 line1).eval (dom i) *
            f.eval (dom i) := hFaEval
    · calc
        u1 i - line0.2.eval (dom i) =
            lineF.2.eval (dom i) - line0.2.eval (dom i) := by rw [hr]
        _ = (primitiveSlope line0 line1).eval (dom i) *
            f.eval (dom i) := hFrEval
  · intro hmasked
    have hcoords := (primitive_coordinates_iff hbezoutEval).mpr hmasked
    constructor
    · linear_combination hFaEval - hcoords.1
    · linear_combination hFrEval - hcoords.2

/-- Finset form of the exact masked factor-code reduction. -/
theorem jointCore_eq_masked_factor_agreement
    (dom : I ↪ F) (u0 u1 : I → F)
    (line0 line1 lineF : PolynomialLine F)
    (f p q : F[X])
    (hFa : lineF.1 - line0.1 = primitiveIntercept line0 line1 * f)
    (hFr : lineF.2 - line0.2 = primitiveSlope line0 line1 * f)
    (hbezout :
      p * primitiveIntercept line0 line1 +
        q * primitiveSlope line0 line1 = 1) :
    jointCore dom u0 u1 lineF.1 lineF.2 =
      Finset.univ.filter fun i ↦
        (primitiveIntercept line0 line1).eval (dom i) *
              (u1 i - line0.2.eval (dom i)) -
            (primitiveSlope line0 line1).eval (dom i) *
              (u0 i - line0.1.eval (dom i)) = 0 ∧
          f.eval (dom i) =
            p.eval (dom i) * (u0 i - line0.1.eval (dom i)) +
              q.eval (dom i) * (u1 i - line0.2.eval (dom i)) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact mem_jointCore_iff_primitive_factor_agrees
    dom u0 u1 line0 line1 lineF f p q hFa hFr hbezout

/-- If two cluster lines have primitive factors `f` and `g`, equality of the
two polynomial pairs at one coordinate forces `f(x)=g(x)`. -/
theorem factor_sub_eval_eq_zero_of_line_values_eq
    (line0 line1 lineF lineG : PolynomialLine F)
    (f g : F[X]) (x : F)
    (hne : line0 ≠ line1)
    (hFa : lineF.1 - line0.1 = primitiveIntercept line0 line1 * f)
    (hFr : lineF.2 - line0.2 = primitiveSlope line0 line1 * f)
    (hGa : lineG.1 - line0.1 = primitiveIntercept line0 line1 * g)
    (hGr : lineG.2 - line0.2 = primitiveSlope line0 line1 * g)
    (ha : lineF.1.eval x = lineG.1.eval x)
    (hr : lineF.2.eval x = lineG.2.eval x) :
    (f - g).eval x = 0 := by
  have hFaEval := congrArg (fun p : F[X] ↦ p.eval x) hFa
  have hFrEval := congrArg (fun p : F[X] ↦ p.eval x) hFr
  have hGaEval := congrArg (fun p : F[X] ↦ p.eval x) hGa
  have hGrEval := congrArg (fun p : F[X] ↦ p.eval x) hGr
  simp only [eval_sub, eval_mul] at hFaEval hFrEval hGaEval hGrEval
  have hAprod :
      (primitiveIntercept line0 line1).eval x * (f - g).eval x = 0 := by
    simp only [eval_sub, mul_sub]
    rw [← hFaEval, ← hGaEval, ha, sub_self]
  have hRprod :
      (primitiveSlope line0 line1).eval x * (f - g).eval x = 0 := by
    simp only [eval_sub, mul_sub]
    rw [← hFrEval, ← hGrEval, hr, sub_self]
  by_contra hfg
  have hAzero : (primitiveIntercept line0 line1).eval x = 0 :=
    (mul_eq_zero.mp hAprod).resolve_right hfg
  have hRzero : (primitiveSlope line0 line1).eval x = 0 :=
    (mul_eq_zero.mp hRprod).resolve_right hfg
  rcases primitiveDirection_eval_ne_zero hne x with hAne | hRne
  · exact hAne hAzero
  · exact hRne hRzero

/-- The intersection of two received-word cores in a primitive cluster maps
into the evaluation-domain root set of the factor difference. -/
theorem core_intersection_subset_factor_sub_roots
    (dom : I ↪ F) (u0 u1 : I → F)
    (line0 line1 lineF lineG : PolynomialLine F)
    (f g : F[X])
    (hne : line0 ≠ line1)
    (hFa : lineF.1 - line0.1 = primitiveIntercept line0 line1 * f)
    (hFr : lineF.2 - line0.2 = primitiveSlope line0 line1 * f)
    (hGa : lineG.1 - line0.1 = primitiveIntercept line0 line1 * g)
    (hGr : lineG.2 - line0.2 = primitiveSlope line0 line1 * g) :
    jointCore dom u0 u1 lineF.1 lineF.2 ∩
        jointCore dom u0 u1 lineG.1 lineG.2 ⊆
      Finset.univ.filter fun i ↦ (f - g).eval (dom i) = 0 := by
  intro i hi
  simp only [Finset.mem_inter, jointCore, Finset.mem_filter,
    Finset.mem_univ, true_and] at hi ⊢
  apply factor_sub_eval_eq_zero_of_line_values_eq
    line0 line1 lineF lineG f g (dom i) hne hFa hFr hGa hGr
  · exact hi.1.1.trans hi.2.1.symm
  · exact hi.1.2.trans hi.2.2.symm

/-- Distinct factor polynomials bound the intersection of two cluster cores by
their difference degree. -/
theorem core_intersection_card_le_factor_sub_natDegree
    (dom : I ↪ F) (u0 u1 : I → F)
    (line0 line1 lineF lineG : PolynomialLine F)
    (f g : F[X])
    (hne : line0 ≠ line1)
    (hfg : f ≠ g)
    (hFa : lineF.1 - line0.1 = primitiveIntercept line0 line1 * f)
    (hFr : lineF.2 - line0.2 = primitiveSlope line0 line1 * f)
    (hGa : lineG.1 - line0.1 = primitiveIntercept line0 line1 * g)
    (hGr : lineG.2 - line0.2 = primitiveSlope line0 line1 * g) :
    (jointCore dom u0 u1 lineF.1 lineF.2 ∩
      jointCore dom u0 u1 lineG.1 lineG.2).card ≤
        (f - g).natDegree := by
  calc
    (jointCore dom u0 u1 lineF.1 lineF.2 ∩
        jointCore dom u0 u1 lineG.1 lineG.2).card ≤
      (Finset.univ.filter fun i ↦ (f - g).eval (dom i) = 0).card :=
        Finset.card_le_card <|
          core_intersection_subset_factor_sub_roots
            dom u0 u1 line0 line1 lineF lineG f g hne
              hFa hFr hGa hGr
    _ ≤ (f - g).natDegree :=
      ArkLib.CS25.card_domain_roots_le dom (f - g) (sub_ne_zero.mpr hfg)

/-- Degree-`<ell` factors give the usual Reed--Solomon intersection cap
`ell-1`, now for the cores of the original polynomial-pair cluster. -/
theorem core_intersection_card_le_factor_dimension_pred
    (dom : I ↪ F) (u0 u1 : I → F)
    (line0 line1 lineF lineG : PolynomialLine F)
    (f g : F[X]) {ell : ℕ}
    (hne : line0 ≠ line1)
    (hfg : f ≠ g)
    (hfdeg : f.natDegree < ell) (hgdeg : g.natDegree < ell)
    (hFa : lineF.1 - line0.1 = primitiveIntercept line0 line1 * f)
    (hFr : lineF.2 - line0.2 = primitiveSlope line0 line1 * f)
    (hGa : lineG.1 - line0.1 = primitiveIntercept line0 line1 * g)
    (hGr : lineG.2 - line0.2 = primitiveSlope line0 line1 * g) :
    (jointCore dom u0 u1 lineF.1 lineF.2 ∩
      jointCore dom u0 u1 lineG.1 lineG.2).card ≤ ell - 1 := by
  have hroot := core_intersection_card_le_factor_sub_natDegree
    dom u0 u1 line0 line1 lineF lineG f g hne hfg hFa hFr hGa hGr
  have hdeg : (f - g).natDegree < ell :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le f g)
      (max_lt hfdeg hgdeg)
  omega

/-- Factoring through a nonzero direction component drops the available
factor degree by that component's degree. -/
theorem factor_natDegree_lt_sub_of_component_factor
    {base component factor : F[X]} {k : ℕ}
    (hcomponent : component ≠ 0) (hfactor : factor ≠ 0)
    (hbaseDeg : base.natDegree < k)
    (hlineDeg : (base + component * factor).natDegree < k) :
    factor.natDegree < k - component.natDegree := by
  have hprodDeg : (component * factor).natDegree < k := by
    have heq : component * factor =
        (base + component * factor) - base := by ring
    rw [heq]
    exact lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
      (max_lt hlineDeg hbaseDeg)
  rw [Polynomial.natDegree_mul hcomponent hfactor] at hprodDeg
  omega

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveFactorRecursion

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveFactorRecursion
#print axioms factor_sub_eval_eq_zero_of_line_values_eq
#print axioms primitive_coordinates_iff
#print axioms jointCore_eq_masked_factor_agreement
#print axioms core_intersection_card_le_factor_sub_natDegree
#print axioms core_intersection_card_le_factor_dimension_pred
#print axioms factor_natDegree_lt_sub_of_component_factor
