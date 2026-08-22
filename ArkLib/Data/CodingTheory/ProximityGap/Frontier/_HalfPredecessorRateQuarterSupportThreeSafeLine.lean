/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AffineRichPointPacking
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterSparseSafeLine
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterOverlapThreeFactorization
import ArkLib.Data.CodingTheory.ProximityGap.LineListSupportRatioFiber

/-!
# Rate-quarter `k = 4`: zero-safe support-three lines

This file closes the first stratum beyond the positive Plotkin denominator.
At `n = 16`, `k = 4`, threshold `9`, and direction support three, the surviving
zero-agreement strata have weights

```text
t = 6: scalar weight 1,
t = 7: scalar weight 1,
t = 8: scalar weight 3.
```

The upper two strata have Plotkin caps five and two.  The bottom stratum is
handled by an affine-function arrangement on the thirteen zero coordinates:
after interpolating the received rows on the three moving coordinates, every
six-zero-agreement codeword is a six-rich parameter-value point.  Identical
coordinate functions occur at most three times, so the generic ordered-pair
packing theorem bounds this stratum by eight.

The apparent aggregate endpoint `8 + 5 + 3*2 = 19` is sharpened when the top
stratum has two members.  Their two size-eight traces meet in exactly three
coordinates and cover all thirteen.  Every size-six trace avoids their common
triple, hence lies in a ten-coordinate universe; Plotkin then improves its cap
from eight to five.  The two cases give `8+5+3` and `5+5+6`, both at most
sixteen.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportThreeSafeLine

open _root_.ProximityGap _root_.ProximityGap.Ownership _root_.ProximityGap.SpikeFloor
open _root_.ProximityGap.LargeZeroWitnessSplit _root_.ProximityGap.LineListMCAWeld
open ArkLib.ProximityGap.Frontier.ConstantWeightPlotkinBound
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSparseSafeLine
open ArkLib.ProximityGap.Frontier.AffineRichPointPacking
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeFactorization

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- Mixed-stratum version of the RS trace-intersection cap. -/
theorem zeroAgreementTrace_pair_card_le_three_of_appearing
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    {c c' : Fin 16 → F}
    (hc : c ∈ lineAppearingCodewords dom 4 9 u0 u1)
    (hc' : c' ∈ lineAppearingCodewords dom 4 9 u0 u1)
    (hne : c ≠ c') :
    (zeroAgreementTrace c u0 u1 ∩ zeroAgreementTrace c' u0 u1).card ≤ 3 := by
  let e : {i : Fin 16 // i ∈ directionZeroSet u1} ↪ Fin 16 :=
    ⟨fun i ↦ i.1, fun _ _ h ↦ Subtype.ext h⟩
  have hsub : (zeroAgreementTrace c u0 u1 ∩
      zeroAgreementTrace c' u0 u1).map e ⊆ agreeSet c c' := by
    intro i hi
    rw [Finset.mem_map] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    rw [Finset.mem_inter] at hj
    have hjc := (Finset.mem_filter.mp hj.1).2
    have hjc' := (Finset.mem_filter.mp hj.2).2
    rw [agreeSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hjc.trans hjc'.symm⟩
  have hcCode : c ∈ (rsCode dom 4 : Submodule F (Fin 16 → F)) := by
    rw [lineAppearingCodewords, Finset.mem_filter] at hc
    exact hc.2.1
  have hc'Code : c' ∈ (rsCode dom 4 : Submodule F (Fin 16 → F)) := by
    rw [lineAppearingCodewords, Finset.mem_filter] at hc'
    exact hc'.2.1
  calc
    (zeroAgreementTrace c u0 u1 ∩ zeroAgreementTrace c' u0 u1).card =
        ((zeroAgreementTrace c u0 u1 ∩
          zeroAgreementTrace c' u0 u1).map e).card := by
            rw [Finset.card_map]
    _ ≤ (agreeSet c c').card := Finset.card_le_card hsub
    _ ≤ 4 - 1 := rsCode_pairwise_agreeSet_card_le
      dom (by omega) hcCode hc'Code hne
    _ = 3 := by omega

/-! ## Plotkin caps for the upper two strata -/

open Classical in
theorem zeroAgreementStratum_seven_card_le_five_of_support_three
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 3) :
    (zeroAgreementStratum dom 4 9 u0 u1 7).card ≤ 5 := by
  let I := {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 7}
  let U := {i : Fin 16 // i ∈ directionZeroSet u1}
  let S : I → Finset U := fun c ↦ zeroAgreementTrace c.1 u0 u1
  have hU : Fintype.card U = 13 := by
    have hpartition := directionSupportSet_card_eq (n := 16) u1
    have hz : (directionZeroSet u1).card = 13 := by omega
    simpa [U] using hz
  have hsize : ∀ c : I, (S c).card = 7 := by
    intro c
    rw [zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp c.2).2
  have hpair : ∀ c c' : I, c ≠ c' → (S c ∩ S c').card ≤ 3 := by
    intro c c' hne
    apply zeroAgreementTrace_pair_card_le_three dom u0 u1 7 c.2 c'.2
    exact fun h ↦ hne (Subtype.ext h)
  have hplotkin := constantWeight_plotkin_div S 7 3 hsize hpair (by
    rw [hU]
    norm_num)
  norm_num [hU] at hplotkin
  simpa [I] using hplotkin

open Classical in
theorem zeroAgreementStratum_eight_card_le_two_of_support_three
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 3) :
    (zeroAgreementStratum dom 4 9 u0 u1 8).card ≤ 2 := by
  let I := {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 8}
  let U := {i : Fin 16 // i ∈ directionZeroSet u1}
  let S : I → Finset U := fun c ↦ zeroAgreementTrace c.1 u0 u1
  have hU : Fintype.card U = 13 := by
    have hpartition := directionSupportSet_card_eq (n := 16) u1
    have hz : (directionZeroSet u1).card = 13 := by omega
    simpa [U] using hz
  have hsize : ∀ c : I, (S c).card = 8 := by
    intro c
    rw [zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp c.2).2
  have hpair : ∀ c c' : I, c ≠ c' → (S c ∩ S c').card ≤ 3 := by
    intro c c' hne
    apply zeroAgreementTrace_pair_card_le_three dom u0 u1 8 c.2 c'.2
    exact fun h ↦ hne (Subtype.ext h)
  have hplotkin := constantWeight_plotkin_div S 8 3 hsize hpair (by
    rw [hU]
    norm_num)
  norm_num [hU] at hplotkin
  simpa [I] using hplotkin

/-! ## Affine arrangement for the bottom stratum -/

/-- Degree-`<3` interpolation of a received row on the moving support. -/
noncomputable def supportInterpolant
    (dom : Fin 16 ↪ F) (u1 w : Fin 16 → F) : F[X] :=
  Lagrange.interpolate (directionSupportSet u1) dom w

theorem supportInterpolant_eval_of_mem_support
    (dom : Fin 16 ↪ F) (u1 w : Fin 16 → F)
    {i : Fin 16} (hi : i ∈ directionSupportSet u1) :
    (supportInterpolant dom u1 w).eval (dom i) = w i := by
  exact Lagrange.eval_interpolate_at_node w dom.injective.injOn hi

theorem natDegree_lt_of_degree_lt_of_pos
    {p : F[X]} {k : Nat} (hk : 0 < k) (hp : p.degree < k) :
    p.natDegree < k := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simpa using hk
  · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp

theorem supportInterpolant_natDegree_lt_three
    (dom : Fin 16 ↪ F) (u1 w : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 3) :
    (supportInterpolant dom u1 w).natDegree < 3 := by
  apply natDegree_lt_of_degree_lt_of_pos (by norm_num)
  have hdeg := Lagrange.degree_interpolate_lt
    (s := directionSupportSet u1) (v := dom) (r := w) dom.injective.injOn
  simpa only [hsupport] using hdeg

theorem exists_codePolynomial_of_mem_zeroAgreementStratum
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F) {t : Nat}
    {c : Fin 16 → F} (hc : c ∈ zeroAgreementStratum dom 4 9 u0 u1 t) :
    ∃ q : F[X], q.degree < 4 ∧ c = fun i ↦ q.eval (dom i) := by
  have hcApp : c ∈ lineAppearingCodewords dom 4 9 u0 u1 :=
    (Finset.mem_filter.mp hc).1
  rw [lineAppearingCodewords, Finset.mem_filter] at hcApp
  exact hcApp.2.1

/-- Canonical polynomial representative of a bottom-stratum codeword. -/
noncomputable def sixCodePolynomial
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (c : {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 6}) : F[X] :=
  Classical.choose (exists_codePolynomial_of_mem_zeroAgreementStratum
    dom u0 u1 c.2)

theorem sixCodePolynomial_degree_lt
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (c : {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 6}) :
    (sixCodePolynomial dom u0 u1 c).degree < 4 :=
  (Classical.choose_spec (exists_codePolynomial_of_mem_zeroAgreementStratum
    dom u0 u1 c.2)).1

theorem sixCodePolynomial_eval
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (c : {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 6})
    (i : Fin 16) :
    (sixCodePolynomial dom u0 u1 c).eval (dom i) = c.1 i := by
  have h := (Classical.choose_spec
    (exists_codePolynomial_of_mem_zeroAgreementStratum dom u0 u1 c.2)).2
  exact congrFun h.symm i

/-- A canonical scalar whose support-ratio fiber witnesses appearance. -/
noncomputable def sixScalar
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (c : {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 6}) : F :=
  Classical.choose
    (exists_supportRatioFiber_card_ge_sub_of_mem_lineAppearingCodewords
      dom 4 9 u0 u1 c.1 (Finset.mem_filter.mp c.2).1)

/-- In the bottom stratum, the heavy ratio fiber is the entire three-point
moving support. -/
theorem supportRatioFiber_sixScalar_eq_support
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 3)
    (c : {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 6}) :
    supportRatioFiber c.1 u0 u1 (sixScalar dom u0 u1 c) =
      directionSupportSet u1 := by
  have hzero : (directionZeroAgreementSet c.1 u0 u1).card = 6 :=
    (Finset.mem_filter.mp c.2).2
  have hlarge : 9 - (directionZeroAgreementSet c.1 u0 u1).card ≤
      (supportRatioFiber c.1 u0 u1 (sixScalar dom u0 u1 c)).card := by
    simpa only [sixScalar] using Classical.choose_spec
      (exists_supportRatioFiber_card_ge_sub_of_mem_lineAppearingCodewords
        dom 4 9 u0 u1 c.1 (Finset.mem_filter.mp c.2).1)
  have hsub : supportRatioFiber c.1 u0 u1 (sixScalar dom u0 u1 c) ⊆
      directionSupportSet u1 := by
    intro i hi
    exact (mem_supportRatioFiber c.1 u0 u1 (sixScalar dom u0 u1 c) i).mp hi |>.1
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hsupport]
  omega

/-- The cubic residual from the support interpolants. -/
noncomputable def sixResidual
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (c : {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 6}) : F[X] :=
  sixCodePolynomial dom u0 u1 c -
    (supportInterpolant dom u1 u0 +
      C (sixScalar dom u0 u1 c) * supportInterpolant dom u1 u1)

/-- The residual vanishes at all three moving coordinates. -/
theorem sixResidual_eval_eq_zero_of_mem_support
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 3)
    (c : {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 6})
    {i : Fin 16} (hi : i ∈ directionSupportSet u1) :
    (sixResidual dom u0 u1 c).eval (dom i) = 0 := by
  have hfiber : i ∈ supportRatioFiber c.1 u0 u1
      (sixScalar dom u0 u1 c) := by
    rw [supportRatioFiber_sixScalar_eq_support dom u0 u1 hsupport c]
    exact hi
  have hratio := (mem_supportRatioFiber c.1 u0 u1
    (sixScalar dom u0 u1 c) i).mp hfiber |>.2
  have hu1 : u1 i ≠ 0 := by
    simpa [directionSupportSet] using hi
  rw [div_eq_iff hu1] at hratio
  simp only [sixResidual, eval_sub, eval_add, eval_mul, eval_C,
    sixCodePolynomial_eval,
    supportInterpolant_eval_of_mem_support dom u1 u0 hi,
    supportInterpolant_eval_of_mem_support dom u1 u1 hi]
  linear_combination hratio

/-- The residual has degree at most three. -/
theorem sixResidual_natDegree_le_three
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 3)
    (c : {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 6}) :
    (sixResidual dom u0 u1 c).natDegree ≤ 3 := by
  have hq : (sixCodePolynomial dom u0 u1 c).natDegree < 4 :=
    natDegree_lt_of_degree_lt_of_pos (by norm_num)
      (sixCodePolynomial_degree_lt dom u0 u1 c)
  have hA := supportInterpolant_natDegree_lt_three dom u1 u0 hsupport
  have hR := supportInterpolant_natDegree_lt_three dom u1 u1 hsupport
  have hCR : (C (sixScalar dom u0 u1 c) *
      supportInterpolant dom u1 u1).natDegree ≤
      (supportInterpolant dom u1 u1).natDegree :=
    natDegree_C_mul_le _ _
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · omega
  · apply (natDegree_add_le _ _).trans
    exact max_le (by omega) (by omega)

/-- Exact common-locator factorization of every bottom-stratum residual. -/
theorem sixResidual_factorization
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 3)
    (c : {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 6}) :
    sixResidual dom u0 u1 c =
      C (sixResidual dom u0 u1 c).leadingCoeff *
        domainRootProduct dom (directionSupportSet u1) := by
  have hdvd : domainRootProduct dom (directionSupportSet u1) ∣
      sixResidual dom u0 u1 c :=
    domainRootProduct_dvd_of_eval_eq_zero dom (directionSupportSet u1)
      (sixResidual dom u0 u1 c)
      (fun i hi ↦ sixResidual_eval_eq_zero_of_mem_support
        dom u0 u1 hsupport c hi)
  apply eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    (domainRootProduct_monic dom (directionSupportSet u1)) hdvd
  rw [domainRootProduct_natDegree, hsupport]
  exact sixResidual_natDegree_le_three dom u0 u1 hsupport c

theorem eval_domainRootProduct_eq_zero_iff_mem
    {I : Type} [Fintype I] [DecidableEq I]
    (dom : I ↪ F) (S : Finset I) (i : I) :
    (domainRootProduct dom S).eval (dom i) = 0 ↔ i ∈ S := by
  rw [domainRootProduct, eval_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨j, hj, hzero⟩
    simp only [eval_sub, eval_X, eval_C] at hzero
    have hij : i = j := dom.injective (sub_eq_zero.mp hzero)
    exact hij ▸ hj
  · intro hi
    exact ⟨i, hi, by simp⟩

theorem domainRootProduct_eval_ne_zero_of_mem_directionZeroSet
    (dom : Fin 16 ↪ F) (u1 : Fin 16 → F)
    (i : {i : Fin 16 // i ∈ directionZeroSet u1}) :
    (domainRootProduct dom (directionSupportSet u1)).eval (dom i.1) ≠ 0 := by
  apply (eval_domainRootProduct_eq_zero_iff_mem
    dom (directionSupportSet u1) i.1).not.mpr
  have hzero : u1 i.1 = 0 := by
    simpa only [directionZeroSet, Finset.mem_filter, Finset.mem_univ,
      true_and] using i.2
  intro hi
  have hnonzero : u1 i.1 ≠ 0 := by
    simpa [directionSupportSet] using hi
  exact hnonzero hzero

/-- The affine coefficient function contributed by one zero coordinate. -/
noncomputable def zeroCoefficientFunction
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (i : {i : Fin 16 // i ∈ directionZeroSet u1}) : F → F :=
  fun gamma ↦
    (u0 i.1 - (supportInterpolant dom u1 u0).eval (dom i.1)) /
        (domainRootProduct dom (directionSupportSet u1)).eval (dom i.1) +
      gamma * (-(supportInterpolant dom u1 u1).eval (dom i.1) /
        (domainRootProduct dom (directionSupportSet u1)).eval (dom i.1))

/-- Parameter-coefficient point attached to a bottom-stratum codeword. -/
noncomputable def sixRichPoint
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (c : {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 6}) :
    F × F :=
  (sixScalar dom u0 u1 c, (sixResidual dom u0 u1 c).leadingCoeff)

/-- Every zero-agreement coordinate of a bottom-stratum codeword is incident
with its affine coefficient point. -/
theorem zeroAgreementTrace_subset_incidence_sixRichPoint
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 3)
    (c : {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 6}) :
    zeroAgreementTrace c.1 u0 u1 ⊆
      incidence (zeroCoefficientFunction dom u0 u1)
        (sixRichPoint dom u0 u1 c) := by
  intro i hi
  have hiData := Finset.mem_filter.mp hi
  have hcAgree : c.1 i.1 = u0 i.1 := hiData.2
  have hp0 := domainRootProduct_eval_ne_zero_of_mem_directionZeroSet dom u1 i
  have hfactor := congrArg (fun p : F[X] ↦ p.eval (dom i.1))
    (sixResidual_factorization dom u0 u1 hsupport c)
  simp only [sixResidual, eval_sub, eval_add, eval_mul, eval_C,
    sixCodePolynomial_eval] at hfactor
  rw [hcAgree] at hfactor
  rw [mem_incidence_iff]
  simp only [zeroCoefficientFunction, sixRichPoint]
  simp only [sixResidual]
  field_simp [hp0]
  linear_combination hfactor

theorem sixRichPoint_mem_richPoints
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 3)
    (c : {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 6}) :
    sixRichPoint dom u0 u1 c ∈
      richPoints (zeroCoefficientFunction dom u0 u1) 6 := by
  rw [richPoints, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hsub := zeroAgreementTrace_subset_incidence_sixRichPoint
    dom u0 u1 hsupport c
  have hcard := Finset.card_le_card hsub
  rw [zeroAgreementTrace_card] at hcard
  have hzero : (directionZeroAgreementSet c.1 u0 u1).card = 6 :=
    (Finset.mem_filter.mp c.2).2
  omega

/-- The parameter-coefficient point determines its bottom-stratum codeword. -/
theorem sixRichPoint_injective
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 3) :
    Function.Injective (sixRichPoint dom u0 u1) := by
  intro c d hpoint
  have hgamma : sixScalar dom u0 u1 c = sixScalar dom u0 u1 d :=
    congrArg Prod.fst hpoint
  have hcoeff : (sixResidual dom u0 u1 c).leadingCoeff =
      (sixResidual dom u0 u1 d).leadingCoeff := congrArg Prod.snd hpoint
  have hfactorC := sixResidual_factorization dom u0 u1 hsupport c
  have hfactorD := sixResidual_factorization dom u0 u1 hsupport d
  apply Subtype.ext
  funext i
  rw [← sixCodePolynomial_eval dom u0 u1 c i,
    ← sixCodePolynomial_eval dom u0 u1 d i]
  have hres : sixResidual dom u0 u1 c = sixResidual dom u0 u1 d := by
    rw [hfactorC, hfactorD, hcoeff]
  have hq : sixCodePolynomial dom u0 u1 c =
      sixCodePolynomial dom u0 u1 d := by
    have h := hres
    simp only [sixResidual] at h
    rw [hgamma] at h
    exact sub_left_injective h
  rw [hq]

/-- The cubic whose domain roots detect coordinates having the same slope as
the fixed zero coordinate `i`. -/
noncomputable def slopeCollisionPolynomial
    (dom : Fin 16 ↪ F) (u1 : Fin 16 → F)
    (i : {i : Fin 16 // i ∈ directionZeroSet u1}) : F[X] :=
  C ((domainRootProduct dom (directionSupportSet u1)).eval (dom i.1)) *
      supportInterpolant dom u1 u1 -
    C ((supportInterpolant dom u1 u1).eval (dom i.1)) *
      domainRootProduct dom (directionSupportSet u1)

theorem slopeCollisionPolynomial_natDegree_le_three
    (dom : Fin 16 ↪ F) (u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 3)
    (i : {i : Fin 16 // i ∈ directionZeroSet u1}) :
    (slopeCollisionPolynomial dom u1 i).natDegree ≤ 3 := by
  have hR := supportInterpolant_natDegree_lt_three dom u1 u1 hsupport
  have hP : (domainRootProduct dom (directionSupportSet u1)).natDegree = 3 := by
    rw [domainRootProduct_natDegree, hsupport]
  have hleft :
      (C ((domainRootProduct dom (directionSupportSet u1)).eval (dom i.1)) *
        supportInterpolant dom u1 u1).natDegree ≤
          (supportInterpolant dom u1 u1).natDegree :=
    natDegree_C_mul_le _ _
  have hright :
      (C ((supportInterpolant dom u1 u1).eval (dom i.1)) *
        domainRootProduct dom (directionSupportSet u1)).natDegree ≤
          (domainRootProduct dom (directionSupportSet u1)).natDegree :=
    natDegree_C_mul_le _ _
  apply (natDegree_sub_le _ _).trans
  exact max_le (by omega) (by omega)

/-- The slope-collision cubic is nonzero: at any moving coordinate, its
value is the product of two nonzero field elements. -/
theorem slopeCollisionPolynomial_ne_zero
    (dom : Fin 16 ↪ F) (u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 3)
    (i : {i : Fin 16 // i ∈ directionZeroSet u1}) :
    slopeCollisionPolynomial dom u1 i ≠ 0 := by
  have hnonempty : (directionSupportSet u1).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨s, hs⟩ := hnonempty
  have hPi := domainRootProduct_eval_ne_zero_of_mem_directionZeroSet dom u1 i
  have hPs :
      (domainRootProduct dom (directionSupportSet u1)).eval (dom s) = 0 :=
    (eval_domainRootProduct_eq_zero_iff_mem
      dom (directionSupportSet u1) s).mpr hs
  have hRs : (supportInterpolant dom u1 u1).eval (dom s) = u1 s :=
    supportInterpolant_eval_of_mem_support dom u1 u1 hs
  have hu1s : u1 s ≠ 0 := by
    simpa only [directionSupportSet, Finset.mem_filter, Finset.mem_univ,
      true_and] using hs
  intro hzero
  have heval := congrArg (fun p : F[X] ↦ p.eval (dom s)) hzero
  simp only [slopeCollisionPolynomial, eval_sub, eval_mul, eval_C,
    eval_zero] at heval
  rw [hPs, hRs] at heval
  simp only [mul_zero, sub_zero] at heval
  exact (mul_ne_zero hPi hu1s) heval

/-- Equal zero-coordinate functions give domain roots of the collision
polynomial. -/
theorem slopeCollisionPolynomial_eval_eq_zero_of_equal
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (i j : {i : Fin 16 // i ∈ directionZeroSet u1})
    (hfun : zeroCoefficientFunction dom u0 u1 j =
      zeroCoefficientFunction dom u0 u1 i) :
    (slopeCollisionPolynomial dom u1 i).eval (dom j.1) = 0 := by
  have hPi := domainRootProduct_eval_ne_zero_of_mem_directionZeroSet dom u1 i
  have hPj := domainRootProduct_eval_ne_zero_of_mem_directionZeroSet dom u1 j
  have hzero := congrFun hfun 0
  have hone := congrFun hfun 1
  simp only [zeroCoefficientFunction, zero_mul, add_zero] at hzero
  simp only [zeroCoefficientFunction, one_mul] at hone
  have hslope :
      -(supportInterpolant dom u1 u1).eval (dom j.1) /
          (domainRootProduct dom (directionSupportSet u1)).eval (dom j.1) =
        -(supportInterpolant dom u1 u1).eval (dom i.1) /
          (domainRootProduct dom (directionSupportSet u1)).eval (dom i.1) := by
    linear_combination hone - hzero
  field_simp [hPi, hPj] at hslope
  simp only [slopeCollisionPolynomial, eval_sub, eval_mul, eval_C]
  linear_combination -hslope

/-- At most three zero coordinates contribute the same affine coefficient
function. -/
theorem zeroCoefficientFunction_equalClass_card_le_three
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 3)
    (i : {i : Fin 16 // i ∈ directionZeroSet u1}) :
    (equalFunctionClass (zeroCoefficientFunction dom u0 u1) i).card ≤ 3 := by
  let U := {i : Fin 16 // i ∈ directionZeroSet u1}
  let e : U ↪ Fin 16 :=
    ⟨fun j ↦ j.1, fun _ _ h ↦ Subtype.ext h⟩
  let Q := slopeCollisionPolynomial dom u1 i
  have hQ0 : Q ≠ 0 := by
    simpa only [Q] using slopeCollisionPolynomial_ne_zero dom u1 hsupport i
  have hQdeg : Q.natDegree ≤ 3 := by
    simpa only [Q] using
      slopeCollisionPolynomial_natDegree_le_three dom u1 hsupport i
  have hsub :
      (equalFunctionClass (zeroCoefficientFunction dom u0 u1) i).map e ⊆
        domainRootSet dom Q := by
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    simp only [domainRootSet, Finset.mem_filter, Finset.mem_univ, true_and]
    apply slopeCollisionPolynomial_eval_eq_zero_of_equal dom u0 u1 i j
    exact (mem_equalFunctionClass_iff
      (zeroCoefficientFunction dom u0 u1) i j).mp hj
  have hroots : (domainRootSet dom Q).card ≤ Q.natDegree := by
    simpa only [domainRootSet] using
      ArkLib.CS25.card_domain_roots_le dom Q hQ0
  calc
    (equalFunctionClass (zeroCoefficientFunction dom u0 u1) i).card =
        ((equalFunctionClass
          (zeroCoefficientFunction dom u0 u1) i).map e).card := by
      rw [Finset.card_map]
    _ ≤ (domainRootSet dom Q).card := Finset.card_le_card hsub
    _ ≤ Q.natDegree := hroots
    _ ≤ 3 := hQdeg

/-- Two genuinely different zero-coordinate affine functions cross at only
one parameter value. -/
theorem zeroCoefficientFunction_crossing_unique
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (i j : {i : Fin 16 // i ∈ directionZeroSet u1})
    (hfun : zeroCoefficientFunction dom u0 u1 i ≠
      zeroCoefficientFunction dom u0 u1 j)
    (gamma beta : F)
    (hgamma : zeroCoefficientFunction dom u0 u1 i gamma =
      zeroCoefficientFunction dom u0 u1 j gamma)
    (hbeta : zeroCoefficientFunction dom u0 u1 i beta =
      zeroCoefficientFunction dom u0 u1 j beta) :
    gamma = beta := by
  let ai :=
    (u0 i.1 - (supportInterpolant dom u1 u0).eval (dom i.1)) /
      (domainRootProduct dom (directionSupportSet u1)).eval (dom i.1)
  let bi :=
    -(supportInterpolant dom u1 u1).eval (dom i.1) /
      (domainRootProduct dom (directionSupportSet u1)).eval (dom i.1)
  let aj :=
    (u0 j.1 - (supportInterpolant dom u1 u0).eval (dom j.1)) /
      (domainRootProduct dom (directionSupportSet u1)).eval (dom j.1)
  let bj :=
    -(supportInterpolant dom u1 u1).eval (dom j.1) /
      (domainRootProduct dom (directionSupportSet u1)).eval (dom j.1)
  change ai + gamma * bi = aj + gamma * bj at hgamma
  change ai + beta * bi = aj + beta * bj at hbeta
  by_contra hne
  have hprod : (gamma - beta) * (bi - bj) = 0 := by
    linear_combination hgamma - hbeta
  have hslope : bi = bj := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)
  have hintercept : ai = aj := by
    rw [hslope] at hgamma
    linear_combination hgamma
  apply hfun
  funext x
  change ai + x * bi = aj + x * bj
  rw [hintercept, hslope]

open Classical in
/-- The affine-arrangement packing bound for the bottom stratum. -/
theorem zeroAgreementStratum_six_card_le_eight_of_support_three
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 3) :
    (zeroAgreementStratum dom 4 9 u0 u1 6).card ≤ 8 := by
  let U := {i : Fin 16 // i ∈ directionZeroSet u1}
  let phi : U → F → F := zeroCoefficientFunction dom u0 u1
  have hU : Fintype.card U = 13 := by
    have hpartition := directionSupportSet_card_eq (n := 16) u1
    have hz : (directionZeroSet u1).card = 13 := by omega
    simpa [U] using hz
  have heqClass : ∀ i : U, (equalFunctionClass phi i).card ≤ 3 := by
    intro i
    exact zeroCoefficientFunction_equalClass_card_le_three
      dom u0 u1 hsupport i
  have hcross : ∀ i j : U, phi i ≠ phi j →
      ∀ gamma beta, phi i gamma = phi j gamma →
        phi i beta = phi j beta → gamma = beta := by
    intro i j hij gamma beta hgamma hbeta
    exact zeroCoefficientFunction_crossing_unique
      dom u0 u1 i j hij gamma beta hgamma hbeta
  have hrich := richPoints_six_card_le_eight phi hU heqClass hcross
  let C6 := zeroAgreementStratum dom 4 9 u0 u1 6
  let f : {c : Fin 16 → F // c ∈ C6} →
      {p : F × F // p ∈ richPoints phi 6} := fun c ↦
    ⟨sixRichPoint dom u0 u1 c,
      sixRichPoint_mem_richPoints dom u0 u1 hsupport c⟩
  have hf : Function.Injective f := by
    intro c d hcd
    apply sixRichPoint_injective dom u0 u1 hsupport
    exact congrArg Subtype.val hcd
  have hcard := Fintype.card_le_of_injective f hf
  have hle : C6.card ≤ (richPoints phi 6).card := by
    simpa only [Fintype.card_coe] using hcard
  change C6.card ≤ 8
  exact hle.trans hrich

/-! ## The two-top-trace reduction -/

/-- Two size-eight subsets of a thirteen-point universe with intersection at
most three have intersection exactly three and cover the universe. -/
theorem two_eight_sets_cover_thirteen
    {U : Type} [Fintype U] [DecidableEq U]
    (hU : Fintype.card U = 13) (A B : Finset U)
    (hA : A.card = 8) (hB : B.card = 8)
    (hinter : (A ∩ B).card ≤ 3) :
    (A ∩ B).card = 3 ∧ A ∪ B = Finset.univ := by
  have hbook := Finset.card_union_add_card_inter A B
  have hunion : (A ∪ B).card ≤ 13 := by
    simpa [hU] using Finset.card_le_univ (A ∪ B)
  have hinterEq : (A ∩ B).card = 3 := by omega
  have hunionEq : (A ∪ B).card = 13 := by omega
  refine ⟨hinterEq, ?_⟩
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simp [hU, hunionEq]

/-- A size-six trace meeting each member of a covering `(8,8,3)` pair in at
most three points avoids the common triple. -/
theorem six_set_avoids_common_three
    {U : Type} [Fintype U] [DecidableEq U]
    (T A B : Finset U) (hT : T.card = 6)
    (hcover : A ∪ B = Finset.univ)
    (hTA : (T ∩ A).card ≤ 3) (hTB : (T ∩ B).card ≤ 3) :
    T ⊆ Finset.univ \ (A ∩ B) := by
  have hunion : (T ∩ A) ∪ (T ∩ B) = T := by
    ext i
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨hiT, _⟩ | ⟨hiT, _⟩) <;> exact hiT
    · intro hiT
      have hiAB : i ∈ A ∨ i ∈ B := by
        have : i ∈ A ∪ B := by rw [hcover]; exact Finset.mem_univ i
        exact Finset.mem_union.mp this
      exact hiAB.elim (fun hi ↦ Or.inl ⟨hiT, hi⟩)
        (fun hi ↦ Or.inr ⟨hiT, hi⟩)
  have hinterEq : (T ∩ A) ∩ (T ∩ B) = T ∩ (A ∩ B) := by
    ext i
    simp only [Finset.mem_inter]
    tauto
  have hbook := Finset.card_union_add_card_inter (T ∩ A) (T ∩ B)
  rw [hunion, hinterEq, hT] at hbook
  have hempty : (T ∩ (A ∩ B)).card = 0 := by omega
  intro i hiT
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hiAB
  have hi : i ∈ T ∩ (A ∩ B) := Finset.mem_inter.mpr ⟨hiT, hiAB⟩
  rw [Finset.card_eq_zero.mp hempty] at hi
  simp at hi

/-- Restrict a finset to the subtype carried by a containing ambient finset. -/
noncomputable def restrictToFinsetSubtype
    {U : Type} [DecidableEq U] (W T : Finset U) :
    Finset {x : U // x ∈ W} :=
  (Finset.univ : Finset {x : U // x ∈ W}).filter fun x ↦ x.1 ∈ T

theorem restrictToFinsetSubtype_card
    {U : Type} [Fintype U] [DecidableEq U]
    (W T : Finset U) (hsub : T ⊆ W) :
    (restrictToFinsetSubtype W T).card = T.card := by
  let e : {x : U // x ∈ W} ↪ U :=
    ⟨fun x ↦ x.1, fun _ _ h ↦ Subtype.ext h⟩
  have hmap : (restrictToFinsetSubtype W T).map e = T := by
    ext x
    simp only [restrictToFinsetSubtype, Finset.mem_map,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨y, hyT, rfl⟩
      exact hyT
    · intro hxT
      exact ⟨⟨x, hsub hxT⟩, hxT, rfl⟩
  calc
    (restrictToFinsetSubtype W T).card =
        ((restrictToFinsetSubtype W T).map e).card := by rw [Finset.card_map]
    _ = T.card := congrArg Finset.card hmap

theorem restrictToFinsetSubtype_inter
    {U : Type} [Fintype U] [DecidableEq U]
    (W A B : Finset U) :
    restrictToFinsetSubtype W (A ∩ B) =
      restrictToFinsetSubtype W A ∩ restrictToFinsetSubtype W B := by
  ext x
  simp [restrictToFinsetSubtype]

open Classical in
/-- If the top stratum has two codewords, all size-six traces lie off their
common triple, and Plotkin on the resulting ten-point universe gives five. -/
theorem zeroAgreementStratum_six_card_le_five_of_two_top
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 3)
    (htop : 2 ≤ (zeroAgreementStratum dom 4 9 u0 u1 8).card) :
    (zeroAgreementStratum dom 4 9 u0 u1 6).card ≤ 5 := by
  let C6 := zeroAgreementStratum dom 4 9 u0 u1 6
  let C8 := zeroAgreementStratum dom 4 9 u0 u1 8
  let U := {i : Fin 16 // i ∈ directionZeroSet u1}
  have hU : Fintype.card U = 13 := by
    have hpartition := directionSupportSet_card_eq (n := 16) u1
    have hz : (directionZeroSet u1).card = 13 := by omega
    simpa [U] using hz
  have htopCap := zeroAgreementStratum_eight_card_le_two_of_support_three
    dom u0 u1 hsupport
  have hC8card : C8.card = 2 := by
    change C8.card ≤ 2 at htopCap
    change 2 ≤ C8.card at htop
    omega
  obtain ⟨c, c', hcc', hC8eq⟩ := Finset.card_eq_two.mp hC8card
  have hc : c ∈ C8 := by rw [hC8eq]; simp
  have hc' : c' ∈ C8 := by rw [hC8eq]; simp
  let A := zeroAgreementTrace c u0 u1
  let B := zeroAgreementTrace c' u0 u1
  have hA : A.card = 8 := by
    calc
      A.card = (directionZeroAgreementSet c u0 u1).card := by
        simpa only [A] using zeroAgreementTrace_card c u0 u1
      _ = 8 := (Finset.mem_filter.mp hc).2
  have hB : B.card = 8 := by
    calc
      B.card = (directionZeroAgreementSet c' u0 u1).card := by
        simpa only [B] using zeroAgreementTrace_card c' u0 u1
      _ = 8 := (Finset.mem_filter.mp hc').2
  have hAB : (A ∩ B).card ≤ 3 := by
    exact zeroAgreementTrace_pair_card_le_three dom u0 u1 8 hc hc' hcc'
  obtain ⟨hKcard, hcover⟩ := two_eight_sets_cover_thirteen hU A B hA hB hAB
  let K := A ∩ B
  let W : Finset U := Finset.univ \ K
  have hWcard : W.card = 10 := by
    have hK : K.card = 3 := by simpa only [K] using hKcard
    dsimp only [W]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ K),
      Finset.card_univ, hU, hK]
  have htraceSub : ∀ d ∈ C6, zeroAgreementTrace d u0 u1 ⊆ W := by
    intro d hd
    have hDcard : (zeroAgreementTrace d u0 u1).card = 6 := by
      rw [zeroAgreementTrace_card]
      exact (Finset.mem_filter.mp hd).2
    have hdApp : d ∈ lineAppearingCodewords dom 4 9 u0 u1 :=
      (Finset.mem_filter.mp hd).1
    have hcApp : c ∈ lineAppearingCodewords dom 4 9 u0 u1 :=
      (Finset.mem_filter.mp hc).1
    have hc'App : c' ∈ lineAppearingCodewords dom 4 9 u0 u1 :=
      (Finset.mem_filter.mp hc').1
    have hdc : d ≠ c := by
      intro heq
      subst d
      have h6 := (Finset.mem_filter.mp hd).2
      have h8 := (Finset.mem_filter.mp hc).2
      omega
    have hdc' : d ≠ c' := by
      intro heq
      subst d
      have h6 := (Finset.mem_filter.mp hd).2
      have h8 := (Finset.mem_filter.mp hc').2
      omega
    have hDA := zeroAgreementTrace_pair_card_le_three_of_appearing
      dom u0 u1 hdApp hcApp hdc
    have hDB := zeroAgreementTrace_pair_card_le_three_of_appearing
      dom u0 u1 hdApp hc'App hdc'
    exact six_set_avoids_common_three
      (zeroAgreementTrace d u0 u1) A B hDcard hcover hDA hDB
  let J := {d : Fin 16 → F // d ∈ C6}
  let S : J → Finset {x : U // x ∈ W} := fun d ↦
    restrictToFinsetSubtype W (zeroAgreementTrace d.1 u0 u1)
  have hsize : ∀ d : J, (S d).card = 6 := by
    intro d
    change (restrictToFinsetSubtype W
      (zeroAgreementTrace d.1 u0 u1)).card = 6
    rw [restrictToFinsetSubtype_card W _ (htraceSub d.1 d.2),
      zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp d.2).2
  have hpair : ∀ d e : J, d ≠ e → (S d ∩ S e).card ≤ 3 := by
    intro d e hde
    change (restrictToFinsetSubtype W (zeroAgreementTrace d.1 u0 u1) ∩
      restrictToFinsetSubtype W (zeroAgreementTrace e.1 u0 u1)).card ≤ 3
    rw [← restrictToFinsetSubtype_inter,
      restrictToFinsetSubtype_card]
    · exact zeroAgreementTrace_pair_card_le_three dom u0 u1 6 d.2 e.2
        (fun h ↦ hde (Subtype.ext h))
    · exact fun x hx ↦ htraceSub d.1 d.2 (Finset.mem_inter.mp hx).1
  have hUW : Fintype.card {x : U // x ∈ W} = 10 := by
    simpa using hWcard
  have hplotkin := constantWeight_plotkin_div S 6 3 hsize hpair (by
    rw [hUW]
    norm_num)
  norm_num [hUW] at hplotkin
  simpa [J, C6] using hplotkin

open Classical in
/-- A zero-safe `RS[16,4]` line whose direction has support three has at most
sixteen bad scalars. -/
theorem lineBadScalars_card_le_sixteen_of_support_three
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsafe : ZeroDirectionSafeLine dom 4 9 u0 u1)
    (hsupport : (directionSupportSet u1).card = 3) :
    (lineBadScalars dom 4 9 u0 u1).card ≤ 16 := by
  apply (lineBadScalars_card_le_puncturedZeroStratifiedLineWeight
    dom 4 9 u0 u1 hsafe).trans
  rw [puncturedZeroStratifiedLineWeight_eq_sum_zeroAgreementStrata
    dom 4 9 u0 u1 hsafe]
  have hempty : ∀ t, t < 6 →
      zeroAgreementStratum dom 4 9 u0 u1 t = ∅ := by
    intro t ht
    apply zeroAgreementStratum_eq_empty_of_add_support_lt
      dom 4 9 u0 u1
    omega
  have hsix := zeroAgreementStratum_six_card_le_eight_of_support_three
    dom u0 u1 hsupport
  have hseven := zeroAgreementStratum_seven_card_le_five_of_support_three
    dom u0 u1 hsupport
  have height := zeroAgreementStratum_eight_card_le_two_of_support_three
    dom u0 u1 hsupport
  have hweight :
      (∑ t ∈ Finset.range 9,
        (zeroAgreementStratum dom 4 9 u0 u1 t).card *
          ((directionSupportSet u1).card / (9 - t))) =
        (zeroAgreementStratum dom 4 9 u0 u1 6).card +
          (zeroAgreementStratum dom 4 9 u0 u1 7).card +
          (zeroAgreementStratum dom 4 9 u0 u1 8).card * 3 := by
    norm_num [Finset.sum_range_succ, hempty, hsupport]
  rw [hweight]
  by_cases htop :
      (zeroAgreementStratum dom 4 9 u0 u1 8).card ≤ 1
  · omega
  · have htwo :
        2 ≤ (zeroAgreementStratum dom 4 9 u0 u1 8).card := by omega
    have hsixFive := zeroAgreementStratum_six_card_le_five_of_two_top
      dom u0 u1 hsupport htwo
    omega

#print axioms zeroAgreementStratum_seven_card_le_five_of_support_three
#print axioms zeroAgreementStratum_eight_card_le_two_of_support_three
#print axioms zeroAgreementStratum_six_card_le_eight_of_support_three
#print axioms zeroAgreementStratum_six_card_le_five_of_two_top
#print axioms lineBadScalars_card_le_sixteen_of_support_three

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportThreeSafeLine
