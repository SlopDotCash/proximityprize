/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterOverlapThreeRigidity

/-!
# Rate-quarter half predecessor: overlap-three factorization

Saturation of the degree-`<k` root cap has an exact algebraic consequence.  A
nonzero polynomial of degree `<k` with `k-1` distinct evaluation-domain roots
has degree exactly `k-1` and is its leading coefficient times the monic
locator of those roots.

Applied to the two off-line residuals in the overlap-three configuration, this
factors both residuals through their two saturated root blocks.  Subtracting
the factorizations gives the two-block reconciliation identity

```text
c1 * P_S1 - c2 * P_S2
  = (a2 - a1) + gamma * (r2 - r1).
```
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeRigidity

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeFactorization

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- The monic locator of a finite set of evaluation-domain coordinates. -/
noncomputable def domainRootProduct (dom : I ↪ F) (S : Finset I) : F[X] :=
  ∏ i ∈ S, (X - C (dom i))

/-- The evaluation-domain root set of a polynomial. -/
def domainRootSet (dom : I ↪ F) (p : F[X]) : Finset I :=
  Finset.univ.filter fun i => p.eval (dom i) = 0

theorem domainRootProduct_monic (dom : I ↪ F) (S : Finset I) :
    (domainRootProduct dom S).Monic := by
  exact monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (dom i)

theorem domainRootProduct_natDegree (dom : I ↪ F) (S : Finset I) :
    (domainRootProduct dom S).natDegree = S.card := by
  rw [domainRootProduct,
    natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C (dom i)]
  simp

/-- A polynomial vanishing at every coordinate in `S` is divisible by the
monic locator of `S`.  Injectivity of `dom` makes the linear factors pairwise
coprime. -/
theorem domainRootProduct_dvd_of_eval_eq_zero
    (dom : I ↪ F) (S : Finset I) (p : F[X])
    (hroot : ∀ i ∈ S, p.eval (dom i) = 0) :
    domainRootProduct dom S ∣ p := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [domainRootProduct]
  | @insert a S ha ih =>
      rw [domainRootProduct, Finset.prod_insert ha]
      have hA : X - C (dom a) ∣ p :=
        dvd_iff_isRoot.mpr (hroot a (Finset.mem_insert_self a S))
      have hS : (∏ i ∈ S, (X - C (dom i))) ∣ p := by
        have hrec := ih fun i hi => hroot i (Finset.mem_insert_of_mem hi)
        simpa only [domainRootProduct] using hrec
      refine IsCoprime.mul_dvd ?_ hA hS
      refine IsCoprime.prod_right fun i hi => ?_
      apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      have hne : dom a ≠ dom i := by
        intro heq
        exact ha ((dom.injective heq) ▸ hi)
      exact (sub_ne_zero.mpr hne).isUnit

/-- **Saturated root-set factorization.**  A nonzero degree-`<k`
polynomial with `k-1` distinct evaluation-domain roots has degree exactly
`k-1` and equals its leading coefficient times their monic locator. -/
theorem factorization_of_domain_root_subset_card_eq_pred
    (dom : I ↪ F) {k : Nat} (hk : 1 ≤ k) (p : F[X])
    (hp0 : p ≠ 0) (hpdeg : p.natDegree < k)
    (S : Finset I) (hScard : S.card = k - 1)
    (hroot : ∀ i ∈ S, p.eval (dom i) = 0) :
    p.natDegree = k - 1 ∧ p.leadingCoeff ≠ 0 ∧
      p = C p.leadingCoeff * domainRootProduct dom S := by
  have hsub : S ⊆ domainRootSet dom p := by
    intro i hi
    simp only [domainRootSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hroot i hi
  have hrootCount : S.card ≤ p.natDegree :=
    (Finset.card_le_card hsub).trans
      (ArkLib.CS25.card_domain_roots_le dom p hp0)
  have hpdegEq : p.natDegree = k - 1 := by omega
  have hlocatorDeg : (domainRootProduct dom S).natDegree = k - 1 := by
    rw [domainRootProduct_natDegree, hScard]
  have hdvd : domainRootProduct dom S ∣ p :=
    domainRootProduct_dvd_of_eval_eq_zero dom S p hroot
  have hfactor : p = C p.leadingCoeff * domainRootProduct dom S :=
    eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
      (domainRootProduct_monic dom S) hdvd (by omega)
  exact ⟨hpdegEq, leadingCoeff_ne_zero.mpr hp0, hfactor⟩

/-- Canonical form using the entire evaluation-domain root set. -/
theorem factorization_of_domain_root_set_card_eq_pred
    (dom : I ↪ F) {k : Nat} (hk : 1 ≤ k) (p : F[X])
    (hp0 : p ≠ 0) (hpdeg : p.natDegree < k)
    (hcard : (domainRootSet dom p).card = k - 1) :
    p.natDegree = k - 1 ∧ p.leadingCoeff ≠ 0 ∧
      p = C p.leadingCoeff *
        domainRootProduct dom (domainRootSet dom p) := by
  apply factorization_of_domain_root_subset_card_eq_pred
    dom hk p hp0 hpdeg (domainRootSet dom p) hcard
  intro i hi
  simpa only [domainRootSet, Finset.mem_filter, Finset.mem_univ, true_and] using hi

/-! ## The overlap-three specialization -/

/-- The residual polynomial from a decoded line to a selected lifted point. -/
noncomputable def lineResidual
    (q : F[X]) (gamma : F) (line : F[X] × F[X]) : F[X] :=
  q - (line.1 + C gamma * line.2)

/-- The root block supplied by simultaneous agreement with the received word
and membership in a decoded line's joint core. -/
def overlapRootBlock (dom : I ↪ F) (u0 u1 : I → F)
    (gamma : F) (q : F[X]) (line : F[X] × F[X]) : Finset I :=
  fullAgreement dom u0 u1 gamma q ∩
    jointCore dom u0 u1 line.1 line.2

theorem lineResidual_natDegree_lt
    {k : Nat} {q : F[X]} {gamma : F} {line : F[X] × F[X]}
    (hqdeg : q.natDegree < k) (hadeg : line.1.natDegree < k)
    (hrdeg : line.2.natDegree < k) :
    (lineResidual q gamma line).natDegree < k := by
  have hCr : (C gamma * line.2).natDegree ≤ line.2.natDegree :=
    natDegree_C_mul_le gamma line.2
  have hlineDeg : (line.1 + C gamma * line.2).natDegree < k :=
    lt_of_le_of_lt (natDegree_add_le _ _)
      (max_lt hadeg (lt_of_le_of_lt hCr hrdeg))
  exact lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hqdeg hlineDeg)

theorem lineResidual_eval_eq_zero_of_mem_overlapRootBlock
    (dom : I ↪ F) (u0 u1 : I → F)
    (gamma : F) (q : F[X]) (line : F[X] × F[X])
    {i : I} (hi : i ∈ overlapRootBlock dom u0 u1 gamma q line) :
    (lineResidual q gamma line).eval (dom i) = 0 := by
  simp only [overlapRootBlock, Finset.mem_inter, fullAgreement,
    jointCore, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp only [lineResidual, eval_sub, eval_add, eval_mul, eval_C]
  rw [hi.1, hi.2.1, hi.2.2]
  ring

/-- Subtracting the two residuals cancels the selected polynomial and leaves
the affine difference of the two decoded lines. -/
theorem lineResidual_sub_lineResidual
    (q : F[X]) (gamma : F) (line1 line2 : F[X] × F[X]) :
    lineResidual q gamma line1 - lineResidual q gamma line2 =
      (line2.1 - line1.1) + C gamma * (line2.2 - line1.2) := by
  simp only [lineResidual]
  ring

/-- **Two saturated residual factorizations.**  In the overlap-three equality
case, each off-line residual has degree exactly `k-1` and is a nonzero scalar
multiple of the locator of its corresponding root block. -/
theorem overlap_three_residual_factorizations
    {dom : I ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h)
    (hsaturated : h = 2 * k)
    (hthreshold : h + 1 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = h)
    (hcore2 :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = h)
    (hinter :
      (jointCore dom (u 0) (u 1) line1.1 line1.2 ∩
        jointCore dom (u 0) (u 1) line2.1 line2.2).card = 3)
    {gamma : F} (hgamma : gamma ∈ family.G)
    (hoff1 : family.q gamma ≠ line1.1 + C gamma * line1.2)
    (hoff2 : family.q gamma ≠ line2.1 + C gamma * line2.2) :
    ∃ c1 c2 : F,
      c1 ≠ 0 ∧ c2 ≠ 0 ∧
      (lineResidual (family.q gamma) gamma line1).natDegree = k - 1 ∧
      (lineResidual (family.q gamma) gamma line2).natDegree = k - 1 ∧
      lineResidual (family.q gamma) gamma line1 =
        C c1 * domainRootProduct dom
          (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line1) ∧
      lineResidual (family.q gamma) gamma line2 =
        C c2 * domainRootProduct dom
          (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line2) := by
  have hrigid := fullAgreement_overlap_three_rigidity
    family hk hn hsaturated hthreshold line1 line2 hline1 hline2
      hcore1 hcore2 hinter hgamma hoff1 hoff2
  have hdegq := family.degree_lt gamma hgamma
  have hdeg1 := lineParameter_degree_lt family hline1
  have hdeg2 := lineParameter_degree_lt family hline2
  let p1 := lineResidual (family.q gamma) gamma line1
  let p2 := lineResidual (family.q gamma) gamma line2
  let S1 := overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line1
  let S2 := overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line2
  have hp10 : p1 ≠ 0 := by
    simpa only [p1, lineResidual, sub_ne_zero] using hoff1
  have hp20 : p2 ≠ 0 := by
    simpa only [p2, lineResidual, sub_ne_zero] using hoff2
  have hp1deg : p1.natDegree < k := by
    exact lineResidual_natDegree_lt hdegq hdeg1.1 hdeg1.2
  have hp2deg : p2.natDegree < k := by
    exact lineResidual_natDegree_lt hdegq hdeg2.1 hdeg2.2
  have hS1card : S1.card = k - 1 := by
    simpa only [S1, overlapRootBlock] using hrigid.first_root_cap
  have hS2card : S2.card = k - 1 := by
    simpa only [S2, overlapRootBlock] using hrigid.second_root_cap
  have hroot1 : ∀ i ∈ S1, p1.eval (dom i) = 0 := by
    intro i hi
    exact lineResidual_eval_eq_zero_of_mem_overlapRootBlock
      dom (u 0) (u 1) gamma (family.q gamma) line1 hi
  have hroot2 : ∀ i ∈ S2, p2.eval (dom i) = 0 := by
    intro i hi
    exact lineResidual_eval_eq_zero_of_mem_overlapRootBlock
      dom (u 0) (u 1) gamma (family.q gamma) line2 hi
  have hfactor1 := factorization_of_domain_root_subset_card_eq_pred
    dom hk p1 hp10 hp1deg S1 hS1card hroot1
  have hfactor2 := factorization_of_domain_root_subset_card_eq_pred
    dom hk p2 hp20 hp2deg S2 hS2card hroot2
  refine ⟨p1.leadingCoeff, p2.leadingCoeff,
    hfactor1.2.1, hfactor2.2.1, hfactor1.1, hfactor2.1, ?_, ?_⟩
  · simpa only [p1, S1] using hfactor1.2.2
  · simpa only [p2, S2] using hfactor2.2.2

/-- **Two-block reconciliation identity.**  The two saturated root locators
reconstruct the affine difference between the decoded lines. -/
theorem overlap_three_two_block_reconciliation
    {dom : I ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h)
    (hsaturated : h = 2 * k)
    (hthreshold : h + 1 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = h)
    (hcore2 :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = h)
    (hinter :
      (jointCore dom (u 0) (u 1) line1.1 line1.2 ∩
        jointCore dom (u 0) (u 1) line2.1 line2.2).card = 3)
    {gamma : F} (hgamma : gamma ∈ family.G)
    (hoff1 : family.q gamma ≠ line1.1 + C gamma * line1.2)
    (hoff2 : family.q gamma ≠ line2.1 + C gamma * line2.2) :
    ∃ c1 c2 : F, c1 ≠ 0 ∧ c2 ≠ 0 ∧
      C c1 * domainRootProduct dom
          (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line1) -
        C c2 * domainRootProduct dom
          (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line2) =
        (line2.1 - line1.1) + C gamma * (line2.2 - line1.2) := by
  obtain ⟨c1, c2, hc1, hc2, _hp1deg, _hp2deg, hfactor1, hfactor2⟩ :=
    overlap_three_residual_factorizations
      family hk hn hsaturated hthreshold line1 line2 hline1 hline2
        hcore1 hcore2 hinter hgamma hoff1 hoff2
  refine ⟨c1, c2, hc1, hc2, ?_⟩
  rw [← hfactor1, ← hfactor2]
  exact lineResidual_sub_lineResidual (family.q gamma) gamma line1 line2

#print axioms factorization_of_domain_root_set_card_eq_pred
#print axioms overlap_three_residual_factorizations
#print axioms overlap_three_two_block_reconciliation

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeFactorization
