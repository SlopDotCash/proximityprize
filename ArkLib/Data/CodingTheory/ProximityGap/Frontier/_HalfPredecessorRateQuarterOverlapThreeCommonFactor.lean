/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterOverlapThreeFactorization

/-!
# Rate-quarter half predecessor: the common cubic factor

The three coordinates common to two decoded-line cores are simultaneous roots
of both decoded-line differences.  Their monic locator therefore divides both
the intercept difference and the slope difference.  When `4 <= k`, removing
this cubic locator drops both quotient degrees below `k-3`.

Combining these two factorizations with the overlap-three reconciliation
identity exposes an exact recursive form: the difference of the two saturated
`(k-1)`-root locators is the common cubic locator times a degree-`<k-3`
affine polynomial pencil.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeFactorization

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeCommonFactor

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- The common coordinate block of two decoded polynomial lines. -/
def commonCoreBlock (dom : I ↪ F) (u0 u1 : I → F)
    (line1 line2 : F[X] × F[X]) : Finset I :=
  jointCore dom u0 u1 line1.1 line1.2 ∩
    jointCore dom u0 u1 line2.1 line2.2

/-- **Three-root quotient degree drop.**  A degree-`<k` polynomial vanishing
on three distinct evaluation coordinates factors through their monic cubic
locator, with quotient degree `< k-3`.  The `4 <= k` assumption is also needed
for the zero-polynomial branch, whose `natDegree` is conventionally zero. -/
theorem exists_quotient_natDegree_lt_sub_three_of_three_roots
    (dom : I ↪ F) {k : Nat} (hk : 4 ≤ k) (p : F[X])
    (hpdeg : p.natDegree < k) (T : Finset I) (hTcard : T.card = 3)
    (hroot : ∀ i ∈ T, p.eval (dom i) = 0) :
    ∃ q : F[X],
      p = domainRootProduct dom T * q ∧ q.natDegree < k - 3 := by
  have hdvd : domainRootProduct dom T ∣ p :=
    domainRootProduct_dvd_of_eval_eq_zero dom T p hroot
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨q, hq, ?_⟩
  by_cases hq0 : q = 0
  · rw [hq0, natDegree_zero]
    omega
  · have hlocator0 : domainRootProduct dom T ≠ 0 :=
      (domainRootProduct_monic dom T).ne_zero
    have hlocatorDeg : (domainRootProduct dom T).natDegree = 3 := by
      rw [domainRootProduct_natDegree, hTcard]
    have hprodDeg :
        (domainRootProduct dom T * q).natDegree =
          (domainRootProduct dom T).natDegree + q.natDegree :=
      natDegree_mul hlocator0 hq0
    have hprodLt : (domainRootProduct dom T * q).natDegree < k := by
      rw [← hq]
      exact hpdeg
    omega

/-- Both decoded-line differences vanish on the common core. -/
theorem decoded_line_difference_eval_eq_zero_on_commonCore
    (dom : I ↪ F) (u0 u1 : I → F)
    (line1 line2 : F[X] × F[X]) {i : I}
    (hi : i ∈ commonCoreBlock dom u0 u1 line1 line2) :
    (line2.1 - line1.1).eval (dom i) = 0 ∧
      (line2.2 - line1.2).eval (dom i) = 0 := by
  simp only [commonCoreBlock, Finset.mem_inter, jointCore,
    Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp only [eval_sub]
  constructor
  · rw [hi.2.1, hi.1.1, sub_self]
  · rw [hi.2.2, hi.1.2, sub_self]

/-- **Decoded-line common cubic factor.**  If two relevant decoded lines have
a three-coordinate common core, their intercept and slope differences share
the monic locator of that core.  Both quotient polynomials have degree
strictly below `k-3`. -/
theorem decoded_line_differences_factor_through_commonCore
    {dom : I ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 4 ≤ k) (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hinter : (commonCoreBlock dom (u 0) (u 1) line1 line2).card = 3) :
    ∃ qa qr : F[X],
      line2.1 - line1.1 =
        domainRootProduct dom
          (commonCoreBlock dom (u 0) (u 1) line1 line2) * qa ∧
      line2.2 - line1.2 =
        domainRootProduct dom
          (commonCoreBlock dom (u 0) (u 1) line1 line2) * qr ∧
      qa.natDegree < k - 3 ∧ qr.natDegree < k - 3 := by
  have hdeg1 := lineParameter_degree_lt family hline1
  have hdeg2 := lineParameter_degree_lt family hline2
  have haDeg : (line2.1 - line1.1).natDegree < k :=
    lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hdeg2.1 hdeg1.1)
  have hrDeg : (line2.2 - line1.2).natDegree < k :=
    lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hdeg2.2 hdeg1.2)
  have hrootA : ∀ i ∈ commonCoreBlock dom (u 0) (u 1) line1 line2,
      (line2.1 - line1.1).eval (dom i) = 0 := by
    intro i hi
    exact (decoded_line_difference_eval_eq_zero_on_commonCore
      dom (u 0) (u 1) line1 line2 hi).1
  have hrootR : ∀ i ∈ commonCoreBlock dom (u 0) (u 1) line1 line2,
      (line2.2 - line1.2).eval (dom i) = 0 := by
    intro i hi
    exact (decoded_line_difference_eval_eq_zero_on_commonCore
      dom (u 0) (u 1) line1 line2 hi).2
  obtain ⟨qa, hfactorA, hqa⟩ :=
    exists_quotient_natDegree_lt_sub_three_of_three_roots
      dom hk (line2.1 - line1.1) haDeg
        (commonCoreBlock dom (u 0) (u 1) line1 line2) hinter hrootA
  obtain ⟨qr, hfactorR, hqr⟩ :=
    exists_quotient_natDegree_lt_sub_three_of_three_roots
      dom hk (line2.2 - line1.2) hrDeg
        (commonCoreBlock dom (u 0) (u 1) line1 line2) hinter hrootR
  exact ⟨qa, qr, hfactorA, hfactorR, hqa, hqr⟩

/-- **Cubic recursive overlap-three form.**  The two saturated residual
locators reconcile through the cubic locator of the common core and an affine
pencil whose two coefficients, and hence the pencil itself, have degree
strictly below `k-3`. -/
theorem overlap_three_cubic_recursive_reconciliation
    {dom : I ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 4 ≤ k) (hn : Fintype.card I = 2 * h)
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
      (commonCoreBlock dom (u 0) (u 1) line1 line2).card = 3)
    {gamma : F} (hgamma : gamma ∈ family.G)
    (hoff1 : family.q gamma ≠ line1.1 + C gamma * line1.2)
    (hoff2 : family.q gamma ≠ line2.1 + C gamma * line2.2) :
    ∃ c1 c2 : F, ∃ qa qr : F[X],
      c1 ≠ 0 ∧ c2 ≠ 0 ∧
      qa.natDegree < k - 3 ∧ qr.natDegree < k - 3 ∧
      (qa + C gamma * qr).natDegree < k - 3 ∧
      (domainRootProduct dom
        (commonCoreBlock dom (u 0) (u 1) line1 line2)).natDegree = 3 ∧
      line2.1 - line1.1 =
        domainRootProduct dom
          (commonCoreBlock dom (u 0) (u 1) line1 line2) * qa ∧
      line2.2 - line1.2 =
        domainRootProduct dom
          (commonCoreBlock dom (u 0) (u 1) line1 line2) * qr ∧
      C c1 * domainRootProduct dom
          (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line1) -
        C c2 * domainRootProduct dom
          (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line2) =
        domainRootProduct dom
          (commonCoreBlock dom (u 0) (u 1) line1 line2) *
            (qa + C gamma * qr) := by
  have hinter' :
      (jointCore dom (u 0) (u 1) line1.1 line1.2 ∩
        jointCore dom (u 0) (u 1) line2.1 line2.2).card = 3 := by
    simpa only [commonCoreBlock] using hinter
  obtain ⟨c1, c2, hc1, hc2, hreconcile⟩ :=
    overlap_three_two_block_reconciliation
      family (by omega) hn hsaturated hthreshold line1 line2 hline1 hline2
        hcore1 hcore2 hinter' hgamma hoff1 hoff2
  obtain ⟨qa, qr, hfactorA, hfactorR, hqa, hqr⟩ :=
    decoded_line_differences_factor_through_commonCore
      family hk line1 line2 hline1 hline2 hinter
  have hCqr : (C gamma * qr).natDegree ≤ qr.natDegree :=
    natDegree_C_mul_le gamma qr
  have hpencil : (qa + C gamma * qr).natDegree < k - 3 :=
    lt_of_le_of_lt (natDegree_add_le _ _)
      (max_lt hqa (lt_of_le_of_lt hCqr hqr))
  have hcommonDeg :
      (domainRootProduct dom
        (commonCoreBlock dom (u 0) (u 1) line1 line2)).natDegree = 3 := by
    rw [domainRootProduct_natDegree, hinter]
  refine ⟨c1, c2, qa, qr, hc1, hc2, hqa, hqr, hpencil,
    hcommonDeg, hfactorA, hfactorR, ?_⟩
  calc
    C c1 * domainRootProduct dom
          (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line1) -
        C c2 * domainRootProduct dom
          (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line2) =
        (line2.1 - line1.1) + C gamma * (line2.2 - line1.2) := hreconcile
    _ = domainRootProduct dom
          (commonCoreBlock dom (u 0) (u 1) line1 line2) * qa +
        C gamma *
          (domainRootProduct dom
            (commonCoreBlock dom (u 0) (u 1) line1 line2) * qr) := by
      rw [hfactorA, hfactorR]
    _ = domainRootProduct dom
          (commonCoreBlock dom (u 0) (u 1) line1 line2) *
        (qa + C gamma * qr) := by ring

#print axioms decoded_line_differences_factor_through_commonCore
#print axioms overlap_three_cubic_recursive_reconciliation

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeCommonFactor
