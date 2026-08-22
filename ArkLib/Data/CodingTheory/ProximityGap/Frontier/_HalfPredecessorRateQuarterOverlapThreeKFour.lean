/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterOverlapThreeCommonFactor

/-!
# Rate-quarter half predecessor: the overlap-three `k = 4` base case

At `k = 4`, the common cubic locator from the overlap-three cell consumes the
entire nonconstant degree budget.  The two quotient polynomials therefore
have natural degree zero and are honest constant polynomials; this includes
the zero-polynomial case, whose `natDegree` is also zero.

Thus both decoded-line differences are scalar multiples of one cubic
locator.  Their determinant is zero, their reconciliation quotient pencil is
constant, and two distinct decoded polynomial lines have at most one common
point in the scalar parameter.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeCommonFactor

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFour

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Degree `< 1` means constant, including for the zero polynomial. -/
theorem eq_C_coeff_zero_of_natDegree_lt_one (p : F[X])
    (hp : p.natDegree < 1) :
    p.natDegree = 0 ∧ p = C (p.coeff 0) := by
  have hp0 : p.natDegree = 0 := by omega
  exact ⟨hp0, Polynomial.eq_C_of_natDegree_eq_zero hp0⟩

/-- **`k = 4` decoded-line common factor.**  The quotient polynomials supplied
by the common-cubic theorem are constants.  In particular both line
differences are scalar multiples of the same cubic locator and satisfy the
corresponding proportionality identity. -/
theorem decoded_line_differences_kfour_common_factor
    {dom : I ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hinter : (commonCoreBlock dom (u 0) (u 1) line1 line2).card = 3) :
    ∃ qa qr : F[X], ∃ alpha rho : F,
      qa.natDegree = 0 ∧ qr.natDegree = 0 ∧
      qa = C alpha ∧ qr = C rho ∧
      line2.1 - line1.1 =
        domainRootProduct dom
          (commonCoreBlock dom (u 0) (u 1) line1 line2) * qa ∧
      line2.2 - line1.2 =
        domainRootProduct dom
          (commonCoreBlock dom (u 0) (u 1) line1 line2) * qr ∧
      line2.1 - line1.1 =
        C alpha * domainRootProduct dom
          (commonCoreBlock dom (u 0) (u 1) line1 line2) ∧
      line2.2 - line1.2 =
        C rho * domainRootProduct dom
          (commonCoreBlock dom (u 0) (u 1) line1 line2) ∧
      C rho * (line2.1 - line1.1) =
        C alpha * (line2.2 - line1.2) ∧
      (domainRootProduct dom
        (commonCoreBlock dom (u 0) (u 1) line1 line2)).natDegree = 3 := by
  obtain ⟨qa, qr, hfactorA, hfactorR, hqa, hqr⟩ :=
    decoded_line_differences_factor_through_commonCore
      family (by norm_num) line1 line2 hline1 hline2 hinter
  obtain ⟨hqa0, hqaC⟩ := eq_C_coeff_zero_of_natDegree_lt_one qa (by simpa using hqa)
  obtain ⟨hqr0, hqrC⟩ := eq_C_coeff_zero_of_natDegree_lt_one qr (by simpa using hqr)
  let alpha := qa.coeff 0
  let rho := qr.coeff 0
  have hfactorA' : line2.1 - line1.1 =
      C alpha * domainRootProduct dom
        (commonCoreBlock dom (u 0) (u 1) line1 line2) := by
    rw [hfactorA, hqaC]
    ring
  have hfactorR' : line2.2 - line1.2 =
      C rho * domainRootProduct dom
        (commonCoreBlock dom (u 0) (u 1) line1 line2) := by
    rw [hfactorR, hqrC]
    ring
  have hproportional : C rho * (line2.1 - line1.1) =
      C alpha * (line2.2 - line1.2) := by
    rw [hfactorA', hfactorR']
    ring
  have hcommonDeg :
      (domainRootProduct dom
        (commonCoreBlock dom (u 0) (u 1) line1 line2)).natDegree = 3 := by
    rw [domainRootProduct_natDegree, hinter]
  exact ⟨qa, qr, alpha, rho, hqa0, hqr0,
    hqaC, hqrC, hfactorA, hfactorR, hfactorA', hfactorR',
    hproportional, hcommonDeg⟩

/-- A nonzero common factor and a nonzero coefficient pair make the affine
polynomial pencil intersect zero at at most one scalar. -/
theorem unique_line_intersection_of_common_factor
    (P : F[X]) (hP : P ≠ 0) (alpha rho : F)
    (line1 line2 : F[X] × F[X])
    (hfactorA : line2.1 - line1.1 = C alpha * P)
    (hfactorR : line2.2 - line1.2 = C rho * P)
    (hcoeff : alpha ≠ 0 ∨ rho ≠ 0) :
    ∀ gamma beta : F,
      line1.1 + C gamma * line1.2 = line2.1 + C gamma * line2.2 →
      line1.1 + C beta * line1.2 = line2.1 + C beta * line2.2 →
      gamma = beta := by
  have hscalar : ∀ theta : F,
      line1.1 + C theta * line1.2 = line2.1 + C theta * line2.2 →
      alpha + theta * rho = 0 := by
    intro theta htheta
    have hdiff :
        (line2.1 - line1.1) + C theta * (line2.2 - line1.2) = 0 := by
      calc
        (line2.1 - line1.1) + C theta * (line2.2 - line1.2) =
            (line2.1 + C theta * line2.2) -
              (line1.1 + C theta * line1.2) := by ring
        _ = 0 := sub_eq_zero.mpr htheta.symm
    have hfactor :
        (line2.1 - line1.1) + C theta * (line2.2 - line1.2) =
          C (alpha + theta * rho) * P := by
      rw [hfactorA, hfactorR, C_add, C_mul]
      ring
    have hprod : C (alpha + theta * rho) * P = 0 := by
      rw [← hfactor]
      exact hdiff
    have hC : C (alpha + theta * rho) = 0 :=
      (mul_eq_zero.mp hprod).resolve_right hP
    exact C_eq_zero.mp hC
  intro gamma beta hgamma hbeta
  have hgammaScalar := hscalar gamma hgamma
  have hbetaScalar := hscalar beta hbeta
  by_cases hrho : rho = 0
  · have halpha : alpha ≠ 0 := hcoeff.resolve_right (by simpa [hrho])
    apply False.elim
    apply halpha
    simpa [hrho] using hgammaScalar
  · have hmul : (gamma - beta) * rho = 0 := by
      linear_combination hgammaScalar - hbetaScalar
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hrho)

/-- If two polynomial pairs differ through one nonzero common factor and are
distinct, their scalar coefficient pair cannot vanish simultaneously. -/
theorem coefficient_pair_nonzero_of_distinct
    (P : F[X]) (alpha rho : F) (line1 line2 : F[X] × F[X])
    (hfactorA : line2.1 - line1.1 = C alpha * P)
    (hfactorR : line2.2 - line1.2 = C rho * P)
    (hline : line1 ≠ line2) :
    alpha ≠ 0 ∨ rho ≠ 0 := by
  by_cases halpha : alpha = 0
  · right
    intro hrho
    apply hline
    have hfirst : line2.1 = line1.1 := by
      apply sub_eq_zero.mp
      rw [hfactorA, halpha]
      simp
    have hsecond : line2.2 = line1.2 := by
      apply sub_eq_zero.mp
      rw [hfactorR, hrho]
      simp
    exact Prod.ext hfirst.symm hsecond.symm
  · exact Or.inl halpha

/-- **Canonical `k = 4` overlap-three closure API.**  On a length-sixteen,
dimension-four saturated cell, the reconciliation quotient is the constant
`alpha + gamma * rho`.  The two line differences are scalar multiples of the
same cubic locator, their coefficient pair is nonzero, and the decoded lines
have at most one common scalar point. -/
theorem overlap_three_kfour_constant_quotient_reconciliation
    {dom : I ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = 8)
    (hcore2 :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 8)
    (hinter :
      (commonCoreBlock dom (u 0) (u 1) line1 line2).card = 3)
    {gamma : F} (hgamma : gamma ∈ family.G)
    (hoff1 : family.q gamma ≠ line1.1 + C gamma * line1.2)
    (hoff2 : family.q gamma ≠ line2.1 + C gamma * line2.2) :
    ∃ c1 c2 alpha rho : F,
      c1 ≠ 0 ∧ c2 ≠ 0 ∧
      (alpha ≠ 0 ∨ rho ≠ 0) ∧
      (domainRootProduct dom
        (commonCoreBlock dom (u 0) (u 1) line1 line2)).natDegree = 3 ∧
      line2.1 - line1.1 =
        C alpha * domainRootProduct dom
          (commonCoreBlock dom (u 0) (u 1) line1 line2) ∧
      line2.2 - line1.2 =
        C rho * domainRootProduct dom
          (commonCoreBlock dom (u 0) (u 1) line1 line2) ∧
      C rho * (line2.1 - line1.1) =
        C alpha * (line2.2 - line1.2) ∧
      C c1 * domainRootProduct dom
          (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line1) -
        C c2 * domainRootProduct dom
          (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line2) =
        C (alpha + gamma * rho) * domainRootProduct dom
          (commonCoreBlock dom (u 0) (u 1) line1 line2) ∧
      ∀ beta theta : F,
        line1.1 + C beta * line1.2 = line2.1 + C beta * line2.2 →
        line1.1 + C theta * line1.2 = line2.1 + C theta * line2.2 →
        beta = theta := by
  obtain ⟨c1, c2, qa, qr, hc1, hc2, hqa, hqr, _hpencil,
      hcommonDeg, hfactorA, hfactorR, hreconcile⟩ :=
    overlap_three_cubic_recursive_reconciliation
      family (by norm_num) (h := 8) (by simpa using hn) rfl
        (by simpa using hthreshold) line1 line2 hline1 hline2
        hcore1 hcore2 hinter hgamma hoff1 hoff2
  obtain ⟨hqa0, hqaC⟩ :=
    eq_C_coeff_zero_of_natDegree_lt_one qa (by simpa using hqa)
  obtain ⟨hqr0, hqrC⟩ :=
    eq_C_coeff_zero_of_natDegree_lt_one qr (by simpa using hqr)
  let alpha := qa.coeff 0
  let rho := qr.coeff 0
  have hfactorA' : line2.1 - line1.1 =
      C alpha * domainRootProduct dom
        (commonCoreBlock dom (u 0) (u 1) line1 line2) := by
    rw [hfactorA, hqaC]
    ring
  have hfactorR' : line2.2 - line1.2 =
      C rho * domainRootProduct dom
        (commonCoreBlock dom (u 0) (u 1) line1 line2) := by
    rw [hfactorR, hqrC]
    ring
  have hlineNe : line1 ≠ line2 := by
    intro heq
    subst line2
    simp only [commonCoreBlock, Finset.inter_self] at hinter
    omega
  have hcoeff : alpha ≠ 0 ∨ rho ≠ 0 :=
    coefficient_pair_nonzero_of_distinct
      (domainRootProduct dom
        (commonCoreBlock dom (u 0) (u 1) line1 line2))
      alpha rho line1 line2 hfactorA' hfactorR' hlineNe
  have hproportional : C rho * (line2.1 - line1.1) =
      C alpha * (line2.2 - line1.2) := by
    rw [hfactorA', hfactorR']
    ring
  have hreconcile' :
      C c1 * domainRootProduct dom
          (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line1) -
        C c2 * domainRootProduct dom
          (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line2) =
        C (alpha + gamma * rho) * domainRootProduct dom
          (commonCoreBlock dom (u 0) (u 1) line1 line2) := by
    calc
      C c1 * domainRootProduct dom
            (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line1) -
          C c2 * domainRootProduct dom
            (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line2) =
          domainRootProduct dom
            (commonCoreBlock dom (u 0) (u 1) line1 line2) *
              (qa + C gamma * qr) := hreconcile
      _ = C (alpha + gamma * rho) * domainRootProduct dom
            (commonCoreBlock dom (u 0) (u 1) line1 line2) := by
        rw [hqaC, hqrC, C_add, C_mul]
        ring
  have hcommon0 : domainRootProduct dom
      (commonCoreBlock dom (u 0) (u 1) line1 line2) ≠ 0 :=
    (domainRootProduct_monic dom
      (commonCoreBlock dom (u 0) (u 1) line1 line2)).ne_zero
  have hunique := unique_line_intersection_of_common_factor
    (domainRootProduct dom
      (commonCoreBlock dom (u 0) (u 1) line1 line2))
    hcommon0 alpha rho line1 line2 hfactorA' hfactorR' hcoeff
  exact ⟨c1, c2, alpha, rho, hc1, hc2, hcoeff, hcommonDeg,
    hfactorA', hfactorR', hproportional, hreconcile', hunique⟩

#print axioms decoded_line_differences_kfour_common_factor
#print axioms unique_line_intersection_of_common_factor
#print axioms overlap_three_kfour_constant_quotient_reconciliation

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFour
