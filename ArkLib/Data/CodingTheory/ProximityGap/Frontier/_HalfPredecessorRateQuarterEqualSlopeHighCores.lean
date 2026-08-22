/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterHighCoreFreshPetalDichotomy

/-!
# Rate-quarter high cores with equal slope

Two distinct relevant half-core lines with the same slope polynomial force
that polynomial to agree with the received direction row outside at most
`k - 1` coordinates.  Determinant collapse then forces every other relevant
half-core line to have the same slope.

This has a direct counting consequence.  Every selected point on one of those
lines has a fresh agreement outside its own joint core, by the no-joint
condition.  Equal slope forces every such fresh agreement into the common
direction-error set.  Fresh fibres on one line are disjoint, so every relevant
half-core line contains at most `k - 1` selected scalars, improving the generic
half-domain line cap `h` to the exact direction-error budget.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCoreBandSynthesis

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterEqualSlopeHighCores

attribute [local instance] Classical.propDecidable

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Coordinates where a polynomial direction fails to match the received
direction row. -/
noncomputable def directionDisagreement (dom : ι ↪ F) (u1 : ι → F)
    (r : F[X]) : Finset ι :=
  Finset.univ.filter fun i => r.eval (dom i) ≠ u1 i

/-- Distinct degree-`<k` intercept polynomials have at most `k-1` common joint
core coordinates. -/
theorem jointCore_inter_card_le_pred_of_intercept_ne
    (dom : ι ↪ F) (u0 u1 : ι → F) {k : Nat} (hk : 1 ≤ k)
    (line0 line1 : PolynomialLine F)
    (hintercept : line0.1 ≠ line1.1)
    (hdeg0 : line0.1.natDegree < k)
    (hdeg1 : line1.1.natDegree < k) :
    (jointCore dom u0 u1 line0.1 line0.2 ∩
      jointCore dom u0 u1 line1.1 line1.2).card ≤ k - 1 := by
  let p : F[X] := line1.1 - line0.1
  have hp : p ≠ 0 := sub_ne_zero.mpr fun h => hintercept h.symm
  have hpDeg : p.natDegree < k :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
      (max_lt hdeg1 hdeg0)
  have hsub : jointCore dom u0 u1 line0.1 line0.2 ∩
      jointCore dom u0 u1 line1.1 line1.2 ⊆
      Finset.univ.filter fun i => p.eval (dom i) = 0 := by
    intro i hi
    simp only [Finset.mem_inter, jointCore, Finset.mem_filter,
      Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, p, eval_sub]
    rw [hi.1.1, hi.2.1, sub_self]
  exact (Finset.card_le_card hsub).trans
    (domain_root_card_le_pred dom hk p hp hpDeg)

/-- **Two equal-slope half cores determine the direction almost everywhere.**
If two distinct degree-`<k` polynomial lines have the same slope and each
joint core contains at least half of a `2h`-coordinate domain, their common
slope disagrees with the received direction row on at most `k-1` coordinates. -/
theorem directionDisagreement_card_le_pred_of_two_equalSlope_halfCores
    (dom : ι ↪ F) (u0 u1 : ι → F) {k h : Nat} (hk : 1 ≤ k)
    (hn : Fintype.card ι = 2 * h)
    (line0 line1 : PolynomialLine F) (hne : line0 ≠ line1)
    (hslope : line1.2 = line0.2)
    (hdeg0 : line0.1.natDegree < k)
    (hdeg1 : line1.1.natDegree < k)
    (hcore0 : h ≤ (jointCore dom u0 u1 line0.1 line0.2).card)
    (hcore1 : h ≤ (jointCore dom u0 u1 line1.1 line1.2).card) :
    (directionDisagreement dom u1 line0.2).card ≤ k - 1 := by
  let D0 := jointCore dom u0 u1 line0.1 line0.2
  let D1 := jointCore dom u0 u1 line1.1 line1.2
  have hintercept : line0.1 ≠ line1.1 := by
    intro h
    apply hne
    exact Prod.ext h hslope.symm
  have hinter : (D0 ∩ D1).card ≤ k - 1 := by
    simpa only [D0, D1] using
      jointCore_inter_card_le_pred_of_intercept_ne
        dom u0 u1 hk line0 line1 hintercept hdeg0 hdeg1
  have hEsub : directionDisagreement dom u1 line0.2 ⊆
      Finset.univ \ (D0 ∪ D1) := by
    intro i hi
    have hiError : line0.2.eval (dom i) ≠ u1 i := by
      simpa only [directionDisagreement, Finset.mem_filter,
        Finset.mem_univ, true_and] using hi
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hiUnion
    rcases Finset.mem_union.mp hiUnion with hi0 | hi1
    · have hi0Core :
          line0.1.eval (dom i) = u0 i ∧ line0.2.eval (dom i) = u1 i := by
        simpa only [D0, jointCore, Finset.mem_filter,
          Finset.mem_univ, true_and] using hi0
      have hi0' : line0.2.eval (dom i) = u1 i := hi0Core.2
      exact hiError hi0'
    · have hi1Core :
          line1.1.eval (dom i) = u0 i ∧ line1.2.eval (dom i) = u1 i := by
        simpa only [D1, jointCore, Finset.mem_filter,
          Finset.mem_univ, true_and] using hi1
      have hi1' : line1.2.eval (dom i) = u1 i := hi1Core.2
      apply hiError
      rw [← hslope]
      exact hi1'
  have hmissing : (Finset.univ \ (D0 ∪ D1)).card ≤ (D0 ∩ D1).card := by
    have hunionInter := Finset.card_union_add_card_inter D0 D1
    have hmissingEq : (Finset.univ \ (D0 ∪ D1)).card =
        Fintype.card ι - (D0 ∪ D1).card := by
      simp only [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    rw [hmissingEq, hn]
    have hcore0' : h ≤ D0.card := by simpa only [D0] using hcore0
    have hcore1' : h ≤ D1.card := by simpa only [D1] using hcore1
    omega
  exact (Finset.card_le_card hEsub).trans (hmissing.trans hinter)

/-- With equal reference slopes, determinant collapse is literal slope
collapse, provided the two reference intercepts are distinct. -/
theorem slope_eq_of_lineDeterminant_eq_zero_of_equal_reference_slope
    (line0 line1 line : PolynomialLine F)
    (hintercept : line0.1 ≠ line1.1)
    (hslope : line1.2 = line0.2)
    (hdet : lineDeterminant line0 line1 line = 0) :
    line.2 = line0.2 := by
  have hprod : (line1.1 - line0.1) * (line.2 - line0.2) = 0 := by
    simpa only [lineDeterminant, hslope, sub_self, mul_zero, sub_zero]
      using hdet
  rcases mul_eq_zero.mp hprod with hleft | hright
  · exact (sub_ne_zero.mpr fun h => hintercept h.symm) hleft |>.elim
  · exact sub_eq_zero.mp hright

/-- Agreement outside a line's own core can occur only where its slope
polynomial disagrees with the received direction row. -/
theorem freshAgreement_subset_directionDisagreement
    (dom : ι ↪ F) (u0 u1 : ι → F)
    (line : PolynomialLine F) (gamma : F) :
    fullAgreement dom u0 u1 gamma
        (line.1 + C gamma * line.2) \
        jointCore dom u0 u1 line.1 line.2 ⊆
      directionDisagreement dom u1 line.2 := by
  intro i hi
  have hiFresh := Finset.mem_sdiff.mp hi
  have hiAgree :
      line.1.eval (dom i) + gamma * line.2.eval (dom i) =
        u0 i + gamma * u1 i := by
    simpa only [fullAgreement, Finset.mem_filter, Finset.mem_univ,
      true_and, eval_add, eval_mul, eval_C] using hiFresh.1
  simp only [directionDisagreement, Finset.mem_filter,
    Finset.mem_univ, true_and]
  intro hslope
  apply hiFresh.2
  simp only [jointCore, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, hslope⟩
  rw [hslope] at hiAgree
  exact add_right_cancel hiAgree

/-- **Direction-error line cap.**  Every selected point on a relevant line
has a nonempty fresh fibre by the no-joint condition.  These fibres are
pairwise disjoint and lie in the direction-error set, so the line population
is at most the number of direction errors. -/
theorem pointsOn_card_le_directionDisagreement_card
    {dom : ι ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (line : LineParameter F) (hline : line ∈ lineParameters family) :
    (pointsOn family line).card ≤
      (directionDisagreement dom (u 1) line.2).card := by
  have hdeg := lineParameter_degree_lt family hline
  have hfresh : ∀ gamma : {gamma // gamma ∈ pointsOn family line},
      ∃ i, i ∈ fullAgreement dom (u 0) (u 1) gamma.1
          (family.q gamma.1) \
        jointCore dom (u 0) (u 1) line.1 line.2 := by
    intro gamma
    have hgamma' := (mem_pointsOn_iff family line gamma.1).mp gamma.2
    exact Finset.sdiff_nonempty.mpr <|
      not_subset_jointCore_of_not_pairJointAgreesOn
        dom (u 0) (u 1)
          (fullAgreement dom (u 0) (u 1) gamma.1 (family.q gamma.1))
          line.1 line.2 hdeg.1 hdeg.2
          (family.noJoint gamma.1 hgamma'.1)
  choose coord hcoord using hfresh
  have hcoordError : ∀ gamma : {gamma // gamma ∈ pointsOn family line},
      coord gamma ∈ directionDisagreement dom (u 1) line.2 := by
    intro gamma
    have hm := hcoord gamma
    have hq := (mem_pointsOn_iff family line gamma.1).mp gamma.2 |>.2
    rw [hq] at hm
    exact freshAgreement_subset_directionDisagreement
      dom (u 0) (u 1) line gamma.1 hm
  let f : {gamma // gamma ∈ pointsOn family line} →
      {i // i ∈ directionDisagreement dom (u 1) line.2} := fun gamma =>
    ⟨coord gamma, hcoordError gamma⟩
  have hf : Function.Injective f := by
    intro gamma beta heq
    apply Subtype.ext
    by_contra hne
    have hcoordEq : coord gamma = coord beta :=
      congrArg Subtype.val heq
    have hgammaFresh := hcoord gamma
    have hbetaFresh := hcoord beta
    have hgammaQ :=
      (mem_pointsOn_iff family line gamma.1).mp gamma.2 |>.2
    have hbetaQ :=
      (mem_pointsOn_iff family line beta.1).mp beta.2 |>.2
    rw [hgammaQ] at hgammaFresh
    rw [hbetaQ] at hbetaFresh
    have hbetaAtGamma : coord gamma ∈
        fullAgreement dom (u 0) (u 1) beta.1
            (line.1 + C beta.1 * line.2) \
          jointCore dom (u 0) (u 1) line.1 line.2 := by
      rw [hcoordEq]
      exact hbetaFresh
    exact (Finset.disjoint_left.mp
      (freshAgreement_disjoint dom (u 0) (u 1)
        line.1 line.2 hne)) hgammaFresh hbetaAtGamma
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe] using hcard

/-- Family-level form of the almost-everywhere direction conclusion. -/
theorem directionDisagreement_card_le_pred_of_distinct_relevant_equalSlope_halfCores
    {dom : ι ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h)
    (line0 line1 : LineParameter F)
    (hline0 : line0 ∈ lineParameters family)
    (hline1 : line1 ∈ lineParameters family)
    (hne : line0 ≠ line1) (hslope : line1.2 = line0.2)
    (hcore0 : h ≤
      (jointCore dom (u 0) (u 1) line0.1 line0.2).card)
    (hcore1 : h ≤
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card) :
    (directionDisagreement dom (u 1) line0.2).card ≤ k - 1 := by
  have hdeg0 := lineParameter_degree_lt family hline0
  have hdeg1 := lineParameter_degree_lt family hline1
  exact directionDisagreement_card_le_pred_of_two_equalSlope_halfCores
    dom (u 0) (u 1) hk hn line0 line1 hne hslope
      hdeg0.1 hdeg1.1 hcore0 hcore1

/-- Every relevant half-core line belongs to the common-slope cluster
determined by two distinct equal-slope reference half cores. -/
theorem slope_eq_reference_of_relevant_halfCore_in_equalSlope_cluster
    {dom : ι ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h) (hrate : 2 * k ≤ h)
    (line0 line1 line : LineParameter F)
    (hline0 : line0 ∈ lineParameters family)
    (hline1 : line1 ∈ lineParameters family)
    (hline : line ∈ lineParameters family)
    (hne : line0 ≠ line1) (hslope : line1.2 = line0.2)
    (hcore0 : h ≤
      (jointCore dom (u 0) (u 1) line0.1 line0.2).card)
    (hcore1 : h ≤
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card)
    (hcore : h ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card) :
    line.2 = line0.2 := by
  have hintercept : line0.1 ≠ line1.1 := by
    intro h
    apply hne
    exact Prod.ext h hslope.symm
  apply slope_eq_of_lineDeterminant_eq_zero_of_equal_reference_slope
    line0 line1 line hintercept hslope
  exact lineDeterminant_eq_zero_of_three_relevant_half_core_lines
    family hk hn hrate line0 line1 line hline0 hline1 hline
      hcore0 hcore1 hcore

/-- **Equal-slope high-core population bound.**  Under two distinct
equal-slope half-core references, every relevant half-core line contains at
most `k-1` selected scalars. -/
theorem pointsOn_card_le_pred_of_relevant_halfCore_in_equalSlope_cluster
    {dom : ι ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h) (hrate : 2 * k ≤ h)
    (line0 line1 line : LineParameter F)
    (hline0 : line0 ∈ lineParameters family)
    (hline1 : line1 ∈ lineParameters family)
    (hline : line ∈ lineParameters family)
    (hne : line0 ≠ line1) (hslope : line1.2 = line0.2)
    (hcore0 : h ≤
      (jointCore dom (u 0) (u 1) line0.1 line0.2).card)
    (hcore1 : h ≤
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card)
    (hcore : h ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card) :
    (pointsOn family line).card ≤ k - 1 := by
  have hslopeLine :=
    slope_eq_reference_of_relevant_halfCore_in_equalSlope_cluster
      family hk hn hrate line0 line1 line hline0 hline1 hline
        hne hslope hcore0 hcore1 hcore
  have hlineCap := pointsOn_card_le_directionDisagreement_card
    family line hline
  have herrorCap :=
    directionDisagreement_card_le_pred_of_distinct_relevant_equalSlope_halfCores
      family hk hn line0 line1 hline0 hline1 hne hslope hcore0 hcore1
  rw [hslopeLine] at hlineCap
  exact hlineCap.trans herrorCap

/-- Relevant decoded lines whose joint cores contain at least half of the
domain. -/
noncomputable def halfCoreLines
    {dom : ι ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u) (h : Nat) :
    Finset (LineParameter F) :=
  (lineParameters family).filter fun line =>
    h ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card

/-- Selected scalars covered by at least one relevant half-core line. -/
noncomputable def halfCoreCoveredScalars
    {dom : ι ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u) (h : Nat) : Finset F :=
  (halfCoreLines family h).biUnion fun line => pointsOn family line

/-- The equal-slope cluster covers at most `k-1` selected scalars per
half-core line. -/
theorem halfCoreCoveredScalars_card_le_lines_mul_pred_of_equalSlope_cluster
    {dom : ι ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h) (hrate : 2 * k ≤ h)
    (line0 line1 : LineParameter F)
    (hline0 : line0 ∈ lineParameters family)
    (hline1 : line1 ∈ lineParameters family)
    (hne : line0 ≠ line1) (hslope : line1.2 = line0.2)
    (hcore0 : h ≤
      (jointCore dom (u 0) (u 1) line0.1 line0.2).card)
    (hcore1 : h ≤
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card) :
    (halfCoreCoveredScalars family h).card ≤
      (halfCoreLines family h).card * (k - 1) := by
  apply Finset.card_biUnion_le_card_mul
  intro line hline
  have hline' := Finset.mem_filter.mp hline
  exact pointsOn_card_le_pred_of_relevant_halfCore_in_equalSlope_cluster
    family hk hn hrate line0 line1 line hline0 hline1 hline'.1
      hne hslope hcore0 hcore1 hline'.2

/-- If the relevant half-core lines cover the selected family, the entire
family is bounded by the number of such lines times the exact `k-1` per-line
budget. -/
theorem G_card_le_halfCoreLines_mul_pred_of_equalSlope_cluster
    {dom : ι ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h) (hrate : 2 * k ≤ h)
    (line0 line1 : LineParameter F)
    (hline0 : line0 ∈ lineParameters family)
    (hline1 : line1 ∈ lineParameters family)
    (hne : line0 ≠ line1) (hslope : line1.2 = line0.2)
    (hcore0 : h ≤
      (jointCore dom (u 0) (u 1) line0.1 line0.2).card)
    (hcore1 : h ≤
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card)
    (hcover : family.G ⊆ halfCoreCoveredScalars family h) :
    family.G.card ≤ (halfCoreLines family h).card * (k - 1) := by
  exact (Finset.card_le_card hcover).trans <|
    halfCoreCoveredScalars_card_le_lines_mul_pred_of_equalSlope_cluster
      family hk hn hrate line0 line1 hline0 hline1 hne hslope
        hcore0 hcore1

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterEqualSlopeHighCores

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterEqualSlopeHighCores
#print axioms directionDisagreement_card_le_pred_of_two_equalSlope_halfCores
#print axioms slope_eq_of_lineDeterminant_eq_zero_of_equal_reference_slope
#print axioms pointsOn_card_le_directionDisagreement_card
#print axioms slope_eq_reference_of_relevant_halfCore_in_equalSlope_cluster
#print axioms pointsOn_card_le_pred_of_relevant_halfCore_in_equalSlope_cluster
#print axioms halfCoreCoveredScalars_card_le_lines_mul_pred_of_equalSlope_cluster
#print axioms G_card_le_halfCoreLines_mul_pred_of_equalSlope_cluster
