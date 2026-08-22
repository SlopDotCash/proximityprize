/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourCrossTripleThreeHoleConsumer

/-!
# Rate-quarter `k = 4`: the four-hole cross-triple wall

The forced cross-triple consumer leaves one exceptional cell: the source eight-core and a
six-core secant meet twice and leave four coordinates outside their union. Every selected point
off both decoded lines agrees on three or four of those holes.

This file makes that cell explicit. The all-four subpopulation lies on the polynomial line
obtained by interpolating the received offset and direction on the four holes, and has cardinality
at most four. The complement splits into four disjoint classes indexed by the uniquely omitted
hole. Each class has a canonical cubic-locator normal form on the other three holes. The final
consumer theorem identifies the global exceptional branch with precisely this four-class wall;
it does not assert a bound on the combined four omitted-hole classes.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSignatures
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCrossTripleUniqueCoreConsumer
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCrossTripleThreeHoleConsumer
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeFactorization
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeCommonFactor
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFour

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourFourHoleClasses

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- The forced cross-triple secant line. -/
noncomputable def crossSecantLine
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    {residual : UniqueEightCoreResidual family}
    (cross : UniqueCoreCrossTripleResidual family residual) : LineParameter F :=
  secantParameter family cross.gamma1 cross.gamma2

/-- Coordinates outside both the source core and the forced cross-triple secant core. -/
noncomputable def crossResidualHoles
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual) : Finset I :=
  Finset.univ \ (
    jointCore dom (u 0) (u 1) residual.source.1 residual.source.2 ∪
      jointCore dom (u 0) (u 1)
        (crossSecantLine family cross).1 (crossSecantLine family cross).2)

/-- Proof data for the exceptional core-six, overlap-two, four-hole branch. -/
structure FourHoleCrossTripleResidual
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual) : Prop where
  secant_core_card :
    (jointCore dom (u 0) (u 1)
      (crossSecantLine family cross).1 (crossSecantLine family cross).2).card = 6
  source_secant_inter_card :
    (jointCore dom (u 0) (u 1) residual.source.1 residual.source.2 ∩
      jointCore dom (u 0) (u 1)
        (crossSecantLine family cross).1 (crossSecantLine family cross).2).card = 2
  holes_card : (crossResidualHoles family residual cross).card = 4
  off_both_three : ∀ theta ∈ family.G,
    family.q theta ≠ residual.source.1 + C theta * residual.source.2 →
    family.q theta ≠
      (crossSecantLine family cross).1 + C theta * (crossSecantLine family cross).2 →
    3 ≤ (fullAgreement dom (u 0) (u 1) theta (family.q theta) ∩
      crossResidualHoles family residual cross).card

/-- Selected parameters lying off both distinguished decoded lines. -/
noncomputable def fourHoleOffBothPopulation
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual) : Finset F :=
  family.G \ (pointsOn family residual.source ∪
    pointsOn family (crossSecantLine family cross))

theorem mem_fourHoleOffBothPopulation
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual) (theta : F) :
    theta ∈ fourHoleOffBothPopulation family residual cross ↔
      theta ∈ family.G ∧ theta ∉ pointsOn family residual.source ∧
        theta ∉ pointsOn family (crossSecantLine family cross) := by
  simp only [fourHoleOffBothPopulation, Finset.mem_sdiff, Finset.mem_union, not_or]

/-- The trace of one off-both point on the four residual holes. -/
noncomputable def fourHoleAgreement
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual) (theta : F) : Finset I :=
  fullAgreement dom (u 0) (u 1) theta (family.q theta) ∩
    crossResidualHoles family residual cross

theorem fourHoleAgreement_subset_holes
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual) (theta : F) :
    fourHoleAgreement family residual cross theta ⊆
      crossResidualHoles family residual cross :=
  Finset.inter_subset_right

/-- Exact support-four dichotomy: every selected point off both lines uses three or four holes. -/
theorem fourHoleAgreement_card_eq_three_or_four
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual)
    (cell : FourHoleCrossTripleResidual family residual cross)
    {theta : F} (htheta : theta ∈ fourHoleOffBothPopulation family residual cross) :
    (fourHoleAgreement family residual cross theta).card = 3 ∨
      (fourHoleAgreement family residual cross theta).card = 4 := by
  have hthetaData := (mem_fourHoleOffBothPopulation family residual cross theta).mp htheta
  have hoffSource :
      family.q theta ≠ residual.source.1 + C theta * residual.source.2 := by
    intro heq
    exact hthetaData.2.1 ((mem_pointsOn_iff family residual.source theta).mpr
      ⟨hthetaData.1, heq⟩)
  have hoffSecant :
      family.q theta ≠
        (crossSecantLine family cross).1 +
          C theta * (crossSecantLine family cross).2 := by
    intro heq
    exact hthetaData.2.2
      ((mem_pointsOn_iff family (crossSecantLine family cross) theta).mpr
        ⟨hthetaData.1, heq⟩)
  have hlower : 3 ≤ (fourHoleAgreement family residual cross theta).card := by
    simpa only [fourHoleAgreement] using
      cell.off_both_three theta hthetaData.1 hoffSource hoffSecant
  have hupper : (fourHoleAgreement family residual cross theta).card ≤ 4 := by
    have := Finset.card_le_card
      (fourHoleAgreement_subset_holes family residual cross theta)
    rw [cell.holes_card] at this
    omega
  omega

/-- Off-both points agreeing on all four residual holes. -/
noncomputable def allFourHolePopulation
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual) : Finset F :=
  (fourHoleOffBothPopulation family residual cross).filter fun theta =>
    fourHoleAgreement family residual cross theta =
      crossResidualHoles family residual cross

theorem mem_allFourHolePopulation
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual) (theta : F) :
    theta ∈ allFourHolePopulation family residual cross ↔
      theta ∈ fourHoleOffBothPopulation family residual cross ∧
        fourHoleAgreement family residual cross theta =
          crossResidualHoles family residual cross := by
  simp only [allFourHolePopulation, Finset.mem_filter]

/-- Lagrange interpolation on the four residual holes. -/
noncomputable def fourHoleInterpolant
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual)
    (w : I → F) : F[X] :=
  Lagrange.interpolate (crossResidualHoles family residual cross) dom w

theorem fourHoleInterpolant_eval
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual)
    (w : I → F) {i : I} (hi : i ∈ crossResidualHoles family residual cross) :
    (fourHoleInterpolant family residual cross w).eval (dom i) = w i := by
  exact Lagrange.eval_interpolate_at_node w dom.injective.injOn hi

theorem natDegree_lt_of_degree_lt_of_pos
    {p : F[X]} {k : Nat} (hk : 0 < k) (hp : p.degree < k) :
    p.natDegree < k := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simpa using hk
  · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp

theorem fourHoleInterpolant_natDegree_lt_four
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual)
    (cell : FourHoleCrossTripleResidual family residual cross) (w : I → F) :
    (fourHoleInterpolant family residual cross w).natDegree < 4 := by
  apply natDegree_lt_of_degree_lt_of_pos (by norm_num)
  have hdeg := Lagrange.degree_interpolate_lt
    (s := crossResidualHoles family residual cross) (v := dom) (r := w)
      dom.injective.injOn
  simpa only [cell.holes_card] using hdeg

/-- The explicit polynomial line interpolating the received line on all four holes. -/
noncomputable def fourHoleInterpolatedLine
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual) : LineParameter F :=
  (fourHoleInterpolant family residual cross (u 0),
    fourHoleInterpolant family residual cross (u 1))

/-- Four common hole agreements pin the selected polynomial to the interpolated line. -/
theorem q_eq_fourHoleInterpolatedLine_of_mem
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual)
    (cell : FourHoleCrossTripleResidual family residual cross)
    {theta : F} (htheta : theta ∈ allFourHolePopulation family residual cross) :
    family.q theta =
      (fourHoleInterpolatedLine family residual cross).1 +
        C theta * (fourHoleInterpolatedLine family residual cross).2 := by
  let H := crossResidualHoles family residual cross
  let A := fourHoleInterpolant family residual cross (u 0)
  let R := fourHoleInterpolant family residual cross (u 1)
  have hthetaData := (mem_allFourHolePopulation family residual cross theta).mp htheta
  have hthetaG :=
    (mem_fourHoleOffBothPopulation family residual cross theta).mp hthetaData.1 |>.1
  have hAdeg : A.natDegree < 4 := by
    simpa only [A] using
      fourHoleInterpolant_natDegree_lt_four family residual cross cell (u 0)
  have hRdeg : R.natDegree < 4 := by
    simpa only [R] using
      fourHoleInterpolant_natDegree_lt_four family residual cross cell (u 1)
  have hlineDeg : (A + C theta * R).natDegree < 4 := by
    exact lt_of_le_of_lt (natDegree_add_le _ _)
      (max_lt hAdeg (lt_of_le_of_lt (natDegree_C_mul_le _ _) hRdeg))
  have heq : family.q theta = A + C theta * R := by
    refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq'
      (family.q theta) (A + C theta * R) (H.image dom) ?_ ?_
    · intro x hx
      obtain ⟨i, hiH, rfl⟩ := Finset.mem_image.mp hx
      have hiTrace : i ∈ fourHoleAgreement family residual cross theta := by
        rw [hthetaData.2]
        simpa only [H] using hiH
      have hiFull := (Finset.mem_inter.mp (by
        simpa only [fourHoleAgreement] using hiTrace)).1
      have hiEq : (family.q theta).eval (dom i) = u 0 i + theta * u 1 i := by
        simpa only [fullAgreement, Finset.mem_filter, Finset.mem_univ,
          true_and] using hiFull
      simp only [eval_add, eval_mul, eval_C]
      rw [show A.eval (dom i) = u 0 i by
          simpa only [A, H] using fourHoleInterpolant_eval
            family residual cross (u 0) hiH,
        show R.eval (dom i) = u 1 i by
          simpa only [R, H] using fourHoleInterpolant_eval
            family residual cross (u 1) hiH]
      exact hiEq
    · rw [Finset.card_image_of_injective _ dom.injective]
      simpa only [H, cell.holes_card] using
        max_lt (family.degree_lt theta hthetaG) hlineDeg
  simpa only [fourHoleInterpolatedLine, A, R] using heq

theorem allFourHolePopulation_subset_interpolatedLine
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual)
    (cell : FourHoleCrossTripleResidual family residual cross) :
    allFourHolePopulation family residual cross ⊆
      pointsOn family (fourHoleInterpolatedLine family residual cross) := by
  intro theta htheta
  rw [mem_pointsOn_iff]
  exact ⟨(mem_fourHoleOffBothPopulation family residual cross theta).mp
      ((mem_allFourHolePopulation family residual cross theta).mp htheta).1 |>.1,
    q_eq_fourHoleInterpolatedLine_of_mem family residual cross cell htheta⟩

/-- Two all-four points certify that the interpolated line is an actual selected secant. -/
theorem fourHoleInterpolatedLine_mem_lineParameters_of_two
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual)
    (cell : FourHoleCrossTripleResidual family residual cross)
    (htwo : 2 ≤ (allFourHolePopulation family residual cross).card) :
    fourHoleInterpolatedLine family residual cross ∈ lineParameters family := by
  have hone : 1 < (allFourHolePopulation family residual cross).card := by omega
  obtain ⟨alpha, halpha, beta, hbeta, hab⟩ := Finset.one_lt_card.mp hone
  let line := fourHoleInterpolatedLine family residual cross
  let A := line.1
  let R := line.2
  have halphaG := (mem_fourHoleOffBothPopulation family residual cross alpha).mp
    ((mem_allFourHolePopulation family residual cross alpha).mp halpha).1 |>.1
  have hbetaG := (mem_fourHoleOffBothPopulation family residual cross beta).mp
    ((mem_allFourHolePopulation family residual cross beta).mp hbeta).1 |>.1
  have hqAlpha : family.q alpha = A + C alpha * R := by
    simpa only [A, R, line] using
      q_eq_fourHoleInterpolatedLine_of_mem family residual cross cell halpha
  have hqBeta : family.q beta = A + C beta * R := by
    simpa only [A, R, line] using
      q_eq_fourHoleInterpolatedLine_of_mem family residual cross cell hbeta
  have hslope :
      slopePolynomial alpha beta (family.q alpha) (family.q beta) = R := by
    have hdiff : family.q alpha - family.q beta = C (alpha - beta) * R := by
      rw [hqAlpha, hqBeta]
      simp only [map_sub]
      ring
    rw [slopePolynomial, hdiff, ← mul_assoc, ← C_mul,
      inv_mul_cancel₀ (sub_ne_zero.mpr hab), C_1, one_mul]
  have hlineEq : secantParameter family alpha beta = line := by
    apply Prod.ext
    · simp only [secantParameter, hslope]
      rw [hqAlpha]
      ring
    · simpa only [secantParameter] using hslope
  change line ∈ lineParameters family
  rw [← hlineEq]
  exact secantParameter_mem_lineParameters family halphaG hbetaG hab

/-- The interpolated all-four line contains the four holes in its joint core. -/
theorem holes_subset_fourHoleInterpolatedLine_core
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual) :
    crossResidualHoles family residual cross ⊆
      jointCore dom (u 0) (u 1)
        (fourHoleInterpolatedLine family residual cross).1
        (fourHoleInterpolatedLine family residual cross).2 := by
  intro i hi
  simp only [jointCore, Finset.mem_filter, Finset.mem_univ, true_and,
    fourHoleInterpolatedLine]
  exact ⟨fourHoleInterpolant_eval family residual cross (u 0) hi,
    fourHoleInterpolant_eval family residual cross (u 1) hi⟩

/-- Sharp line-population consequence for the all-four subpopulation. -/
theorem allFourHolePopulation_card_le_four
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual)
    (cell : FourHoleCrossTripleResidual family residual cross) :
    (allFourHolePopulation family residual cross).card ≤ 4 := by
  by_cases hone : (allFourHolePopulation family residual cross).card ≤ 1
  · omega
  have htwo : 2 ≤ (allFourHolePopulation family residual cross).card := by omega
  let line := fourHoleInterpolatedLine family residual cross
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  have hline : line ∈ lineParameters family := by
    simpa only [line] using
      fourHoleInterpolatedLine_mem_lineParameters_of_two
        family residual cross cell htwo
  have hDlower : 4 ≤ D.card := by
    have hsub := holes_subset_fourHoleInterpolatedLine_core family residual cross
    have hcard := Finset.card_le_card hsub
    simpa only [D, line, cell.holes_card] using hcard
  have honeMem : (allFourHolePopulation family residual cross).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨theta, htheta⟩ := honeMem
  have hthetaOn : theta ∈ pointsOn family line := by
    simpa only [line] using
      allFourHolePopulation_subset_interpolatedLine
        family residual cross cell htheta
  have hthetaOffSource : theta ∉ pointsOn family residual.source :=
    (mem_fourHoleOffBothPopulation family residual cross theta).mp
      ((mem_allFourHolePopulation family residual cross theta).mp htheta).1 |>.2.1
  have hlineNe : line ≠ residual.source := by
    intro heq
    exact hthetaOffSource (by simpa only [heq] using hthetaOn)
  have hDupper : D.card ≤ 7 := by
    by_contra hnot
    have height : 8 ≤
        (jointCore dom (u 0) (u 1) line.1 line.2).card := by
      simpa only [D] using (show 8 ≤ D.card by omega)
    exact hlineNe (residual.source_unique line hline height)
  have hpack := pointsOn_card_mul_max_add_core_le family hline
  change (pointsOn family line).card * max 1
      (⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ - D.card) + D.card ≤
    Fintype.card I at hpack
  rw [hthreshold, hn] at hpack
  have hlineCard : (pointsOn family line).card ≤ 4 := by
    interval_cases hD : D.card <;> norm_num [hD] at hpack ⊢ <;> omega
  exact (Finset.card_le_card
    (allFourHolePopulation_subset_interpolatedLine
      family residual cross cell)).trans (by simpa only [line] using hlineCard)

/-! ## The four omitted-hole classes -/

/-- Off-both points which do not agree on all four holes. -/
noncomputable def threeOfFourHolePopulation
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual) : Finset F :=
  fourHoleOffBothPopulation family residual cross \
    allFourHolePopulation family residual cross

theorem mem_threeOfFourHolePopulation
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual) (theta : F) :
    theta ∈ threeOfFourHolePopulation family residual cross ↔
      theta ∈ fourHoleOffBothPopulation family residual cross ∧
        theta ∉ allFourHolePopulation family residual cross := by
  simp only [threeOfFourHolePopulation, Finset.mem_sdiff]

theorem fourHoleAgreement_card_eq_three_of_mem_residual
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual)
    (cell : FourHoleCrossTripleResidual family residual cross)
    {theta : F} (htheta : theta ∈ threeOfFourHolePopulation family residual cross) :
    (fourHoleAgreement family residual cross theta).card = 3 := by
  have hthetaData := (mem_threeOfFourHolePopulation family residual cross theta).mp htheta
  rcases fourHoleAgreement_card_eq_three_or_four
      family residual cross cell hthetaData.1 with hthree | hfour
  · exact hthree
  · exfalso
    have heq : fourHoleAgreement family residual cross theta =
        crossResidualHoles family residual cross := by
      apply Finset.eq_of_subset_of_card_le
        (fourHoleAgreement_subset_holes family residual cross theta)
      rw [cell.holes_card, hfour]
    exact hthetaData.2 ((mem_allFourHolePopulation family residual cross theta).mpr
      ⟨hthetaData.1, heq⟩)

/-- Each residual point omits one and only one of the four holes. -/
theorem existsUnique_omittedHole_of_mem_residual
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual)
    (cell : FourHoleCrossTripleResidual family residual cross)
    {theta : F} (htheta : theta ∈ threeOfFourHolePopulation family residual cross) :
    ∃! i : I, i ∈ crossResidualHoles family residual cross ∧
      fourHoleAgreement family residual cross theta =
        (crossResidualHoles family residual cross).erase i := by
  let H := crossResidualHoles family residual cross
  let T := fourHoleAgreement family residual cross theta
  have hTsub : T ⊆ H := by
    simpa only [T, H] using
      fourHoleAgreement_subset_holes family residual cross theta
  have hTcard : T.card = 3 := by
    simpa only [T] using
      fourHoleAgreement_card_eq_three_of_mem_residual
        family residual cross cell htheta
  have hdiffCard : (H \ T).card = 1 := by
    rw [Finset.card_sdiff_of_subset hTsub, show H.card = 4 by
      simpa only [H] using cell.holes_card, hTcard]
  obtain ⟨i, hiDiff⟩ := Finset.card_eq_one.mp hdiffCard
  have hiMem : i ∈ H \ T := by rw [hiDiff]; simp
  have hiH : i ∈ H := (Finset.mem_sdiff.mp hiMem).1
  have hiNotT : i ∉ T := (Finset.mem_sdiff.mp hiMem).2
  have hTsubErase : T ⊆ H.erase i := by
    intro j hj
    exact Finset.mem_erase.mpr
      ⟨fun hji => hiNotT (hji ▸ hj), hTsub hj⟩
  have hTeq : T = H.erase i := by
    apply Finset.eq_of_subset_of_card_le hTsubErase
    rw [Finset.card_erase_of_mem hiH,
      show H.card = 4 by simpa only [H] using cell.holes_card, hTcard]
  refine ⟨i, ⟨by simpa only [H] using hiH, by simpa only [T, H] using hTeq⟩, ?_⟩
  intro j hj
  have hjH : j ∈ H := by simpa only [H] using hj.1
  have herase : H.erase i = H.erase j := by
    simpa only [T, H] using hTeq.symm.trans hj.2
  by_contra hij
  have hiIn : i ∈ H.erase j :=
    Finset.mem_erase.mpr ⟨fun h => hij h.symm, hiH⟩
  have : i ∈ H.erase i := by rwa [herase]
  exact Finset.notMem_erase i H this

/-- The class of residual points omitting a specified hole. -/
noncomputable def omittedHoleClass
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual) (i : I) : Finset F :=
  (threeOfFourHolePopulation family residual cross).filter fun theta =>
    fourHoleAgreement family residual cross theta =
      (crossResidualHoles family residual cross).erase i

theorem mem_omittedHoleClass
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual) (i : I) (theta : F) :
    theta ∈ omittedHoleClass family residual cross i ↔
      theta ∈ threeOfFourHolePopulation family residual cross ∧
        fourHoleAgreement family residual cross theta =
          (crossResidualHoles family residual cross).erase i := by
  simp only [omittedHoleClass, Finset.mem_filter]

/-- The residual population is exactly the union of its four omitted-hole classes. -/
theorem threeOfFourHolePopulation_eq_biUnion_omittedHoleClass
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual)
    (cell : FourHoleCrossTripleResidual family residual cross) :
    threeOfFourHolePopulation family residual cross =
      (crossResidualHoles family residual cross).biUnion
        (omittedHoleClass family residual cross) := by
  ext theta
  constructor
  · intro htheta
    obtain ⟨i, hi, _⟩ :=
      existsUnique_omittedHole_of_mem_residual family residual cross cell htheta
    exact Finset.mem_biUnion.mpr ⟨i, hi.1,
      (mem_omittedHoleClass family residual cross i theta).mpr
        ⟨htheta, hi.2⟩⟩
  · intro htheta
    obtain ⟨i, _hiH, hi⟩ := Finset.mem_biUnion.mp htheta
    exact (mem_omittedHoleClass family residual cross i theta).mp hi |>.1

/-- Distinct omitted holes give disjoint classes. -/
theorem omittedHoleClass_pairwise_disjoint
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual)
    {i j : I}
    (hi : i ∈ crossResidualHoles family residual cross)
    (_hj : j ∈ crossResidualHoles family residual cross)
    (hij : i ≠ j) :
    Disjoint (omittedHoleClass family residual cross i)
      (omittedHoleClass family residual cross j) := by
  rw [Finset.disjoint_left]
  intro theta hthetaI hthetaJ
  have hI := (mem_omittedHoleClass family residual cross i theta).mp hthetaI |>.2
  have hJ := (mem_omittedHoleClass family residual cross j theta).mp hthetaJ |>.2
  have herase :
      (crossResidualHoles family residual cross).erase i =
        (crossResidualHoles family residual cross).erase j := hI.symm.trans hJ
  have hiInJ : i ∈ (crossResidualHoles family residual cross).erase j :=
    Finset.mem_erase.mpr ⟨hij, hi⟩
  have hiInI : i ∈ (crossResidualHoles family residual cross).erase i := by
    rwa [herase]
  exact Finset.notMem_erase i _ hiInI

/-! ## Cubic-locator normal form inside one omitted-hole class -/

noncomputable def omittedHoleInterpolant
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual)
    (i : I) (w : I → F) : F[X] :=
  Lagrange.interpolate ((crossResidualHoles family residual cross).erase i) dom w

theorem omittedHoleInterpolant_eval
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual)
    (i : I) (w : I → F) {j : I}
    (hj : j ∈ (crossResidualHoles family residual cross).erase i) :
    (omittedHoleInterpolant family residual cross i w).eval (dom j) = w j := by
  exact Lagrange.eval_interpolate_at_node w dom.injective.injOn hj

theorem omittedHoleInterpolant_natDegree_lt_three
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual)
    (cell : FourHoleCrossTripleResidual family residual cross)
    {i : I} (hi : i ∈ crossResidualHoles family residual cross) (w : I → F) :
    (omittedHoleInterpolant family residual cross i w).natDegree < 3 := by
  apply natDegree_lt_of_degree_lt_of_pos (by norm_num)
  have hdeg := Lagrange.degree_interpolate_lt
    (s := (crossResidualHoles family residual cross).erase i)
      (v := dom) (r := w) dom.injective.injOn
  have hcard : ((crossResidualHoles family residual cross).erase i).card = 3 := by
    rw [Finset.card_erase_of_mem hi, cell.holes_card]
  simpa only [hcard] using hdeg

/-- Canonical cubic-locator normal form for one omitted-hole class. -/
theorem omittedHoleClass_cubic_locator_normal_form
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual)
    (cell : FourHoleCrossTripleResidual family residual cross)
    {i : I} (hi : i ∈ crossResidualHoles family residual cross)
    {theta : F} (htheta : theta ∈ omittedHoleClass family residual cross i) :
    ∃ c : F,
      family.q theta =
        omittedHoleInterpolant family residual cross i (u 0) +
          C theta * omittedHoleInterpolant family residual cross i (u 1) +
        C c * domainRootProduct dom
          ((crossResidualHoles family residual cross).erase i) := by
  let S := (crossResidualHoles family residual cross).erase i
  let A := omittedHoleInterpolant family residual cross i (u 0)
  let R := omittedHoleInterpolant family residual cross i (u 1)
  let base := A + C theta * R
  let p := family.q theta - base
  have hthetaData := (mem_omittedHoleClass family residual cross i theta).mp htheta
  have hthetaG := (mem_fourHoleOffBothPopulation family residual cross theta).mp
    ((mem_threeOfFourHolePopulation family residual cross theta).mp hthetaData.1).1 |>.1
  have hScard : S.card = 3 := by
    simpa only [S] using (show
      ((crossResidualHoles family residual cross).erase i).card = 3 by
        rw [Finset.card_erase_of_mem hi, cell.holes_card])
  have hAdeg : A.natDegree < 3 := by
    simpa only [A] using
      omittedHoleInterpolant_natDegree_lt_three
        family residual cross cell hi (u 0)
  have hRdeg : R.natDegree < 3 := by
    simpa only [R] using
      omittedHoleInterpolant_natDegree_lt_three
        family residual cross cell hi (u 1)
  have hbaseDeg : base.natDegree < 4 := by
    exact lt_of_le_of_lt (natDegree_add_le _ _)
      (max_lt (by omega)
        (lt_of_le_of_lt (natDegree_C_mul_le _ _) (by omega)))
  have hpdeg : p.natDegree < 4 := by
    exact lt_of_le_of_lt (natDegree_sub_le _ _)
      (max_lt (family.degree_lt theta hthetaG) hbaseDeg)
  have hroot : ∀ j ∈ S, p.eval (dom j) = 0 := by
    intro j hj
    have hjTrace : j ∈ fourHoleAgreement family residual cross theta := by
      rw [hthetaData.2]
      simpa only [S] using hj
    have hjFull := (Finset.mem_inter.mp (by
      simpa only [fourHoleAgreement] using hjTrace)).1
    have hjQ : (family.q theta).eval (dom j) = u 0 j + theta * u 1 j := by
      simpa only [fullAgreement, Finset.mem_filter, Finset.mem_univ,
        true_and] using hjFull
    have hjA : A.eval (dom j) = u 0 j := by
      simpa only [A, S] using
        omittedHoleInterpolant_eval family residual cross i (u 0) hj
    have hjR : R.eval (dom j) = u 1 j := by
      simpa only [R, S] using
        omittedHoleInterpolant_eval family residual cross i (u 1) hj
    simp only [p, base, eval_sub, eval_add, eval_mul, eval_C]
    rw [hjQ, hjA, hjR]
    ring
  obtain ⟨q, hfactor, hqdeg⟩ :=
    exists_quotient_natDegree_lt_sub_three_of_three_roots
      dom (k := 4) (by norm_num) p hpdeg S hScard hroot
  obtain ⟨_hq0, hqC⟩ :=
    eq_C_coeff_zero_of_natDegree_lt_one q (by simpa using hqdeg)
  have hmul : domainRootProduct dom S * q =
      C (q.coeff 0) * domainRootProduct dom S := by
    calc
      domainRootProduct dom S * q =
          domainRootProduct dom S * C (q.coeff 0) :=
        congrArg (fun r : F[X] => domainRootProduct dom S * r) hqC
      _ = C (q.coeff 0) * domainRootProduct dom S := by ring
  refine ⟨q.coeff 0, ?_⟩
  change family.q theta = base + C (q.coeff 0) * domainRootProduct dom S
  calc
    family.q theta = base + p := by simp only [p]; ring
    _ = base + domainRootProduct dom S * q := by rw [hfactor]
    _ = base + C (q.coeff 0) * domainRootProduct dom S := by rw [hmul]

/-! ## Reusable four-class wall and global consumer -/

/-- Exact reusable interface for the unresolved four-hole branch. -/
structure FourHoleFourClassWall
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual)
    (cell : FourHoleCrossTripleResidual family residual cross) : Prop where
  support_three_or_four : ∀ theta ∈ fourHoleOffBothPopulation family residual cross,
    (fourHoleAgreement family residual cross theta).card = 3 ∨
      (fourHoleAgreement family residual cross theta).card = 4
  all_four_on_line : allFourHolePopulation family residual cross ⊆
    pointsOn family (fourHoleInterpolatedLine family residual cross)
  all_four_card_le_four : (allFourHolePopulation family residual cross).card ≤ 4
  omitted_partition : threeOfFourHolePopulation family residual cross =
    (crossResidualHoles family residual cross).biUnion
      (omittedHoleClass family residual cross)
  omitted_classes_disjoint : ∀ i ∈ crossResidualHoles family residual cross,
    ∀ j ∈ crossResidualHoles family residual cross, i ≠ j →
      Disjoint (omittedHoleClass family residual cross i)
        (omittedHoleClass family residual cross j)
  omitted_cubic_normal_form : ∀ i ∈ crossResidualHoles family residual cross,
    ∀ theta ∈ omittedHoleClass family residual cross i,
      ∃ c : F,
        family.q theta =
          omittedHoleInterpolant family residual cross i (u 0) +
            C theta * omittedHoleInterpolant family residual cross i (u 1) +
          C c * domainRootProduct dom
            ((crossResidualHoles family residual cross).erase i)

theorem fourHoleFourClassWall
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual)
    (cell : FourHoleCrossTripleResidual family residual cross) :
    FourHoleFourClassWall family hn hthreshold residual cross cell where
  support_three_or_four := fun _ htheta =>
    fourHoleAgreement_card_eq_three_or_four family residual cross cell htheta
  all_four_on_line :=
    allFourHolePopulation_subset_interpolatedLine family residual cross cell
  all_four_card_le_four :=
    allFourHolePopulation_card_le_four family hn hthreshold residual cross cell
  omitted_partition :=
    threeOfFourHolePopulation_eq_biUnion_omittedHoleClass
      family residual cross cell
  omitted_classes_disjoint := fun _ hi _ hj hij =>
    omittedHoleClass_pairwise_disjoint family residual cross hi hj hij
  omitted_cubic_normal_form := fun _ hi _ htheta =>
    omittedHoleClass_cubic_locator_normal_form
      family residual cross cell hi htheta

/-- The favorable three-hole population alternative, named for reuse. -/
def ThreeHoleCrossPopulationAlternative
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual) : Prop :=
  ∃ residual2 : UniqueEightCoreResidual family,
    residual2.source = residual.source ∧
    residual2.gamma = cross.gamma1 ∧ residual2.beta = cross.gamma2 ∧
    4 ≤ (regularOffResidualSecant family residual2).card ∧
      (regularOffResidualSecant family residual2).card ≤ 5

/-- **Global branch identification.** The forced cross-triple either enters the already controlled
three-hole population alternative or is exactly the four-class wall formalized above. -/
theorem crossTriple_threeHole_population_or_fourClassWall
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual) :
    ThreeHoleCrossPopulationAlternative family residual cross ∨
      ∃ cell : FourHoleCrossTripleResidual family residual cross,
        FourHoleFourClassWall family hn hthreshold residual cross cell := by
  rcases crossTriple_threeHole_population_or_fourHole
      family hn hthreshold residual cross with hfavorable | hfour
  · exact Or.inl (by
      simpa only [ThreeHoleCrossPopulationAlternative] using hfavorable)
  · rcases hfour with ⟨hcore, hinter, hholes, hoff⟩
    let cell : FourHoleCrossTripleResidual family residual cross := {
      secant_core_card := by simpa only [crossSecantLine] using hcore
      source_secant_inter_card := by simpa only [crossSecantLine] using hinter
      holes_card := by
        simpa only [crossResidualHoles, crossSecantLine] using hholes
      off_both_three := by
        intro theta htheta hoffSource hoffSecant
        simpa only [crossResidualHoles, crossSecantLine] using
          hoff theta htheta hoffSource hoffSecant }
    exact Or.inr ⟨cell,
      fourHoleFourClassWall family hn hthreshold residual cross cell⟩

#print axioms fourHoleAgreement_card_eq_three_or_four
#print axioms allFourHolePopulation_card_le_four
#print axioms existsUnique_omittedHole_of_mem_residual
#print axioms threeOfFourHolePopulation_eq_biUnion_omittedHoleClass
#print axioms omittedHoleClass_cubic_locator_normal_form
#print axioms crossTriple_threeHole_population_or_fourClassWall

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourFourHoleClasses
