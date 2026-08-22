/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourLongOutsiderCollapse
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterOverlapThreeFactorization

/-!
# Rate-quarter `k = 4`: rigidity of regular-outsider signatures

Relative to a fixed eight-coordinate source core, a regular outsider has a
three-coordinate root block in the core and misses exactly two coordinates in
the eight-coordinate complement.  Its residual from the source polynomial
line is a nonzero scalar multiple of the cubic locator of that root block.

The key new observation is that three outsiders cannot have the same root
block and pairwise-disjoint missed edges.  After dividing conceptually by the
common locator, one coordinate missed by none makes the three residual
coefficients affine in their scalar parameters.  At every other coordinate,
pairwise disjointness leaves two valid rows, and those two rows force the third
one as well.  This fills every purported miss, a contradiction.

Thus three equal-root signatures force two intersecting missed edges.  Their
two secant points then share at least five fresh coordinates as well as the
three source-core coordinates, producing a second core of size at least eight
and overlap exactly three with the source core.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourLongOutsiderCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeFactorization

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourRegularSignatureRigidity

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-! ## The affine-row filling lemma -/

/-- If two affine rows agree with coefficient data lying on the same affine
coefficient line, then the third row agrees as well. -/
theorem affine_third_value
    {gamma1 gamma2 gamma3 c1 c2 c3 A R L : F}
    (hgamma12 : gamma1 ≠ gamma2)
    (hcoeff :
      (gamma1 - gamma2) * (c3 - c2) =
        (gamma3 - gamma2) * (c1 - c2))
    (hrow1 : A + gamma1 * R = c1 * L)
    (hrow2 : A + gamma2 * R = c2 * L) :
    A + gamma3 * R = c3 * L := by
  apply (mul_left_cancel₀ (sub_ne_zero.mpr hgamma12))
  linear_combination
    (gamma1 - gamma2) * hrow2 +
      (gamma3 - gamma2) * (hrow1 - hrow2) - hcoeff * L

/-- Three coefficient pairs are collinear if their corresponding affine rows
agree at one coordinate where the common locator is nonzero. -/
theorem coefficient_collinear_of_three_rows
    {gamma1 gamma2 gamma3 c1 c2 c3 A R L : F}
    (hL : L ≠ 0)
    (hrow1 : A + gamma1 * R = c1 * L)
    (hrow2 : A + gamma2 * R = c2 * L)
    (hrow3 : A + gamma3 * R = c3 * L) :
    (gamma1 - gamma2) * (c3 - c2) =
      (gamma3 - gamma2) * (c1 - c2) := by
  apply mul_right_cancel₀ hL
  linear_combination
    -(gamma1 - gamma2) * (hrow3 - hrow2) +
      (gamma3 - gamma2) * (hrow1 - hrow2)

/-- **Pairwise-disjoint misses are removable.**

Suppose three distinct scalar rows have the form

`A(i) + gamma_j R(i) = c_j L(i)`

away from their respective missed sets.  If the missed sets are pairwise
disjoint and one coordinate is missed by none, then all three equations hold
at every coordinate. -/
theorem affine_rows_fill_pairwise_disjoint_misses
    (V E1 E2 E3 : Finset I) (A R L : I → F)
    (gamma1 gamma2 gamma3 c1 c2 c3 : F)
    (hgamma12 : gamma1 ≠ gamma2)
    (hgamma13 : gamma1 ≠ gamma3)
    (hgamma23 : gamma2 ≠ gamma3)
    (hdis12 : Disjoint E1 E2)
    (hdis13 : Disjoint E1 E3)
    (hdis23 : Disjoint E2 E3)
    (hanchor : ∃ i, i ∈ V ∧ i ∉ E1 ∧ i ∉ E2 ∧ i ∉ E3)
    (hL : ∀ i ∈ V, L i ≠ 0)
    (hrow1 : ∀ i ∈ V, i ∉ E1 →
      A i + gamma1 * R i = c1 * L i)
    (hrow2 : ∀ i ∈ V, i ∉ E2 →
      A i + gamma2 * R i = c2 * L i)
    (hrow3 : ∀ i ∈ V, i ∉ E3 →
      A i + gamma3 * R i = c3 * L i) :
    ∀ i ∈ V,
      A i + gamma1 * R i = c1 * L i ∧
      A i + gamma2 * R i = c2 * L i ∧
      A i + gamma3 * R i = c3 * L i := by
  obtain ⟨anchor, hanchorV, hanchor1, hanchor2, hanchor3⟩ := hanchor
  have hcoeff :
      (gamma1 - gamma2) * (c3 - c2) =
        (gamma3 - gamma2) * (c1 - c2) :=
    coefficient_collinear_of_three_rows
      (hL anchor hanchorV)
      (hrow1 anchor hanchorV hanchor1)
      (hrow2 anchor hanchorV hanchor2)
      (hrow3 anchor hanchorV hanchor3)
  have hcoeff231 :
      (gamma2 - gamma3) * (c1 - c3) =
        (gamma1 - gamma3) * (c2 - c3) := by
    linear_combination hcoeff
  have hcoeff132 :
      (gamma1 - gamma3) * (c2 - c3) =
        (gamma2 - gamma3) * (c1 - c3) := hcoeff231.symm
  intro i hiV
  by_cases hi1 : i ∈ E1
  · have hi2 : i ∉ E2 := by
      intro hi2
      exact Finset.disjoint_left.mp hdis12 hi1 hi2
    have hi3 : i ∉ E3 := by
      intro hi3
      exact Finset.disjoint_left.mp hdis13 hi1 hi3
    have hr2 := hrow2 i hiV hi2
    have hr3 := hrow3 i hiV hi3
    have hr1 := affine_third_value hgamma23 hcoeff231 hr2 hr3
    exact ⟨hr1, hr2, hr3⟩
  · have hr1 := hrow1 i hiV hi1
    by_cases hi2 : i ∈ E2
    · have hi3 : i ∉ E3 := by
        intro hi3
        exact Finset.disjoint_left.mp hdis23 hi2 hi3
      have hr3 := hrow3 i hiV hi3
      have hr2 := affine_third_value hgamma13 hcoeff132 hr1 hr3
      exact ⟨hr1, hr2, hr3⟩
    · have hr2 := hrow2 i hiV hi2
      have hr3 := affine_third_value hgamma12 hcoeff hr1 hr2
      exact ⟨hr1, hr2, hr3⟩

/-! ## Regular signatures -/

/-- The three source-core roots carried by a regular outsider. -/
noncomputable def regularRootTriple
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line : LineParameter F) (gamma : F) : Finset I :=
  fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
    jointCore dom (u 0) (u 1) line.1 line.2

/-- The coordinates outside the source core missed by a regular outsider. -/
noncomputable def regularMissedEdge
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line : LineParameter F) (gamma : F) : Finset I :=
  (Finset.univ \ jointCore dom (u 0) (u 1) line.1 line.2) \
    sourceFreshAgreement family line gamma

theorem eval_domainRootProduct_eq_zero_iff_mem
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

theorem sourceFreshAgreement_subset_coreComplement
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line : LineParameter F) (gamma : F) :
    sourceFreshAgreement family line gamma ⊆
      Finset.univ \ jointCore dom (u 0) (u 1) line.1 line.2 := by
  intro i hi
  exact Finset.mem_sdiff.mpr
    ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩

/-- A regular signature has a root triple and a missed edge of size two. -/
theorem regular_signature_cardinalities
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F}
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8)
    {gamma : F} (hgamma : gamma ∈ regularOutsideLine family line) :
    (regularRootTriple family line gamma).card = 3 ∧
      (regularMissedEdge family line gamma).card = 2 := by
  have hgammaData := hgamma
  simp only [regularOutsideLine, Finset.mem_filter] at hgammaData
  constructor
  · simpa only [regularRootTriple] using hgammaData.2.2.2
  · have hVcard :
        (Finset.univ \
          jointCore dom (u 0) (u 1) line.1 line.2).card = 8 := by
      rw [Finset.card_sdiff, Finset.inter_univ,
        Finset.card_univ, hn, hcore]
    rw [regularMissedEdge,
      Finset.card_sdiff_of_subset
        (sourceFreshAgreement_subset_coreComplement family line gamma),
      hVcard, hgammaData.2.1]

/-- The residual of a regular outsider is a nonzero scalar multiple of the
monic locator of its root triple. -/
theorem regular_residual_factorization
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    {gamma : F} (hgamma : gamma ∈ regularOutsideLine family line) :
    ∃ c : F, c ≠ 0 ∧
      lineResidual (family.q gamma) gamma line =
        C c * domainRootProduct dom (regularRootTriple family line gamma) := by
  have hgammaData := hgamma
  simp only [regularOutsideLine, Finset.mem_filter] at hgammaData
  have houtside := (mem_outsideLine_iff family line gamma).mp hgammaData.1
  have hp0 : lineResidual (family.q gamma) gamma line ≠ 0 := by
    simpa only [lineResidual, sub_ne_zero] using houtside.2
  have hlineDeg := lineParameter_degree_lt family hline
  have hpdeg :
      (lineResidual (family.q gamma) gamma line).natDegree < 4 :=
    lineResidual_natDegree_lt
      (family.degree_lt gamma houtside.1) hlineDeg.1 hlineDeg.2
  have hTcard : (regularRootTriple family line gamma).card = 4 - 1 := by
    simpa only [regularRootTriple] using hgammaData.2.2.2
  have hroot : ∀ i ∈ regularRootTriple family line gamma,
      (lineResidual (family.q gamma) gamma line).eval (dom i) = 0 := by
    intro i hi
    exact lineResidual_eval_eq_zero_of_mem_overlapRootBlock
      dom (u 0) (u 1) gamma (family.q gamma) line
        (by simpa only [regularRootTriple, overlapRootBlock] using hi)
  have hfactor := factorization_of_domain_root_subset_card_eq_pred
    dom (k := 4) (by norm_num)
      (lineResidual (family.q gamma) gamma line) hp0 hpdeg
      (regularRootTriple family line gamma) hTcard hroot
  exact ⟨(lineResidual (family.q gamma) gamma line).leadingCoeff,
    hfactor.2.1, hfactor.2.2⟩

/-- On a fresh agreement coordinate, residual factorization becomes the
affine-row equation used by the signature rigidity lemma. -/
theorem regular_affine_row_on_fresh
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line : LineParameter F) (gamma c : F)
    (hfactor :
      lineResidual (family.q gamma) gamma line =
        C c * domainRootProduct dom (regularRootTriple family line gamma))
    {i : I} (hi : i ∈ sourceFreshAgreement family line gamma) :
    (u 0 i - line.1.eval (dom i)) +
        gamma * (u 1 i - line.2.eval (dom i)) =
      c * (domainRootProduct dom
        (regularRootTriple family line gamma)).eval (dom i) := by
  have hiData := Finset.mem_sdiff.mp hi
  have hagree := hiData.1
  simp only [fullAgreement, Finset.mem_filter, Finset.mem_univ,
    true_and] at hagree
  have hev := congrArg (fun p : F[X] ↦ p.eval (dom i)) hfactor
  simp only [lineResidual, eval_sub, eval_add, eval_mul, eval_C] at hev
  rw [hagree] at hev
  linear_combination hev

/-- Conversely, a residual affine-row equation outside the source core is a
fresh agreement. -/
theorem mem_sourceFreshAgreement_of_affine_row
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line : LineParameter F) (gamma c : F)
    (hfactor :
      lineResidual (family.q gamma) gamma line =
        C c * domainRootProduct dom (regularRootTriple family line gamma))
    {i : I}
    (hiV : i ∈ Finset.univ \
      jointCore dom (u 0) (u 1) line.1 line.2)
    (hrow :
      (u 0 i - line.1.eval (dom i)) +
          gamma * (u 1 i - line.2.eval (dom i)) =
        c * (domainRootProduct dom
          (regularRootTriple family line gamma)).eval (dom i)) :
    i ∈ sourceFreshAgreement family line gamma := by
  have hev := congrArg (fun p : F[X] ↦ p.eval (dom i)) hfactor
  simp only [lineResidual, eval_sub, eval_add, eval_mul, eval_C] at hev
  apply Finset.mem_sdiff.mpr
  constructor
  · simp only [fullAgreement, Finset.mem_filter, Finset.mem_univ, true_and]
    linear_combination hev - hrow
  · exact (Finset.mem_sdiff.mp hiV).2

/-- **Three equal-root regular signatures cannot have pairwise-disjoint
missed edges.**  This is the polynomial constraint absent from the bare
`(triple, edge)` set system. -/
theorem not_pairwise_disjoint_missedEdges_of_three_regular_same_rootTriple
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8)
    {gamma1 gamma2 gamma3 : F}
    (hgamma1 : gamma1 ∈ regularOutsideLine family line)
    (hgamma2 : gamma2 ∈ regularOutsideLine family line)
    (hgamma3 : gamma3 ∈ regularOutsideLine family line)
    (hgamma12 : gamma1 ≠ gamma2)
    (hgamma13 : gamma1 ≠ gamma3)
    (hgamma23 : gamma2 ≠ gamma3)
    (hroot12 : regularRootTriple family line gamma1 =
      regularRootTriple family line gamma2)
    (hroot13 : regularRootTriple family line gamma1 =
      regularRootTriple family line gamma3) :
    ¬ (Disjoint (regularMissedEdge family line gamma1)
          (regularMissedEdge family line gamma2) ∧
        Disjoint (regularMissedEdge family line gamma1)
          (regularMissedEdge family line gamma3) ∧
        Disjoint (regularMissedEdge family line gamma2)
          (regularMissedEdge family line gamma3)) := by
  rintro ⟨hdis12, hdis13, hdis23⟩
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let V : Finset I := Finset.univ \ D
  let T := regularRootTriple family line gamma1
  let E1 := regularMissedEdge family line gamma1
  let E2 := regularMissedEdge family line gamma2
  let E3 := regularMissedEdge family line gamma3
  obtain ⟨c1, hc1, hfactor1⟩ :=
    regular_residual_factorization family hline hgamma1
  obtain ⟨c2, hc2, hfactor2⟩ :=
    regular_residual_factorization family hline hgamma2
  obtain ⟨c3, hc3, hfactor3⟩ :=
    regular_residual_factorization family hline hgamma3
  have hVcard : V.card = 8 := by
    simp only [V, D, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, hn, hcore]
  have hE1card : E1.card = 2 := by
    simpa only [E1] using
      (regular_signature_cardinalities family hn hcore hgamma1).2
  have hE2card : E2.card = 2 := by
    simpa only [E2] using
      (regular_signature_cardinalities family hn hcore hgamma2).2
  have hE3card : E3.card = 2 := by
    simpa only [E3] using
      (regular_signature_cardinalities family hn hcore hgamma3).2
  have hE1sub : E1 ⊆ V := by
    intro i hi
    exact (Finset.mem_sdiff.mp hi).1
  have hE2sub : E2 ⊆ V := by
    intro i hi
    exact (Finset.mem_sdiff.mp hi).1
  have hE3sub : E3 ⊆ V := by
    intro i hi
    exact (Finset.mem_sdiff.mp hi).1
  have hdis12' : Disjoint E1 E2 := by
    simpa only [E1, E2] using hdis12
  have hdis13' : Disjoint E1 E3 := by
    simpa only [E1, E3] using hdis13
  have hdis23' : Disjoint E2 E3 := by
    simpa only [E2, E3] using hdis23
  have hdisUnion : Disjoint (E1 ∪ E2) E3 :=
    Finset.disjoint_union_left.mpr ⟨hdis13', hdis23'⟩
  have hUnionCard : (E1 ∪ E2 ∪ E3).card = 6 := by
    rw [Finset.card_union_of_disjoint hdisUnion,
      Finset.card_union_of_disjoint hdis12',
      hE1card, hE2card, hE3card]
  have hUnionSub : E1 ∪ E2 ∪ E3 ⊆ V :=
    Finset.union_subset (Finset.union_subset hE1sub hE2sub) hE3sub
  obtain ⟨anchor, hanchorV, hanchorUnion⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card
      (s := E1 ∪ E2 ∪ E3) (t := V) (by omega)
  have hanchor :
      ∃ i, i ∈ V ∧ i ∉ E1 ∧ i ∉ E2 ∧ i ∉ E3 := by
    refine ⟨anchor, hanchorV, ?_, ?_, ?_⟩
    · intro hi
      exact hanchorUnion (by simp [hi])
    · intro hi
      exact hanchorUnion (by simp [hi])
    · intro hi
      exact hanchorUnion (by simp [hi])
  let A : I → F := fun i ↦ u 0 i - line.1.eval (dom i)
  let R : I → F := fun i ↦ u 1 i - line.2.eval (dom i)
  let L : I → F := fun i ↦ (domainRootProduct dom T).eval (dom i)
  have hTsubD : T ⊆ D := by
    intro i hi
    exact (Finset.mem_inter.mp hi).2
  have hL : ∀ i ∈ V, L i ≠ 0 := by
    intro i hiV
    have hiD : i ∉ D := (Finset.mem_sdiff.mp hiV).2
    have hiT : i ∉ T := fun hi ↦ hiD (hTsubD hi)
    exact (eval_domainRootProduct_eq_zero_iff_mem dom T i).not.mpr hiT
  have hrow1 : ∀ i ∈ V, i ∉ E1 →
      A i + gamma1 * R i = c1 * L i := by
    intro i hiV hiE
    have hiFresh : i ∈ sourceFreshAgreement family line gamma1 := by
      by_contra hi
      apply hiE
      exact Finset.mem_sdiff.mpr ⟨hiV, hi⟩
    simpa only [A, R, L, T] using
      regular_affine_row_on_fresh
        family line gamma1 c1 hfactor1 hiFresh
  have hrow2 : ∀ i ∈ V, i ∉ E2 →
      A i + gamma2 * R i = c2 * L i := by
    intro i hiV hiE
    have hiFresh : i ∈ sourceFreshAgreement family line gamma2 := by
      by_contra hi
      apply hiE
      exact Finset.mem_sdiff.mpr ⟨hiV, hi⟩
    have hrow := regular_affine_row_on_fresh
      family line gamma2 c2 hfactor2 hiFresh
    rw [← hroot12] at hrow
    simpa only [A, R, L, T] using hrow
  have hrow3 : ∀ i ∈ V, i ∉ E3 →
      A i + gamma3 * R i = c3 * L i := by
    intro i hiV hiE
    have hiFresh : i ∈ sourceFreshAgreement family line gamma3 := by
      by_contra hi
      apply hiE
      exact Finset.mem_sdiff.mpr ⟨hiV, hi⟩
    have hrow := regular_affine_row_on_fresh
      family line gamma3 c3 hfactor3 hiFresh
    rw [← hroot13] at hrow
    simpa only [A, R, L, T] using hrow
  have hfilled := affine_rows_fill_pairwise_disjoint_misses
    V E1 E2 E3 A R L gamma1 gamma2 gamma3 c1 c2 c3
      hgamma12 hgamma13 hgamma23 hdis12' hdis13' hdis23'
      hanchor hL hrow1 hrow2 hrow3
  have hE1pos : 0 < E1.card := by omega
  obtain ⟨i, hiE1⟩ := Finset.card_pos.mp hE1pos
  have hiV := hE1sub hiE1
  have hiFilled := (hfilled i hiV).1
  have hiFresh : i ∈ sourceFreshAgreement family line gamma1 := by
    apply mem_sourceFreshAgreement_of_affine_row
      family line gamma1 c1 hfactor1 hiV
    simpa only [A, R, L, T] using hiFilled
  exact (Finset.mem_sdiff.mp hiE1).2 hiFresh

/-- Intersecting missed edges leave at least five coordinates on which both
regular outsiders agree freshly. -/
theorem five_le_fresh_inter_of_not_disjoint_missedEdges
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F}
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8)
    {gamma beta : F}
    (hgamma : gamma ∈ regularOutsideLine family line)
    (hbeta : beta ∈ regularOutsideLine family line)
    (hnotDisjoint : ¬ Disjoint (regularMissedEdge family line gamma)
      (regularMissedEdge family line beta)) :
    5 ≤ (sourceFreshAgreement family line gamma ∩
      sourceFreshAgreement family line beta).card := by
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let V : Finset I := Finset.univ \ D
  let Sg := sourceFreshAgreement family line gamma
  let Sb := sourceFreshAgreement family line beta
  let Eg := regularMissedEdge family line gamma
  let Eb := regularMissedEdge family line beta
  have hgammaData := hgamma
  have hbetaData := hbeta
  simp only [regularOutsideLine, Finset.mem_filter] at hgammaData hbetaData
  have hSgcard : Sg.card = 6 := by
    simpa only [Sg] using hgammaData.2.1
  have hSbcard : Sb.card = 6 := by
    simpa only [Sb] using hbetaData.2.1
  have hVcard : V.card = 8 := by
    simp only [V, D, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, hn, hcore]
  have hSgsub : Sg ⊆ V := by
    simpa only [Sg, V, D] using
      sourceFreshAgreement_subset_coreComplement family line gamma
  have hSbsub : Sb ⊆ V := by
    simpa only [Sb, V, D] using
      sourceFreshAgreement_subset_coreComplement family line beta
  have hnotDisjoint' : ¬ Disjoint Eg Eb := by
    simpa only [Eg, Eb] using hnotDisjoint
  obtain ⟨x, hxEg, hxEb⟩ := Finset.not_disjoint_iff.mp hnotDisjoint'
  have hxV : x ∈ V := (Finset.mem_sdiff.mp hxEg).1
  have hxSg : x ∉ Sg := (Finset.mem_sdiff.mp hxEg).2
  have hxSb : x ∉ Sb := (Finset.mem_sdiff.mp hxEb).2
  have hUnionSub : Sg ∪ Sb ⊆ V \ {x} := by
    intro i hi
    have hiCases := Finset.mem_union.mp hi
    apply Finset.mem_sdiff.mpr
    constructor
    · exact hiCases.elim (fun hi ↦ hSgsub hi) (fun hi ↦ hSbsub hi)
    · simp only [Finset.mem_singleton]
      intro hix
      subst i
      exact hiCases.elim hxSg hxSb
  have hVxcard : (V \ {x}).card = 7 := by
    rw [Finset.card_sdiff_of_subset
      (Finset.singleton_subset_iff.mpr hxV), hVcard, Finset.card_singleton]
  have hUnionCard : (Sg ∪ Sb).card ≤ 7 :=
    (Finset.card_le_card hUnionSub).trans_eq hVxcard
  have hbook := Finset.card_union_add_card_inter Sg Sb
  change 5 ≤ (Sg ∩ Sb).card
  omega

/-- Two equal-root regular outsiders with intersecting missed edges determine
a relevant secant core of size at least eight and source-core overlap exactly
three. -/
theorem exists_overlap_three_high_core_of_equal_root_not_disjoint_missedEdges
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F}
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8)
    {gamma beta : F}
    (hgamma : gamma ∈ regularOutsideLine family line)
    (hbeta : beta ∈ regularOutsideLine family line)
    (hne : gamma ≠ beta)
    (hroot : regularRootTriple family line gamma =
      regularRootTriple family line beta)
    (hnotDisjoint : ¬ Disjoint (regularMissedEdge family line gamma)
      (regularMissedEdge family line beta)) :
    ∃ line2 ∈ lineParameters family,
      8 ≤ (jointCore dom (u 0) (u 1) line2.1 line2.2).card ∧
      (jointCore dom (u 0) (u 1) line.1 line.2 ∩
        jointCore dom (u 0) (u 1) line2.1 line2.2).card = 3 := by
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let T := regularRootTriple family line gamma
  let Sg := sourceFreshAgreement family line gamma
  let Sb := sourceFreshAgreement family line beta
  let line2 := secantParameter family gamma beta
  let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
  have hgammaData := hgamma
  have hbetaData := hbeta
  simp only [regularOutsideLine, Finset.mem_filter] at hgammaData hbetaData
  have hgammaOut := (mem_outsideLine_iff family line gamma).mp hgammaData.1
  have hbetaOut := (mem_outsideLine_iff family line beta).mp hbetaData.1
  have hline2 : line2 ∈ lineParameters family :=
    secantParameter_mem_lineParameters family
      hgammaOut.1 hbetaOut.1 hne
  have hgammaOn : gamma ∈ pointsOn family line2 :=
    first_point_mem_pointsOn_secant family hgammaOut.1
  have hbetaOn : beta ∈ pointsOn family line2 :=
    second_point_mem_pointsOn_secant family hbetaOut.1 hne
  have hgammaEq := (mem_pointsOn_iff family line2 gamma).mp hgammaOn |>.2
  have hbetaEq := (mem_pointsOn_iff family line2 beta).mp hbetaOn |>.2
  have hcoreEq :
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
          fullAgreement dom (u 0) (u 1) beta (family.q beta) = D2 := by
    dsimp only [D2]
    rw [hgammaEq, hbetaEq]
    exact fullAgreement_inter_eq_jointCore
      dom (u 0) (u 1) line2.1 line2.2 hne
  have hTcard : T.card = 3 := by
    simpa only [T, regularRootTriple] using hgammaData.2.2.2
  have hinterD : D2 ∩ D = T := by
    rw [← hcoreEq]
    ext i
    simp only [T, regularRootTriple, D, Finset.mem_inter]
    constructor
    · rintro ⟨⟨hiGamma, _hiBeta⟩, hiD⟩
      exact ⟨hiGamma, hiD⟩
    · intro hiT
      have hiGamma : i ∈
          fullAgreement dom (u 0) (u 1) gamma (family.q gamma) := hiT.1
      have hiD : i ∈ D := hiT.2
      have hiGammaRoot : i ∈ regularRootTriple family line gamma := by
        exact Finset.mem_inter.mpr hiT
      have hiBetaRoot : i ∈ regularRootTriple family line beta := by
        rw [← hroot]
        exact hiGammaRoot
      exact ⟨⟨hiGamma, (Finset.mem_inter.mp hiBetaRoot).1⟩, hiD⟩
  have hfreshEq : D2 \ D = Sg ∩ Sb := by
    rw [← hcoreEq]
    ext i
    simp only [Sg, Sb, sourceFreshAgreement, D,
      Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro ⟨⟨hiGamma, hiBeta⟩, hiD⟩
      exact ⟨⟨hiGamma, hiD⟩, ⟨hiBeta, hiD⟩⟩
    · rintro ⟨⟨hiGamma, hiD⟩, ⟨hiBeta, _⟩⟩
      exact ⟨⟨hiGamma, hiBeta⟩, hiD⟩
  have hfresh : 5 ≤ (Sg ∩ Sb).card := by
    simpa only [Sg, Sb] using
      five_le_fresh_inter_of_not_disjoint_missedEdges
        family hn hcore hgamma hbeta hnotDisjoint
  have hsplit := Finset.card_sdiff_add_card_inter D2 D
  refine ⟨line2, hline2, ?_, ?_⟩
  · change 8 ≤ D2.card
    rw [hfreshEq, hinterD] at hsplit
    omega
  · change (D ∩ D2).card = 3
    rw [Finset.inter_comm, hinterD, hTcard]

/-- **Three equal-root outsiders force the desired overlap-three high core.** -/
theorem exists_overlap_three_high_core_of_three_regular_same_rootTriple
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8)
    {gamma1 gamma2 gamma3 : F}
    (hgamma1 : gamma1 ∈ regularOutsideLine family line)
    (hgamma2 : gamma2 ∈ regularOutsideLine family line)
    (hgamma3 : gamma3 ∈ regularOutsideLine family line)
    (hgamma12 : gamma1 ≠ gamma2)
    (hgamma13 : gamma1 ≠ gamma3)
    (hgamma23 : gamma2 ≠ gamma3)
    (hroot12 : regularRootTriple family line gamma1 =
      regularRootTriple family line gamma2)
    (hroot13 : regularRootTriple family line gamma1 =
      regularRootTriple family line gamma3) :
    ∃ line2 ∈ lineParameters family,
      8 ≤ (jointCore dom (u 0) (u 1) line2.1 line2.2).card ∧
      (jointCore dom (u 0) (u 1) line.1 line.2 ∩
        jointCore dom (u 0) (u 1) line2.1 line2.2).card = 3 := by
  have hnotAll :=
    not_pairwise_disjoint_missedEdges_of_three_regular_same_rootTriple
      family hn hline hcore hgamma1 hgamma2 hgamma3
      hgamma12 hgamma13 hgamma23 hroot12 hroot13
  by_cases hdis12 : Disjoint (regularMissedEdge family line gamma1)
      (regularMissedEdge family line gamma2)
  · by_cases hdis13 : Disjoint (regularMissedEdge family line gamma1)
        (regularMissedEdge family line gamma3)
    · have hnotDis23 : ¬ Disjoint (regularMissedEdge family line gamma2)
          (regularMissedEdge family line gamma3) := by
        intro hdis23
        exact hnotAll ⟨hdis12, hdis13, hdis23⟩
      apply exists_overlap_three_high_core_of_equal_root_not_disjoint_missedEdges
        family hn hcore hgamma2 hgamma3 hgamma23
          (hroot12.symm.trans hroot13) hnotDis23
    · exact exists_overlap_three_high_core_of_equal_root_not_disjoint_missedEdges
        family hn hcore hgamma1 hgamma3 hgamma13 hroot13 hdis13
  · exact exists_overlap_three_high_core_of_equal_root_not_disjoint_missedEdges
      family hn hcore hgamma1 hgamma2 hgamma12 hroot12 hdis12

/-- Under the surviving global core cap, the forced high core has size
exactly eight, matching the overlap-three closure interface. -/
theorem exists_overlap_three_core_eq_eight_of_three_regular_same_rootTriple
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8)
    (hcoreCap : ∀ line2 ∈ lineParameters family,
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card ≤ 8)
    {gamma1 gamma2 gamma3 : F}
    (hgamma1 : gamma1 ∈ regularOutsideLine family line)
    (hgamma2 : gamma2 ∈ regularOutsideLine family line)
    (hgamma3 : gamma3 ∈ regularOutsideLine family line)
    (hgamma12 : gamma1 ≠ gamma2)
    (hgamma13 : gamma1 ≠ gamma3)
    (hgamma23 : gamma2 ≠ gamma3)
    (hroot12 : regularRootTriple family line gamma1 =
      regularRootTriple family line gamma2)
    (hroot13 : regularRootTriple family line gamma1 =
      regularRootTriple family line gamma3) :
    ∃ line2 ∈ lineParameters family,
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 8 ∧
      (jointCore dom (u 0) (u 1) line.1 line.2 ∩
        jointCore dom (u 0) (u 1) line2.1 line2.2).card = 3 := by
  obtain ⟨line2, hline2, hcore2, hinter⟩ :=
    exists_overlap_three_high_core_of_three_regular_same_rootTriple
      family hn hline hcore hgamma1 hgamma2 hgamma3
        hgamma12 hgamma13 hgamma23 hroot12 hroot13
  exact ⟨line2, hline2, Nat.le_antisymm (hcoreCap line2 hline2) hcore2,
    hinter⟩

#print axioms affine_rows_fill_pairwise_disjoint_misses
#print axioms regular_signature_cardinalities
#print axioms regular_residual_factorization
#print axioms regular_affine_row_on_fresh
#print axioms not_pairwise_disjoint_missedEdges_of_three_regular_same_rootTriple
#print axioms five_le_fresh_inter_of_not_disjoint_missedEdges
#print axioms exists_overlap_three_high_core_of_equal_root_not_disjoint_missedEdges
#print axioms exists_overlap_three_high_core_of_three_regular_same_rootTriple
#print axioms exists_overlap_three_core_eq_eight_of_three_regular_same_rootTriple

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourRegularSignatureRigidity
