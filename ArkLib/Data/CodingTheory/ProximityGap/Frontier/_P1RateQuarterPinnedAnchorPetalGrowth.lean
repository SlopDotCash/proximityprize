/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterHighCorePetalGrowth
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterScaleArithmetic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ConstantWeightPlotkinBound

/-!
# P1 pinned-anchor fresh-petal growth

At the literal P1 predecessor, an isolated two-point secant with core at least
`327272221` has complement size at most `746469603`.  Every outsider contributes
at least `T-(K-1)=324359511` fresh agreement coordinates in that complement.
The exact reduced Rankin budget

`746469603 * 140942232 <= 324359511^2 - 1`

therefore forces two outsiders whose fresh intersection—and hence canonical
secant petal—has size at least `140942233`.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterPinnedAnchorPetalGrowth

open HalfPredecessorLineCoreGeometry
open HalfPredecessorSecantLines
open HalfPredecessorBadEventRichPointBridge
open HalfPredecessorLargeCoreCollapse
open HalfPredecessorRateQuarterFreshPetalPruning
open HalfPredecessorRateQuarterHighCorePetalGrowth
open P1RateQuarterScaleArithmetic

attribute [local instance] Classical.propDecidable

abbrev T : Nat := 592794966

theorem pinnedAnchor_reduced_rankin_budget :
    746469603 * 140942232 ≤ 324359511 ^ 2 - 1 := by norm_num

/-- **Pinned-anchor petal growth.**  In an over-budget P1 family, an isolated
two-point line with core at least `327272221` forces a fresh outsider secant
petal of size at least `140942233`. -/
theorem exists_outside_secantPetal_card_ge_140942233
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hover : N < family.G.card)
    (hthreshold : T ≤
      ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore : 327272221 ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card)
    (htwo : (pointsOn family line).card = 2) :
    ∃ gamma ∈ outsideLine family line,
      ∃ beta ∈ outsideLine family line, gamma ≠ beta ∧
        140942233 ≤ (secantPetal family line gamma beta).card := by
  classical
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let V : Finset (Fin N) := Finset.univ \ D
  let K := {gamma // gamma ∈ outsideLine family line}
  let A : K → Finset (Fin N) := fun gamma =>
    fullAgreement dom (u 0) (u 1) gamma.1 (family.q gamma.1) \ D
  have hVcard : V.card = N - D.card := by
    simp only [V, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, Fintype.card_fin]
  have hVle : V.card ≤ 746469603 := by
    rw [hVcard]
    change 327272221 ≤ D.card at hcore
    have hN : N = 1073741824 := by norm_num [N]
    omega
  have hAsub : ∀ gamma : K, A gamma ⊆ V := by
    intro gamma x hx
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
  have hAsize : ∀ gamma : K, 324359511 ≤ (A gamma).card := by
    intro gamma
    have hfresh := threshold_sub_pred_le_fresh_card
      family line (by norm_num [k]) hline gamma.2
    have hmono : T - (k - 1) ≤
        ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊ - (k - 1) :=
      Nat.sub_le_sub_right hthreshold (k - 1)
    have hTk : T - (k - 1) = 324359511 := by norm_num [T, k]
    rw [hTk] at hmono
    exact hmono.trans (by simpa only [A, D] using hfresh)
  by_contra hnot
  push_neg at hnot
  have hpair : Pairwise fun gamma beta : K =>
      (A gamma ∩ A beta).card ≤ 140942232 := by
    intro gamma beta hne
    have hvalue : gamma.1 ≠ beta.1 := fun heq => hne (Subtype.ext heq)
    have heq : A gamma ∩ A beta = secantPetal family line gamma.1 beta.1 := by
      simpa only [A, D] using fresh_inter_eq_secantPetal
        family line
          ((mem_outsideLine_iff family line gamma.1).mp gamma.2).1
          ((mem_outsideLine_iff family line beta.1).mp beta.2).1 hvalue
    rw [heq]
    have hlt := hnot gamma.1 gamma.2 beta.1 beta.2 hvalue
    omega
  have hbudget : V.card * 140942232 ≤ 324359511 ^ 2 - 1 :=
    (Nat.mul_le_mul_right 140942232 hVle).trans pinnedAnchor_reduced_rankin_budget
  have houtside := card_le_finset_of_card_ge_pair_inter_le
    V A 324359511 140942232 (by norm_num) hAsub hAsize hpair hbudget
  have houtsideCard : (outsideLine family line).card = family.G.card - 2 := by
    have hpartition := pointsOn_card_add_outsideLine_card family line
    omega
  simp only [K, Fintype.card_coe] at houtside
  rw [houtsideCard, hVcard] at houtside
  have hD : 327272221 ≤ D.card := hcore
  have hN : N = 1073741824 := by norm_num [N]
  omega

/-- Geometric form: the forced petal is contained in the joint core of a
distinct relevant outsider secant line. -/
theorem exists_distinct_outsideLine_core_ge_140942233
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hover : N < family.G.card)
    (hthreshold : T ≤
      ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore : 327272221 ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card)
    (htwo : (pointsOn family line).card = 2) :
    ∃ line2 ∈ lineParameters family, line2 ≠ line ∧
      140942233 ≤ (jointCore dom (u 0) (u 1) line2.1 line2.2).card := by
  obtain ⟨gamma, hgamma, beta, hbeta, hne, hpetal⟩ :=
    exists_outside_secantPetal_card_ge_140942233
      family hover hthreshold hline hcore htwo
  exact exists_second_high_core_of_large_petal
    family hgamma hbeta hne hpetal

/-! ## Two-core recursive supply -/

/-- Selected scalars lying on neither of two relevant lines. -/
noncomputable def outsideBothLines
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (line1 line2 : LineParameter F) : Finset F :=
  family.G \ (pointsOn family line1 ∪ pointsOn family line2)

/-- The isolated anchor and a second `140,942,233`-core line leave at least
`140,942,232` selected points off both lines. -/
theorem outsideBothLines_card_ge_140942232
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hover : N < family.G.card)
    (line1 line2 : LineParameter F)
    (hline2 : line2 ∈ lineParameters family)
    (htwo : (pointsOn family line1).card = 2)
    (hcore2 : 140942233 ≤
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card) :
    140942232 ≤ (outsideBothLines family line1 line2).card := by
  have hline2card := pointsOn_card_le_core_complement family
    (h := 536870912) (by norm_num [N]) hline2
  have hunion := Finset.card_union_le
    (pointsOn family line1) (pointsOn family line2)
  have hsub : pointsOn family line1 ∪ pointsOn family line2 ⊆ family.G :=
    Finset.union_subset (pointsOn_subset_G family line1)
      (pointsOn_subset_G family line2)
  have hpartition := Finset.card_sdiff_add_card_inter family.G
    (pointsOn family line1 ∪ pointsOn family line2)
  have hinter : family.G ∩ (pointsOn family line1 ∪ pointsOn family line2) =
      pointsOn family line1 ∪ pointsOn family line2 := by
    exact Finset.inter_eq_right.mpr hsub
  rw [hinter] at hpartition
  change (outsideBothLines family line1 line2).card +
      (pointsOn family line1 ∪ pointsOn family line2).card = family.G.card at hpartition
  have hN : N = 1073741824 := by norm_num [N]
  omega

/-- Every selected point off both distinct relevant lines retains at least
`T-2*(k-1)=55,924,056` agreement coordinates outside the two-core union. -/
theorem twoCore_fresh_card_ge_55924056
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hthreshold : T ≤
      ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    {gamma : F} (hgamma : gamma ∈ outsideBothLines family line1 line2) :
    55924056 ≤
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) \
        (jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
          jointCore dom (u 0) (u 1) line2.1 line2.2)).card := by
  let A := fullAgreement dom (u 0) (u 1) gamma (family.q gamma)
  let D1 := jointCore dom (u 0) (u 1) line1.1 line1.2
  let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
  have hgammaG : gamma ∈ family.G := (Finset.mem_sdiff.mp hgamma).1
  have hnot := (Finset.mem_sdiff.mp hgamma).2
  simp only [Finset.mem_union, not_or] at hnot
  have hnot1 : family.q gamma ≠ line1.1 + C gamma * line1.2 := by
    intro heq
    exact hnot.1 ((mem_pointsOn_iff family line1 gamma).mpr ⟨hgammaG, heq⟩)
  have hnot2 : family.q gamma ≠ line2.1 + C gamma * line2.2 := by
    intro heq
    exact hnot.2 ((mem_pointsOn_iff family line2 gamma).mpr ⟨hgammaG, heq⟩)
  have hdegq := family.degree_lt gamma hgammaG
  have hdeg1 := lineParameter_degree_lt family hline1
  have hdeg2 := lineParameter_degree_lt family hline2
  have hcap1 : (A ∩ D1).card ≤ k - 1 := by
    exact fullAgreement_inter_jointCore_card_le dom (u 0) (u 1)
      (by norm_num [k]) hdegq hdeg1.1 hdeg1.2 hnot1
  have hcap2 : (A ∩ D2).card ≤ k - 1 := by
    exact fullAgreement_inter_jointCore_card_le dom (u 0) (u 1)
      (by norm_num [k]) hdegq hdeg2.1 hdeg2.2 hnot2
  have hsplit := Finset.card_sdiff_add_card_inter A (D1 ∪ D2)
  have hinterSub : A ∩ (D1 ∪ D2) ⊆ (A ∩ D1) ∪ (A ∩ D2) := by
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_union] at hx ⊢
    exact hx.2.elim (fun h => Or.inl ⟨hx.1, h⟩) (fun h => Or.inr ⟨hx.1, h⟩)
  have hinter : (A ∩ (D1 ∪ D2)).card ≤ 2 * (k - 1) := by
    exact (Finset.card_le_card hinterSub).trans
      ((Finset.card_union_le _ _).trans (by omega))
  have hA : T ≤ A.card := hthreshold.trans (family.threshold_le gamma hgammaG)
  have hTk : T - 2 * (k - 1) = 55924056 := by norm_num [T, k]
  change 55924056 ≤ (A \ (D1 ∪ D2)).card
  omega

/-! ## Next reduced Plotkin rung -/

/-- The pinned anchor and its forced disjoint petal cover at least `468,214,454`
coordinates, leaving at most `605,527,370`. -/
theorem twoCore_union_complement_ceiling_eq :
    N - (327272221 + 140942233) = 605527370 := by
  norm_num [N]

/-- At the certified outside-both population and fresh weight, a pairwise
intersection cap `5,164,919` violates exact constant-weight Plotkin.  Thus the
next extraction target is a third petal of size at least `5,164,920`. -/
theorem twoCore_reduced_plotkin_forces_5164920 :
    ¬ 140942232 * (55924056 ^ 2 - 605527370 * 5164919) ≤
      605527370 * (55924056 - 5164919) := by
  norm_num

/-- The genuinely new part of a secant core beyond two established cores. -/
noncomputable def secantPetalOutsideTwo
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (line1 line2 : LineParameter F) (gamma beta : F) : Finset (Fin N) :=
  jointCore dom (u 0) (u 1)
      (secantParameter family gamma beta).1
      (secantParameter family gamma beta).2 \
    (jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
      jointCore dom (u 0) (u 1) line2.1 line2.2)

/-- **Third recursive petal.**  If the second core contributes the certified
`140,942,233` coordinates outside the isolated pinned anchor, exact reduced
Plotkin forces two points off both lines whose secant core contributes at
least `5,164,920` further coordinates outside both established cores. -/
theorem exists_outsideBoth_secantPetal_card_ge_5164920
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hover : N < family.G.card)
    (hthreshold : T ≤
      ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (htwo : (pointsOn family line1).card = 2)
    (hcore1 : 327272221 ≤
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card)
    (hpetal2 : 140942233 ≤
      (jointCore dom (u 0) (u 1) line2.1 line2.2 \
        jointCore dom (u 0) (u 1) line1.1 line1.2).card) :
    ∃ gamma ∈ outsideBothLines family line1 line2,
      ∃ beta ∈ outsideBothLines family line1 line2, gamma ≠ beta ∧
        5164920 ≤ (secantPetalOutsideTwo family line1 line2 gamma beta).card := by
  classical
  let D1 := jointCore dom (u 0) (u 1) line1.1 line1.2
  let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
  let V : Finset (Fin N) := Finset.univ \ (D1 ∪ D2)
  let K := {gamma // gamma ∈ outsideBothLines family line1 line2}
  let A : K → Finset (Fin N) := fun gamma =>
    fullAgreement dom (u 0) (u 1) gamma.1 (family.q gamma.1) \ (D1 ∪ D2)
  have hcore2 : 140942233 ≤ D2.card := by
    exact hpetal2.trans (Finset.card_le_card Finset.sdiff_subset)
  have hKcard : 140942232 ≤ Fintype.card K := by
    simpa only [K, Fintype.card_coe] using
      outsideBothLines_card_ge_140942232
        family hover line1 line2 hline2 htwo hcore2
  have hVcard : V.card = N - (D1 ∪ D2).card := by
    simp only [V, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, Fintype.card_fin]
  have hunionLower : 327272221 + 140942233 ≤ (D1 ∪ D2).card := by
    have hsplit := Finset.card_sdiff_add_card D2 D1
    have hD1 : 327272221 ≤ D1.card := hcore1
    have hpetal : 140942233 ≤ (D2 \ D1).card := hpetal2
    have hunion := Finset.card_union_add_card_inter D1 D2
    have hD2split := Finset.card_sdiff_add_card_inter D2 D1
    rw [Finset.inter_comm] at hD2split
    omega
  have hVle : V.card ≤ 605527370 := by
    rw [hVcard]
    have hN : N = 1073741824 := by norm_num [N]
    omega
  have hAsub : ∀ gamma : K, A gamma ⊆ V := by
    intro gamma x hx
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
  have hAsize : ∀ gamma : K, 55924056 ≤ (A gamma).card := by
    intro gamma
    simpa only [A, D1, D2] using twoCore_fresh_card_ge_55924056
      family hthreshold line1 line2 hline1 hline2 gamma.2
  by_contra hnot
  push_neg at hnot
  let S : K → Finset (Fin N) := fun gamma =>
    Classical.choose (Finset.exists_subset_card_eq (hAsize gamma))
  have hSsub : ∀ gamma, S gamma ⊆ A gamma := fun gamma =>
    (Classical.choose_spec (Finset.exists_subset_card_eq (hAsize gamma))).1
  have hScard : ∀ gamma, (S gamma).card = 55924056 := fun gamma =>
    (Classical.choose_spec (Finset.exists_subset_card_eq (hAsize gamma))).2
  have hSV : ∀ gamma, S gamma ⊆ V := fun gamma =>
    (hSsub gamma).trans (hAsub gamma)
  let R : K → Finset V := fun gamma => restrictTo V (S gamma)
  have hRcard : ∀ gamma, (R gamma).card = 55924056 := by
    intro gamma
    exact (card_restrictTo V (S gamma) (hSV gamma)).trans (hScard gamma)
  have hRpair : Pairwise fun gamma beta : K =>
      (R gamma ∩ R beta).card ≤ 5164919 := by
    intro gamma beta hne
    have hvalue : gamma.1 ≠ beta.1 := fun heq => hne (Subtype.ext heq)
    rw [show R gamma = restrictTo V (S gamma) by rfl,
      show R beta = restrictTo V (S beta) by rfl, ← restrictTo_inter]
    rw [card_restrictTo V (S gamma ∩ S beta)]
    · have hsubA : S gamma ∩ S beta ⊆ A gamma ∩ A beta :=
        Finset.inter_subset_inter (hSsub gamma) (hSsub beta)
      have hcommon : A gamma ∩ A beta ⊆
          secantPetalOutsideTwo family line1 line2 gamma.1 beta.1 := by
        intro x hx
        have hx' := hx
        simp only [A, Finset.mem_inter, Finset.mem_sdiff] at hx'
        have hfull : x ∈ fullAgreement dom (u 0) (u 1) gamma.1 (family.q gamma.1) ∩
            fullAgreement dom (u 0) (u 1) beta.1 (family.q beta.1) := by
          exact Finset.mem_inter.mpr ⟨hx'.1.1, hx'.2.1⟩
        let line3 := secantParameter family gamma.1 beta.1
        have hgammaOn : gamma.1 ∈ pointsOn family line3 :=
          first_point_mem_pointsOn_secant family
            ((Finset.mem_sdiff.mp gamma.2).1)
        have hbetaOn : beta.1 ∈ pointsOn family line3 :=
          second_point_mem_pointsOn_secant family
            ((Finset.mem_sdiff.mp beta.2).1) hvalue
        have hgammaLine := (mem_pointsOn_iff family line3 gamma.1).mp hgammaOn |>.2
        have hbetaLine := (mem_pointsOn_iff family line3 beta.1).mp hbetaOn |>.2
        have hfull3 : x ∈ jointCore dom (u 0) (u 1) line3.1 line3.2 := by
          rw [← fullAgreement_inter_eq_jointCore
            dom (u 0) (u 1) line3.1 line3.2 hvalue]
          simpa only [hgammaLine, hbetaLine] using hfull
        exact Finset.mem_sdiff.mpr ⟨hfull3, hx'.1.2⟩
      have hle := Finset.card_le_card (hsubA.trans hcommon)
      have hlt := hnot gamma.1 gamma.2 beta.1 beta.2 hvalue
      omega
    · exact Finset.inter_subset_left.trans (hSV gamma)
  have hplot := ConstantWeightPlotkinBound.constantWeight_plotkin
    R 55924056 5164919 hRcard hRpair
  simp only [Fintype.card_coe] at hplot
  have hgap : 55924056 ^ 2 - 605527370 * 5164919 ≤
      55924056 ^ 2 - V.card * 5164919 := by
    exact Nat.sub_le_sub_left (Nat.mul_le_mul_right 5164919 hVle) _
  have hlower : 140942232 *
      (55924056 ^ 2 - 605527370 * 5164919) ≤
      Fintype.card K * (55924056 ^ 2 - V.card * 5164919) :=
    Nat.mul_le_mul hKcard hgap
  have hright : V.card * (55924056 - 5164919) ≤
      605527370 * (55924056 - 5164919) :=
    Nat.mul_le_mul_right _ hVle
  exact twoCore_reduced_plotkin_forces_5164920
    (hlower.trans (hplot.trans hright))

/-- Geometric third-line form of the recursive petal extraction. -/
theorem exists_third_distinctLine_with_newCorePetal_ge_5164920
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hover : N < family.G.card)
    (hthreshold : T ≤
      ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (htwo : (pointsOn family line1).card = 2)
    (hcore1 : 327272221 ≤
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card)
    (hpetal2 : 140942233 ≤
      (jointCore dom (u 0) (u 1) line2.1 line2.2 \
        jointCore dom (u 0) (u 1) line1.1 line1.2).card) :
    ∃ line3 ∈ lineParameters family, line3 ≠ line1 ∧ line3 ≠ line2 ∧
      5164920 ≤
        (jointCore dom (u 0) (u 1) line3.1 line3.2 \
          (jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
            jointCore dom (u 0) (u 1) line2.1 line2.2)).card := by
  obtain ⟨gamma, hgamma, beta, hbeta, hne, hpetal3⟩ :=
    exists_outsideBoth_secantPetal_card_ge_5164920
      family hover hthreshold line1 line2 hline1 hline2 htwo hcore1 hpetal2
  let line3 := secantParameter family gamma beta
  have hgammaG : gamma ∈ family.G := (Finset.mem_sdiff.mp hgamma).1
  have hbetaG : beta ∈ family.G := (Finset.mem_sdiff.mp hbeta).1
  have hline3 : line3 ∈ lineParameters family :=
    secantParameter_mem_lineParameters family hgammaG hbetaG hne
  have hgammaOn : gamma ∈ pointsOn family line3 :=
    first_point_mem_pointsOn_secant family hgammaG
  have hne1 : line3 ≠ line1 := by
    intro heq
    have := (Finset.mem_sdiff.mp hgamma).2
    simp only [Finset.mem_union, not_or] at this
    exact this.1 (heq ▸ hgammaOn)
  have hne2 : line3 ≠ line2 := by
    intro heq
    have := (Finset.mem_sdiff.mp hgamma).2
    simp only [Finset.mem_union, not_or] at this
    exact this.2 (heq ▸ hgammaOn)
  exact ⟨line3, hline3, hne1, hne2, by simpa only [line3, secantPetalOutsideTwo]
    using hpetal3⟩

/-! ## High-core jump or isolated secant -/

/-- Every relevant P1 threshold line either has the exact three-point core
floor `352,321,537`, or contains exactly its determining pair. -/
theorem relevantLine_core_ge_352321537_or_card_eq_two
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hthreshold : T ≤
      ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family) :
    352321537 ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card ∨
      (pointsOn family line).card = 2 := by
  by_cases hthree : 3 ≤ (pointsOn family line).card
  · left
    have hpack := pointsOn_card_mul_max_add_core_le family hline
    simp only [Fintype.card_fin] at hpack
    have hfactor : T - (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ max 1
        (⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊ -
          (jointCore dom (u 0) (u 1) line.1 line.2).card) :=
      (Nat.sub_le_sub_right hthreshold _).trans (le_max_right _ _)
    have hmul : 3 * (T - (jointCore dom (u 0) (u 1) line.1 line.2).card) ≤
        (pointsOn family line).card * max 1
          (⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊ -
            (jointCore dom (u 0) (u 1) line.1 line.2).card) :=
      Nat.mul_le_mul hthree hfactor
    simp only [Fintype.card_fin] at hmul
    have hbase : 3 * (T - (jointCore dom (u 0) (u 1) line.1 line.2).card) +
        (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ N :=
      by omega
    norm_num [T, N] at hbase ⊢
    omega
  · right
    have htwo := two_le_pointsOn_card_of_mem_lineParameters family hline
    omega

/-- With the isolated pinned anchor and certified second petal, the recursive
construction yields a third distinct line; each of the two new lines either
jumps to the high-core floor or is itself an isolated two-point secant. -/
theorem exists_thirdLine_with_highCore_or_isolated_branches
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hover : N < family.G.card)
    (hthreshold : T ≤
      ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (htwo : (pointsOn family line1).card = 2)
    (hcore1 : 327272221 ≤
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card)
    (hpetal2 : 140942233 ≤
      (jointCore dom (u 0) (u 1) line2.1 line2.2 \
        jointCore dom (u 0) (u 1) line1.1 line1.2).card) :
    ∃ line3 ∈ lineParameters family, line3 ≠ line1 ∧ line3 ≠ line2 ∧
      5164920 ≤
        (jointCore dom (u 0) (u 1) line3.1 line3.2 \
          (jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
            jointCore dom (u 0) (u 1) line2.1 line2.2)).card ∧
      (352321537 ≤ (jointCore dom (u 0) (u 1) line2.1 line2.2).card ∨
        (pointsOn family line2).card = 2) ∧
      (352321537 ≤ (jointCore dom (u 0) (u 1) line3.1 line3.2).card ∨
        (pointsOn family line3).card = 2) := by
  obtain ⟨line3, hline3, hne31, hne32, hpetal3⟩ :=
    exists_third_distinctLine_with_newCorePetal_ge_5164920
      family hover hthreshold line1 line2 hline1 hline2 htwo hcore1 hpetal2
  exact ⟨line3, hline3, hne31, hne32, hpetal3,
    relevantLine_core_ge_352321537_or_card_eq_two family hthreshold hline2,
    relevantLine_core_ge_352321537_or_card_eq_two family hthreshold hline3⟩

/-! ## High-core branch increment and three-core barrier -/

/-- Three independent line-core root caps exhaust the threshold before any
positive fourth fresh floor is obtained by naive subtraction. -/
theorem naive_threeCore_fresh_floor_eq_zero : T - 3 * (k - 1) = 0 := by
  norm_num [T, k]

/-- A line at the three-point core floor carrying at most three selected points
forces a stronger P1 outsider petal of size `145,836,060`. -/
theorem exists_highCore_outside_secantPetal_card_ge_145836060
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hover : N < family.G.card)
    (hthreshold : T ≤
      ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore : 352321537 ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card)
    (hthree : (pointsOn family line).card ≤ 3) :
    ∃ gamma ∈ outsideLine family line,
      ∃ beta ∈ outsideLine family line, gamma ≠ beta ∧
        145836060 ≤ (secantPetal family line gamma beta).card := by
  classical
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let V : Finset (Fin N) := Finset.univ \ D
  let K := {gamma // gamma ∈ outsideLine family line}
  let A : K → Finset (Fin N) := fun gamma =>
    fullAgreement dom (u 0) (u 1) gamma.1 (family.q gamma.1) \ D
  have hVcard : V.card = N - D.card := by
    simp only [V, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, Fintype.card_fin]
  have hVle : V.card ≤ 721420287 := by
    rw [hVcard]
    change 352321537 ≤ D.card at hcore
    have hN : N = 1073741824 := by norm_num [N]
    omega
  have hAsub : ∀ gamma : K, A gamma ⊆ V := by
    intro gamma x hx
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
  have hAsize : ∀ gamma : K, 324359511 ≤ (A gamma).card := by
    intro gamma
    have hfresh := threshold_sub_pred_le_fresh_card
      family line (by norm_num [k]) hline gamma.2
    have hmono : T - (k - 1) ≤
        ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊ - (k - 1) :=
      Nat.sub_le_sub_right hthreshold (k - 1)
    have hTk : T - (k - 1) = 324359511 := by norm_num [T, k]
    rw [hTk] at hmono
    exact hmono.trans (by simpa only [A, D] using hfresh)
  by_contra hnot
  push_neg at hnot
  have hpair : Pairwise fun gamma beta : K =>
      (A gamma ∩ A beta).card ≤ 145836059 := by
    intro gamma beta hne
    have hvalue : gamma.1 ≠ beta.1 := fun heq => hne (Subtype.ext heq)
    rw [show A gamma ∩ A beta = secantPetal family line gamma.1 beta.1 by
      simpa only [A, D] using fresh_inter_eq_secantPetal
        family line
          ((mem_outsideLine_iff family line gamma.1).mp gamma.2).1
          ((mem_outsideLine_iff family line beta.1).mp beta.2).1 hvalue]
    have hlt := hnot gamma.1 gamma.2 beta.1 beta.2 hvalue
    omega
  have hbudget : V.card * 145836059 ≤ 324359511 ^ 2 - 1 := by
    have harith : 721420287 * 145836059 ≤ 324359511 ^ 2 - 1 := by norm_num
    exact (Nat.mul_le_mul_right 145836059 hVle).trans harith
  have houtside := card_le_finset_of_card_ge_pair_inter_le
    V A 324359511 145836059 (by norm_num) hAsub hAsize hpair hbudget
  simp only [K, Fintype.card_coe] at houtside
  have hpartition := pointsOn_card_add_outsideLine_card family line
  rw [hVcard] at houtside
  have hD : 352321537 ≤ D.card := hcore
  have hN : N = 1073741824 := by norm_num [N]
  omega

/-- Four-point packing split, local to this independent lane. -/
theorem relevantLine_core_ge_432479347_or_card_le_three
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hthreshold : T ≤
      ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family) :
    432479347 ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card ∨
      (pointsOn family line).card ≤ 3 := by
  by_cases hfour : 4 ≤ (pointsOn family line).card
  · left
    have hpack := pointsOn_card_mul_max_add_core_le family hline
    simp only [Fintype.card_fin] at hpack
    have hfactor : T - (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ max 1
        (⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊ -
          (jointCore dom (u 0) (u 1) line.1 line.2).card) :=
      (Nat.sub_le_sub_right hthreshold _).trans (le_max_right _ _)
    have hmul : 4 * (T - (jointCore dom (u 0) (u 1) line.1 line.2).card) ≤
        (pointsOn family line).card * max 1
          (⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊ -
            (jointCore dom (u 0) (u 1) line.1 line.2).card) :=
      Nat.mul_le_mul hfour hfactor
    simp only [Fintype.card_fin] at hmul
    have hbase : 4 * (T - (jointCore dom (u 0) (u 1) line.1 line.2).card) +
        (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ N :=
      by omega
    norm_num [T, N] at hbase ⊢
    omega
  · right
    omega

/-- **High-core continuation.**  A `352,321,537`-core in an over-budget P1
family either jumps to the four-point floor `432,479,347`, or forces an
outsider secant petal of size at least `145,836,060`. -/
theorem core_ge_432479347_or_exists_petal_ge_145836060
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {dom : Fin N ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin N)}
    (family : BadScalarRichPointFamily dom k delta u)
    (hover : N < family.G.card)
    (hthreshold : T ≤
      ⌈(1 - delta) * (Fintype.card (Fin N) : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore : 352321537 ≤
      (jointCore dom (u 0) (u 1) line.1 line.2).card) :
    432479347 ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card ∨
      ∃ gamma ∈ outsideLine family line,
        ∃ beta ∈ outsideLine family line, gamma ≠ beta ∧
          145836060 ≤ (secantPetal family line gamma beta).card := by
  rcases relevantLine_core_ge_432479347_or_card_le_three
    family hthreshold hline with hhigh | hthree
  · exact Or.inl hhigh
  · exact Or.inr (exists_highCore_outside_secantPetal_card_ge_145836060
      family hover hthreshold hline hcore hthree)

end ArkLib.ProximityGap.Frontier.P1RateQuarterPinnedAnchorPetalGrowth

open ArkLib.ProximityGap.Frontier.P1RateQuarterPinnedAnchorPetalGrowth

#print axioms pinnedAnchor_reduced_rankin_budget
#print axioms exists_outside_secantPetal_card_ge_140942233
#print axioms exists_distinct_outsideLine_core_ge_140942233
#print axioms outsideBothLines_card_ge_140942232
#print axioms twoCore_fresh_card_ge_55924056
#print axioms twoCore_union_complement_ceiling_eq
#print axioms twoCore_reduced_plotkin_forces_5164920
#print axioms exists_outsideBoth_secantPetal_card_ge_5164920
#print axioms exists_third_distinctLine_with_newCorePetal_ge_5164920
#print axioms relevantLine_core_ge_352321537_or_card_eq_two
#print axioms exists_thirdLine_with_highCore_or_isolated_branches
#print axioms naive_threeCore_fresh_floor_eq_zero
#print axioms exists_highCore_outside_secantPetal_card_ge_145836060
#print axioms relevantLine_core_ge_432479347_or_card_le_three
#print axioms core_ge_432479347_or_exists_petal_ge_145836060
