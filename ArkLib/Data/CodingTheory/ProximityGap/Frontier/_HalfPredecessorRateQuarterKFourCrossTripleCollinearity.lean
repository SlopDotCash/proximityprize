/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CoveragePigeonhole
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourRegularSignatureRigidity

/-!
# Rate-quarter `k = 4`: cross-root-triple collinearity

The equal-root multiplicity bound does not control eight regular outsiders
using distinct root triples.  Their missed edges still give a global
constraint.  Eight two-subsets of an eight-point set contain three whose
union has size at most four.  Otherwise every edge would meet at most one
other edge; the coverage second moment then bounds the family by six.

For regular outsiders, a missed-edge union of size at most four leaves at
least four common fresh agreements.  The degree-three noncollinear root cap
therefore forces the three lifted polynomial points onto one secant line.
Fresh-fibre line packing makes that secant core have size at least six.  Under
the global core-eight ceiling, the extracted line is either a second
eight-core or a distinct three-point core of size six or seven.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourRegularSignatureRigidity

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCrossTripleCollinearity

attribute [local instance] Classical.propDecidable

/-! ## Eight two-edges force a compact triple -/

variable {K U : Type} [Fintype K] [Fintype U] [DecidableEq U]

/-- Restrict an ambient finset to a containing finset, represented by its
subtype. -/
def restrictToGround (V A : Finset U) : Finset V :=
  Finset.univ.filter fun x : V => x.1 ∈ A

theorem card_restrictToGround (V A : Finset U) (hA : A ⊆ V) :
    (restrictToGround V A).card = A.card := by
  classical
  refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro x hx
    refine ⟨⟨x, hA hx⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩

theorem restrictToGround_union (V A B : Finset U) :
    restrictToGround V (A ∪ B) =
      restrictToGround V A ∪ restrictToGround V B := by
  ext x
  simp only [restrictToGround, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_union]

/-- **Compact triple of two-edges.**  A family of at least eight two-subsets
of an eight-point ground type contains three distinct members whose union has
cardinality at most four. -/
theorem exists_three_union_card_le_four_of_eight_two_sets
    (E : K → Finset U)
    (hK : 8 ≤ Fintype.card K) (hU : Fintype.card U = 8)
    (hcard : ∀ i, (E i).card = 2) :
    ∃ i j k : K, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (E i ∪ E j ∪ E k).card ≤ 4 := by
  classical
  by_contra hnone
  have hlarge : ∀ i j k : K, i ≠ j → i ≠ k → j ≠ k →
      5 ≤ (E i ∪ E j ∪ E k).card := by
    intro i j k hij hik hjk
    by_contra hsmall
    apply hnone
    exact ⟨i, j, k, hij, hik, hjk, by omega⟩
  have hEinj : Function.Injective E := by
    intro i j hE
    by_contra hij
    have hnotSubset : ¬ (Finset.univ : Finset K) ⊆ {i, j} := by
      intro hsub
      have hc := Finset.card_le_card hsub
      rw [Finset.card_univ] at hc
      have hp : ({i, j} : Finset K).card ≤ 2 :=
        (Finset.card_insert_le i {j}).trans (by simp)
      omega
    simp only [Finset.not_subset] at hnotSubset
    obtain ⟨k, _hk, hkpair⟩ := hnotSubset
    have hkpair' : k ≠ i ∧ k ≠ j := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hkpair
    have hki : k ≠ i := hkpair'.1
    have hkj : k ≠ j := hkpair'.2
    have hsmall : (E i ∪ E j ∪ E k).card ≤ 4 := by
      rw [hE, Finset.union_self]
      exact (Finset.card_union_le (E j) (E k)).trans (by
        rw [hcard j, hcard k])
    have := hlarge i j k hij hki.symm hkj.symm
    omega
  have hpair : ∀ i j : K, i ≠ j → (E i ∩ E j).card ≤ 1 := by
    intro i j hij
    by_contra hnot
    have hinterLower : 2 ≤ (E i ∩ E j).card := by omega
    have hinterEq : E i ∩ E j = E i := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      rw [hcard i]
      exact hinterLower
    have hsub : E i ⊆ E j := by
      rw [← hinterEq]
      exact Finset.inter_subset_right
    have hEq : E i = E j := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [hcard i, hcard j]
    exact hij (hEinj hEq)
  let neighbors : K → Finset K := fun i =>
    (Finset.univ.erase i).filter fun j => (E i ∩ E j).Nonempty
  have hneighbors : ∀ i, (neighbors i).card ≤ 1 := by
    intro i
    by_contra hnot
    have htwo : 1 < (neighbors i).card := by omega
    obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp htwo
    have hjData := Finset.mem_filter.mp hj
    have hkData := Finset.mem_filter.mp hk
    have hji : j ≠ i := (Finset.mem_erase.mp hjData.1).1
    have hki : k ≠ i := (Finset.mem_erase.mp hkData.1).1
    have hijInter : 1 ≤ (E i ∩ E j).card :=
      Finset.card_pos.mpr hjData.2
    have hikInter : 1 ≤ (E i ∩ E k).card :=
      Finset.card_pos.mpr hkData.2
    have hjDiff : (E j \ E i).card ≤ 1 := by
      rw [Finset.card_sdiff, hcard j]
      have : 1 ≤ (E j ∩ E i).card := by
        simpa only [Finset.inter_comm] using hijInter
      omega
    have hkDiff : (E k \ E i).card ≤ 1 := by
      rw [Finset.card_sdiff, hcard k]
      have : 1 ≤ (E k ∩ E i).card := by
        simpa only [Finset.inter_comm] using hikInter
      omega
    have hunionEq : E i ∪ E j ∪ E k =
        E i ∪ (E j \ E i) ∪ (E k \ E i) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      tauto
    have hsmall : (E i ∪ E j ∪ E k).card ≤ 4 := by
      rw [hunionEq]
      calc
        (E i ∪ (E j \ E i) ∪ (E k \ E i)).card
            ≤ (E i ∪ (E j \ E i)).card + (E k \ E i).card :=
              Finset.card_union_le _ _
        _ ≤ (E i).card + (E j \ E i).card + (E k \ E i).card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
        _ ≤ 4 := by rw [hcard i]; omega
    have := hlarge i j k hji.symm hki.symm hjk
    omega
  have hoffdiag : ∀ i,
      (∑ j ∈ Finset.univ.erase i, (E i ∩ E j).card) ≤ 1 := by
    intro i
    calc
      (∑ j ∈ Finset.univ.erase i, (E i ∩ E j).card)
          ≤ ∑ j ∈ Finset.univ.erase i,
              if (E i ∩ E j).Nonempty then 1 else 0 := by
            apply Finset.sum_le_sum
            intro j hj
            by_cases hinter : (E i ∩ E j).Nonempty
            · simp only [hinter, if_true]
              have hji : j ≠ i := (Finset.mem_erase.mp hj).1
              exact hpair i j hji.symm
            · have hempty : E i ∩ E j = ∅ :=
                Finset.not_nonempty_iff_eq_empty.mp hinter
              simp [hempty]
      _ = (neighbors i).card := by
        simp only [neighbors, Finset.card_filter]
      _ ≤ 1 := hneighbors i
  have hinner : ∀ i, (∑ j, (E i ∩ E j).card) ≤ 3 := by
    intro i
    rw [← Finset.add_sum_erase Finset.univ
      (fun j => (E i ∩ E j).card) (Finset.mem_univ i)]
    have hdiag : (E i ∩ E i).card = 2 := by rw [Finset.inter_self, hcard i]
    have hoff := hoffdiag i
    omega
  have hupper : (∑ i, ∑ j, (E i ∩ E j).card) ≤
      Fintype.card K * 3 := by
    calc
      (∑ i, ∑ j, (E i ∩ E j).card) ≤ ∑ _i : K, 3 :=
        Finset.sum_le_sum fun i _ => hinner i
      _ = Fintype.card K * 3 := by simp
  have hsum : (∑ i, (E i).card) = Fintype.card K * 2 := by
    simp only [hcard, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hmass := ArkLib.Coverage.sq_sum_card_le_card_mul_sum_inter E
  rw [hsum, hU] at hmass
  have hkey : (Fintype.card K * 2) ^ 2 ≤
      8 * (Fintype.card K * 3) :=
    hmass.trans (Nat.mul_le_mul_left 8 hupper)
  have hleft : (Fintype.card K * 2) ^ 2 =
      Fintype.card K * (Fintype.card K * 4) := by ring
  have hright : 8 * (Fintype.card K * 3) =
      Fintype.card K * 24 := by ring
  rw [hleft, hright] at hkey
  have hKpos : 0 < Fintype.card K := by omega
  have hbound : Fintype.card K * 4 ≤ 24 :=
    Nat.le_of_mul_le_mul_left hkey hKpos
  omega

/-- Ambient-finset form of the compact-edge theorem. -/
theorem exists_three_union_card_le_four_of_eight_two_subsets
    (V : Finset U) (E : K → Finset U)
    (hK : 8 ≤ Fintype.card K) (hV : V.card = 8)
    (hsub : ∀ i, E i ⊆ V) (hcard : ∀ i, (E i).card = 2) :
    ∃ i j k : K, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (E i ∪ E j ∪ E k).card ≤ 4 := by
  let R : K → Finset V := fun i => restrictToGround V (E i)
  have hRcard : ∀ i, (R i).card = 2 := by
    intro i
    rw [show R i = restrictToGround V (E i) by rfl,
      card_restrictToGround V (E i) (hsub i), hcard i]
  have hVtype : Fintype.card V = 8 := by simpa only [Fintype.card_coe] using hV
  obtain ⟨i, j, k, hij, hik, hjk, hunion⟩ :=
    exists_three_union_card_le_four_of_eight_two_sets
      R hK hVtype hRcard
  have hunionSub : E i ∪ E j ∪ E k ⊆ V :=
    Finset.union_subset (Finset.union_subset (hsub i) (hsub j)) (hsub k)
  have hrestrict : restrictToGround V (E i ∪ E j ∪ E k) =
      R i ∪ R j ∪ R k := by
    simp only [R, restrictToGround_union]
  refine ⟨i, j, k, hij, hik, hjk, ?_⟩
  rw [← card_restrictToGround V (E i ∪ E j ∪ E k) hunionSub,
    hrestrict]
  exact hunion

/-! ## Regular-signature consequence -/

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Eight regular outsiders contain three distinct signatures with compact
missed-edge union. -/
theorem exists_three_regular_missedUnion_card_le_four
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F}
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8)
    (hpopulation : 8 ≤ (regularOutsideLine family line).card) :
    ∃ gamma1 ∈ regularOutsideLine family line,
      ∃ gamma2 ∈ regularOutsideLine family line,
        ∃ gamma3 ∈ regularOutsideLine family line,
          gamma1 ≠ gamma2 ∧ gamma1 ≠ gamma3 ∧ gamma2 ≠ gamma3 ∧
          (regularMissedEdge family line gamma1 ∪
            regularMissedEdge family line gamma2 ∪
            regularMissedEdge family line gamma3).card ≤ 4 := by
  let K := {gamma // gamma ∈ regularOutsideLine family line}
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let V : Finset I := Finset.univ \ D
  let E : K → Finset I := fun gamma =>
    regularMissedEdge family line gamma.1
  have hK : 8 ≤ Fintype.card K := by
    simpa only [K, Fintype.card_coe] using hpopulation
  have hV : V.card = 8 := by
    simp only [V, D, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, hn, hcore]
  have hEsub : ∀ gamma, E gamma ⊆ V := by
    intro gamma i hi
    exact (Finset.mem_sdiff.mp hi).1
  have hEcard : ∀ gamma, (E gamma).card = 2 := by
    intro gamma
    simpa only [E] using
      (regular_signature_cardinalities family hn hcore gamma.2).2
  obtain ⟨gamma1, gamma2, gamma3, h12, h13, h23, hunion⟩ :=
    exists_three_union_card_le_four_of_eight_two_subsets
      V E hK hV hEsub hEcard
  refine ⟨gamma1.1, gamma1.2, gamma2.1, gamma2.2,
    gamma3.1, gamma3.2, ?_, ?_, ?_, ?_⟩
  · exact fun h => h12 (Subtype.ext h)
  · exact fun h => h13 (Subtype.ext h)
  · exact fun h => h23 (Subtype.ext h)
  · simpa only [E] using hunion

/-- **Cross-root-triple collinearity.**  Among eight regular outsiders, three
distinct lifted polynomial points lie on one canonical secant, and their
missed edges have union size at most four. -/
theorem exists_three_regular_collinear_of_eight
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F}
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8)
    (hpopulation : 8 ≤ (regularOutsideLine family line).card) :
    ∃ gamma1 ∈ regularOutsideLine family line,
      ∃ gamma2 ∈ regularOutsideLine family line,
        ∃ gamma3 ∈ regularOutsideLine family line,
          gamma1 ≠ gamma2 ∧ gamma1 ≠ gamma3 ∧ gamma2 ≠ gamma3 ∧
          (regularMissedEdge family line gamma1 ∪
            regularMissedEdge family line gamma2 ∪
            regularMissedEdge family line gamma3).card ≤ 4 ∧
          gamma3 ∈ pointsOn family
            (secantParameter family gamma1 gamma2) := by
  obtain ⟨gamma1, hgamma1, gamma2, hgamma2, gamma3, hgamma3,
      h12, h13, h23, hunion⟩ :=
    exists_three_regular_missedUnion_card_le_four
      family hn hcore hpopulation
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let V : Finset I := Finset.univ \ D
  let E1 := regularMissedEdge family line gamma1
  let E2 := regularMissedEdge family line gamma2
  let E3 := regularMissedEdge family line gamma3
  let R : Finset I := V \ (E1 ∪ E2 ∪ E3)
  let A : F → Finset I := fun gamma =>
    fullAgreement dom (u 0) (u 1) gamma (family.q gamma)
  have hVcard : V.card = 8 := by
    simp only [V, D, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, hn, hcore]
  have hEsub : E1 ∪ E2 ∪ E3 ⊆ V := by
    apply Finset.union_subset
    · apply Finset.union_subset <;> intro i hi
      · exact (Finset.mem_sdiff.mp hi).1
      · exact (Finset.mem_sdiff.mp hi).1
    · intro i hi
      exact (Finset.mem_sdiff.mp hi).1
  have hRcard : 4 ≤ R.card := by
    have hsplit := Finset.card_sdiff_add_card_inter V (E1 ∪ E2 ∪ E3)
    have hinter : V ∩ (E1 ∪ E2 ∪ E3) = E1 ∪ E2 ∪ E3 :=
      Finset.inter_eq_right.mpr hEsub
    rw [hinter] at hsplit
    rw [hVcard] at hsplit
    change R.card + (E1 ∪ E2 ∪ E3).card = 8 at hsplit
    change (E1 ∪ E2 ∪ E3).card ≤ 4 at hunion
    omega
  have hRsub : R ⊆ (A gamma1 ∩ A gamma2) ∩ A gamma3 := by
    intro i hi
    have hiData := Finset.mem_sdiff.mp hi
    have hiV : i ∈ V := hiData.1
    have hiNot := hiData.2
    have hiFresh : ∀ gamma E,
        E = regularMissedEdge family line gamma →
        i ∉ E → i ∈ sourceFreshAgreement family line gamma := by
      intro gamma E hE hiE
      by_contra hiS
      apply hiE
      rw [hE]
      exact Finset.mem_sdiff.mpr ⟨hiV, hiS⟩
    have hi1 : i ∈ sourceFreshAgreement family line gamma1 :=
      hiFresh gamma1 E1 rfl (fun hi => hiNot (by simp [hi]))
    have hi2 : i ∈ sourceFreshAgreement family line gamma2 :=
      hiFresh gamma2 E2 rfl (fun hi => hiNot (by simp [hi]))
    have hi3 : i ∈ sourceFreshAgreement family line gamma3 :=
      hiFresh gamma3 E3 rfl (fun hi => hiNot (by simp [hi]))
    apply Finset.mem_inter.mpr
    refine ⟨Finset.mem_inter.mpr ?_, (Finset.mem_sdiff.mp hi3).1⟩
    exact ⟨(Finset.mem_sdiff.mp hi1).1, (Finset.mem_sdiff.mp hi2).1⟩
  have htriple : 3 < ((A gamma1 ∩ A gamma2) ∩ A gamma3).card :=
    lt_of_lt_of_le (by omega) (Finset.card_le_card hRsub)
  have hgamma1Data := hgamma1
  have hgamma2Data := hgamma2
  have hgamma3Data := hgamma3
  simp only [regularOutsideLine, Finset.mem_filter] at hgamma1Data
  simp only [regularOutsideLine, Finset.mem_filter] at hgamma2Data
  simp only [regularOutsideLine, Finset.mem_filter] at hgamma3Data
  have hgamma1G := (mem_outsideLine_iff family line gamma1).mp
    hgamma1Data.1 |>.1
  have hgamma2G := (mem_outsideLine_iff family line gamma2).mp
    hgamma2Data.1 |>.1
  have hgamma3G := (mem_outsideLine_iff family line gamma3).mp
    hgamma3Data.1 |>.1
  have hslope :
      slopePolynomial gamma1 gamma2 (family.q gamma1) (family.q gamma2) =
        slopePolynomial gamma1 gamma3 (family.q gamma1) (family.q gamma3) := by
    by_contra hslopeNe
    have hupper := triple_fullAgreement_card_le_pred_of_slope_ne
      dom (u 0) (u 1) (k := 4) (by norm_num) h12 h13
        (family.degree_lt gamma1 hgamma1G)
        (family.degree_lt gamma2 hgamma2G)
        (family.degree_lt gamma3 hgamma3G) hslopeNe
    change ((A gamma1 ∩ A gamma2) ∩ A gamma3).card ≤ 4 - 1 at hupper
    norm_num only at hupper
    exact (Nat.not_lt_of_ge hupper htriple).elim
  have hthird := third_point_on_secant_line_of_slope_eq h13 hslope.symm
  refine ⟨gamma1, hgamma1, gamma2, hgamma2, gamma3, hgamma3,
    h12, h13, h23, hunion, ?_⟩
  exact (mem_pointsOn_iff family
      (secantParameter family gamma1 gamma2) gamma3).mpr
    ⟨hgamma3G, by simpa only [secantParameter] using hthird⟩

/-- A relevant line containing three distinct selected points has core size
at least six at the `n=16`, threshold-nine endpoint. -/
theorem six_le_core_of_three_pointsOn
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    {gamma1 gamma2 gamma3 : F}
    (hgamma1 : gamma1 ∈ pointsOn family line)
    (hgamma2 : gamma2 ∈ pointsOn family line)
    (hgamma3 : gamma3 ∈ pointsOn family line)
    (h12 : gamma1 ≠ gamma2) (h13 : gamma1 ≠ gamma3)
    (h23 : gamma2 ≠ gamma3) :
    6 ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card := by
  let z := (jointCore dom (u 0) (u 1) line.1 line.2).card
  let L := (pointsOn family line).card
  have hthree : 2 < L := by
    apply Finset.two_lt_card_iff.mpr
    exact ⟨gamma1, gamma2, gamma3, hgamma1, hgamma2, hgamma3,
      h12, h13, h23⟩
  have hpack := pointsOn_card_mul_max_add_core_le family hline
  change L * max 1
      (⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ - z) + z ≤
    Fintype.card I at hpack
  have hfactor : 9 - z ≤ max 1
      (⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ - z) :=
    (Nat.sub_le_sub_right hthreshold z).trans (le_max_right _ _)
  have hmul : 3 * (9 - z) ≤ L * max 1
      (⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ - z) :=
    Nat.mul_le_mul (by omega) hfactor
  have hbase : 3 * (9 - z) + z ≤ Fintype.card I :=
    (Nat.add_le_add_right hmul z).trans hpack
  rw [hn] at hbase
  change 6 ≤ z
  by_contra hnot
  omega

/-- **Cross-triple residual under the core-eight ceiling.**  Eight regular
outsiders force either a second eight-core or a distinct three-point secant
core of size six or seven. -/
theorem exists_second_eight_core_or_crossTriple_six_seven_core
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    {line : LineParameter F}
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8)
    (hcoreCap : ∀ line2 ∈ lineParameters family,
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card ≤ 8)
    (hpopulation : 8 ≤ (regularOutsideLine family line).card) :
    (∃ line2 ∈ lineParameters family, line2 ≠ line ∧
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 8) ∨
      ∃ gamma1 ∈ regularOutsideLine family line,
        ∃ gamma2 ∈ regularOutsideLine family line,
          ∃ gamma3 ∈ regularOutsideLine family line,
            gamma1 ≠ gamma2 ∧ gamma1 ≠ gamma3 ∧ gamma2 ≠ gamma3 ∧
            (regularMissedEdge family line gamma1 ∪
              regularMissedEdge family line gamma2 ∪
              regularMissedEdge family line gamma3).card ≤ 4 ∧
            let line2 := secantParameter family gamma1 gamma2
            line2 ∈ lineParameters family ∧ line2 ≠ line ∧
              gamma3 ∈ pointsOn family line2 ∧
              ((jointCore dom (u 0) (u 1) line2.1 line2.2).card = 6 ∨
                (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 7) := by
  obtain ⟨gamma1, hgamma1, gamma2, hgamma2, gamma3, hgamma3,
      h12, h13, h23, hunion, hgamma3On⟩ :=
    exists_three_regular_collinear_of_eight family hn hcore hpopulation
  let line2 := secantParameter family gamma1 gamma2
  have hgamma1Data := hgamma1
  have hgamma2Data := hgamma2
  simp only [regularOutsideLine, Finset.mem_filter] at hgamma1Data hgamma2Data
  have hgamma1G := (mem_outsideLine_iff family line gamma1).mp
    hgamma1Data.1 |>.1
  have hgamma2G := (mem_outsideLine_iff family line gamma2).mp
    hgamma2Data.1 |>.1
  have hline2 : line2 ∈ lineParameters family :=
    secantParameter_mem_lineParameters family hgamma1G hgamma2G h12
  have hgamma1On : gamma1 ∈ pointsOn family line2 :=
    first_point_mem_pointsOn_secant family hgamma1G
  have hgamma2On : gamma2 ∈ pointsOn family line2 :=
    second_point_mem_pointsOn_secant family hgamma2G h12
  have hlineNe : line2 ≠ line := by
    intro heq
    have hsourceOn : gamma1 ∈ pointsOn family line := by
      rw [← heq]
      exact hgamma1On
    have hq := (mem_pointsOn_iff family line gamma1).mp hsourceOn |>.2
    exact ((mem_outsideLine_iff family line gamma1).mp hgamma1Data.1).2 hq
  have hcoreLower : 6 ≤
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card :=
    six_le_core_of_three_pointsOn family hn hthreshold hline2
      hgamma1On hgamma2On hgamma3On h12 h13 h23
  have hcoreUpper := hcoreCap line2 hline2
  by_cases height :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 8
  · exact Or.inl ⟨line2, hline2, hlineNe, height⟩
  apply Or.inr
  refine ⟨gamma1, hgamma1, gamma2, hgamma2, gamma3, hgamma3,
    h12, h13, h23, hunion, ?_⟩
  dsimp only
  refine ⟨hline2, hlineNe, hgamma3On, ?_⟩
  change
    (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 6 ∨
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 7
  omega

#print axioms exists_three_union_card_le_four_of_eight_two_sets
#print axioms exists_three_regular_missedUnion_card_le_four
#print axioms exists_three_regular_collinear_of_eight
#print axioms six_le_core_of_three_pointsOn
#print axioms exists_second_eight_core_or_crossTriple_six_seven_core

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCrossTripleCollinearity
