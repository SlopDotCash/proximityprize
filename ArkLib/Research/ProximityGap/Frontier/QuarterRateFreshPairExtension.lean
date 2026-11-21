/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterRateSaturatedCores

/-! # Scalar labels requiring two fresh agreements -/

open Finset Polynomial Code
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.QuarterRateFreshPairExtension
open HalfPredecessorBadEventRichPointBridge HalfPredecessorSecantLines HalfPredecessorLineCoreGeometry
open HalfPredecessorRateEighthFullWiring HalfPredecessorRateQuarterComplementaryCores

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

private abbrev core (dom : I ↪ F) (u : WordStack F (Fin 2) I) (a : LineParameter F) :=
  jointCore dom (u 0) (u 1) a.1 a.2

/-- When the two heads share all but at most one of the degree-many roots,
a secant requiring two fresh sites per scalar has at most one scalar whose
fresh agreements all land in the opposite core. -/
theorem points_on_one_short {k t : ℕ} (fam : BadScalarRichPointFamily dom k δ u)
    {a b : LineParameter F} (ha : a ∈ lineParameters fam) (hb : b ∈ lineParameters fam)
    (hab : a ≠ b) (ht : t ≤ ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊)
    (two : (core dom u a).card + 2 ≤ t)
    (shared : k-1 ≤ (core dom u a ∩ core dom u b).card + 1) :
    (pointsOn fam a).card ≤ (univ \ (core dom u a ∪ core dom u b)).card+1 := by
  classical
  let D := core dom u
  let outside := univ \ (D a ∪ D b)
  let p := a.1-b.1
  let q := a.2-b.2
  let G := (pointsOn fam a).filter fun z => p + C z*q = 0
  let lab (i : I) := (u 0 i - a.1.eval (dom i)) / (a.2.eval (dom i)-u 1 i)
  have small : G.card ≤ 1 := by
    apply card_le_one.mpr
    intro z hz v hv
    have eq : (C z-C v)*q=0 := by
      rw [sub_mul]
      have h1 := (mem_filter.mp hz).2
      have h2 := (mem_filter.mp hv).2
      linear_combination h1-h2
    rcases mul_eq_zero.mp eq with he | hq
    · exact C_injective (sub_eq_zero.mp he)
    · have hp : p=0 := by simpa only [hq,mul_zero,add_zero] using (mem_filter.mp hz).2
      exact (hab (Prod.ext (sub_eq_zero.mp hp) (sub_eq_zero.mp hq))).elim
  have hsub : pointsOn fam a ⊆ outside.image lab ∪ G := by
    intro z hz
    obtain ⟨hzm,eq⟩ := (mem_pointsOn_iff fam a z).mp hz
    let A := fullAgreement dom (u 0) (u 1) z (fam.q z)
    by_cases fresh : (A ∩ outside).Nonempty
    · obtain ⟨i,hi⟩ := fresh
      obtain ⟨hf,ho⟩ := mem_inter.mp hi
      have hx : i ∈ fullAgreement dom (u 0) (u 1) z (fam.q z) := hf
      rw [eq] at hx
      simp only [fullAgreement,mem_filter,mem_univ,true_and,eval_add,eval_mul,eval_C] at hx
      have ha' : i ∉ D a := fun h => (mem_sdiff.mp ho).2 (mem_union_left _ h)
      have hd : a.2.eval (dom i) - u 1 i ≠ 0 := by
        intro he
        have hzero := sub_eq_zero.mp he
        apply ha'
        exact mem_filter.mpr ⟨mem_univ _,by rw [hzero] at hx; exact ⟨add_right_cancel hx,hzero⟩⟩
      refine mem_union_left _ (mem_image.mpr ⟨i,ho,?_⟩)
      exact Eq.symm ((eq_div_iff hd).mpr (by linear_combination hx))
    · refine mem_union_right _ (mem_filter.mpr ⟨hz,?_⟩)
      let T := (D a ∩ D b) ∪ (A \ D a)
      have dis : Disjoint (D a ∩ D b) (A \ D a) := by
        apply disjoint_left.mpr
        intro i hi ha
        exact (mem_sdiff.mp ha).2 (mem_inter.mp hi).1
      have fit : t ≤ A.card := ht.trans (fam.threshold_le z hzm)
      have exc : 2 ≤ (A \ D a).card := by
        have lower := card_le_card (show A ⊆ (A \ D a) ∪ D a by
          intro x hx
          by_cases h : x ∈ D a
          · exact mem_union_right _ h
          · exact mem_union_left _ (mem_sdiff.mpr ⟨hx,h⟩))
        have h := lower.trans (card_union_le ..)
        change (D a).card+2≤t at two
        omega
      have hi : k-1 < T.card := by
        dsimp only [T]
        rw [card_union_of_disjoint dis]
        change k-1 ≤ (D a ∩ D b).card+1 at shared
        omega
      obtain ⟨a₁,a₂⟩ := lineParameter_degree_lt fam ha
      obtain ⟨b₁,b₂⟩ := lineParameter_degree_lt fam hb
      have dp : p.natDegree ≤ k-1 := (natDegree_sub_le ..).trans (max_le (by omega) (by omega))
      have dq : q.natDegree ≤ k-1 := (natDegree_sub_le ..).trans (max_le (by omega) (by omega))
      apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f:=fun i:T => dom i.val)
        (dom.injective.comp Subtype.val_injective)
      · intro i
        rcases mem_union.mp i.property with h | h
        · obtain ⟨ha,hb⟩ := mem_inter.mp h
          obtain ⟨ha₁,ha₂⟩ := (mem_filter.mp ha).2
          obtain ⟨hb₁,hb₂⟩ := (mem_filter.mp hb).2
          simp only [p,q,eval_add,eval_mul,eval_C,eval_sub,ha₁,ha₂,hb₁,hb₂,sub_self,mul_zero,add_zero]
        · obtain ⟨fit,out⟩ := mem_sdiff.mp h
          have hb : i.val ∈ D b := by
            by_contra hbad
            exact fresh ⟨i.val,mem_inter.mpr ⟨fit,mem_sdiff.mpr ⟨mem_univ _,fun hu => (mem_union.mp hu).elim out hbad⟩⟩⟩
          obtain ⟨hb₁,hb₂⟩ := (mem_filter.mp hb).2
          change i.val ∈ fullAgreement dom (u 0) (u 1) z (fam.q z) at fit
          rw [eq] at fit
          simp only [fullAgreement,mem_filter,mem_univ,true_and,eval_add,eval_mul,eval_C] at fit
          simp only [p,q,eval_add,eval_mul,eval_C,eval_sub,hb₁,hb₂]
          linear_combination fit
      · simpa only [Fintype.card_coe] using ((natDegree_add_le ..).trans (max_le dp ((natDegree_C_mul_le ..).trans dq))).trans_lt hi
  exact (card_le_card hsub).trans ((card_union_le ..).trans (Nat.add_le_add card_image_le small))


/-- Two secants of unequal population already preclude a scalar beyond the exact
two-head numerator, including the case where their overlap falls one root short. -/
theorem impossible_asymmetric (fam : BadScalarRichPointFamily dom 268435456 δ u)
    (hn : Fintype.card I = 1073741824)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = 626349397)
    (large : 894784856 < fam.G.card)
    {a b : LineParameter F} (ha : a ∈ lineParameters fam) (hb : b ∈ lineParameters fam) (hab : a ≠ b)
    (h₁ : 223696214 < (pointsOn fam a).card) (h₂ : 150000000 < (pointsOn fam b).card) : False := by
  classical
  let D := core dom u
  have size (x : LineParameter F) (hx : x ∈ lineParameters fam) {L : ℕ} (h : L ≤ (pointsOn fam x).card) :
      L * (626349397-(D x).card) + (D x).card ≤ 1073741824 := by
    have hs := pointsOn_card_mul_max_add_core_le fam hx
    rw [ht,hn] at hs
    exact (Nat.add_le_add_right (Nat.mul_le_mul h (Nat.le_max_right ..)) _).trans hs
  have sz₁ := size a ha h₁
  have sz₂ := size b hb h₂
  have hA : 626349396 ≤ (D a).card := by omega
  have hB : 626349395 ≤ (D b).card := by omega
  have cap (x : LineParameter F) (hx : x ∈ lineParameters fam) : (pointsOn fam x).card ≤ 447392428 :=
    TwoLargeCoreCount.line_occupancy_le fam (e:=447392427) hn ht hx
  have hole : 626349397 ≤ (univ \ (D a ∪ D b)).card + 2 * 268435455 := by
    by_contra! below
    have cc := G_subset_two_lines_of_small_core_complement fam (by decide) (h:=626349396)
      (by omega) a b ha hb below
    have hg := (card_le_card cc).trans (card_union_le ..)
    have one := cap a ha
    have two := cap b hb
    omega
  have hi : (D a ∩ D b).card ≤ 268435455 := jointCore_inter_card_le_degree_pred fam (by decide) ha hb hab
  have un := card_union_add_card_inter (D a) (D b)
  have nU := (card_le_univ (D a ∪ D b)).trans_eq hn
  rw [card_sdiff_of_subset (subset_univ _),card_univ,hn] at hole
  by_cases near : 626349396 ≤ (D b).card
  · have common : 268435455 ≤ (D a ∩ D b).card := by omega
    have hl := QuarterRateSaturatedCores.points_on_saturated fam ha hb hab common
    change (pointsOn fam a).card ≤ (univ \ (D a ∪ D b)).card+1 at hl
    rw [card_sdiff_of_subset (subset_univ _),card_univ,hn] at hl
    omega
  · have common : 268435455 ≤ (D b ∩ D a).card+1 := by rw [inter_comm];omega
    have hb₂ : (D b).card+2 ≤ 626349397 := by omega
    have hl := points_on_one_short fam hb ha hab.symm ht.ge hb₂ common
    change (pointsOn fam b).card ≤ (univ \ (D b ∪ D a)).card+1 at hl
    rw [union_comm,card_sdiff_of_subset (subset_univ _),card_univ,hn] at hl
    omega

#print axioms points_on_one_short
#print axioms impossible_asymmetric
end ArkLib.ProximityGap.Frontier.QuarterRateFreshPairExtension
