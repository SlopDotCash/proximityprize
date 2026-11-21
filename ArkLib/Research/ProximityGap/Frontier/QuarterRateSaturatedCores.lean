/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterRateQuadraticSafety

/-! # Saturated joint cores on the first quarter-rate domain -/

open Finset Polynomial Code
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.QuarterRateSaturatedCores
open HalfPredecessorBadEventRichPointBridge HalfPredecessorSecantLines HalfPredecessorLineCoreGeometry
open HalfPredecessorRateEighthFullWiring HalfPredecessorRateQuarterComplementaryCores

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

private abbrev core (dom : I ↪ F) (u : WordStack F (Fin 2) I) (a : LineParameter F) :=
  jointCore dom (u 0) (u 1) a.1 a.2

/-- When the shared core saturates the degree, all fresh agreements that land
in the other core supply at most one scalar label in total. -/
theorem points_on_saturated {k : ℕ} (fam : BadScalarRichPointFamily dom k δ u)
    {a b : LineParameter F} (ha : a ∈ lineParameters fam) (hb : b ∈ lineParameters fam) (hab : a ≠ b)
    (hk : k-1 ≤ (core dom u a ∩ core dom u b).card) :
    (pointsOn fam a).card ≤ (univ \ (core dom u a ∪ core dom u b)).card+1 := by
  classical
  let S := (core dom u a ∩ core dom u b).image dom
  let p := a.1-b.1
  let q := a.2-b.2
  let G := (pointsOn fam a).filter fun z => ∃ x ∉ S, p.eval x + z*q.eval x = 0
  let outside := univ \ (core dom u a ∪ core dom u b)
  let lab (i : I) := (u 0 i - a.1.eval (dom i)) / (a.2.eval (dom i) - u 1 i)
  have hsub : pointsOn fam a ⊆ outside.image lab ∪ G := by
    intro z hz
    obtain ⟨hzm,eq⟩ := (mem_pointsOn_iff fam a z).mp hz
    obtain ⟨hA,hB⟩ := lineParameter_degree_lt fam ha
    have hn := not_subset_jointCore_of_not_pairJointAgreesOn dom (u 0) (u 1)
      _ a.1 a.2 hA hB (fam.noJoint z hzm)
    obtain ⟨i,hfit,ho⟩ := Finset.not_subset.mp hn
    rw [eq] at hfit
    simp only [fullAgreement,mem_filter,mem_univ,true_and,eval_add,eval_mul,eval_C] at hfit
    by_cases hb : i ∈ core dom u b
    · refine mem_union_right _ (mem_filter.mpr ⟨hz,dom i,?_,?_⟩)
      · rintro his
        obtain ⟨j,hj,eqj⟩ := mem_image.mp his
        exact ho (dom.injective eqj ▸ (mem_inter.mp hj).1)
      · obtain ⟨hb₁,hb₂⟩ := (mem_filter.mp hb).2
        dsimp [p,q]
        rw [eval_sub,eval_sub,hb₁,hb₂]
        linear_combination hfit
    · refine mem_union_left _ (mem_image.mpr ⟨i,mem_sdiff.mpr ⟨mem_univ _,fun hi => (mem_union.mp hi).elim ho hb⟩,?_⟩)
      have hd : a.2.eval (dom i) - u 1 i ≠ 0 := by
        intro he
        have hzero := sub_eq_zero.mp he
        apply ho
        exact mem_filter.mpr ⟨mem_univ _,by rw [hzero] at hfit; exact ⟨add_right_cancel hfit,hzero⟩⟩
      apply Eq.symm
      apply (eq_div_iff hd).mpr
      linear_combination hfit
  have hS : S.card = (core dom u a ∩ core dom u b).card := card_image_of_injective _ dom.injective
  have hneq : p ≠ 0 ∨ q ≠ 0 := by
    by_contra! z
    exact hab (Prod.ext (sub_eq_zero.mp z.1) (sub_eq_zero.mp z.2))
  have ha' := lineParameter_degree_lt fam ha
  have hcard (hb : b.1.natDegree < k ∧ b.2.natDegree < k) : G.card ≤ 1 := by
    apply QuarterRateApolarBracket.saturated_overlap p q S G hneq
    · exact (natDegree_sub_le ..).trans (max_le (by omega) (by omega))
    · exact (natDegree_sub_le ..).trans (max_le (by omega) (by omega))
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
      obtain ⟨ha,hb⟩ := mem_inter.mp hi
      obtain ⟨ha₁,ha₂⟩ := (mem_filter.mp ha).2
      obtain ⟨hb₁,hb₂⟩ := (mem_filter.mp hb).2
      simp only [p,q,eval_sub,ha₁,ha₂,hb₁,hb₂,sub_self,and_self]
    · exact fun z hz => (mem_filter.mp hz).2
  exact (card_le_card hsub).trans ((card_union_le ..).trans
    (Nat.add_le_add card_image_le (hcard (lineParameter_degree_lt fam hb))))

/-- Two distinct cores at least one site below the agreement target force the
degree-saturated intersection, and hence contradict a large first secant. -/
theorem impossible_pair (fam : BadScalarRichPointFamily dom 268435456 δ u)
    (hn : Fintype.card I = 1073741824)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = 626349397)
    (large : 894784856 < fam.G.card)
    {a b : LineParameter F} (ha : a∈lineParameters fam) (hb : b∈lineParameters fam) (hab : a≠b)
    (h₁ : 223696214 < (pointsOn fam a).card) (h₂ : 223696214 < (pointsOn fam b).card) : False := by
  classical
  let D := core dom u
  have near (x : LineParameter F) (hx : x∈lineParameters fam) (h : 223696214 < (pointsOn fam x).card) :
      626349396 ≤ (D x).card := by
    have hs := pointsOn_card_mul_max_add_core_le fam hx
    rw [ht,hn] at hs
    change (pointsOn fam x).card * max 1 (626349397 - (D x).card) + (D x).card ≤ _ at hs
    have grow := Nat.mul_le_mul (show 223696215 ≤ (pointsOn fam x).card by omega)
      (Nat.le_max_right 1 (626349397-(D x).card))
    omega
  have hA := near a ha h₁
  have hB := near b hb h₂
  have cap (x : LineParameter F) (hx : x∈lineParameters fam) : (pointsOn fam x).card ≤ 447392428 :=
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
  have hu := card_union_add_card_inter (D a) (D b)
  have hnU := (card_le_univ (D a ∪ D b)).trans_eq hn
  rw [card_sdiff_of_subset (subset_univ _),card_univ,hn] at hole
  have eq : 268435455 ≤ (D a ∩ D b).card := by omega
  have hl := points_on_saturated fam ha hb hab eq
  change (pointsOn fam a).card ≤ (univ \ (D a ∪ D b)).card+1 at hl
  rw [card_sdiff_of_subset (subset_univ _),card_univ,hn] at hl
  omega

#print axioms points_on_saturated
#print axioms impossible_pair

end ArkLib.ProximityGap.Frontier.QuarterRateSaturatedCores
