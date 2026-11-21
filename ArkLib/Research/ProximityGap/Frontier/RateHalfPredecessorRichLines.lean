/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorLargeCoreCollapse

/-! # Pairwise overlap bounds for rich affine witness lines

Seven selected points on one line outside another yield a sixfold miss
inequality on the intersection of the two exceptional coordinate sets.
-/

set_option autoImplicit false

open Finset Polynomial
open _root_.ProximityGap Code
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapse
open scoped NNReal BigOperators

namespace ArkLib.ProximityGap.Frontier.RateHalfPredecessorRichLines

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]
variable {dom : ι ↪ F} {k : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) ι}

private theorem seven_disjoint_agreements
    {T J : Type*} [DecidableEq T] (G : Finset J) (U : Finset T) (A : J → Finset T)
    {b : ℕ} (hseven : G.card = 7)
    (hmiss : ∀ j ∈ G, (U \ A j).card ≤ b)
    (hdis : ∀ i ∈ G, ∀ j ∈ G, i ≠ j → Disjoint (U ∩ A i) (U ∩ A j)) :
    6 * U.card ≤ 7 * b := by
  classical
  have hsum : ∑ j ∈ G, (U ∩ A j).card ≤ U.card := by
    rw [← Finset.card_biUnion hdis]
    exact Finset.card_le_card (Finset.biUnion_subset.mpr fun _ _ => Finset.inter_subset_left)
  have hbudget : 7 * U.card ≤ 7 * b + ∑ j ∈ G, (U ∩ A j).card := by
    calc
      7 * U.card = ∑ _j ∈ G, U.card := by simp [hseven]
      _ ≤ ∑ j ∈ G, (b + (U ∩ A j).card) := Finset.sum_le_sum fun j hj => by
        have h := Finset.card_sdiff_add_card_inter U (A j)
        have hm := hmiss j hj
        omega
      _ = _ := by simp [Finset.sum_add_distrib, hseven]
  omega

/-- On the intersection of two core complements, seven points on the second
line outside the first contribute at least six misses per coordinate. -/
theorem overlap_of_eight_points (fam : BadScalarRichPointFamily dom k δ u)
    (l r : LineParameter F) (hl : l ∈ lineParameters fam) (hlr : l ≠ r)
    (hrich : 8 ≤ (pointsOn fam r).card) (hk : 1 ≤ k) {b : ℕ}
    (hbudget : (jointCore dom (u 0) (u 1) l.1 l.2)ᶜ.card + (k - 1) ≤
      b + ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) :
    6 * ((jointCore dom (u 0) (u 1) l.1 l.2)ᶜ ∩
      (jointCore dom (u 0) (u 1) r.1 r.2)ᶜ).card ≤ 7 * b := by
  classical
  let D (v : LineParameter F) := jointCore dom (u 0) (u 1) v.1 v.2
  let U := (D l)ᶜ ∩ (D r)ᶜ
  let A (x : F) := fullAgreement dom (u 0) (u 1) x (fam.q x)
  have hone : (pointsOn fam r ∩ pointsOn fam l).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra hne
    have hr := secantParameter_eq_of_mem_pointsOn fam r
      (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hy).1 hne
    have hh := secantParameter_eq_of_mem_pointsOn fam l
      (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hy).2 hne
    exact hlr (hh.symm.trans hr)
  have hsize := Finset.card_sdiff_add_card_inter (pointsOn fam r) (pointsOn fam l)
  obtain ⟨G, hG, hseven⟩ := Finset.exists_subset_card_eq (show
      7 ≤ (pointsOn fam r \ pointsOn fam l).card by omega)
  apply seven_disjoint_agreements G U A hseven
  · intro j hj
    obtain ⟨hr, ho⟩ := Finset.mem_sdiff.mp (hG hj)
    have hjG := pointsOn_subset_G fam r hr
    have hdeg := lineParameter_degree_lt fam hl
    have hoff : fam.q j ≠ l.1 + C j * l.2 := by
      intro h
      exact ho ((mem_pointsOn_iff fam l j).mpr ⟨hjG, h⟩)
    have hc := fullAgreement_inter_jointCore_card_le dom (u 0) (u 1) hk
      (fam.degree_lt j hjG) hdeg.1 hdeg.2 hoff
    change (A j ∩ D l).card ≤ k - 1 at hc
    have hthreshold := fam.threshold_le j hjG
    change _ ≤ (A j).card at hthreshold
    change (D l)ᶜ.card + (k - 1) ≤ _ at hbudget
    have hc1 := Finset.card_sdiff_add_card_inter (A j) (D l)
    have hc2 := Finset.card_sdiff_add_card_inter (D l)ᶜ (A j)
    have heq : (D l)ᶜ ∩ A j = A j \ D l := by ext x; simp [and_comm]
    rw [heq] at hc2
    have hsub : U \ A j ⊆ (D l)ᶜ \ A j :=
      Finset.sdiff_subset_sdiff_left _ Finset.inter_subset_left
    have hle := Finset.card_le_card hsub
    omega
  · intro x hx y hy hxy
    have hh (z : F) (hz : z ∈ G) :=
      (mem_pointsOn_iff fam r z).mp (Finset.mem_sdiff.mp (hG hz)).1 |>.2
    have hpair := fullAgreement_inter_eq_jointCore dom (u 0) (u 1) r.1 r.2 hxy
    rw [← hh x hx, ← hh y hy] at hpair
    change A x ∩ A y = D r at hpair
    rw [Finset.disjoint_left]
    intro z hz hz'
    have hcore : z ∈ D r := hpair ▸ Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hz).2, (Finset.mem_inter.mp hz').2⟩
    exact (Finset.mem_compl.mp (Finset.mem_inter.mp (Finset.mem_inter.mp hz).1).2) hcore

private theorem union_budget {I T : Type*} [DecidableEq I] [DecidableEq T]
    (G : Finset I) (E : I → Finset T) (b : I → ℕ)
    (ho : ∀ i ∈ G, ∀ j ∈ G, i ≠ j → 12 * (E i ∩ E j).card ≤ 7 * (b i + b j)) :
    12 * (∑ i ∈ G, (E i).card) + 7 * (∑ i ∈ G, b i) ≤
      12 * (G.biUnion E).card + 7 * G.card * (∑ i ∈ G, b i) := by
  classical
  induction G using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs := ih (fun i hi j hj h => ho i (Finset.mem_insert_of_mem hi)
      j (Finset.mem_insert_of_mem hj) h)
    have hcap : (E a ∩ s.biUnion E).card ≤ ∑ j ∈ s, (E a ∩ E j).card := by
      rw [Finset.inter_biUnion]
      exact Finset.card_biUnion_le
    have hsum : 12 * (∑ j ∈ s, (E a ∩ E j).card) ≤ 7 * (s.card * b a + ∑ j ∈ s, b j) := by
      rw [Finset.mul_sum]
      calc
        ∑ j ∈ s, 12 * (E a ∩ E j).card ≤ ∑ j ∈ s, 7 * (b a + b j) := by
          apply Finset.sum_le_sum
          intro j hj
          exact ho a (Finset.mem_insert_self ..) j (Finset.mem_insert_of_mem hj)
            (fun h => ha (h ▸ hj))
        _ = _ := by rw [← Finset.mul_sum]; simp [Finset.sum_add_distrib]
    have hu := Finset.card_union_add_card_inter (E a) (s.biUnion E)
    simp only [Finset.sum_insert ha, Finset.biUnion_insert, Finset.card_insert_of_notMem ha]
    nlinarith

/-- Five eight-rich exceptional sets cannot fit. All cardinalities and pair
intersections in the hypotheses refer to the sets themselves. -/
theorem no_five_exceptional_sets {I T : Type*} [DecidableEq I] [DecidableEq T] [Fintype T]
    (G : Finset I) (E : I → Finset T) (b : I → ℕ) (h : ℕ) (hG : G.card = 5)
    (hn : Fintype.card T = 4 * h)
    (hE : ∀ i ∈ G, (E i).card = h + 2 + b i)
    (hs : ∀ i ∈ G, 7 * (b i + 3) + 1 ≤ h)
    (ho : ∀ i ∈ G, ∀ j ∈ G, i ≠ j → 6 * (E i ∩ E j).card ≤ 7 * b i) : False := by
  classical
  have hpack := union_budget G E b (fun i hi j hj hne => by
    have h₁ := ho i hi j hj hne
    have h₂ := ho j hj i hi hne.symm
    rw [Finset.inter_comm (E j) (E i)] at h₂
    omega)
  have hsums : ∑ i ∈ G, (E i).card = 5 * (h + 2) + ∑ i ∈ G, b i := by
    calc
      _ = ∑ i ∈ G, (h + 2 + b i) := Finset.sum_congr rfl hE
      _ = _ := by simp [Finset.sum_add_distrib, hG]
  have htotal : ∑ i ∈ G, (7 * b i + 22) ≤ ∑ _i ∈ G, h :=
    Finset.sum_le_sum (fun i hi => by have := hs i hi; omega)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at htotal
  simp [hG] at htotal
  have hdom := Finset.card_le_univ (G.biUnion E)
  rw [hn] at hdom
  rw [hsums, hG] at hpack
  omega

/-- At the half-rate predecessor on any domain of size (4h), a putative
counterexample to the single-line cap has at most four eight-rich lines.
The bound applies to the actual non-joint decoding witness family. -/
theorem at_most_four_rich_lines (fam : BadScalarRichPointFamily dom k δ u)
    (h : ℕ) (hh : 1 ≤ h) (hn : Fintype.card ι = 4 * h) (hk : k = 2 * h)
    (ht : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ = 3 * h + 1)
    (hm : h < fam.G.card) :
    ((lineParameters fam).filter fun l => 8 ≤ (pointsOn fam l).card).card ≤ 4 := by
  classical
  let D (l : LineParameter F) := jointCore dom (u 0) (u 1) l.1 l.2
  let E (l : LineParameter F) := (D l)ᶜ
  let b (l : LineParameter F) := (E l).card - (h + 2)
  by_contra! hlarge
  obtain ⟨G, hG, hfive⟩ := Finset.exists_subset_card_eq (show
      5 ≤ ((lineParameters fam).filter fun l => 8 ≤ (pointsOn fam l).card).card by omega)
  have hparam {l} (hl : l ∈ G) := (Finset.mem_filter.mp (hG hl)).1
  have hrich {l} (hl : l ∈ G) := (Finset.mem_filter.mp (hG hl)).2
  have hpack (l) (hl : l ∈ G) :
      (pointsOn fam l).card * max 1 (3 * h + 1 - (D l).card) + (D l).card ≤ 4 * h := by
    have hp := pointsOn_card_mul_max_add_core_le fam (hparam hl)
    rwa [ht, hn] at hp
  have hE (l) (hl : l ∈ G) : (E l).card = h + 2 + b l := by
    have hz := Finset.card_le_univ (D l)
    rw [hn] at hz
    have hr := hrich hl
    have hcap := line_card_le_complement_threshold_succ (by omega : 3 * h + 1 ≤ 4 * h)
      hz (by omega : 1 ≤ (pointsOn fam l).card) (hpack l hl)
    have hp := pointsOn_card_add_outsideLine_card fam l
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < (outsideLine fam l).card)
    have hf := threshold_sub_pred_le_fresh_card fam l (by omega) (hparam hl) hx
    rw [ht] at hf
    have hsub : fullAgreement dom (u 0) (u 1) x (fam.q x) \ D l ⊆ E l :=
      fun _ hi => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2
    have hc := Finset.card_le_card hsub
    change _ ≤ (fullAgreement dom (u 0) (u 1) x (fam.q x) \ D l).card at hf
    dsimp only [b]
    omega
  apply no_five_exceptional_sets G E b h hfive hn hE
  · intro l hl
    have he := hE l hl
    change (D l)ᶜ.card = _ at he
    rw [Finset.card_compl, hn] at he
    have hz := Finset.card_le_univ (D l)
    rw [hn] at hz
    have hp := hpack l hl
    have hm := Nat.mul_le_mul_right (max 1 (3 * h + 1 - (D l).card)) (hrich hl)
    omega
  · intro l hl r hr hne
    apply overlap_of_eight_points fam l r (hparam hl) hne (hrich hr) (by omega)
    change (E l).card + (k - 1) ≤ _
    rw [hE l hl, ht, hk]
    omega

end ArkLib.ProximityGap.Frontier.RateHalfPredecessorRichLines

#print axioms ArkLib.ProximityGap.Frontier.RateHalfPredecessorRichLines.overlap_of_eight_points

#print axioms ArkLib.ProximityGap.Frontier.RateHalfPredecessorRichLines.no_five_exceptional_sets

#print axioms ArkLib.ProximityGap.Frontier.RateHalfPredecessorRichLines.at_most_four_rich_lines
