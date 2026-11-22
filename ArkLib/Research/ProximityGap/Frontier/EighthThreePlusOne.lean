/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.EighthFourPlusOne

/-! # Three collinear heads and one transverse head through five eighths

The only quartet left near the second-prime budget has no collinear triple.
-/
set_option autoImplicit false
noncomputable section
open Finset Polynomial Code
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.EighthThreePlusOne
open HalfPredecessorLineCoreGeometry HalfPredecessorRateQuarterDeterminantMultiplicity
open HalfPredecessorRateQuarterDeterminantCollapse HalfPredecessorRateQuarterPrimitiveDirection
open HalfPredecessorSecantLines HalfPredecessorBadEventRichPointBridge
open CollinearFreshMultiplicity _root_.ProximityGap
variable {F I : Type} [Field F] [DecidableEq F] [Fintype F] [Fintype I] [DecidableEq I]
variable [Nonempty I] {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

set_option maxHeartbeats 800000 in
private theorem count_sorted (fam : BadScalarRichPointFamily dom 134217728 δ u)
    (n : Fintype.card I = 1073741824) (ht : 402653184 ≤ ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊)
    (a b z : LineParameter F) (ab : a ≠ b) (outside : threeLineDeterminant a b z ≠ 0)
    (L : Fin 3 → LineParameter F) (inj : Function.Injective L)
    (ha : a ∈ lineParameters fam) (hz : z ∈ lineParameters fam) (hl : ∀ i, L i ∈ lineParameters fam)
    (coll : ∀ i, lineDeterminant a b (L i) = 0)
    (G : Fin 3 → Finset F) (assign : ∀ i, G i ⊆ pointsOn fam (L i))
    (dis : ∀ i j, i ≠ j → Disjoint (G i) (G j))
    (sorted : Monotone fun i => max 1 (402653184 - (core dom u (L i)).card)) :
    (∑ i, (G i).card) + (pointsOn fam z).card ≤ 2013265929 := by
  classical
  let C (i : Fin 3) := core dom u (L i)
  let O := core dom u z
  let U := (C 0 ∪ C 1) ∪ C 2
  let J := C 0 ∩ C 1
  let A (i : Fin 3) := max 1 (402653184 - (C i).card)
  let B := max 1 (402653184 - O.card)
  let x (i : Fin 3) := (G i).card
  let y := (pointsOn fam z).card
  let h := max (primitiveIntercept a b).natDegree (primitiveSlope a b).natDegree
  have deg {w : LineParameter F} (hw : w ∈ lineParameters fam) :
      w.1.natDegree ≤ 134217727 ∧ w.2.natDegree ≤ 134217727 := by
    have ⟨h,h'⟩ := lineParameter_degree_lt fam hw
    exact ⟨Nat.le_of_lt_succ h,Nat.le_of_lt_succ h'⟩
  obtain ⟨pair,trans⟩ := EighthCollinearOutlier.overlap dom (u 0) (u 1) a b z ab outside L inj
    coll (deg ha) (deg hz) (fun i => deg (hl i))

  let W := univ.biUnion fun i => C i
  have CW (i : Fin 3) : C i ⊆ W := subset_biUnion_of_mem _ (mem_univ i)
  have UW : U ⊆ W := union_subset (union_subset (CW 0) (CW 1)) (CW 2)
  have owned {t : I} (tU : t ∈ U) : ∃ w, t ∈ core dom u w ∧ lineDeterminant a b w = 0 := by
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp (UW tU)
    exact ⟨L i, hi, coll i⟩
  have get_trans (T : Finset I) (sub : T ⊆ W) :
      T.card + O.card ≤ 1073741824 + (134217727 + h) := by
    have b := (card_le_card (inter_subset_inter_right sub)).trans trans
    change (T ∩ O).card ≤ 134217727 + h at b
    have a' := card_union_add_card_inter T O
    have c' := card_le_univ (T ∪ O)
    omega
  have three : (C 0).card + (C 1).card + (C 2).card ≤
      U.card + J.card + (C 0 ∩ C 2).card + (C 1 ∩ C 2).card := by
    have q := card_union_add_card_inter (C 0) (C 1)
    have r := card_union_add_card_inter (C 0 ∪ C 1) (C 2)
    rw [union_inter_distrib_right] at r
    have j := card_union_le (C 0 ∩ C 2) (C 1 ∩ C 2)
    dsimp [U, J]; omega
  have p01 : J.card + h ≤ 134217727 := pair 0 1 (by decide)
  have p02 := pair 0 2 (by decide)
  have p12 := pair 1 2 (by decide)
  change (C 0 ∩ C 2).card + h ≤ _ at p02
  change (C 1 ∩ C 2).card + h ≤ _ at p12
  have local_mass {w : LineParameter F} (hw : w ∈ lineParameters fam) :
      (pointsOn fam w).card * max 1 (402653184 - (core dom u w).card) +
        (core dom u w).card ≤ 1073741824 := by
    have e := pointsOn_card_mul_max_add_core_le fam hw
    rw [← n]
    exact (Nat.add_le_add_right (Nat.mul_le_mul_left _ (max_le_max_left _ (Nat.sub_le_sub_right ht _))) _).trans e
  have α (i : Fin 3) : 402653184 ≤ (C i).card + A i := by dsimp [A]; omega
  have α₀ := α 0; have α₁ := α 1; have α₂ := α 2
  have β : 402653184 ≤ O.card + B := by dsimp [B]; omega
  have positive (i : Fin 3) : 1 ≤ A i := le_max_left ..
  have bp : 1 ≤ B := le_max_left ..
  have order01 : A 0 ≤ A 1 := sorted (by decide : (0 : Fin 3) ≤ 1)
  have order12 : A 1 ≤ A 2 := sorted (by decide : (1 : Fin 3) ≤ 2)
  have cap (i : Fin 3) : A i * x i ≤ 671088640 + A i := by
    have l := local_mass (hl i)
    have r := Nat.mul_le_mul_right (A i) (card_le_card (assign i))
    change _ * A i + (C i).card ≤ _ at l
    rw [Nat.mul_comm]
    have := α i
    dsimp only [x]
    omega
  have outer : B * y ≤ 671088640 + B := by
    have l := local_mass hz
    change y * B + O.card ≤ _ at l
    rw [mul_comm]; omega

  have each (i : Fin 3) (j : ℕ) (pos : 0 < j) (hj : j ≤ A i) :
      x i ≤ 671088640 / j + 1 := EighthFourPlusOne.population_bound (cap i) _ pos hj
  have outcap (j : ℕ) (pos : 0 < j) (hj : j ≤ B) :
      y ≤ 671088640 / j + 1 := EighthFourPlusOne.population_bound outer _ pos hj
  have sform : (∑ i, x i) = x 0 + x 1 + x 2 := Fin.sum_univ_three _
  change (∑ i, x i) + y ≤ _
  have x₀ := each 0 1 (by decide) (positive 0)
  have x₁ := each 1 1 (by decide) (positive 1)
  have x₂ := each 2 1 (by decide) (positive 2)
  have y₁ := outcap 1 (by decide) bp
  by_cases b₂ : 2 ≤ A 1
  · have v := each 1 2 (by decide) b₂
    have w := each 2 2 (by decide) (by omega)
    omega
  by_cases both : 2 ≤ B ∧ 2 ≤ A 2
  · have v := each 2 2 (by decide) both.2
    have w := outcap 2 (by decide) both.1
    omega
  have nU : U.card ≤ 1073741824 := n ▸ card_le_univ U
  have sj : J ⊆ U := fun t ht => mem_union_left _ (mem_union_left _ (mem_inter.mp ht).1)
  have cij := card_le_card sj
  have c01 := card_union_add_card_inter (C 0) (C 1)
  have c01U : (C 0 ∪ C 1).card ≤ U.card := card_le_card (subset_union_left)
  have upper := get_trans U UW
  by_cases zero : h = 0
  · have cn := EighthFourPlusOne.constant_direction fam ab hl coll assign dis zero U UW
    change (∑ i, x i) ≤ _ at cn
    rw [n] at cn
    change (C 0 ∪ C 1).card + J.card = _ at c01
    omega
  have wt {r : ℕ} (j : Fin r → Fin 3) (ji : Function.Injective j) (D : Finset I)
      (dc : ∀ i, D ⊆ C (j i)) :
      (∑ i, A (j i) * x (j i)) ≤ (U \ D).card + (1073741824 - U.card)*r := by
    have bnd := weighted fam a b ab (L ∘ j) (G ∘ j) (fun _ => hl _) (fun _ => assign _)
      (fun i k ik => dis _ _ (ji.ne ik)) (fun _ => coll _) U D (fun _ => owned) dc
    rw [← n]
    apply le_trans _ bnd
    apply sum_le_sum
    intro i _
    apply Nat.mul_le_mul_right
    dsimp [A]
    exact max_le_max_left 1 (Nat.sub_le_sub_right ht (C (j i)).card)

  let j₂ : Fin 2 → Fin 3 := ![0,1]
  have w₂ := wt j₂ (by decide) J (by
    intro i
    fin_cases i
    · exact inter_subset_left
    · exact inter_subset_right)
  have w₃ := wt id Function.injective_id ∅ (fun _ => empty_subset _)
  rw [card_sdiff_of_subset sj, Fin.sum_univ_two] at w₂
  rw [sdiff_empty, Fin.sum_univ_three] at w₃
  change A 0 * x 0 + A 1 * x 1 ≤ _ at w₂
  change A 0 * x 0 + A 1 * x 1 + A 2 * x 2 ≤ _ at w₃
  have a₀ : A 0 = 1 := by have := positive 0; omega
  have a₁ : A 1 = 1 := by have := positive 1; omega
  rw [a₀, a₁, one_mul, one_mul] at w₂ w₃
  have tri : 6 ≤ A 0 + A 1 + A 2 + B := by omega
  by_cases c₁ : A 2 = 1
  · have y₃ := outcap 3 (by decide) (by omega)
    rw [c₁, one_mul] at w₃
    omega
  have c₃ : 3 ≤ A 2 := by have := positive 2; omega
  have geom : 939524098 ≤ U.card + J.card + A 2 := by omega
  have geom' : 805306372 ≤ U.card + A 2 := by omega
  have total₂ : x 0 + x 1 ≤ 1207959550 + A 2 := by omega
  have total₃ : x 0 + x 1 + A 2 * x 2 ≤ 1610612728 + 2 * A 2 := by omega
  by_cases enormous : 134217717 ≤ A 2
  · have v := each 2 134217717 (by decide) enormous
    omega
  by_cases veryLarge : 67108864 ≤ A 2
  · have v := each 2 67108864 (by decide) veryLarge
    omega
  by_cases large : 11 ≤ A 2
  · have v := each 2 11 (by decide) large
    omega
  by_cases mid : 6 ≤ A 2
  · have v := each 2 6 (by decide) mid
    omega
  have low := Nat.mul_le_mul_right (x 2) c₃
  omega

/-- At most three leading heads' personal capacities plus six additional
labels can lie on a collinear triple and a transverse fourth head. -/
theorem covered (fam : BadScalarRichPointFamily dom 134217728 δ u)
    (n : Fintype.card I = 1073741824)
    (ht : 402653184 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (L : Fin 3 → LineParameter F) (inj : Function.Injective L)
    (hl : ∀ i, L i ∈ lineParameters fam)
    (coll : ∀ i, lineDeterminant (L 0) (L 1) (L i) = 0)
    (z : LineParameter F) (hz : z ∈ lineParameters fam)
    (out : threeLineDeterminant (L 0) (L 1) z ≠ 0) :
    ((univ.biUnion fun i => pointsOn fam (L i)) ∪ pointsOn fam z).card ≤ 2013265929 := by
  apply EighthFiveRichSafety.cover_of_sorted_assignments _ _
    (fun i => max 1 (402653184 - (core dom u (L i)).card))
  intro p sorted G assigned dis
  exact count_sorted fam n ht (L 0) (L 1) z (inj.ne (by decide)) out (L ∘ p)
    (inj.comp p.injective) (hl 0) hz (fun _ => hl _) (fun _ => coll _) G assigned dis sorted

#print axioms covered
end ArkLib.ProximityGap.Frontier.EighthThreePlusOne
