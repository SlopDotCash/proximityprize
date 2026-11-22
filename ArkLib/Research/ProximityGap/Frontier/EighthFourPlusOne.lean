/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.CollinearFreshMultiplicity
import ArkLib.Research.ProximityGap.Frontier.EighthFiveRichSafety
import ArkLib.Research.ProximityGap.Frontier.EighthOutlierArithmetic

/-! # Four collinear heads and one transverse head through five eighths -/
set_option autoImplicit false
noncomputable section
open Finset Polynomial Code
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.EighthFourPlusOne
open HalfPredecessorLineCoreGeometry HalfPredecessorRateQuarterDeterminantMultiplicity
open HalfPredecessorRateQuarterDeterminantCollapse HalfPredecessorRateQuarterPrimitiveDirection
open HalfPredecessorSecantLines HalfPredecessorBadEventRichPointBridge
open CollinearFreshMultiplicity _root_.ProximityGap
variable {F I : Type} [Field F] [DecidableEq F] [Fintype F] [Fintype I] [DecidableEq I]
variable [Nonempty I] {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

/-- The available fresh sites bound the population at any smaller positive deficit. -/
theorem population_bound {w v : ℕ} (bound : w * v ≤ 671088640 + w) (j : ℕ)
      (jpos : 0 < j) (h : j ≤ w) : v ≤ 671088640 / j + 1 := by
  have lim : (v-1)*w ≤ 671088640 := by rw [Nat.sub_mul, one_mul, mul_comm]; omega
  have ok := (Nat.le_div_iff_mul_le jpos).mpr ((Nat.mul_le_mul_left (v-1) h).trans lim)
  omega

/-- A constant primitive direction accounts for at most one covered label across
the cluster, even when some of the listed heads have few assigned labels. -/
theorem constant_direction {k s : ℕ} {L : Fin s → LineParameter F} {G : Fin s → Finset F}
    {a b : LineParameter F} (fam : BadScalarRichPointFamily dom k δ u) (ab : a ≠ b)
    (hl : ∀ i, L i ∈ lineParameters fam) (coll : ∀ i, lineDeterminant a b (L i) = 0)
    (assign : ∀ i, G i ⊆ pointsOn fam (L i)) (dis : ∀ i j, i ≠ j → Disjoint (G i) (G j))
    (zero : max (primitiveIntercept a b).natDegree (primitiveSlope a b).natDegree = 0)
    (U : Finset I) (owned : U ⊆ univ.biUnion fun i => core dom u (L i)) :
    (∑ i, (G i).card) ≤ 1 + (Fintype.card I - U.card) * s := by
  classical
  let H := univ.image L
  have hH : H ⊆ lineParameters fam := by
    intro c hc
    obtain ⟨i, _, rfl⟩ := mem_image.mp hc
    exact hl i
  have Hcoll (c : LineParameter F) (hc : c ∈ H) : lineDeterminant a b c = 0 := by
    obtain ⟨i, _, rfl⟩ := mem_image.mp hc
    exact coll i
  have imageBound := TerminalCollinearHeadCount.collinear_card_image fam H hH a b ab Hcoll
  let V := H.biUnion (core dom u)
  change (H.biUnion (pointsOn fam)).card ≤ (V.image _).card + (Fintype.card I - V.card)*H.card
    at imageBound
  have Usub : U ⊆ V := by
    intro i hi
    obtain ⟨j, _, hj⟩ := mem_biUnion.mp (owned hi)
    exact mem_biUnion.mpr ⟨L j, mem_image_of_mem L (mem_univ _), hj⟩
  have vs := card_le_card Usub
  have Hsize : H.card ≤ s := card_image_le.trans (by simp)
  have cv (p : F[X]) (zero : p.natDegree = 0) (t : F) : p.eval t = p.coeff 0 := by
    conv_lhs => rw [eq_C_of_natDegree_eq_zero zero]
    simp
  have z1 : (primitiveIntercept a b).natDegree = 0 := by omega
  have z2 : (primitiveSlope a b).natDegree = 0 := by omega
  have singleton : (V.image fun i => primitiveScalarAt a b (dom i)).card ≤ 1 := by
    apply card_le_one.mpr
    intro c hc f hf
    obtain ⟨i, _, rfl⟩ := mem_image.mp hc
    obtain ⟨j, _, rfl⟩ := mem_image.mp hf
    simp only [primitiveScalarAt, cv _ z1, cv _ z2]
  have mass : (∑ i, (G i).card) ≤ (H.biUnion (pointsOn fam)).card := by
    have sub : univ.biUnion G ⊆ H.biUnion (pointsOn fam) := by
      intro t ht
      obtain ⟨i, _, hi⟩ := mem_biUnion.mp ht
      exact mem_biUnion.mpr ⟨L i, mem_image_of_mem L (mem_univ _), assign i hi⟩
    have lin := card_le_card sub
    rw [card_biUnion (fun i _ j _ hij => dis i j hij)] at lin
    exact lin
  have rem := Nat.mul_le_mul_left (Fintype.card I - V.card) Hsize
  have ud := Nat.mul_le_mul_right s (Nat.sub_le_sub_left vs (Fintype.card I))
  exact mass.trans (imageBound.trans ((Nat.add_le_add singleton (rem.trans ud))))

private theorem count_sorted (fam : BadScalarRichPointFamily dom 134217728 δ u)
    (n : Fintype.card I = 1073741824) (ht : 402653184 ≤ ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊)
    (a b z : LineParameter F) (ab : a ≠ b) (outside : threeLineDeterminant a b z ≠ 0)
    (L : Fin 4 → LineParameter F) (inj : Function.Injective L)
    (ha : a ∈ lineParameters fam) (hz : z ∈ lineParameters fam) (hl : ∀ i, L i ∈ lineParameters fam)
    (coll : ∀ i, lineDeterminant a b (L i) = 0)
    (G : Fin 4 → Finset F) (assign : ∀ i, G i ⊆ pointsOn fam (L i))
    (dis : ∀ i j, i ≠ j → Disjoint (G i) (G j))
    (sorted : Monotone fun i => max 1 (402653184 - (core dom u (L i)).card)) :
    (∑ i, (G i).card) + (pointsOn fam z).card ≤ 2058021547 := by
  classical
  let C (i : Fin 4) := core dom u (L i)
  let O := core dom u z
  let U := (C 0 ∪ C 1) ∪ C 2
  let J := C 0 ∩ C 1
  let A (i : Fin 4) := max 1 (402653184 - (C i).card)
  let B := max 1 (402653184 - O.card)
  let x (i : Fin 4) := (G i).card
  let y := (pointsOn fam z).card
  let h := max (primitiveIntercept a b).natDegree (primitiveSlope a b).natDegree
  have deg {w : LineParameter F} (hw : w ∈ lineParameters fam) :
      w.1.natDegree ≤ 134217727 ∧ w.2.natDegree ≤ 134217727 := by
    have ⟨h,h'⟩ := lineParameter_degree_lt fam hw
    exact ⟨Nat.le_of_lt_succ h,Nat.le_of_lt_succ h'⟩
  obtain ⟨pair,trans⟩ := EighthCollinearOutlier.overlap dom (u 0) (u 1) a b z ab outside L inj
    coll (deg ha) (deg hz) (fun i => deg (hl i))

  let W := univ.biUnion fun i => C i
  have CW (i : Fin 4) : C i ⊆ W := subset_biUnion_of_mem _ (mem_univ i)
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
  have four : U.card + (C 3).card ≤ W.card + (C 0 ∩ C 3).card +
      (C 1 ∩ C 3).card + (C 2 ∩ C 3).card := by
    have q := card_union_add_card_inter U (C 3)
    have r := card_le_card (union_subset UW (CW 3))
    dsimp [U] at q r
    rw [union_inter_distrib_right, union_inter_distrib_right] at q
    have j := card_union_le (C 0 ∩ C 3) (C 1 ∩ C 3)
    have k := card_union_le ((C 0 ∩ C 3) ∪ (C 1 ∩ C 3)) (C 2 ∩ C 3)
    dsimp [U]; omega
  have p01 : J.card + h ≤ 134217727 := pair 0 1 (by decide)
  have p02 := pair 0 2 (by decide)
  have p12 := pair 1 2 (by decide)
  have p03 := pair 0 3 (by decide)
  have p13 := pair 1 3 (by decide)
  have p23 := pair 2 3 (by decide)
  change (C 0 ∩ C 2).card + h ≤ _ at p02
  change (C 1 ∩ C 2).card + h ≤ _ at p12
  change (C 0 ∩ C 3).card + h ≤ _ at p03
  change (C 1 ∩ C 3).card + h ≤ _ at p13
  change (C 2 ∩ C 3).card + h ≤ _ at p23
  have local_mass {w : LineParameter F} (hw : w ∈ lineParameters fam) :
      (pointsOn fam w).card * max 1 (402653184 - (core dom u w).card) +
        (core dom u w).card ≤ 1073741824 := by
    have e := pointsOn_card_mul_max_add_core_le fam hw
    rw [← n]
    exact (Nat.add_le_add_right (Nat.mul_le_mul_left _ (max_le_max_left _ (Nat.sub_le_sub_right ht _))) _).trans e
  have α (i : Fin 4) : 402653184 ≤ (C i).card + A i := by dsimp [A]; omega
  have α₀ := α 0; have α₁ := α 1; have α₂ := α 2; have α₃ := α 3
  have β : 402653184 ≤ O.card + B := by dsimp [B]; omega
  have positive (i : Fin 4) : 1 ≤ A i := le_max_left ..
  have bp : 1 ≤ B := le_max_left ..
  have order01 : A 0 ≤ A 1 := sorted (by decide : (0 : Fin 4) ≤ 1)
  have order12 : A 1 ≤ A 2 := sorted (by decide : (1 : Fin 4) ≤ 2)
  have order23 : A 2 ≤ A 3 := sorted (by decide : (2 : Fin 4) ≤ 3)
  have cap (i : Fin 4) : A i * x i ≤ 671088640 + A i := by
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
  have each (i : Fin 4) := population_bound (cap i) 1 (by decide) (positive i)
  have yb := population_bound outer 1 (by decide) bp
  have sform : (∑ i, x i) = x 0 + x 1 + x 2 + x 3 := Fin.sum_univ_four _
  change (∑ i, x i) + y ≤ _
  by_cases weak : 1025 ≤ A 2
  · have a₂ := population_bound (cap 2) 1025 (by decide) weak
    have a₃ := population_bound (cap 3) 1025 (by decide) (by omega)
    have a₀ := each 0; have a₁ := each 1
    omega
  have us : 805303296 ≤ U.card := by omega
  have usj : 939521024 ≤ U.card + J.card := by omega
  have nU : U.card ≤ 1073741824 := n ▸ card_le_univ U
  have sj : J ⊆ U := fun t ht => mem_union_left _ (mem_union_left _ (mem_inter.mp ht).1)
  have wt {r : ℕ} (j : Fin r → Fin 4) (ji : Function.Injective j) (D : Finset I)
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
  let j₂ : Fin 2 → Fin 4 := ![0,1]
  let j₃ : Fin 3 → Fin 4 := ![0,1,2]
  have w₂ := wt j₂ (by decide) J (by intro i; fin_cases i; exact inter_subset_left; exact inter_subset_right)
  have w₃ := wt j₃ (by decide) ∅ (fun _ => empty_subset _)
  have w₄ := wt id Function.injective_id ∅ (fun _ => empty_subset _)
  rw [card_sdiff_of_subset sj, Fin.sum_univ_two] at w₂
  rw [sdiff_empty, Fin.sum_univ_three] at w₃
  rw [sdiff_empty, Fin.sum_univ_four] at w₄
  dsimp only [j₂, j₃, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_zero,
    id_eq] at w₂ w₃ w₄
  change A 0 * x 0 + A 1 * x 1 + A 2 * x 2 ≤ _ at w₃
  have cij := card_le_card sj
  have p₂ : A 0 * x 0 + A 1 * x 1 ≤ 1207959552 + 16384 := by omega
  have p₃ : A 0 * x 0 + A 1 * x 1 + A 2 * x 2 ≤ 1610612736 + 16384 := by omega
  have p₄ : A 0 * x 0 + A 1 * x 1 + A 2 * x 2 + A 3 * x 3 ≤ 1879048192 + 16384 := by omega
  have total : (∑ i, x i) ≤ 1879048192 + 16384 := by
    rw [sform]
    have h0 := Nat.le_mul_of_pos_left (x 0) (positive 0)
    have h1 := Nat.le_mul_of_pos_left (x 1) (positive 1)
    have h2 := Nat.le_mul_of_pos_left (x 2) (positive 2)
    have h3 := Nat.le_mul_of_pos_left (x 3) (positive 3)
    omega
  by_cases big : 4 ≤ B
  · have h := population_bound outer 4 (by decide) big
    omega
  by_cases zero : h = 0
  · have cn := constant_direction fam ab hl coll assign dis zero U UW
    change (∑ i, x i) ≤ _ at cn
    rw [n] at cn
    omega
  let c (i : Fin 4) := min 12 (A i)
  have c_le (i : Fin 4) : c i ≤ A i := min_le_right _ _
  have c₀ := Nat.mul_le_mul_right (x 0) (c_le 0)
  have c₁ := Nat.mul_le_mul_right (x 1) (c_le 1)
  have c₂ := Nat.mul_le_mul_right (x 2) (c_le 2)
  have c₃ := Nat.mul_le_mul_right (x 3) (c_le 3)
  have tu := get_trans U UW
  have tv := get_trans W (Subset.rfl)
  have trip : 6 ≤ c 0 + c 1 + c 2 + B := by dsimp [c]; omega
  have quad : 12 ≤ c 0 + c 1 + c 2 + c 3 + B := by dsimp [c]; omega
  have one := cap 0
  have h0 := positive 0
  rw [sform]
  apply EighthOutlierArithmetic.count (a := c 0) (b := c 1) (c := c 2) (d := c 3)
    (z := B) (by dsimp [c]; omega) (min_le_min_left _ order01) (min_le_min_left _ order12)
    (min_le_min_left _ order23) bp trip quad
  · omega
  · omega
  · omega
  · omega
  · exact outer

/-- Four distinct collinear polynomial heads and a transverse fifth head carry
at most 2,058,021,547 labels at eighth rate through 671,088,640 errors. -/
theorem covered (fam : BadScalarRichPointFamily dom 134217728 δ u)
    (n : Fintype.card I = 1073741824)
    (ht : 402653184 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (L : Fin 4 → LineParameter F) (inj : Function.Injective L)
    (hl : ∀ i, L i ∈ lineParameters fam)
    (coll : ∀ i, lineDeterminant (L 0) (L 1) (L i) = 0)
    (z : LineParameter F) (hz : z ∈ lineParameters fam)
    (out : threeLineDeterminant (L 0) (L 1) z ≠ 0) :
    ((univ.biUnion fun i => pointsOn fam (L i)) ∪ pointsOn fam z).card ≤ 2058021547 := by
  apply EighthFiveRichSafety.cover_of_sorted_assignments _ _
    (fun i => max 1 (402653184 - (core dom u (L i)).card))
  intro p sorted G assigned dis
  exact count_sorted fam n ht (L 0) (L 1) z (inj.ne (by decide)) out (L ∘ p)
    (inj.comp p.injective) (hl 0) hz (fun _ => hl _) (fun _ => coll _) G assigned dis sorted

#print axioms covered
end ArkLib.ProximityGap.Frontier.EighthFourPlusOne
