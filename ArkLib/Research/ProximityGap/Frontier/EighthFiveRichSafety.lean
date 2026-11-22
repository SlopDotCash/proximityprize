/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.CollinearFreshMultiplicity
import Mathlib.Data.Fin.Tuple.Sort

/-! # The five-rich-head allocation at two errors before five eighths -/
set_option autoImplicit false
noncomputable section
open Finset Polynomial Code
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.EighthFiveRichSafety
open HalfPredecessorLineCoreGeometry HalfPredecessorRateQuarterDeterminantMultiplicity
open HalfPredecessorRateQuarterDeterminantCollapse HalfPredecessorRateQuarterPrimitiveDirection
open HalfPredecessorSecantLines HalfPredecessorBadEventRichPointBridge
open CollinearFreshMultiplicity _root_.ProximityGap
variable {F I : Type} [Field F] [DecidableEq F] [Fintype F] [Fintype I] [DecidableEq I]
variable [Nonempty I] {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

omit [Nonempty I] in
/-- Upper bounds for the two helpful unions, and the common core lost by
both leading heads. All four cores have the agreed minimum size. -/
private theorem unions (C : Fin 4 → Finset I) (O : Finset I) (h : ℕ)
    (n : Fintype.card I = 1073741824) (rich : ∀ i, 402587648 ≤ (C i).card)
    (pair : ∀ i j, i ≠ j → (C i ∩ C j).card + h ≤ 134217727)
    (out : (((C 0 ∪ C 1) ∪ C 2) ∩ O).card ≤ 134217727 + h) :
    let U := (C 0 ∪ C 1) ∪ C 2
    let V := U ∪ C 3
    805044224 ≤ V.card ∧
      (402653183 ≤ O.card → 939196416 ≤ U.card + (C 0 ∩ C 1).card) ∧
      (C 0).card + (C 1).card + (C 2).card + O.card ≤ 1610612732 := by
  let U := (C 0 ∪ C 1) ∪ C 2
  let V := U ∪ C 3
  have three :
      (C 0).card + (C 1).card + (C 2).card ≤ U.card +
      (C 0 ∩ C 1).card + (C 0 ∩ C 2).card + (C 1 ∩ C 2).card := by
    have d1 := card_union_add_card_inter (C 0) (C 1)
    have d2 := card_union_add_card_inter (C 0 ∪ C 1) (C 2)
    rw [union_inter_distrib_right] at d2
    have l := card_union_le (C 0 ∩ C 2) (C 1 ∩ C 2)
    dsimp [U]; omega
  have four : U.card + (C 3).card ≤ V.card + (C 0 ∩ C 3).card +
      (C 1 ∩ C 3).card + (C 2 ∩ C 3).card := by
    have l := card_union_add_card_inter U (C 3)
    dsimp [U] at l
    rw [union_inter_distrib_right,union_inter_distrib_right] at l
    have d1 := card_union_le (C 0 ∩ C 3) (C 1 ∩ C 3)
    have d2 := card_union_le ((C 0 ∩ C 3) ∪ (C 1 ∩ C 3)) (C 2 ∩ C 3)
    dsimp [V,U]; omega
  have together : U.card + O.card ≤ 1073741824 + (134217727 + h) := by
    have l := card_union_add_card_inter U O
    have hl := card_le_univ (U ∪ O)
    change (U ∩ O).card ≤ _ at out
    omega
  have p01 := pair 0 1 (by decide)
  have p02 := pair 0 2 (by decide)
  have p12 := pair 1 2 (by decide)
  have p03 := pair 0 3 (by decide)
  have p13 := pair 1 3 (by decide)
  have p23 := pair 2 3 (by decide)
  have r0 := rich 0; have r1 := rich 1; have r2 := rich 2; have r3 := rich 3
  change _ ≤ V.card ∧ (_ → _ ≤ U.card + _) ∧ _
  omega

private theorem count_sorted (fam : BadScalarRichPointFamily dom 134217728 δ u)
    (n : Fintype.card I = 1073741824) (ht : 402653186 ≤ ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊)
    (a b z : LineParameter F) (ab : a ≠ b) (outside : threeLineDeterminant a b z ≠ 0)
    (L : Fin 4 → LineParameter F) (inj : Function.Injective L)
    (ha : a ∈ lineParameters fam) (hz : z ∈ lineParameters fam) (hl : ∀ i, L i ∈ lineParameters fam)
    (coll : ∀ i, lineDeterminant a b (L i) = 0)
    (G : Fin 4 → Finset F) (assign : ∀ i, G i ⊆ pointsOn fam (L i))
    (dis : ∀ i j, i ≠ j → Disjoint (G i) (G j))
    (large : ∀ i, 20000 ≤ (pointsOn fam (L i)).card)
    (sorted : Monotone fun i => max 1 (402653186 - (core dom u (L i)).card)) :
    (∑ i, (G i).card) + (pointsOn fam z).card ≤ 2049000000 := by
  classical
  let C (i : Fin 4) := core dom u (L i)
  let O := core dom u z
  let U := (C 0 ∪ C 1) ∪ C 2
  let V := U ∪ C 3
  let J := C 0 ∩ C 1
  let A (i : Fin 4) := max 1 (402653186 - (C i).card)
  let B := max 1 (402653186 - O.card)
  let x (i : Fin 4) := (G i).card
  let y := (pointsOn fam z).card
  let h := max (primitiveIntercept a b).natDegree (primitiveSlope a b).natDegree
  have deg {w : LineParameter F} (hw : w ∈ lineParameters fam) :
      w.1.natDegree ≤ 134217727 ∧ w.2.natDegree ≤ 134217727 := by
    have ⟨h,h'⟩ := lineParameter_degree_lt fam hw
    exact ⟨Nat.le_of_lt_succ h,Nat.le_of_lt_succ h'⟩
  obtain ⟨pair,trans⟩ := EighthCollinearOutlier.overlap dom (u 0) (u 1) a b z ab outside L inj
    coll (deg ha) (deg hz) (fun i => deg (hl i))
  have owned {t : I} (tV : t ∈ V) : ∃ w, t ∈ core dom u w ∧ lineDeterminant a b w = 0 := by
    simp only [V,U,mem_union] at tV
    rcases tV with ((h|h)|h)|h
    · exact ⟨L 0,h,coll 0⟩
    · exact ⟨L 1,h,coll 1⟩
    · exact ⟨L 2,h,coll 2⟩
    · exact ⟨L 3,h,coll 3⟩
  have tu : (U ∩ O).card ≤ 134217727 + h := by
    apply (card_le_card (inter_subset_inter_right ?_)).trans trans
    intro i hi
    simp only [U,mem_union] at hi
    rcases hi with (h|h)|h
    · exact mem_biUnion.mpr ⟨0,mem_univ _,h⟩
    · exact mem_biUnion.mpr ⟨1,mem_univ _,h⟩
    · exact mem_biUnion.mpr ⟨2,mem_univ _,h⟩
  have local_mass {w : LineParameter F} (hw : w ∈ lineParameters fam) :
      (pointsOn fam w).card * max 1 (402653186 - (core dom u w).card) +
        (core dom u w).card ≤ 1073741824 := by
    have e := pointsOn_card_mul_max_add_core_le fam hw
    rw [← n]
    exact (Nat.add_le_add_right (Nat.mul_le_mul_left _ (max_le_max_left _ (Nat.sub_le_sub_right ht _))) _).trans e
  have big (i : Fin 4) : 402587648 ≤ (C i).card := by
    have e := local_mass (hl i)
    have lb := Nat.mul_le_mul (large i) (le_max_right 1 (402653186 - (C i).card))
    change _ * max 1 (402653186 - (C i).card) + (C i).card ≤ _ at e
    omega
  have ⟨vsize,usize,sumC⟩ := unions C O h n big pair tu
  have vN : V.card ≤ 1073741824 := n ▸ card_le_univ V
  have uN : U.card ≤ 1073741824 := n ▸ card_le_univ U
  have sj : J ⊆ U := fun t ht => mem_union_left _ (mem_union_left _ (mem_inter.mp ht).1)
  have overall : (∑ i, x i) ≤ V.card + (1073741824 - V.card)*4 := by
    have bnd := weighted fam a b ab L G hl assign dis coll V ∅ (fun _ => owned) (fun _ => empty_subset _)
    simp only [sdiff_empty,n] at bnd
    exact (sum_le_sum fun i _ => Nat.le_mul_of_pos_left _ (by omega)).trans bnd
  let j : Fin 2 → Fin 4 := ![0,1]
  have both : x 0 + x 1 ≤ U.card - J.card + (1073741824 - U.card)*2 := by
    have bnd := weighted fam a b ab (L ∘ j) (G ∘ j) (fun _ => hl _) (fun _ => assign _)
      (fun i k ik => dis _ _ ((by decide : Function.Injective j).ne ik)) (fun _ => coll _) U J
      (fun _ hi => owned (mem_union_left _ hi)) (by
        intro i; fin_cases i
        · exact inter_subset_left
        · exact inter_subset_right)
    dsimp only at bnd
    rw [card_sdiff_of_subset sj,n,Fin.sum_univ_two] at bnd
    exact (Nat.add_le_add (Nat.le_mul_of_pos_left _ (by omega)) (Nat.le_mul_of_pos_left _ (by omega))).trans bnd
  have alpha (i : Fin 4) : 402653186 ≤ (C i).card + A i := by dsimp [A]; omega
  have beta : 402653186 ≤ O.card + B := by dsimp [B]; omega
  have one (w : LineParameter F) (hw : w ∈ lineParameters fam) (j g : ℕ)
      (hj : 0 < j) (h : j ≤ max 1 (402653186 - (core dom u w).card))
      (hg : g ≤ (pointsOn fam w).card) : g ≤ 671088638/j + 1 := by
    let a := max 1 (402653186 - (core dom u w).card)
    have cap := local_mass hw
    have le := Nat.mul_le_mul_right a hg
    change _ * a + (core dom u w).card ≤ _ at cap
    have rel : 402653186 ≤ (core dom u w).card + a := by dsimp [a]; omega
    have al : j ≤ a := h
    have limg : (g-1)*a ≤ 671088638 := by rw [Nat.sub_mul,Nat.one_mul]; omega
    have lim := (Nat.mul_le_mul_left (g-1) al).trans limg
    have ok := (Nat.le_div_iff_mul_le hj).mpr lim
    omega
  have each (i : Fin 4) (j : ℕ) (jp : 0<j) (h : j ≤ A i) : x i ≤ 671088638/j+1 :=
    one _ (hl i) j _ jp h (card_le_card (assign i))
  have outcap (j : ℕ) (jp : 0<j) (h : j ≤ B) : y ≤ 671088638/j+1 :=
    one _ hz j _ jp h (le_refl _)
  have ord01 : A 0 ≤ A 1 := sorted (by decide : (0:Fin 4)≤1)
  have ord12 : A 1 ≤ A 2 := sorted (by decide : (1:Fin 4)≤2)
  have ord23 : A 2 ≤ A 3 := sorted (by decide : (2:Fin 4)≤3)
  have posA (i : Fin 4) : 1 ≤ A i := le_max_left ..
  have posB : 1 ≤ B := le_max_left ..
  have deficit : 12 ≤ A 0+A 1+A 2+B := by
    have h₀ := alpha 0; have h₁ := alpha 1; have h₂ := alpha 2; omega
  have sform : (∑ i, x i) = x 0 + x 1 + x 2 + x 3 := by
    rw [Fin.sum_univ_four]
  change (∑ i, x i) + y ≤ _
  by_cases hz4 : 4 ≤ B
  · have h := outcap 4 (by decide) hz4
    change 805044224 ≤ V.card at vsize
    omega
  rw [sform]
  have yb := outcap 1 (by decide) posB
  by_cases h0 : 2 ≤ A 0
  · have h₀ := each 0 2 (by decide) h0; have h₁ := each 1 2 (by decide) (by omega)
    have h₂ := each 2 2 (by decide) (by omega); have h₃ := each 3 2 (by decide) (by omega); omega
  have h₀ := each 0 1 (by decide) (posA 0)
  by_cases h1 : 3 ≤ A 1
  · have h₁ := each 1 3 (by decide) h1; have h₂ := each 2 3 (by decide) (by omega)
    have h₃ := each 3 3 (by decide) (by omega); omega
  by_cases h1' : 2 ≤ A 1
  · have h₁ := each 1 2 (by decide) h1'
    have h₂ := each 2 6 (by decide) (by omega); have h₃ := each 3 6 (by decide) (by omega); omega
  have h₂ := each 2 7 (by decide) (by omega); have h₃ := each 3 7 (by decide) (by omega)
  have uc : 939196416 ≤ U.card + J.card := usize (by omega)
  have js := card_le_card sj
  by_cases zz : 2 ≤ B
  · have y₂ := outcap 2 (by decide) zz; omega
  have h₂' := each 2 9 (by decide) (by omega); have h₃' := each 3 9 (by decide) (by omega)
  omega

/-- Sort the heads and assign each covered label to its first representative. -/
theorem cover_of_sorted_assignments {s B : ℕ} {Label : Type*} [DecidableEq Label]
    (T : Fin s → Finset Label) (O : Finset Label) (deficit : Fin s → ℕ)
    (bound : ∀ (p : Equiv.Perm (Fin s)), Monotone (deficit ∘ p) →
      ∀ (G : Fin s → Finset Label), (∀ i, G i ⊆ T (p i)) →
      (∀ i j, i ≠ j → Disjoint (G i) (G j)) →
      (∑ i, (G i).card) + O.card ≤ B) : ((univ.biUnion T) ∪ O).card ≤ B := by
  classical
  let p := Tuple.sort deficit
  let S (i : Fin s) := T (p i)
  let G (i : Fin s) := S i \ (Iio i).biUnion S
  have assigned (i : Fin s) : G i ⊆ T (p i) := sdiff_subset
  have dis (i j : Fin s) (ij : i ≠ j) : Disjoint (G i) (G j) := by
    rw [disjoint_left]
    intro x xi xj
    have hi := mem_sdiff.mp xi
    have hj := mem_sdiff.mp xj
    rcases lt_or_gt_of_ne ij with h | h
    · exact hj.2 (mem_biUnion.mpr ⟨i,mem_Iio.mpr h,hi.1⟩)
    · exact hi.2 (mem_biUnion.mpr ⟨j,mem_Iio.mpr h,hj.1⟩)
  have bd := bound p (Tuple.monotone_sort deficit) G assigned dis
  have sub : (univ.biUnion T) ⊆ univ.biUnion G := by
    intro x hx
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hx
    let W := univ.filter fun j : Fin s => x ∈ S j
    have hw : W.Nonempty := ⟨p.symm i,mem_filter.mpr ⟨mem_univ _,
      by simpa [S] using hi⟩⟩
    let j := W.min' hw
    have hj := mem_filter.mp (W.min'_mem hw)
    exact mem_biUnion.mpr ⟨j,mem_univ _,mem_sdiff.mpr ⟨hj.2,by
      intro use
      obtain ⟨i,ij,xi⟩ := mem_biUnion.mp use
      exact (mem_Iio.mp ij).not_ge (W.min'_le _ (mem_filter.mpr ⟨mem_univ _,xi⟩))⟩⟩
  exact (card_union_le ..).trans ((Nat.add_le_add_right ((card_le_card sub).trans card_biUnion_le) _).trans bd)

/-- Four collinear heads each carrying at least 20,000 labels, together with an
arbitrary transverse head, carry at most 2,049,000,000 distinct bad scalars at
this step or any earlier step. Fresh scalar assignments are constructed internally. -/
theorem covered (fam : BadScalarRichPointFamily dom 134217728 δ u)
    (n : Fintype.card I = 1073741824) (ht : 402653186 ≤ ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊)
    (L : Fin 4 → LineParameter F) (inj : Function.Injective L)
    (hl : ∀ i, L i ∈ lineParameters fam) (large : ∀ i, 20000 ≤ (pointsOn fam (L i)).card)
    (coll : ∀ i, lineDeterminant (L 0) (L 1) (L i) = 0)
    (z : LineParameter F) (hz : z ∈ lineParameters fam) (out : threeLineDeterminant (L 0) (L 1) z ≠ 0) :
    ((univ.biUnion fun i => pointsOn fam (L i)) ∪ pointsOn fam z).card ≤ 2049000000 := by
  apply cover_of_sorted_assignments _ _ (fun i => max 1 (402653186 - (core dom u (L i)).card))
  intro p sorted G assigned dis
  exact count_sorted fam n ht (L 0) (L 1) z (inj.ne (by decide)) out (L ∘ p)
    (inj.comp p.injective) (hl 0) hz (fun _ => hl _) (fun _ => coll _) G assigned dis
    (fun _ => large _) sorted

#print axioms covered
end ArkLib.ProximityGap.Frontier.EighthFiveRichSafety
