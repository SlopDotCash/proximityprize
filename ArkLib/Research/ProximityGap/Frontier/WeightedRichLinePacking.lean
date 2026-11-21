/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib

/-! # Counting rich lines in a weighted finite point set

Only the intersection property of affine lines is needed: two different lines
have at most one common point. Distinct pairs of points charge the lines away
from the heavy atoms. Lines through a given heavy atom use disjoint light sets.
-/
set_option autoImplicit false
noncomputable section
open Finset
namespace ArkLib.ProximityGap.Frontier.WeightedRichLinePacking
variable {P J : Type*} [DecidableEq P] [DecidableEq J]

abbrev mass {A : Type*} (w : A → ℕ) (S : Finset A) := ∑ x ∈ S, w x

/-- A finite weighted linear incidence system at a prescribed agreement count. -/
structure Arrangement (P J : Type*) [DecidableEq P] (t : ℕ) where
  points : Finset P
  lines : Finset J
  block : J → Finset P
  w : P → ℕ
  positive : ∀ x ∈ points, 0 < w x
  inside : ∀ i ∈ lines, block i ⊆ points
  rich : ∀ i ∈ lines, t ≤ mass w (block i)
  nontrivial : ∀ i ∈ lines, 2 ≤ (block i).card
  linear : ∀ i ∈ lines, ∀ j ∈ lines, i ≠ j → ((block i) ∩ (block j)).card ≤ 1

namespace Arrangement

variable {t : ℕ} (A : Arrangement P J t)

omit [DecidableEq J] in
private theorem shared {i j : J} (hi : i ∈ A.lines) (hj : j ∈ A.lines) (hne : i≠j)
    {x y : P} (xi : x ∈ A.block i) (xj : x ∈ A.block j)
    (yi : y ∈ A.block i) (yj : y ∈ A.block j) : x=y :=
  card_le_one.mp (A.linear i hi j hj hne) x (mem_inter.mpr ⟨xi,xj⟩) y (mem_inter.mpr ⟨yi,yj⟩)

private theorem disjoint_mass {I Q : Type*} [DecidableEq Q] {G : Finset I}
    (w : Q → ℕ) (U : Finset Q) (D : I → Finset Q)
    (hd : (G : Set I).PairwiseDisjoint D) (hsub : ∀ i ∈ G, D i ⊆ U) :
    ∑ i ∈ G, mass w (D i) ≤ mass w U := by
  change (∑ i ∈ G, ∑ x ∈ D i, w x) ≤ _
  rw [← sum_biUnion hd]
  exact sum_le_sum_of_subset (biUnion_subset.mpr hsub)

/-- Lines meeting no chosen centre. -/
def away (H : Finset P) := A.lines.filter (fun i => Disjoint (A.block i) H)

/-- Lines meeting the chosen set at exactly x. -/
def solo (H : Finset P) (x : P) := A.lines.filter (fun i => A.block i ∩ H = {x})

private def multiple (H : Finset P) := A.lines.filter (fun i => 2 ≤ (A.block i ∩ H).card)

private theorem multi_bound (H : Finset P) : (A.multiple H).card ≤ H.card*H.card-H.card := by
  let D := fun i => (A.block i ∩ H).offDiag
  have hd : (A.multiple H : Set J).PairwiseDisjoint D := by
    intro i hi j hj hij
    apply disjoint_left.mpr
    intro z zi zj
    obtain ⟨xi,yi,ne⟩ := mem_offDiag.mp zi
    obtain ⟨xj,yj,_⟩ := mem_offDiag.mp zj
    exact ne (A.shared (mem_filter.mp hi).1 (mem_filter.mp hj).1 hij
      (mem_inter.mp xi).1 (mem_inter.mp xj).1 (mem_inter.mp yi).1 (mem_inter.mp yj).1)
  have hex (i) (hi : i ∈ A.multiple H) : (D i).Nonempty := by
    obtain ⟨x,hx,y,hy,hne⟩ := one_lt_card.mp (mem_filter.mp hi).2
    exact ⟨(x,y), mem_offDiag.mpr ⟨hx,hy,hne⟩⟩
  rw [← offDiag_card]
  exact (card_le_card_biUnion hd hex).trans (card_le_card (biUnion_subset.mpr
    fun i _ => offDiag_mono inter_subset_right))

/-- Count lines outside all centres, through two centres, and through just one. -/
theorem decomposition (H : Finset P) : A.lines.card ≤
    (A.away H).card + (H.card*H.card-H.card) + ∑ x ∈ H, (A.solo H x).card := by
  have hsub : A.lines ⊆ (A.away H ∪ A.multiple H) ∪ H.biUnion (A.solo H) := by
    intro i hi
    by_cases h : Disjoint (A.block i) H
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hi,h⟩))
    by_cases h2 : 2 ≤ (A.block i ∩ H).card
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hi,h2⟩))
    obtain ⟨x,xi,xh⟩ := not_disjoint_iff.mp h
    have hs : A.block i ∩ H = {x} := by
      ext y
      rw [mem_singleton]
      exact ⟨fun hy => card_le_one.mp (by omega : (A.block i ∩ H).card ≤ 1)
        y hy x (mem_inter.mpr ⟨xi,xh⟩), fun h => h ▸ mem_inter.mpr ⟨xi,xh⟩⟩
    exact mem_union_right _ (mem_biUnion.mpr ⟨x,xh,mem_filter.mpr ⟨hi,hs⟩⟩)
  have h1 := card_union_le (A.away H ∪ A.multiple H) (H.biUnion (A.solo H))
  have h2 := card_union_le (A.away H) (A.multiple H)
  have h3 := card_biUnion_le (s:=H) (t:=A.solo H)
  have h4 := A.multi_bound H
  have h5 := card_le_card hsub
  omega

private theorem solo_disjoint (H : Finset P) (x : P) :
    (A.solo H x : Set J).PairwiseDisjoint (fun i => A.block i \ H) := by
  intro i hi j hj hne
  obtain ⟨hi,hs⟩ := mem_filter.mp hi
  obtain ⟨hj,hr⟩ := mem_filter.mp hj
  have hx : x ∈ A.block i ∩ H := by rw [hs]; simp
  have hx' : x ∈ A.block j ∩ H := by rw [hr]; simp
  apply disjoint_left.mpr
  intro y yi yj
  have h := A.shared hi hj hne (mem_sdiff.mp yi).1 (mem_sdiff.mp yj).1
    (mem_inter.mp hx).1 (mem_inter.mp hx').1
  exact (mem_sdiff.mp yi).2 (h ▸ (mem_inter.mp hx).2)

/-- A one-centre line needs at least one other point and at least t−w(x)
units of outside weight. Through one centre these outside points are disjoint. -/
theorem solo_bounds (H : Finset P) (x : P) :
    (A.solo H x).card ≤ (A.points \ H).card ∧
    (A.solo H x).card*(t-A.w x) ≤ mass A.w (A.points \ H) := by
  let D := fun i => A.block i \ H
  have hd := A.solo_disjoint H x
  have sub (i) (hi : i ∈ A.solo H x) : D i ⊆ A.points \ H :=
    fun _ hy => mem_sdiff.mpr ⟨A.inside _ (mem_filter.mp hi).1 (mem_sdiff.mp hy).1, (mem_sdiff.mp hy).2⟩
  have parts (i) (hi : i ∈ A.solo H x) : A.block i = D i ∪ {x} := by
    rw [← (mem_filter.mp hi).2]
    exact (sdiff_union_inter (A.block i) H).symm
  have hn (i) (hi : i ∈ A.solo H x) : (D i).Nonempty := by
    by_contra! he
    have h := A.nontrivial i (mem_filter.mp hi).1
    rw [parts i hi,he] at h
    simp at h
  have amt (i) (hi : i ∈ A.solo H x) : t-A.w x ≤ mass A.w (D i) := by
    have h := A.rich i (mem_filter.mp hi).1
    rw [parts i hi] at h
    have hb : Disjoint (D i) {x} := by
      have hx : x ∈ A.block i ∩ H := by rw [(mem_filter.mp hi).2]; simp
      exact disjoint_singleton_right.mpr (fun hz => (mem_sdiff.mp hz).2 (mem_inter.mp hx).2)
    simp only [mass,sum_union hb,sum_singleton] at h ⊢
    omega
  refine ⟨(card_le_card_biUnion hd hn).trans (card_le_card (biUnion_subset.mpr sub)),?_⟩
  have h := sum_le_sum amt
  simpa [sum_const] using h.trans (disjoint_mass A.w _ D hd sub)

/-- Ordered pairs on the off-diagonal in a weighted set. -/
private def pairs (w : P → ℕ) (S : Finset P) := mass (fun z : P×P => w z.1*w z.2) S.offDiag

private theorem pair_identity (w : P → ℕ) (S : Finset P) :
    pairs w S + ∑ x ∈ S, w x*w x = mass w S * mass w S := by
  let f := fun z : P×P => w z.1*w z.2
  have hg : mass f S.diag = ∑ x ∈ S, w x*w x := by simp [mass,diag,f,Function.diag]
  have hp : mass f (S ×ˢ S) = mass w S*mass w S := by
    simp only [mass,sum_product,f,←mul_sum,←sum_mul]
  rw [← hp,← diag_union_offDiag, mass, sum_union (disjoint_diag_offDiag _)]
  change pairs w S + ∑ x ∈ S, w x*w x = mass f S.diag + pairs w S
  rw [hg,add_comm]

/-- Pair counting on lines without a heavy atom. -/
theorem away_pairs (H : Finset P) (c : ℕ) (hc : c ≤ t)
    (light : ∀ x ∈ A.points \ H, A.w x ≤ t-c) :
    (A.away H).card*(t*c) ≤ mass A.w A.points * mass A.w A.points := by
  let U := A.away H
  have hd : (U : Set J).PairwiseDisjoint (fun i => (A.block i).offDiag) := by
    intro i hi j hj hij
    apply disjoint_left.mpr
    intro z zi zj
    obtain ⟨xi,yi,ne⟩ := mem_offDiag.mp zi
    obtain ⟨xj,yj,_⟩ := mem_offDiag.mp zj
    exact ne (A.shared (mem_filter.mp hi).1 (mem_filter.mp hj).1 hij xi xj yi yj)
  have lower (i) (hi : i ∈ U) : t*c ≤ pairs A.w (A.block i) := by
    have rich := A.rich i (mem_filter.mp hi).1
    have hj : ∑ x ∈ A.block i, A.w x*A.w x ≤ mass A.w (A.block i)*(t-c) := by
      rw [mass,sum_mul]
      apply sum_le_sum
      intro x hx
      apply Nat.mul_le_mul_left
      exact light x (mem_sdiff.mpr ⟨A.inside i (mem_filter.mp hi).1 hx,
        (disjoint_left.mp (mem_filter.mp hi).2 hx)⟩)
    have hp := pair_identity A.w (A.block i)
    have hm := Nat.mul_le_mul (Nat.le_refl (mass A.w (A.block i))) rich
    have he := Nat.mul_le_mul_right c rich
    have heq : mass A.w (A.block i)*t = mass A.w (A.block i)*(t-c) + mass A.w (A.block i)*c := by
      rw [←Nat.mul_add,Nat.sub_add_cancel hc]
    omega
  have sum := sum_le_sum lower
  have up := disjoint_mass (fun z : P×P => A.w z.1*A.w z.2) A.points.offDiag
    (fun i => (A.block i).offDiag) hd (fun i hi => offDiag_mono (A.inside i (mem_filter.mp hi).1))
  have h := pair_identity A.w A.points
  simp only [sum_const,nsmul_eq_mul] at sum
  change (∑ i ∈ U, pairs A.w (A.block i)) ≤ pairs A.w A.points at up
  exact (sum.trans up).trans (by omega)

private theorem union_mass_le {I Q : Type*} [DecidableEq Q] (w : Q → ℕ) (G : Finset I)
    (D : I → Finset Q) : mass w (G.biUnion D) ≤ ∑ j ∈ G, mass w (D j) := by
  classical
  induction G using Finset.induction_on with
  | empty => simp [mass]
  | @insert j G hj ih =>
    rw [biUnion_insert, sum_insert hj]
    have h : mass w (D j ∪ G.biUnion D) + mass w (D j ∩ G.biUnion D) =
        mass w (D j) + mass w (G.biUnion D) := sum_union_inter
    omega

/-- If points outside H have weight at most v, a small set of k rich lines
away from H requires at least kt−k²v units of outside weight. -/
theorem away_few (H : Finset P) (v : ℕ) (light : ∀ x ∈ A.points \ H, A.w x ≤ v)
    (G : Finset J) (hG : G ⊆ A.away H) :
    G.card*t ≤ mass A.w (A.points \ H) + G.card^2*v := by
  have bound (j) (hj : j ∈ A.away H) : A.block j ⊆ A.points \ H :=
    fun _ hx => mem_sdiff.mpr ⟨A.inside j (mem_filter.mp hj).1 hx,
      disjoint_left.mp (mem_filter.mp hj).2 hx⟩
  suffices hg : G.card*t ≤ mass A.w (G.biUnion A.block) + G.card^2*v by
    exact hg.trans (Nat.add_le_add_right (sum_le_sum_of_subset
      (biUnion_subset.mpr (fun j hj => bound j (hG hj)))) _)
  induction G using Finset.induction_on with
  | empty => simp
  | @insert i G hi ih =>
    have hs : G ⊆ A.away H := fun _ h => hG (mem_insert_of_mem h)
    have hii : i ∈ A.away H := hG (mem_insert_self ..)
    have hb (j) (hj : j ∈ G) : mass A.w (A.block i ∩ A.block j) ≤ v := by
      have hc := A.linear i (mem_filter.mp hii).1 j (mem_filter.mp (hs hj)).1 (by aesop)
      rcases (A.block i ∩ A.block j).eq_empty_or_nonempty with h | ⟨x,hx⟩
      · simp [h,mass]
      · have sub : A.block i ∩ A.block j ⊆ {x} := fun y hy => mem_singleton.mpr
            (card_le_one.mp hc y hy x hx)
        exact (sum_le_sum_of_subset (f:=A.w) sub).trans
          (by simpa using light x (bound _ hii (mem_inter.mp hx).1))
    have cover : A.block i ∩ G.biUnion A.block ⊆ G.biUnion (fun j => A.block i ∩ A.block j) := by
      intro x hx
      obtain ⟨j,hj,hxj⟩ := mem_biUnion.mp (mem_inter.mp hx).2
      exact mem_biUnion.mpr ⟨j,hj,mem_inter.mpr ⟨(mem_inter.mp hx).1,hxj⟩⟩
    have overlap : mass A.w (A.block i ∩ G.biUnion A.block) ≤ G.card*v := by
      have h := (sum_le_sum_of_subset (f:=A.w) cover).trans
        ((union_mass_le A.w G _).trans (sum_le_sum hb))
      simpa using h
    have add : mass A.w (A.block i ∪ G.biUnion A.block) + mass A.w (A.block i ∩ G.biUnion A.block) =
        mass A.w (A.block i) + mass A.w (G.biUnion A.block) := sum_union_inter
    have rich := A.rich i (mem_filter.mp hii).1
    have old := ih hs
    rw [card_insert_of_notMem hi,biUnion_insert]
    nlinarith only [old,add,overlap,rich,Nat.zero_le (G.card*v),Nat.zero_le v]

private theorem card_le_mass (S : Finset P) (hs : S ⊆ A.points) :
    S.card ≤ mass A.w S := by
  have h := sum_le_sum (s := S) (f := fun _ => 1) (g := A.w)
    (fun x hx => A.positive x (hs hx))
  simpa using h

/-- At agreement count 2²⁷+2, every weighted linear arrangement of total
weight 2³⁰ contains at most 2³¹ nontrivial rich lines. -/
theorem predecessor (A : Arrangement P J 134217730)
    (total : mass A.w A.points = 1073741824) : A.lines.card ≤ 2147483648 := by
  classical
  let H := A.points.filter (fun x => 134217219 ≤ A.w x)
  let Q := A.points \ H
  let L := mass A.w Q
  have hsub : H ⊆ A.points := filter_subset _ _
  have hparts : L + mass A.w H = 1073741824 := (sum_sdiff hsub).trans total
  have cost : H.card * 134217219 ≤ mass A.w H := by
    simpa using sum_le_sum (s:=H) (f:=fun _ => 134217219) (g:=A.w)
      (fun x hx => (mem_filter.mp hx).2)
  have h8 : H.card ≤ 8 := by omega
  have hcard : Q.card ≤ L := A.card_le_mass Q sdiff_subset
  have pairs := A.away_pairs H 512 (by decide) (by
    intro x hx
    have hm := mem_sdiff.mp hx
    have hh : ¬ 134217219 ≤ A.w x := fun he => hm.2 (mem_filter.mpr ⟨hm.1,he⟩)
    omega)
  rw [total] at pairs
  have away : (A.away H).card < 16777216 := by omega
  have solo (x : P) : (A.solo H x).card ≤ Q.card := (A.solo_bounds H x).1
  have sumq : (∑ x ∈ H, (A.solo H x).card) ≤ H.card * Q.card := by
    simpa using sum_le_sum (s:=H) (fun x _ => solo x)
  have decomp := A.decomposition H
  by_cases four : H.card = 4
  · have lightBudget : L ≤ 536872948 := by omega
    by_cases weak : ∃ x ∈ H, A.w x ≤ 134217728
    · obtain ⟨x,hx,hw⟩ := weak
      have two : 2 ≤ 134217730-A.w x := by omega
      have half : (A.solo H x).card * 2 ≤ L :=
        (Nat.mul_le_mul_left _ two).trans (A.solo_bounds H x).2
      have rest : (∑ y ∈ H.erase x, (A.solo H y).card) ≤ 3 * L := by
        have h := sum_le_sum (s:=H.erase x) (g:=fun _ => L) (fun y _ => (solo y).trans hcard)
        simpa [card_erase_of_mem hx,four] using h
      have e := sum_erase_add (f:=fun y => (A.solo H y).card) H hx
      rw [four] at decomp
      omega
    · have high (x) (hx : x ∈ H) : 134217729 ≤ A.w x := by
        by_contra! h
        exact weak ⟨x,hx,by omega⟩
      have cost' : 4*134217729 ≤ mass A.w H := by
        simpa [four] using sum_le_sum (s:=H) (f:=fun _ => 134217729) (g:=A.w) high
      have budget : L ≤ 536870908 := by omega
      rw [four] at sumq decomp
      by_cases medium : ∃ x ∈ Q, 4194304 ≤ A.w x
      · obtain ⟨x,hx,hw⟩ := medium
        have rest := A.card_le_mass (Q.erase x) ((erase_subset x Q).trans sdiff_subset)
        rw [card_erase_of_mem hx] at rest
        have split : mass A.w (Q.erase x) + A.w x = L := sum_erase_add Q A.w hx
        have pos : 0 < Q.card := card_pos.mpr ⟨x,hx⟩
        omega
      · have few : (A.away H).card ≤ 4 := by
          by_contra! hn
          obtain ⟨G,hsubG,hfive⟩ := exists_subset_card_eq (show 5 ≤ (A.away H).card by omega)
          have h := A.away_few H 4194304 (by
            intro x hx
            by_contra! h
            exact medium ⟨x,hx,by omega⟩) G hsubG
          rw [hfive] at h
          change 5*134217730 ≤ L + 5^2*4194304 at h
          omega
        omega
  · have lb : L ≤ 1073741824 - H.card*134217219 := by omega
    have prod := Nat.mul_le_mul_left H.card (hcard.trans lb)
    have check : ∀ s : Fin 9, s.val ≠ 4 →
        16777215 + (s.val*s.val-s.val) + s.val*(1073741824-s.val*134217219) ≤ 2147483648 := by
      decide
    have hn := check ⟨H.card,by omega⟩ four
    change 16777215 + (H.card*H.card-H.card) +
      H.card*(1073741824-H.card*134217219) ≤ 2147483648 at hn
    omega
#print axioms predecessor

end Arrangement
end ArkLib.ProximityGap.Frontier.WeightedRichLinePacking
