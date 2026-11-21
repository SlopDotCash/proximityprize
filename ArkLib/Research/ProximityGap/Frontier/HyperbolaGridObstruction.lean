/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! # Core incidences for one-fresh hyperbola grids

On each ordinary site, a received point on the hyperbola can serve at most
one vertical and one horizontal head. For a polynomial quotient of degree
`d`, each vertical/horizontal pair can share at most `d` ordinary sites. -/

namespace ProximityGap.HyperbolaGridObstruction

open Finset Polynomial

variable {F I : Type} [Field F] [DecidableEq F] [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
/-- A nonconstant polynomial has at most its degree many occurrences of each
given value on an injective evaluation domain. -/
theorem fiber_bound (D : I ↪ F) (T : F[X]) (ht : 0 < T.natDegree) (c : F)
    (sites : Finset I) (h : ∀ i ∈ sites, T.eval (D i) = c) : sites.card ≤ T.natDegree := by
  classical
  have hn : T - C c ≠ 0 := by
    intro he
    have heq := sub_eq_zero.mp he
    simp [heq] at ht
  have sub : sites.map D ⊆ (T - C c).roots.toFinset := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
    exact Multiset.mem_toFinset.mpr ((mem_roots hn).mpr (by simp [h i hi]))
  have hc := (card_le_card sub).trans ((Multiset.toFinset_card_le _).trans (card_roots' _))
  simpa [natDegree_sub_C] using hc

/-- Ordinary sites whose received pair lies on the quotient hyperbola. -/
def onCurve (R : Finset I) (T u v : I → F) : Finset I :=
  Rᶜ.filter fun i => u i * v i = T i

/-- Any received point on a vertical ruling is determined by its first
coordinate. The horizontal ruling uses its second coordinate. -/
def visible (S : Finset I) (u : I → F) (a : F) : ℕ := (S.filter fun i => u i = a).card

omit [Field F] [Fintype I] [DecidableEq I] in
private theorem axis_bound (S : Finset I) (u : I → F) (A : Finset F) (c r : ℕ)
    (ha : ∀ a ∈ A, c ≤ r + visible S u a) :
    A.card*c ≤ A.card*r + (S.filter fun i => u i ∈ A).card := by
  have lower := Finset.sum_le_sum ha
  simpa only [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib, visible,
    Finset.sum_card_fiberwise_eq_card_filter] using lower

/-- Bounds on core incidences for every selected rectangular subfamily. All
common roots may count toward all cores, whatever their received values. -/
theorem incidence_bounds (D : I ↪ F) (T : F[X]) (ht : 0 < T.natDegree)
    (R : Finset I) (u v : I → F) (A B : Finset F) (c : ℕ)
    (ha : ∀ a ∈ A, c ≤ R.card + visible (onCurve R (fun i => T.eval (D i)) u v) u a)
    (hb : ∀ b ∈ B, c ≤ R.card + visible (onCurve R (fun i => T.eval (D i)) u v) v b) :
    let m := A.card+B.card
    m*c ≤ m*R.card+2*Rᶜ.card ∧
    m*c ≤ m*R.card+Rᶜ.card+A.card*B.card*T.natDegree := by
  classical
  let S := onCurve R (fun i => T.eval (D i)) u v
  let U := S.filter fun i => u i ∈ A
  let V := S.filter fun i => v i ∈ B
  have hu : U ⊆ Rᶜ := (filter_subset ..).trans (filter_subset ..)
  have hv : V ⊆ Rᶜ := (filter_subset ..).trans (filter_subset ..)
  have hj : U.card+V.card ≤ 2*Rᶜ.card := by
    have := card_le_card hu
    have := card_le_card hv
    omega
  have hm : U ∩ V ⊆ S := (inter_subset_left).trans (filter_subset ..)
  let pair (i : I) := (u i, v i)
  have maps : (↑(U ∩ V) : Set I).MapsTo pair (↑(A ×ˢ B : Finset (F × F)) : Set (F × F)) := by
    intro i hi
    exact mem_product.mpr ⟨(mem_filter.mp (mem_inter.mp hi).1).2,
      (mem_filter.mp (mem_inter.mp hi).2).2⟩
  have hdouble : (U ∩ V).card ≤ A.card*B.card*T.natDegree := by
    rw [card_eq_sum_card_fiberwise maps, ← card_product]
    apply Finset.sum_le_card_nsmul
    intro ab _
    apply fiber_bound D T ht (ab.1*ab.2)
    intro i hi
    have hcurve := (mem_filter.mp (hm (mem_filter.mp hi).1)).2
    have hab := (mem_filter.mp hi).2
    simpa [pair] using hcurve.symm.trans (congrArg (fun p : F × F => p.1*p.2) hab)
  have htotal := card_union_add_card_inter U V
  have huvc := card_le_card (union_subset hu hv)
  have hsum := Nat.add_le_add (axis_bound S u A c R.card ha) (axis_bound S v B c R.card hb)
  change A.card*c+B.card*c ≤ A.card*R.card+U.card+(B.card*R.card+V.card) at hsum
  dsimp only
  simp only [Nat.add_mul]
  omega

omit [Field F] [DecidableEq F] in
/-- Choosing a specified number of active heads preserves their core bounds. -/
private theorem select (A B : Finset F) {m : ℕ} (h : m ≤ A.card+B.card) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, A'.card+B'.card = m := by
  obtain ⟨A', ha, hca⟩ := exists_subset_card_eq (Nat.min_le_left A.card m)
  obtain ⟨B', hb, hcb⟩ := exists_subset_card_eq (s := B) (n := m - min A.card m) (by omega)
  exact ⟨A', ha, B', hb, by omega⟩

/-- The first named length has at most two active grid heads through
357913941 errors when the common locator and separator have their usual degree. -/
theorem first_head_cap (D : I ↪ F) (hn : Fintype.card I = 1073741824)
    (T : F[X]) (ht : 0 < T.natDegree) (R : Finset I)
    (hd : R.card + T.natDegree + 2 ≤ 536870912) (u v : I → F) (A B : Finset F)
    (ha : ∀ a ∈ A, 715827882 ≤ R.card + visible (onCurve R (fun i => T.eval (D i)) u v) u a)
    (hb : ∀ b ∈ B, 715827882 ≤ R.card + visible (onCurve R (fun i => T.eval (D i)) u v) v b) :
    A.card+B.card ≤ 2 := by
  by_contra! h
  obtain ⟨A', hsA, B', hsB, hm⟩ := select A B (show 3 ≤ A.card+B.card by omega)
  have hc := (incidence_bounds D T ht R u v A' B' 715827882
    (fun a hx => ha a (hsA hx)) (fun b hx => hb b (hsB hx))).2
  have prod : A'.card*B'.card ≤ 2 := by
    generalize A'.card = a, B'.card = b at hm ⊢
    have : a ≤ 3 := by omega
    interval_cases a <;> omega
  have hp := Nat.mul_le_mul_right T.natDegree prod
  rw [hm, card_compl, hn] at hc
  have hr := Finset.card_le_univ R
  rw [hn] at hr
  omega

/-- At length `16s`, no six heads have enough common agreements for a
one-fresh witness at `6s` errors. The quotient can have any positive degree. -/
theorem second_head_cap (D : I ↪ F) {s : ℕ} (hn : Fintype.card I = 16*s)
    (T : F[X]) (ht : 0 < T.natDegree) (R : Finset I)
    (hd : R.card + T.natDegree + 2 ≤ 8*s) (u v : I → F) (A B : Finset F)
    (ha : ∀ a ∈ A, 10*s-1 ≤ R.card + visible (onCurve R (fun i => T.eval (D i)) u v) u a)
    (hb : ∀ b ∈ B, 10*s-1 ≤ R.card + visible (onCurve R (fun i => T.eval (D i)) u v) v b) :
    A.card+B.card ≤ 5 := by
  by_contra! h
  obtain ⟨A', hsA, B', hsB, hm⟩ := select A B (show 6 ≤ A.card+B.card by omega)
  have hc := incidence_bounds D T ht R u v A' B' (10*s-1)
    (fun a hx => ha a (hsA hx)) (fun b hx => hb b (hsB hx))
  dsimp only at hc
  have prod : A'.card*B'.card ≤ 9 := by
    generalize A'.card = a, B'.card = b at hm ⊢
    have : a ≤ 6 := by omega
    interval_cases a <;> omega
  have hp := Nat.mul_le_mul_right T.natDegree prod
  rw [hm, card_compl, hn] at hc
  have hr := Finset.card_le_univ R
  rw [hn] at hr
  omega

/-- Each active head can supply at most one scalar per site outside its core.
The union bound also allows the same label to occur on several heads. -/
theorem label_cap {α L : Type} [DecidableEq L] (A B : Finset α)
    (left right : α → Finset L) (limit : ℕ)
    (hl : ∀ a ∈ A, (left a).card ≤ limit) (hr : ∀ b ∈ B, (right b).card ≤ limit) :
    (A.biUnion left ∪ B.biUnion right).card ≤ (A.card+B.card)*limit := by
  calc
    _ ≤ (A.biUnion left).card+(B.biUnion right).card := card_union_le ..
    _ ≤ (∑ a ∈ A, (left a).card)+(∑ b ∈ B, (right b).card) :=
      Nat.add_le_add card_biUnion_le card_biUnion_le
    _ ≤ _ := by simpa [Nat.add_mul] using
        Nat.add_le_add (A.sum_le_card_nsmul _ _ hl) (B.sum_le_card_nsmul _ _ hr)

/-- The first-prime predecessor cannot exceed its budget by one-fresh labels
from any rectangular hyperbola grid obeying the locator degree allocation. -/
theorem first_labels (D : I ↪ F) (hn : Fintype.card I = 1073741824)
    (T : F[X]) (ht : 0 < T.natDegree) (R : Finset I)
    (hd : R.card + T.natDegree + 2 ≤ 536870912) (u v : I → F) (A B : Finset F)
    (ha : ∀ a ∈ A, 715827882 ≤ R.card + visible (onCurve R (fun i => T.eval (D i)) u v) u a)
    (hb : ∀ b ∈ B, 715827882 ≤ R.card + visible (onCurve R (fun i => T.eval (D i)) u v) v b)
    (L M : F → Finset F) (hl : ∀ a ∈ A, (L a).card ≤ 357913942)
    (hm : ∀ b ∈ B, (M b).card ≤ 357913942) :
    (A.biUnion L ∪ B.biUnion M).card ≤ 715827884 := by
  have nh := first_head_cap D hn T ht R hd u v A B ha hb
  have hc := label_cap A B L M _ hl hm
  omega

/-- The second-prime predecessor admits at most this many one-fresh labels
under the same construction, for every positive quotient degree. -/
theorem second_labels (D : I ↪ F) (hn : Fintype.card I = 1073741824)
    (T : F[X]) (ht : 0 < T.natDegree) (R : Finset I)
    (hd : R.card + T.natDegree + 2 ≤ 536870912) (u v : I → F) (A B : Finset F)
    (ha : ∀ a ∈ A, 671088639 ≤ R.card + visible (onCurve R (fun i => T.eval (D i)) u v) u a)
    (hb : ∀ b ∈ B, 671088639 ≤ R.card + visible (onCurve R (fun i => T.eval (D i)) u v) v b)
    (L M : F → Finset F) (hl : ∀ a ∈ A, (L a).card ≤ 402653185)
    (hm : ∀ b ∈ B, (M b).card ≤ 402653185) :
    (A.biUnion L ∪ B.biUnion M).card ≤ 2013265925 := by
  have nh := second_head_cap D (s := 67108864) hn T ht R hd u v A B ha hb
  have hc := label_cap A B L M _ hl hm
  omega

#print axioms first_labels
#print axioms second_labels
#print axioms incidence_bounds
#print axioms first_head_cap
#print axioms second_head_cap

end ProximityGap.HyperbolaGridObstruction
