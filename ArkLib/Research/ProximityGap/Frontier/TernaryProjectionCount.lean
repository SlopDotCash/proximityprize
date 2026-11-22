/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Tactic

/-! # Two new points per fiber of a ternary sumset

Projection along the next nonzero vector partitions a finite set into lines.
Translation in either direction gives two new points on every occupied line.
-/
namespace ProximityGap.TernaryProjectionCount
open Finset

/-- Two maps preserving a label and strictly decreasing or increasing an integer
height create at least two new members on every occupied fiber. -/
theorem two_per_fiber {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (key : α → β) (height : α → ℤ) (lo hi : α → α)
    (hl : ∀ x, key (lo x) = key x) (hr : ∀ x, key (hi x) = key x)
    (ltlo : ∀ x, height (lo x) < height x) (lthi : ∀ x, height x < height (hi x)) :
    s.card + 2 * (s.image key).card ≤ ((s ∪ s.image lo) ∪ s.image hi).card := by
  classical
  let t := (s ∪ s.image lo) ∪ s.image hi
  let labels := s.image key
  have local_bound (b : β) (hb : b ∈ labels) :
      (s.filter (fun x => key x = b)).card + 2 ≤
        (t.filter (fun x => key x = b)).card := by
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hb
    let f := s.filter (fun a => key a = key x)
    have hn : f.Nonempty := ⟨x,mem_filter.mpr ⟨hx,rfl⟩⟩
    obtain ⟨p,hp,hmin⟩ := f.exists_min_image height hn
    obtain ⟨r,hr',hmax⟩ := f.exists_max_image height hn
    have lp : lo p ∉ f := fun h => (ltlo p).not_ge (hmin _ h)
    have ur : hi r ∉ f := fun h => (lthi r).not_ge (hmax _ h)
    have distinct : lo p ≠ hi r := by
      have h := lt_trans (lt_of_lt_of_le (ltlo p) (hmin r hr')) (lthi r)
      exact fun e => h.ne (congrArg height e)
    have hsub : insert (lo p) (insert (hi r) f) ⊆ t.filter (fun a => key a = key x) := by
      intro a ha
      rcases mem_insert.mp ha with rfl | ha
      · refine mem_filter.mpr ⟨?_, (hl _).trans (mem_filter.mp hp).2⟩
        exact mem_union_left _ (mem_union_right _ (mem_image_of_mem _ (mem_filter.mp hp).1))
      rcases mem_insert.mp ha with rfl | ha
      · refine mem_filter.mpr ⟨?_, (hr _).trans (mem_filter.mp hr').2⟩
        exact mem_union_right _ (mem_image_of_mem _ (mem_filter.mp hr').1)
      · refine mem_filter.mpr ⟨?_, (mem_filter.mp ha).2⟩
        exact mem_union_left _ (mem_union_left _ (mem_filter.mp ha).1)
    have hcard := card_le_card hsub
    rw [card_insert_of_notMem (by simpa only [mem_insert, not_or] using And.intro distinct lp),
      card_insert_of_notMem ur] at hcard
    exact hcard
  have small : s.card = ∑ b ∈ labels, (s.filter fun x => key x = b).card :=
    card_eq_sum_card_fiberwise (fun x hx => mem_image_of_mem _ hx)
  have big : t.card = ∑ b ∈ labels, (t.filter fun x => key x = b).card := by
    apply card_eq_sum_card_fiberwise
    intro x hx
    rcases mem_union.mp hx with h | h
    · rcases mem_union.mp h with h | h
      · exact mem_image_of_mem _ h
      · obtain ⟨a,ha,rfl⟩ := mem_image.mp h
        rw [hl]; exact mem_image_of_mem _ ha
    · obtain ⟨a,ha,rfl⟩ := mem_image.mp h
      rw [hr]; exact mem_image_of_mem _ ha
  change s.card + 2 * labels.card ≤ t.card
  have h := sum_le_sum (fun b hb => local_bound b hb)
  simpa only [sum_add_distrib, sum_const, nsmul_eq_mul, Nat.cast_id, ← small, ← big,
    Nat.mul_comm] using h

#print axioms two_per_fiber
end ProximityGap.TernaryProjectionCount
