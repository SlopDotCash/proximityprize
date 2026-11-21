/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Abel

/-! # Equal block sums in an eight-site triple packing

For a saturated linear triple packing on eight sites, every site misses exactly
one partner. If all blocks have the same sum in an abelian group, then the
labels lie in one fiber of multiplication by three. The statement retains only
the pair multiplicities, so it applies to any incidence system with these data.
-/

set_option autoImplicit false
open scoped BigOperators
open Finset

namespace ProximityGap.OctagonTripleTorsion

variable {I G : Type*} [Fintype I] [DecidableEq I] [AddCommGroup G]

/-- Equal block sums and the saturated pair incidences force a common triple multiple. -/
theorem triple_multiple_constant (blocks : Finset (Finset I)) (f : I → G) (t : G)
    (partner : I → I) (invol : Function.Involutive partner) (distinct : ∀ i, partner i ≠ i)
    (hsum : ∀ b ∈ blocks, ∑ j ∈ b, f j = t)
    (hpair : ∀ i j, (blocks.filter (fun b => i ∈ b ∧ j ∈ b)).card =
      if j = i then 3 else if j = partner i then 0 else 1) :
    ∀ i, 3 • f i = 3 • (3 • t - ∑ j, f j) := by
  classical
  have weighted (i : I) : 3 • t = (∑ j, f j) + 2 • f i - f (partner i) := by
    let through := blocks.filter (fun b => i ∈ b)
    have hdeg : through.card = 3 := by simpa [through] using hpair i i
    have hb (b : Finset I) : (∑ j, if j ∈ b then f j else 0) = ∑ j ∈ b, f j := by
      simp
    have hrow (j : I) : (∑ b ∈ through, if j ∈ b then f j else 0) =
        (if j = i then 3 else if j = partner i then 0 else 1) • f j := by
      rw [← Finset.sum_filter, Finset.sum_const, ← hpair]
      simp [through, Finset.filter_filter]
    have hentry (j : I) :
        (if j = i then 3 else if j = partner i then 0 else 1 : ℕ) • f j =
          f j + (if j = i then 2 • f i else 0) - (if j = partner i then f (partner i) else 0) := by
      by_cases h : j = i
      · subst j
        simp [Ne.symm (distinct i)]
        abel
      · by_cases h' : j = partner i
        · subst j
          simp [distinct i]
        · simp [h, h']
          abel
    calc
      3 • t = ∑ _b ∈ through, t := by simp [hdeg]
      _ = ∑ b ∈ through, ∑ j, if j ∈ b then f j else 0 := by
        apply Finset.sum_congr rfl
        intro b h
        rw [hb, hsum b (Finset.mem_filter.mp h).1]
      _ = ∑ j, ∑ b ∈ through, if j ∈ b then f j else 0 := Finset.sum_comm
      _ = _ := by
        simp_rw [hrow, hentry]
        simp [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  intro i
  have hi := weighted i
  have hp := weighted (partner i)
  rw [invol i] at hp
  calc
    3 • f i = 2 • (∑ j, f j) + 2 • (2 • f i - f (partner i)) +
        ((∑ j, f j) + 2 • f (partner i) - f i) - 3 • (∑ j, f j) := by abel
    _ = 3 • (3 • t - ∑ j, f j) := by
      rw [← hp]
      have h : 2 • (∑ j, f j) + 2 • (2 • f i - f (partner i)) = 2 • (3 • t) := by
        rw [hi]
        abel
      rw [h]
      abel

#print axioms triple_multiple_constant

end ProximityGap.OctagonTripleTorsion
