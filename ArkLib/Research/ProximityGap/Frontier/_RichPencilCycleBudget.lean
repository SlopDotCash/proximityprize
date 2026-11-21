/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Mikhail Izhutkin (mashingaan)
-/
import Mathlib.Tactic

/-!
# Error incidence on a cycle of affine triples

A pencil indexed by i uses its private head and the heads on its incoming and
outgoing edges. At an exceptional coordinate at least two of these three heads
are erroneous. Charge the union for each neighboring pair against those heads.
-/

open scoped BigOperators

namespace ProximityGap.RichPencilCycleBudget

/-- The natural-number indicator of a decidable proposition. -/
def bit (p : Prop) [Decidable p] : ℕ := if p then 1 else 0

/-- The adjacent exception unions charge each private or shared head only once. -/
theorem adjacent_exception_mass_le {I X : Type*} [Fintype I] [Fintype X]
    [DecidableEq X] (σ : Equiv.Perm I) (S P H : I → Finset X)
    (hlocal : ∀ i x, x ∈ S i → 2 ≤
      bit (x ∈ P i) + bit (x ∈ H i) + bit (x ∈ H (σ.symm i))) :
    (∑ i, (S i ∪ S (σ i)).card) ≤ (∑ i, (P i).card) + ∑ i, (H i).card := by
  classical
  have point (x : X) :
      (∑ i, bit (x ∈ S i ∪ S (σ i))) ≤
        (∑ i, bit (x ∈ P i)) + ∑ i, bit (x ∈ H i) := by
    let a : I → ℕ := fun i ↦ bit (x ∈ S i)
    let p : I → ℕ := fun i ↦ bit (x ∈ P i)
    let h : I → ℕ := fun i ↦ bit (x ∈ H i)
    have localCharge (i : I) :
        2 * a i ≤ p i + a i * h i + a i * h (σ.symm i) := by
      by_cases hi : x ∈ S i
      · simpa [a, p, h, bit, hi] using hlocal i x hi
      · simp [a, bit, hi]
    have bridgeCharge (i : I) :
        a i * h i + a (σ i) * h i ≤ h i + a i * a (σ i) := by
      by_cases hi : x ∈ S i
      all_goals by_cases hj : x ∈ S (σ i)
      all_goals by_cases hk : x ∈ H i
      all_goals simp [a, h, bit, hi, hj, hk]
    have cover (i : I) :
        bit (x ∈ S i ∪ S (σ i)) + a i * a (σ i) = a i + a (σ i) := by
      by_cases hi : x ∈ S i
      all_goals by_cases hj : x ∈ S (σ i)
      all_goals simp [a, bit, Finset.mem_union, hi, hj]
    have shift :
        (∑ i, a i * h (σ.symm i)) = ∑ i, a (σ i) * h i := by
      simpa only [Equiv.symm_apply_apply] using
        (Equiv.sum_comp σ (fun i ↦ a i * h (σ.symm i))).symm
    have h₁ := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ localCharge i)
    have h₂ := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ bridgeCharge i)
    have h₃ : (∑ i, (bit (x ∈ S i ∪ S (σ i)) + a i * a (σ i))) =
        ∑ i, (a i + a (σ i)) := Finset.sum_congr rfl (fun i _ ↦ cover i)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, shift, Equiv.sum_comp σ a] at h₁ h₂ h₃
    change (∑ i, bit (x ∈ S i ∪ S (σ i))) ≤ (∑ i, p i) + ∑ i, h i
    omega
  have count (A : Finset X) : (∑ x : X, bit (x ∈ A)) = A.card := by
    simp [bit, Finset.sum_ite]
  have total (A : I → Finset X) :
      (∑ x : X, ∑ i : I, bit (x ∈ A i)) = ∑ i, (A i).card := by
    rw [Finset.sum_comm]
    simp only [count]
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset X)) (fun x _ ↦ point x)
  rw [Finset.sum_add_distrib, total, total, total] at hs
  exact hs

/-- A cyclic family with one private and one shared error row per pencil requires
at least half the pairwise distance budget as its per-head error radius. -/
theorem distance_le_twice_radius_of_cycle {I X : Type*} [Fintype I] [Nonempty I]
    [Fintype X] [DecidableEq X] (σ : Equiv.Perm I) (S P H : I → Finset X)
    (D t : ℕ) (hlocal : ∀ i x, x ∈ S i → 2 ≤
      bit (x ∈ P i) + bit (x ∈ H i) + bit (x ∈ H (σ.symm i)))
    (hpair : ∀ i, D ≤ (S i ∪ S (σ i)).card)
    (hP : ∀ i, (P i).card ≤ t) (hH : ∀ i, (H i).card ≤ t) : D ≤ 2 * t := by
  classical
  have ha := adjacent_exception_mass_le σ S P H hlocal
  have hd := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hpair i)
  have hp := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hP i)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hH i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hd hp hh
  have hb : Fintype.card I * D ≤ Fintype.card I * (2 * t) := by
    rw [Nat.mul_comm 2 t, ← Nat.mul_assoc, Nat.mul_two]
    exact hd.trans (ha.trans (Nat.add_le_add hp hh))
  exact Nat.le_of_mul_le_mul_left hb Fintype.card_pos

end ProximityGap.RichPencilCycleBudget

#print axioms ProximityGap.RichPencilCycleBudget.adjacent_exception_mass_le
#print axioms ProximityGap.RichPencilCycleBudget.distance_le_twice_radius_of_cycle
