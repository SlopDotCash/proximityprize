/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Exact cardinality contractions from uniform-size blocks

The weight of a monomial is the mass of the blocks containing its support,
rescaled by a ratio of binomial coefficients. Taking the blocks to be the
four-cliques of a Paley graph supplies its exact-cardinality quartic moments.
-/

namespace ProximityGap.PaleyQuarticSlice

open Finset

variable {α : Type*} [DecidableEq α]

/-- Mass of the blocks containing a prescribed support. -/
def completionMass (blocks : Finset (Finset α)) (w : Finset α → ℚ) (U : Finset α) : ℚ :=
  ∑ B ∈ blocks, if U ⊆ B then w B else 0

/-- Monomial moment on the size-`k` slice, defined through `d`-site completions. -/
def sliceMoment (blocks : Finset (Finset α)) (w : Finset α → ℚ) (d k : ℕ)
    (U : Finset α) : ℚ :=
  (k.choose d : ℚ) / completionMass blocks w ∅ * completionMass blocks w U /
    ((k - U.card).choose (d - U.card) : ℚ)

variable (blocks : Finset (Finset α)) (w : Finset α → ℚ) {d k : ℕ}

/-- The empty monomial has moment one for nonzero total mass on a feasible slice. -/
theorem sliceMoment_empty (hdk : d ≤ k) (hmass : completionMass blocks w ∅ ≠ 0) :
    sliceMoment blocks w d k ∅ = 1 := by
  have hbin : (k.choose d : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hdk).ne'
  simp [sliceMoment, div_mul_cancel₀ _ hmass, hbin]

/-- Each block extending `U` has exactly `d - U.card` new sites. -/
theorem sum_new_completionMass [Fintype α] (hsize : ∀ B ∈ blocks, B.card = d) (U : Finset α) :
    ∑ v ∈ univ \ U, completionMass blocks w (insert v U) =
      (d - U.card : ℕ) * completionMass blocks w U := by
  classical
  unfold completionMass
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro B hB
  by_cases h : U ⊆ B
  · simp only [insert_subset_iff, h, and_true, ite_true]
    rw [sum_ite_mem]
    have hset : (univ \ U) ∩ B = B \ U := by ext x; simp [and_comm]
    rw [hset, sum_const, nsmul_eq_mul, card_sdiff_of_subset h, hsize B hB]
  · simp [insert_subset_iff, h]

private theorem choose_step {j d k : ℕ} (hj : j < d) (hdk : d ≤ k) :
    (k - j) * (k - (j+1)).choose (d - (j+1)) =
      (d - j) * (k-j).choose (d-j) := by
  have h := Nat.add_one_mul_choose_eq (k-(j+1)) (d-(j+1))
  rwa [show k-(j+1)+1 = k-j by omega, show d-(j+1)+1 = d-j by omega, Nat.mul_comm _ (d-j)] at h

/-- The repeated-variable and fresh-variable contributions together enforce exact cardinality. -/
theorem sum_insert_sliceMoment [Fintype α] (hsize : ∀ B ∈ blocks, B.card = d) (hdk : d ≤ k)
    (U : Finset α) (hj : U.card < d) :
    ∑ v, sliceMoment blocks w d k (insert v U) = k * sliceMoment blocks w d k U := by
  classical
  let j := U.card
  let c := (k.choose d : ℚ) / completionMass blocks w ∅
  let b := (k-j).choose (d-j)
  let b' := (k-(j+1)).choose (d-(j+1))
  have hb : (b : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show d-j ≤ k-j by omega)).ne'
  have hb' : (b' : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show d-(j+1) ≤ k-(j+1) by omega)).ne'
  have hbin : ((k : ℚ) - j) * b' = ((d : ℚ) - j) * b := by
    have h := choose_step (j := j) (by exact hj) hdk
    rw [← Nat.cast_sub (show j ≤ k from le_trans hj.le hdk), ← Nat.cast_sub hj.le]
    exact_mod_cast h
  have hfresh : ∑ v ∈ univ \ U, sliceMoment blocks w d k (insert v U) =
      c / b' * ((d : ℚ) - j) * completionMass blocks w U := by
    calc
      _ = ∑ v ∈ univ \ U, c / b' * completionMass blocks w (insert v U) := by
        apply sum_congr rfl
        intro v hv
        have hv' := (mem_sdiff.mp hv).2
        simp only [sliceMoment, card_insert_of_notMem hv']
        dsimp [c, b', j]
        ring
      _ = _ := by
        rw [← mul_sum, sum_new_completionMass blocks w hsize, Nat.cast_sub hj.le]
        dsimp [j]
        ring
  rw [← sum_sdiff (subset_univ U), hfresh]
  have hold : ∑ v ∈ U, sliceMoment blocks w d k (insert v U) =
      (j : ℚ) * sliceMoment blocks w d k U := by
    convert (sum_const (s := U) (sliceMoment blocks w d k U)) using 1
    · exact sum_congr rfl fun v hv => by rw [insert_eq_of_mem hv]
  rw [hold]
  change c / b' * ((d : ℚ) - j) * completionMass blocks w U +
    j * (c * completionMass blocks w U / b) = k * (c * completionMass blocks w U / b)
  field_simp [hb, hb']
  linear_combination -(c * completionMass blocks w U) * hbin

/-- At top degree, only the queried block can extend its own support. -/
theorem completionMass_of_card (hsize : ∀ B ∈ blocks, B.card = d)
    (U : Finset α) (hU : U.card = d) :
    completionMass blocks w U = if U ∈ blocks then w U else 0 := by
  classical
  unfold completionMass
  calc
    _ = ∑ B ∈ blocks, if U = B then w B else 0 := by
      apply sum_congr rfl
      intro B hB
      have heq : U ⊆ B ↔ U = B :=
        ⟨fun h => eq_of_subset_of_card_le h (by rw [hsize B hB, hU]), fun h => h ▸ Subset.rfl⟩
      simp only [heq]
    _ = _ := by simp

/-- Triple balance cancels the star sum over pairs disjoint from a given two-site support. -/
theorem sum_disjoint_star_of_triple_balance [Fintype α] (hsize : ∀ B ∈ blocks, B.card = 4)
    (hbalance : ∀ T : Finset α, T.card = 3 → completionMass blocks w T = 0)
    (e : Finset α) (he : e.card = 2) (v : α) (hv : v ∉ e) :
    ∑ b ∈ univ \ insert v e,
      (if insert b (insert v e) ∈ blocks then w (insert b (insert v e)) else 0) = 0 := by
  have hthree : (insert v e).card = 3 := by rw [card_insert_of_notMem hv, he]
  calc
    _ = ∑ b ∈ univ \ insert v e, completionMass blocks w (insert b (insert v e)) := by
      apply sum_congr rfl
      intro b hb
      exact (completionMass_of_card blocks w hsize _ (by
        rw [card_insert_of_notMem (mem_sdiff.mp hb).2, hthree])).symm
    _ = _ := by rw [sum_new_completionMass blocks w hsize, hbalance _ hthree, mul_zero]

/-- Any top-degree statistic that accepts every block receives the full binomial mass. -/
theorem sum_sliceMoment_of_contains_blocks (family : Finset (Finset α))
    (hsub : blocks ⊆ family) (hsize : ∀ U ∈ family, U.card = d)
    (hmass : completionMass blocks w ∅ ≠ 0) :
    ∑ U ∈ family, sliceMoment blocks w d k U = k.choose d := by
  classical
  have hB : ∀ B ∈ blocks, B.card = d := fun B h => hsize B (hsub h)
  have htop (U : Finset α) (hU : U ∈ family) :
      sliceMoment blocks w d k U =
        (k.choose d : ℚ) / completionMass blocks w ∅ * (if U ∈ blocks then w U else 0) := by
    simp [sliceMoment, hsize U hU, completionMass_of_card blocks w hB U (hsize U hU)]
  simp_rw [sum_congr rfl htop]
  rw [← mul_sum, sum_ite_mem, inter_eq_right.mpr hsub]
  have hempty : completionMass blocks w ∅ = ∑ B ∈ blocks, w B := by simp [completionMass]
  rw [← hempty, div_mul_cancel₀ _ hmass]

#print axioms sliceMoment_empty
#print axioms sum_insert_sliceMoment
#print axioms sum_disjoint_star_of_triple_balance
#print axioms sum_sliceMoment_of_contains_blocks

end ProximityGap.PaleyQuarticSlice
