/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic

/-! # Counting order-two jet partitions in a weight interval

The two derivative exponents have total at most `t` and derivative weight
`u+2b`. On a fixed weight `s`, the second exponent varies in the interval
from `s-t` (truncated at zero) to `s/2` inclusive.
-/
namespace ProximityGap.SecondOrderBlockCounts
open Finset

/-- Number of ways to write `s=u+2b` with `u+b≤t`. -/
def level (t s : ℕ) := s/2+1 - (s-t)

/-- The two derivative exponents allowed by one half-open weight interval. -/
abbrev Slice (t lo hi : ℕ) := {q : ℕ × ℕ // q.1 + q.2 ≤ t ∧ lo ≤ q.1 + 2*q.2 ∧ q.1 + 2*q.2 < hi}

/-- An index by weight followed by the offset of the second exponent. -/
def sliceEquiv (t lo hi : ℕ) : Slice t lo hi ≃ Σ s : Fin (hi-lo), Fin (level t (s.val+lo)) where
  toFun q :=
    let s := q.val.1+2*q.val.2
    ⟨⟨s-lo, by have := q.property; dsimp [s]; omega⟩,
      ⟨q.val.2-(s-t), by have := q.property; dsimp [s,level]; omega⟩⟩
  invFun c :=
    let s := c.1.val+lo
    let b := c.2.val + (s-t)
    ⟨(s-2*b,b), by
      have h := c.2.isLt
      have h' := c.1.isLt
      dsimp [level] at h
      dsimp [s,b]
      omega⟩
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp
    all_goals have := q.property; omega
  right_inv c := by
    rcases c with ⟨s,e⟩
    have hs := s.isLt
    have he := e.isLt
    dsimp [level] at he
    apply Sigma.ext
    · apply Fin.ext; dsimp; omega
    · apply (Fin.heq_ext_iff ?_).mpr
      · dsimp; omega
      · apply congrArg (level t); dsimp; omega

instance (t lo hi : ℕ) : Fintype (Slice t lo hi) := Fintype.ofEquiv _ (sliceEquiv t lo hi).symm

/-- A triangular countBelow before imposing the degree cutoff. -/
def unrestricted (l : ℕ) := (l-l/2)*(l/2+1)

private theorem unrestricted_succ (l : ℕ) : unrestricted (l+1) = unrestricted l + (l/2+1) := by
  rcases Nat.even_or_odd l with ⟨s,hs⟩ | ⟨s,hs⟩
  · rw [show l=2*s by omega]
    simp only [unrestricted,show 2*s/2=s by omega,show (2*s+1)/2=s by omega,
      show 2*s-s=s by omega,show 2*s+1-s=s+1 by omega]
    ring
  · rw [show l=2*s+1 by omega]
    have he : (2*s+1)/2 = s := by omega
    have he' : (2*s+1+1)/2 = s+1 := by omega
    simp only [unrestricted,he,he']
    have sub : 2*s+1-s=s+1 := by omega
    have sub' : 2*s+1+1-(s+1)=s+1 := by omega
    rw [sub,sub']
    ring

/-- Prefix of the positive part of the linear upper-degree correction. -/
def triangle (l : ℕ) := l*(l-1)/2

private theorem triangle_succ (l : ℕ) : triangle (l+1) = triangle l + l := by
  simp only [triangle, Nat.add_sub_cancel]
  cases l with
  | zero => decide
  | succ l =>
    simp only [Nat.add_succ_sub_one, Nat.succ_sub_one]
    have h : (l+1+1)*(l+1) = (l+1)*l + 2*(l+1) := by ring
    rw [h]
    omega

/-- Closed count below a derivative weight. Clip past the largest weight `2t`. -/
def countBelow (t l : ℕ) :=
  let n := min l (2*t+1)
  unrestricted n - triangle (n-t)

private theorem raw_prefix (t l : ℕ) (hl : l ≤ 2*t+1) :
    (∑ s ∈ range l, level t s) + triangle (l-t) = unrestricted l := by
  induction l with
  | zero => simp [triangle,unrestricted]
  | succ l ih =>
    have hle : l ≤ 2*t := by omega
    have h0 := ih (by omega)
    rw [sum_range_succ, unrestricted_succ]
    by_cases ht : l<t
    · have z : l-t=0 := by omega
      have z' : l+1-t=0 := by omega
      rw [z] at h0
      simp only [level,z,z',Nat.sub_zero] at *
      omega
    · have hsub : l+1-t=(l-t)+1 := by omega
      rw [hsub,triangle_succ]
      have succ : level t l + (l-t) = l/2+1 := by unfold level; omega
      omega

theorem prefix_eq_sum (t h : ℕ) : countBelow t h = ∑ s ∈ range h, level t s := by
  let n := min h (2*t+1)
  have hn : n ≤ 2*t+1 := min_le_right _ _
  have raw := raw_prefix t n hn
  have same : ∑ s ∈ range h, level t s = ∑ s ∈ range n, level t s := by
    symm
    apply sum_subset_zero_on_sdiff (range_mono (min_le_left _ _))
    · intro i hi
      have hi' := mem_sdiff.mp hi
      simp only [mem_range] at hi'
      dsimp [level]
      omega
    · simp
  unfold countBelow
  rw [same]
  change unrestricted n - triangle (n-t) = _
  omega

/-- Exact cardinality of a two-derivative weight slice. -/
theorem card_slice (t lo hi : ℕ) : Fintype.card (Slice t lo hi) = countBelow t hi - countBelow t lo := by
  rw [Fintype.card_congr (sliceEquiv t lo hi), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => level t (i + lo))]
  by_cases h : lo ≤ hi
  · have hs := sum_range_add (level t) lo (hi-lo)
    rw [Nat.add_sub_of_le h] at hs
    rw [prefix_eq_sum, prefix_eq_sum]
    simpa only [Nat.add_comm] using (show (∑ i ∈ range (hi-lo), level t (lo+i)) =
      (∑ i ∈ range hi, level t i) - ∑ i ∈ range lo, level t i by omega)
  · have hsub : hi-lo=0 := by omega
    rw [hsub]
    simp only [range_zero,sum_empty]
    rw [prefix_eq_sum,prefix_eq_sum]
    symm
    apply Nat.sub_eq_zero_of_le
    exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (by simp)

end ProximityGap.SecondOrderBlockCounts

#print axioms ProximityGap.SecondOrderBlockCounts.card_slice
