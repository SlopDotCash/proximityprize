import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.List.Count

/-!
# An exact sum of squared histogram counts

The executable splits natural-number keys by their low bit, removes that bit,
and recurses on the two buckets. Once all key bits are exhausted, the square
of the bucket size counts all ordered pairs of equal keys in that bucket.
-/

open Finset

namespace ProximityGap.ExactHistogram

/-- Sum of squared bucket sizes after partitioning by the lowest `depth` bits. -/
def bucketSquares : ℕ → List ℕ → ℕ
  | 0, xs => xs.length ^ 2
  | k+1, xs => if xs.isEmpty then 0 else
    let even := (xs.filter (fun i => i % 2 == 0)).map (fun i => i / 2)
    let odd := (xs.filter (fun i => i % 2 == 1)).map (fun i => i / 2)
    bucketSquares k even + bucketSquares k odd

private def branch (r : ℕ) (xs : List ℕ) : List ℕ :=
  (xs.filter (fun i => i % 2 == r)).map (fun i => i / 2)

private theorem count_branch (r : ℕ) (hr : r < 2) (xs : List ℕ) (y : ℕ) :
    (branch r xs).count y = xs.count (2*y+r) := by
  induction xs with
  | nil => simp [branch]
  | cons x xs ih =>
    by_cases hx : x%2 = r
    · have htt : x/2 = y ↔ x = 2*y+r := by omega
      simpa [branch, hx, List.count_cons, beq_iff_eq, htt] using congrArg
        (fun k : ℕ ↦ k + if x = 2*y+r then 1 else 0) ih
    · have hne : x ≠ 2*y+r := by omega
      simpa [branch, hx, List.count_cons, beq_iff_eq, hne] using ih

private theorem interleave_sum (m : ℕ) (f : ℕ → ℕ) :
    (∑ i ∈ range m, f (2*i)) + (∑ i ∈ range m, f (2*i+1)) = ∑ i ∈ range (2*m), f i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, sum_range_succ, sum_range_succ]
    rw [show 2*m+2 = (2*m+1)+1 by omega, sum_range_succ, sum_range_succ]
    omega

private theorem bucketSquares_eq_range (depth : ℕ) (xs : List ℕ)
    (h : ∀ x ∈ xs, x < 2^depth) :
    bucketSquares depth xs = ∑ x ∈ range (2^depth), xs.count x ^ 2 := by
  induction depth generalizing xs with
  | zero =>
    have hc : xs.count 0 = xs.length := List.count_eq_length.mpr (by
      intro x hx
      have hz := h x hx
      simp only [pow_zero] at hz
      omega)
    simp [bucketSquares,hc]
  | succ d ih =>
    by_cases hx : xs = []
    · subst xs; simp [bucketSquares]
    have hh (r : ℕ) : ∀ x ∈ branch r xs, x < 2^d := by
      intro x hm
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      have hlt := h a (List.mem_filter.mp ha).1
      rw [pow_succ] at hlt
      omega
    rw [bucketSquares, ite_eq_right (by simpa using hx)]
    change bucketSquares d (branch 0 xs) + bucketSquares d (branch 1 xs) = _
    rw [ih _ (hh 0), ih _ (hh 1), pow_succ, Nat.mul_comm (2^d) 2]
    simp only [count_branch 0 (by decide), count_branch 1 (by decide), Nat.add_zero]
    exact interleave_sum _ (fun i ↦ xs.count i ^ 2)

/-- For keys below `2^depth` the buckets are the exact multiplicities of the
distinct keys. The right side counts every ordered pair of equal entries. -/
theorem bucketSquares_eq_sum (depth : ℕ) (xs : List ℕ) (h : ∀ x ∈ xs, x < 2^depth) :
    bucketSquares depth xs = ∑ x ∈ xs.toFinset, xs.count x ^ 2 := by
  rw [bucketSquares_eq_range depth xs h]
  symm
  apply Finset.sum_subset
  · intro x hx
    exact mem_range.mpr (h x (List.mem_toFinset.mp hx))
  · intro x _ hx
    have hn : x ∉ xs := fun hm ↦ hx (List.mem_toFinset.mpr hm)
    simp [List.count_eq_zero_of_not_mem hn]

#print axioms bucketSquares_eq_sum

end ProximityGap.ExactHistogram
