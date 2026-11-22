/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.RankBoundary

/-! # Binary search for the first failing Hamming count

A nonincreasing Boolean safety test determines an initial segment of the grid.
The search tests zero first, then bisects the remaining interval. Its right
endpoint is a sentinel for the all-safe case and never requires a grid test.
-/

namespace ProximityPrize.RankBinarySearch

private def bisect (safe : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, lo, _ => (lo, 0)
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := lo + (hi - lo) / 2
      let result := if safe mid then bisect safe fuel (mid + 1) hi else bisect safe fuel lo mid
      (result.1, result.2 + 1)
    else (lo, 0)

private theorem bisect_checks (safe : ℕ → Bool) (fuel lo hi : ℕ) :
    (bisect safe fuel lo hi).2 ≤ fuel := by
  induction fuel generalizing lo hi with
  | zero => rfl
  | succ fuel ih =>
    simp only [bisect]
    split
    · split <;> exact Nat.succ_le_succ (ih _ _)
    · exact Nat.zero_le _

private theorem bisect_cut {safe : ℕ → Bool} {cut : ℕ} (test : ∀ x, safe x = true ↔ x < cut)
    (fuel lo hi : ℕ) (left : lo ≤ cut) (right : cut ≤ hi) (width : hi - lo < 2 ^ fuel) :
    (bisect safe fuel lo hi).1 = cut := by
  induction fuel generalizing lo hi with
  | zero =>
    simp only [pow_zero] at width
    change lo = cut
    omega
  | succ fuel ih =>
    rw [pow_succ] at width
    simp only [bisect]
    split
    · rename_i separated
      split
      · rename_i safeMid
        exact ih _ _ (by have := (test _).mp safeMid; omega) right (by omega)
      · rename_i badMid
        exact ih _ _ left (by have := mt (test _).mpr badMid; omega) (by omega)
    · change lo = cut
      omega

private def extend {len : ℕ} (safe : Fin len → Bool) (i : ℕ) : Bool :=
  if h : i < len then safe ⟨i, h⟩ else false

/-- Search an arbitrary finite grid, returning the first failing index and the
number of safety tests. The empty grid returns `(none, 0)`. -/
def searchGrid : (len : ℕ) → (Fin len → Bool) → Option (Fin len) × ℕ
  | 0, _ => (none, 0)
  | n + 1, safe =>
    if safe 0 then
      let result := bisect (extend safe) (n.log2 + 1) 1 (n + 1)
      (if h : result.1 < n + 1 then some ⟨result.1, h⟩ else none, result.2 + 1)
    else (some 0, 1)

/-- Binary search over all `n+1` possible Hamming error counts. -/
def search (n : ℕ) (safe : Fin (n + 1) → Bool) : FullPrizeReview.Boundary n :=
  (searchGrid (n + 1) safe).1

/-- The probe at zero plus binary search uses at most `⌊log₂ n⌋ + 2` safety
tests regardless of the cost of evaluating the safety predicate. -/
theorem checks_le (n : ℕ) (safe : Fin (n + 1) → Bool) :
    (searchGrid (n + 1) safe).2 ≤ n.log2 + 2 := by
  simp only [searchGrid]
  split
  · exact Nat.succ_le_succ (bisect_checks _ _ _ _)
  · omega

/-- Failure at zero is returned after exactly one safety test. -/
theorem failure_at_zero {n : ℕ} {safe : Fin (n + 1) → Bool} (h : safe 0 = false) :
    searchGrid (n + 1) safe = (some 0, 1) := by
  simp [searchGrid, h]

private theorem search_cut {n cut : ℕ} (safe : Fin (n + 1) → Bool) (hcut : cut ≤ n + 1)
    (test : ∀ i, safe i = true ↔ i.val < cut) :
    search n safe = if h : cut < n + 1 then some ⟨cut, h⟩ else none := by
  have all (x : ℕ) : extend safe x = true ↔ x < cut := by
    unfold extend
    split
    · exact test _
    · simp only [Bool.false_eq_true, false_iff]
      omega
  by_cases hz : safe 0 = true
  · have pos : 0 < cut := (test 0).mp hz
    have out := bisect_cut all (n.log2 + 1) 1 (n + 1) (by omega) hcut
      (by simpa using (Nat.lt_log2_self (n := n)))
    simp [search, searchGrid, hz, out]
  · have zero : cut = 0 := by have := mt (test 0).mpr hz; simpa using this
    subst cut
    simp [search, searchGrid, hz]

/-- For antitone safety, binary and linear first-failure searches return the
same index. This also covers an all-safe grid and failure at zero. -/
theorem search_eq_find? (n : ℕ) (safe : Fin (n + 1) → Bool)
    (down : ∀ a b, a ≤ b → safe b = true → safe a = true) :
    search n safe = Fin.find? (fun e => !(safe e)) := by
  by_cases hb : ∃ i, (!safe i) = true
  · let cut := Fin.find (fun i => (!safe i) = true) hb
    have first : (!safe cut) = true ∧ ∀ i < cut, ¬ (!safe i) = true :=
      (Fin.find_eq_iff hb).mp rfl
    have test (i : Fin (n + 1)) : safe i = true ↔ i.val < cut.val := by
      constructor
      · intro hi
        by_contra! h
        have hcut := down cut i h hi
        simpa [hcut] using first.1
      · intro hi
        simpa using first.2 i hi
    rw [Fin.find?_eq_some_find_of_exists hb, search_cut safe cut.isLt.le test,
      dite_eq_left cut.isLt]
  · have test (i : Fin (n + 1)) : safe i = true ↔ i.val < n + 1 := by
      simpa [i.isLt] using (show safe i = true by
        simpa using (show ¬ (!safe i) = true from fun h => hb ⟨i, h⟩))
    rw [Fin.find?_eq_dite, dite_eq_right hb, search_cut safe le_rfl test,
      dite_eq_right (lt_irrefl _)]

end ProximityPrize.RankBinarySearch
