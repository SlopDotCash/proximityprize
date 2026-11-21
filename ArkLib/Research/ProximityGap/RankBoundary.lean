/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.FullPrizeContract

/-! # From a finite failure test to the operational threshold

The first failing count may be zero. An empty failure set gives safety at every radius.
-/

namespace ProximityPrize.RankBoundary
open FullPrizeReview
open scoped NNReal

/-- Search the finite grid of error counts for the first positive failure test. -/
noncomputable def firstFailure (n : ℕ) (fails : Fin (n + 1) → Prop) : Boundary n := by
  classical
  let T := Finset.univ.filter fails
  exact if h : T.Nonempty then some (T.min' h) else none

/-- The exceptional all-safe output is equivalent to passing every grid test. -/
theorem firstFailure_eq_none_iff {n : ℕ} (fails : Fin (n + 1) → Prop) :
    firstFailure n fails = none ↔ ∀ e, ¬ fails e := by
  classical
  let T := Finset.univ.filter fails
  change (if h : T.Nonempty then some (T.min' h) else none) = none ↔ ∀ e, ¬ fails e
  split_ifs with h
  · obtain ⟨e, he⟩ := h
    simp only [false_iff]
    exact fun hall => hall e (Finset.mem_filter.mp he).2
  · exact iff_of_true rfl fun e he => h ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩

/-- The radius-zero endpoint occurs exactly when the zero-error test fails. -/
theorem firstFailure_eq_some_zero_iff {n : ℕ} (fails : Fin (n + 1) → Prop) :
    firstFailure n fails = some 0 ↔ fails 0 := by
  classical
  let T := Finset.univ.filter fails
  change (if h : T.Nonempty then some (T.min' h) else none) = some 0 ↔ fails 0
  split_ifs with h
  · rw [Option.some.injEq]
    constructor
    · intro he
      have hmem := T.min'_mem h
      rw [he] at hmem
      exact (Finset.mem_filter.mp hmem).2
    · intro hf
      have hm : (0 : Fin (n + 1)) ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩
      exact le_antisymm (T.min'_le 0 hm) (Fin.zero_le _)
  · constructor
    · intro hempty
      cases hempty
    · intro hf
      exact False.elim (h ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩⟩)

/-- The grid cell containing a radius in the unit interval. -/
noncomputable def cell (n : ℕ) (δ : ℝ≥0) (hδ : δ ≤ 1) : Fin (n + 1) :=
  ⟨⌊δ * (n : ℝ≥0)⌋₊, by
    have hle : δ * (n : ℝ≥0) ≤ (n : ℝ≥0) := by
      simpa using mul_le_mul_of_nonneg_right hδ (by positivity)
    have h := Nat.floor_mono hle
    rw [Nat.floor_natCast] at h
    omega⟩

/-- An upward-closed finite failure test determining each radius's Hamming cell determines the
entire strict operational boundary, also at zero and on an all-safe grid. -/
theorem firstFailure_correct {n : ℕ} (hn : 0 < n) (fails : Fin (n + 1) → Prop)
    (safe : ℝ≥0 → Prop)
    (up : ∀ i j, i ≤ j → fails i → fails j)
    (test : ∀ δ (hδ : δ ≤ 1), safe δ ↔ ¬ fails (cell n δ hδ)) :
    correctBoundary n (firstFailure n fails) safe := by
  classical
  let T := Finset.univ.filter fails
  intro δ hδ
  rw [test δ hδ]
  change (¬ fails (cell n δ hδ)) ↔
    match (if h : T.Nonempty then some (T.min' h) else none) with
    | none => True
    | some e => δ < (e.val : ℝ≥0) / n
  split_ifs with h
  · let b := T.min' h
    have hb : fails b := (Finset.mem_filter.mp (T.min'_mem h)).2
    change (¬ fails (cell n δ hδ)) ↔ δ < (b.val : ℝ≥0) / n
    have hpos : 0 < (n : ℝ≥0) := by exact_mod_cast hn
    rw [lt_div_iff₀ hpos, ← Nat.floor_lt (by positivity)]
    constructor
    · intro hp
      change cell n δ hδ < b
      exact lt_of_not_ge fun hle => hp (up b (cell n δ hδ) hle hb)
    · intro hlt hf
      have hmem : cell n δ hδ ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩
      exact (not_le.mpr hlt) (T.min'_le _ hmem)
  · simp only [iff_true]
    intro hf
    exact h ⟨cell n δ hδ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩⟩

/-- Grid-level evaluations suffice for predicates constant on Hamming cells and decreasing in
the radius. The algebraic failure test need only be proved equivalent at the grid points. -/
theorem firstFailure_correct_of_grid {n : ℕ} (hn : 0 < n) (fails : Fin (n + 1) → Prop)
    (safe : ℝ≥0 → Prop)
    (down : ∀ a b, a ≤ b → safe b → safe a)
    (step : ∀ a b : ℝ≥0, ⌊a * n⌋₊ = ⌊b * n⌋₊ → (safe a ↔ safe b))
    (atGrid : ∀ i : Fin (n + 1), safe ((i.val : ℝ≥0) / n) ↔ ¬ fails i) :
    correctBoundary n (firstFailure n fails) safe := by
  have hn' : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  apply firstFailure_correct hn
  · intro i j hij hfi
    by_contra hfj
    have hg : (i.val : ℝ≥0) / n ≤ (j.val : ℝ≥0) / n :=
      div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)
    exact (atGrid i).mp (down _ _ hg ((atGrid j).mpr hfj)) hfi
  · intro δ hδ
    apply Iff.trans (step δ (((cell n δ hδ).val : ℝ≥0) / n) ?_) (atGrid _)
    rw [div_mul_cancel₀ _ hn', Nat.floor_natCast]
    rfl

#print axioms firstFailure_eq_none_iff
#print axioms firstFailure_eq_some_zero_iff
#print axioms firstFailure_correct
#print axioms firstFailure_correct_of_grid
end ProximityPrize.RankBoundary
