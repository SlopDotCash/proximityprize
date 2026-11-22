/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.DesignatedPrimeJohnson

/-! # One grid test for each remaining second-prime Johnson comparison

When a real comparison radius lies strictly between consecutive Hamming steps, safety
at the lower step determines which side contains the operational supremum.
-/

namespace ProximityPrize.SecondPrimeJohnsonPivot

open FullPrizeReview ProximityGap ProximityGap.MCAThresholdLedger RankJohnsonComparison
open ArkLib.ProximityGap ArkLib.ProximityGap.Frontier
open scoped NNReal ENNReal

/-- The numerical cutoff of a correct boundary is the supremum of its safe radii.
The supremum of an empty safe set in the nonnegative reals is zero. -/
theorem correctBoundary_supremum {n : ℕ} (hn : 0 < n) {answer : Boundary n}
    {safe : ℝ≥0 → Prop} (spec : correctBoundary n answer safe) :
    sSup {δ : ℝ≥0 | δ ≤ 1 ∧ safe δ} = (cutoff answer : ℝ≥0) / n := by
  have pos : 0 < (n : ℝ≥0) := by exact_mod_cast hn
  cases answer with
  | none =>
    have eq : {δ : ℝ≥0 | δ ≤ 1 ∧ safe δ} = Set.Iic 1 := by
      ext δ
      exact ⟨fun h => h.1, fun h => ⟨h, (spec δ h).mpr trivial⟩⟩
    rw [eq, csSup_Iic]
    exact (div_self pos.ne').symm
  | some e =>
    let r : ℝ≥0 := (e.val : ℝ≥0) / n
    have hr : r ≤ 1 := (div_le_one pos).mpr (by exact_mod_cast Nat.le_of_lt_succ e.isLt)
    have eq : {δ : ℝ≥0 | δ ≤ 1 ∧ safe δ} = Set.Ico 0 r := by
      ext δ
      constructor
      · intro h
        exact ⟨zero_le, (spec δ h.1).mp h.2⟩
      · intro h
        have hδ : δ ≤ 1 := h.2.le.trans hr
        exact ⟨hδ, (spec δ hδ).mpr h.2⟩
    change sSup _ = r
    rw [eq]
    rcases eq_or_lt_of_le (show 0 ≤ r from zero_le) with hz | hp
    · simp [← hz]
    · exact csSup_Ico hp

/-- If `J` falls strictly inside a Hamming cell, the safety test at its left endpoint
decides both strict comparisons with the real supremum. Equality is impossible. -/
theorem correctBoundary_pivot {n g : ℕ} (hg : g < n) {answer : Boundary n}
    {safe : ℝ≥0 → Prop} (spec : correctBoundary n answer safe) {J : ℝ}
    (left : (g : ℝ) / n < J) (right : J < ((g + 1 : ℕ) : ℝ) / n) :
    let R : ℝ := (sSup {δ : ℝ≥0 | δ ≤ 1 ∧ safe δ} : ℝ≥0)
    (safe ((g : ℝ≥0) / n) ↔ J < R) ∧ (¬ safe ((g : ℝ≥0) / n) ↔ R < J) ∧ R ≠ J := by
  dsimp only
  have hn : 0 < n := by omega
  have pos : 0 < (n : ℝ≥0) := by exact_mod_cast hn
  have unit : (g : ℝ≥0) / n ≤ 1 := (div_le_one pos).mpr (by exact_mod_cast hg.le)
  have test : safe ((g : ℝ≥0) / n) ↔ g < cutoff answer := by
    cases answer with
    | none => exact iff_of_true ((spec _ unit).mpr trivial) hg
    | some e =>
      refine (spec _ unit).trans ?_
      change (g : ℝ≥0) / n < (e.val : ℝ≥0) / n ↔ g < e.val
      rw [div_lt_div_iff_of_pos_right pos, Nat.cast_lt]
  rw [correctBoundary_supremum hn spec, test]
  simp only [NNReal.coe_div, NNReal.coe_natCast]
  by_cases lt : g < cutoff answer
  · have above : J < (cutoff answer : ℝ) / n :=
      right.trans_le (div_le_div_of_nonneg_right (by exact_mod_cast lt : ((g + 1 : ℕ) : ℝ) ≤ _)
        (by positivity))
    simp [lt, above, above.ne', not_lt.mpr above.le]
  · have below : (cutoff answer : ℝ) / n < J :=
      (div_le_div_of_nonneg_right (by exact_mod_cast le_of_not_gt lt : (cutoff answer : ℝ) ≤ g)
        (by positivity)).trans_lt left
    simp [lt, below, below.ne, not_lt.mpr below.le]

local instance : Fact PrizeShapePrimeP30Second.P.Prime := ⟨PrizeShapePrimeP30Second.prime_P⟩
open SecondPrimeSmoothSeed (N F dom)

/-- The two strict signs and non-equality for the interleaved code on the actual subgroup.
The pivot test uses the sponsor's 128-bit tolerance. -/
def criterion (k g width : ℕ) : Prop :=
  let C := (ReedSolomon.code dom k : Set (Fin N → F)) ^⋈ (Fin width)
  let ε := ((prizeThreshold : ℝ≥0) : ℝ≥0∞)
  let err := epsMCA (F := F) C ((g : ℝ≥0) / N)
  let R : ℝ := mcaDeltaStar (F := F) C ε
  let J := DesignatedPrimeJohnson.johnson k
  (err ≤ ε ↔ J < R) ∧ (ε < err ↔ R < J) ∧ R ≠ J

private theorem of_cell (k g width : ℕ) [NeZero width] (hg : g < N)
    (left : (g : ℝ) / N < DesignatedPrimeJohnson.johnson k)
    (right : DesignatedPrimeJohnson.johnson k < ((g + 1 : ℕ) : ℝ) / N) :
    criterion k g width := by
  classical
  let _ : SampleableType F := SampleableType.ofFintype _
  let C := (ReedSolomon.code dom k : Set (Fin N → F))
  let ε := (prizeThreshold : ℝ≥0)
  let safe := fun δ : ℝ≥0 => epsMCA (F := F) C δ ≤ (ε : ℝ≥0∞)
  have spec := RankReview.mcaAnswer_correct dom ε k
  simp only [← epsMCA_eq_mcaError] at spec
  have cell := correctBoundary_pivot (n := Fintype.card (Fin N)) (g := g)
    (by simpa using hg) (safe := safe) spec (J := DesignatedPrimeJohnson.johnson k)
    (by simpa using left) (by simpa using right)
  unfold criterion
  simp only [epsMCA_interleaved_eq, mcaDeltaStar_interleaved_eq]
  simpa only [Fintype.card_fin, safe, C, ε, mcaDeltaStar, mcaGoodRadii, not_le] using cell

/-- At half rate, the test at exactly 314,491,699 errors determines the side of Johnson. -/
theorem half (width : ℕ) [NeZero width] : criterion (2 ^ 29) 314491699 width := by
  apply of_cell _ _ _ (by decide)
  · exact (below_iff (n := N) (by decide) (2 ^ 29 - 1)
      (some ⟨314491699, by decide⟩)).mpr (by decide)
  · exact (above_iff (n := N) (by decide) (2 ^ 29 - 1)
      (some ⟨314491700, by decide⟩)).mpr (by decide)

/-- At quarter rate, the test at exactly 536,870,913 errors determines the side of Johnson. -/
theorem quarter (width : ℕ) [NeZero width] : criterion (2 ^ 28) 536870913 width := by
  apply of_cell _ _ _ (by decide)
  · exact (below_iff (n := N) (by decide) (2 ^ 28 - 1)
      (some ⟨536870913, by decide⟩)).mpr (by decide)
  · exact (above_iff (n := N) (by decide) (2 ^ 28 - 1)
      (some ⟨536870914, by decide⟩)).mpr (by decide)

end ProximityPrize.SecondPrimeJohnsonPivot
