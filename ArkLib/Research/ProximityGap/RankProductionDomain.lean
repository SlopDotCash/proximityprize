/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.RankKnownDomain
import ArkLib.Research.ProximityGap.RankExecutable
import ArkLib.Research.ProximityGap.Frontier.BudgetOneProduction
import ArkLib.Data.CodingTheory.ProximityGap.MCAStaircaseRS

/-! # Four computed boundary values from the rank formulas at length 2³⁰

At the 128-bit tolerance the explicit prime supplies a budget of one. The one-error
MCA spike and the minimum-distance midpoint determine both first failures, including
their endpoints. Uniqueness transfers these values to the general rank formulas.
-/

namespace ProximityPrize.RankProductionDomain

open Code CoreDefinitions ProximityGap ProximityGap.GrandChallenges FullPrizeReview
open BudgetOneProduction
open scoped NNReal ENNReal

/-- The first-error staircase and its endpoint for arbitrary domains in the budget-one band. -/
theorem mca_good_iff {I F : Type} [Fintype I] [Nonempty I] [Field F]
    [Fintype F] [SampleableType F] (D : I ↪ F) {k : ℕ}
    (room : k + 2 ≤ Fintype.card I) (budget : Fintype.card F / 2 ^ 128 = 1) (δ : ℝ≥0) :
    mcaError (AffineLineGenerator F) (ReedSolomon.code D k) (δ : ℝ) ≤
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ↔ δ < gridPt (ι := I) 1 := by
  classical
  rw [← epsMCA_eq_mcaError, gridPt, Nat.cast_one]
  have band := FourRateSmoothMca128.prize_band (Fintype.card F) Fintype.card_pos
  rw [budget] at band
  have hn : 0 < (Fintype.card I : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  constructor
  · intro safe
    by_contra! crossed
    have low : (1 : ℝ≥0) ≤ δ * Fintype.card I := (div_le_iff₀ hn).mp crossed
    have two : 2 ≤ Fintype.card I := by omega
    obtain ⟨pos⟩ : Nonempty (Fin 2 ↪ I) :=
      Function.Embedding.nonempty_of_card_le (by simpa using two)
    have bad := SpikeFloor.epsMCA_ge_j_div_card (ReedSolomon.code D k)
      (MCAStaircaseRS.rs_noWeightLE D room) (δ := δ) (by simpa using low)
      (by decide) two pos (pos.trans D) (b := (1 : F)) one_ne_zero
    exact band.2.not_ge (bad.trans safe)
  · intro safe
    have low : δ * Fintype.card I < (1 : ℝ≥0) := (lt_div_iff₀ hn).mp safe
    exact (SpikeFloor.epsMCA_le_j_div_card (j := 1) (ReedSolomon.code D k)
      (MCAStaircaseRS.rs_noWeightLE D (by omega)) (by simpa using low)).trans band.1

private def count {n : ℕ} (e : ℕ) (he : e ≤ n) : Boundary n :=
  some ⟨e, Nat.lt_succ_of_le he⟩

/-- Closed evaluations of the rank formulas on every eligible domain in the one-word band. -/
theorem rank_budget_one {I F : Type} [Fintype I] [Nonempty I] [Field F]
    [Fintype F] [DecidableEq F] [SampleableType F] (D : I ↪ F) [ReedSolomon.Smooth D]
    {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (hr : hasPrizeRate (Fintype.card I) k)
    (room : k + 2 ≤ Fintype.card I) (budget : Fintype.card F / 2 ^ 128 = 1) :
    (RankReview.mcaAnswer D (prizeThreshold : ℝ≥0) k).map Fin.val = some 1 ∧
      (RankReview.listAnswer D (prizeThreshold : ℝ≥0) k m).map Fin.val =
        some ((Fintype.card I - k + 2) / 2) := by
  classical
  let n := Fintype.card I
  let e := (n - k + 2) / 2
  have hle : e ≤ Fintype.card I := by dsimp [e, n]; omega
  have hM' : correctBoundary n (count 1 (by dsimp [n]; omega))
      (fun δ => mcaError (AffineLineGenerator F) (ReedSolomon.code D k) (δ : ℝ) ≤
        ((prizeThreshold : ℝ≥0) : ℝ≥0∞)) := by
    intro δ _
    exact mca_good_iff D room budget δ
  have hL' : correctBoundary n (count e hle) (fun δ =>
      (Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → F)))
        (δ : ℝ) : ℝ≥0∞) ≤ ((prizeThreshold : ℝ≥0) : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞)) := by
    intro δ _
    refine (ListBudgetOne.prize_safe_iff D k m hk (by omega) hm (δ : ℝ) budget).trans ?_
    change (_ < _) ↔ δ < (e : ℝ≥0) / n
    rw [← NNReal.coe_lt_coe, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast]
  obtain ⟨hM, hL⟩ := RankReview.correctForEveryDomain D (prizeThreshold : ℝ≥0) k hr
  exact ⟨congrArg (Option.map Fin.val) (correctBoundary_unique Fintype.card_pos hM hM'),
    congrArg (Option.map Fin.val) (correctBoundary_unique Fintype.card_pos (hL m hm) hL')⟩

/-- The executable search returns the same closed answers for every valid presentation. -/
theorem executable_budget_one {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F]
    [Fintype F] [DecidableEq F] [SampleableType F] (D : I ↪ F) [ReedSolomon.Smooth D]
    (E : Fin (Fintype.card I) ≃ I) (labels : List F) (hf : ∀ g, g ∈ labels)
    (points : List I) (hi : ∀ i, i ∈ points) {k m : ℕ} (hk : 0 < k) (hm : 0 < m)
    (hr : hasPrizeRate (Fintype.card I) k) (room : k + 2 ≤ Fintype.card I)
    (budget : Fintype.card F / 2 ^ 128 = 1) :
    (RankExecutable.mcaBoundary E labels D k 1).map Fin.val = some 1 ∧
      (RankExecutable.listBoundary points D (Fintype.card I) k (Fintype.card F) m 1).map Fin.val =
        some ((Fintype.card I - k + 2) / 2) := by
  have hbudget := (RankExecutable.prizeBudget F).trans budget
  have hM := RankExecutable.mcaBoundary_eq E labels hf D (prizeThreshold : ℝ≥0) k
  have hL := RankExecutable.listBoundary_eq points hi D (prizeThreshold : ℝ≥0) k m
    Fintype.card_pos (by omega)
  rw [hbudget] at hM hL
  rw [hM, hL]
  exact rank_budget_one D hk hm hr room budget

private abbrev I := Fin (2 ^ 30)

noncomputable local instance : SampleableType (ZMod p) := SampleableType.ofFintype _
attribute [local instance] BudgetOneProduction.smooth

private theorem params (j : Fin 4) :
    hasPrizeRate (Fintype.card I) (prizeDimension (ι := I) j) ∧
    0 < prizeDimension (ι := I) j ∧ prizeDimension (ι := I) j + 2 ≤ Fintype.card I ∧
    (Fintype.card I - prizeDimension (ι := I) j + 2) / 2 = firstBad j := by
  simp only [I, prizeDimension, Fintype.card_fin]
  fin_cases j <;> norm_num [prizeDenominator, firstBad, hasPrizeRate]

private theorem sizes_literal (j : Fin 4) :
    prizeDimension (ι := I) j = ![536870912, 268435456, 134217728, 67108864] j := by
  simp only [prizeDimension, I, Fintype.card_fin]
  fin_cases j <;> decide

private theorem budget_one : Fintype.card (ZMod p) / 2 ^ 128 = 1 := by
  rw [ZMod.card]
  decide

/-- The rank and distance calculations give the same first failing counts at each prize rate. -/
theorem formulaValues (j : Fin 4) (m : ℕ) (hm : 0 < m) :
    (RankReview.mcaAnswer domain (prizeThreshold : ℝ≥0) (prizeDimension (ι := I) j)).map
        Fin.val = some 1 ∧
    (RankReview.listAnswer domain (prizeThreshold : ℝ≥0) (prizeDimension (ι := I) j) m).map
        Fin.val = some (firstBad j) := by
  obtain ⟨hr, hk, room, he⟩ := params j
  obtain ⟨hM, hL⟩ := rank_budget_one domain hk hm hr room budget_one
  exact ⟨hM, hL.trans (congrArg some he)⟩

/-- Dimensions followed by the two first failures in decreasing rate order. -/
theorem numericalBoundaries (m : ℕ) (hm : 0 < m) :
    ([0, 1, 2, 3] : List (Fin 4)).map (fun j =>
      let k := prizeDimension (ι := I) j
      (k, (RankReview.mcaAnswer domain (prizeThreshold : ℝ≥0) k).map Fin.val,
        (RankReview.listAnswer domain (prizeThreshold : ℝ≥0) k m).map Fin.val)) =
    [(536870912, some 1, some 268435457), (268435456, some 1, some 402653185),
      (134217728, some 1, some 469762049), (67108864, some 1, some 503316481)] := by
  simp only [List.map_cons, List.map_nil, (formulaValues 0 m hm).1, (formulaValues 0 m hm).2,
    (formulaValues 1 m hm).1, (formulaValues 1 m hm).2, (formulaValues 2 m hm).1,
    (formulaValues 2 m hm).2, (formulaValues 3 m hm).1, (formulaValues 3 m hm).2]
  simp only [sizes_literal]
  rfl

#print axioms mca_good_iff
#print axioms executable_budget_one
#print axioms numericalBoundaries

end ProximityPrize.RankProductionDomain
