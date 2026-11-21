/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.RankReview
import ArkLib.Research.ProximityGap.Frontier.ListSupportGaussian
import ArkLib.Research.ProximityGap.Frontier.SimultaneousSupportGaussian

/-! # Computing operational radii from a presented domain and integer budget

An input budget is the maximum permitted number of field labels or list members.
The executable functions use natural numbers and field arithmetic.
Their correctness statements also apply when the budget is obtained from a real tolerance.
-/
set_option autoImplicit false

namespace ProximityPrize.RankExecutable

open Code FullPrizeReview RankBoundary ProximityGap ProximityGap.GrandChallenges CoreDefinitions
open scoped NNReal ENNReal

/-- Return the least failing error count, or certify that every error count passes. -/
def scan (n : ℕ) (safe : Fin (n + 1) → Bool) : Boundary n :=
  let bad := Finset.univ.filter (fun e => safe e = false)
  if h : bad.Nonempty then some (bad.min' h) else none

/-- The executable search returns the first count satisfying the mathematical failure test. -/
theorem scan_eq_firstFailure {n : ℕ} (safe : Fin (n + 1) → Bool) (fails : Fin (n + 1) → Prop)
    (hs : ∀ e, safe e = true ↔ ¬ fails e) : scan n safe = firstFailure n fails := by
  classical
  have eq : Finset.univ.filter (fun e => safe e = false) = Finset.univ.filter fails := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [Bool.not_eq_true] using (not_congr (hs e)).trans not_not
  unfold scan firstFailure
  simp only [eq]

variable {F I : Type} [Field F] [DecidableEq F] [DecidableEq I]

/-- Compute the list boundary from a coordinate list, its evaluation map, and an integer budget. -/
def listBoundary (points : List I) (D : I ↪ F) (n k q m B : ℕ) : Boundary n :=
  scan n fun e => ListSupportRank.gaussianSafe points D k q m B (n - e.val)

/-- Executing the list search produces the universal operational answer. -/
theorem listBoundary_eq [Fintype I] [Fintype F] (points : List I) (hp : ∀ i, i ∈ points)
    (D : I ↪ F) (ε : NNReal) (k m : ℕ) (hn : 0 < Fintype.card I) (hk : k ≤ Fintype.card I) :
    listBoundary points D (Fintype.card I) k (Fintype.card F) m (RankReview.budget F ε) =
      RankReview.listAnswer D ε k m := by
  apply scan_eq_firstFailure
  intro e
  rw [ListSupportRank.gaussianSafe_iff points hp D k m _ _ hn hk,
    ListSupportRank.rs_vandermonde_safe_iff D k m _ _ hn hk]
  unfold RankReview.listFails
  push Not
  rfl

/-- Compute the MCA boundary from enumerations of the coordinates and the field. -/
def mcaBoundary {n : ℕ} (E : Fin n ≃ I) (labels : List F) (D : I ↪ F) (k B : ℕ) : Boundary n :=
  scan n fun e => SimultaneousSupportGaussian.mcaSafe E labels D k B (n - e.val)

/-- Executing the MCA search produces the universal operational answer. -/
theorem mcaBoundary_eq [Fintype I] [Nonempty I] [Fintype F] [SampleableType F]
    (E : Fin (Fintype.card I) ≃ I) (labels : List F) (hlabels : ∀ g, g ∈ labels)
    (D : I ↪ F) (ε : ℝ≥0) (k : ℕ) :
    mcaBoundary E labels D k (RankReview.budget F ε) = RankReview.mcaAnswer D ε k := by
  classical
  apply scan_eq_firstFailure
  intro e
  rw [SimultaneousSupportGaussian.mcaSafe_iff E labels hlabels D k _ e.val
    (Nat.le_of_lt_succ e.isLt) Fintype.card_pos]
  let δ := gridPt (ι := I) e.val
  change (mcaError (AffineLineGenerator F) (ReedSolomon.code D k) (δ : ℝ) ≤ _) ↔ _
  rw [← epsMCA_eq_mcaError, ← not_lt, SimultaneousSupportRank.budget_failure_iff]
  unfold RankReview.mcaFails
  have hs (S : Finset I) : ((1 - δ) * Fintype.card I ≤ (S.card : ℝ≥0)) ↔
      Fintype.card I - e.val ≤ S.card := by
    rw [← relDist_floor_bound_iff_complement_bound, gridPt_mul_card, Nat.floor_natCast]
  simp_rw [ge_iff_le, hs]

/-- Both executable boundary functions classify every real radius in the prize contract. -/
theorem correctForEveryDomain [Fintype I] [Nonempty I] [Fintype F] [SampleableType F]
    (E : Fin (Fintype.card I) ≃ I) (labels : List F) (hf : ∀ g, g ∈ labels)
    (points : List I) (hi : ∀ i, i ∈ points) (D : I ↪ F) [ReedSolomon.Smooth D] (ε : ℝ≥0) :
    correctForDomain D ε
      (fun k => mcaBoundary E labels D k (RankReview.budget F ε))
      (fun k m => listBoundary points D (Fintype.card I) k (Fintype.card F) m
        (RankReview.budget F ε)) := by
  intro k hk
  have hk' : k ≤ Fintype.card I := by
    rcases hk with h | h | h | h <;> omega
  obtain ⟨hM, hL⟩ := RankReview.correctForEveryDomain D ε k hk
  constructor
  · simpa only [mcaBoundary_eq E labels hf D ε k] using hM
  · intro m hm
    simpa only [listBoundary_eq points hi D ε k m Fintype.card_pos hk'] using hL m hm

/-- At the prize example tolerance, the evaluator only needs ordinary integer division. -/
theorem prizeBudget (F : Type) [Fintype F] :
    RankReview.budget F (prizeThreshold : ℝ≥0) = Fintype.card F / 2 ^ 128 := by
  unfold RankReview.budget
  have h : (prizeThreshold : ℝ≥0) = 1 / (2 ^ 128 : ℕ) := by
    norm_num [prizeThreshold]
  rw [h, one_div, mul_comm, ← div_eq_mul_inv, Nat.floor_div_eq_div]

/-- The executable evaluators at 128-bit tolerance take the field order directly. -/
theorem correctAtPrizeTolerance [Fintype I] [Nonempty I] [Fintype F] [SampleableType F]
    (E : Fin (Fintype.card I) ≃ I) (labels : List F) (hf : ∀ g, g ∈ labels)
    (points : List I) (hi : ∀ i, i ∈ points) (D : I ↪ F) [ReedSolomon.Smooth D] :
    correctForDomain D (prizeThreshold : ℝ≥0)
      (fun k => mcaBoundary E labels D k (Fintype.card F / 2 ^ 128))
      (fun k m => listBoundary points D (Fintype.card I) k (Fintype.card F) m
        (Fintype.card F / 2 ^ 128)) := by
  simpa only [prizeBudget] using correctForEveryDomain E labels hf points hi D
    (prizeThreshold : ℝ≥0)

#print axioms correctAtPrizeTolerance
#print axioms listBoundary_eq
#print axioms mcaBoundary_eq
#print axioms correctForEveryDomain

end ProximityPrize.RankExecutable
