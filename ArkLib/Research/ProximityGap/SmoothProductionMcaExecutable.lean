/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothTwoHeadProduction
import ArkLib.Research.ProximityGap.Frontier.SmoothCubicBudgetWindow

/-! # Computing the known smooth-field MCA thresholds at length 2³⁰ -/

set_option autoImplicit false
namespace ProximityPrize.SmoothProductionMcaExecutable
open ArkLib.ProximityGap.Frontier
open _root_.ProximityGap
open SmoothTwoHeadProduction (n first)
open scoped NNReal

/-- Exact first failure when a proved two-head or three-head budget window applies. -/
def knownCount (k B : ℕ) : Option ℕ :=
  let a := (n-k)/2
  if k = 268435456 ∧ B ≤ 894784857 then some (first 402653184 B)
  else if k = 67108864 ∧ 1565873494 ≤ B ∧ B ≤ 2147483648 then some (max 671088640 (B/3))
  else if 2 ≤ k ∧ k+2*a = n ∧ n < 3*a ∧ B/2 < n ∧
      DoubleQuadraticThreshold.agreements n k ≤ n-B/2+1 then some (first a B)
  else none

variable {F I : Type} [Field F] [DecidableEq F] [Fintype I] [Nonempty I] [Fintype F]

/-- Every successful integer test equals the support-rank answer for any smooth domain. -/
theorem knownCount_correct (D : I ↪ F) [ReedSolomon.Smooth D]
    (hn : Fintype.card I = n) {k B e : ℕ} (hB : Fintype.card F / 2^128 = B)
    (h : knownCount k B = some e) :
    (RankReview.mcaAnswer D (prizeThreshold : ℝ≥0) k).map Fin.val = some e := by
  classical
  unfold knownCount at h
  dsimp only at h
  split at h
  · rename_i test
    obtain ⟨rfl,cap⟩ := test
    cases h
    exact SmoothQuarterTwoHeadWindow.complete_rank_answer D hn hB cap
  · split at h
    · rename_i test
      obtain ⟨rfl,lo,hi⟩ := test
      cases h
      exact SmoothCubicBudgetWindow.rank_answer D hn hB lo hi
    · split at h
      · rename_i test
        obtain ⟨hk,shape,low,bound,cap⟩ := test
        cases h
        exact SmoothTwoHeadProduction.rank_answer D hn hk shape low hB cap bound
      · contradiction

/-- Compute the 128-bit MCA boundary using integer windows first and the certified search
on the supplied coordinates and field otherwise. -/
def answer [DecidableEq I] (E : Fin n ≃ I) (labels : Unit → List F) (D : I ↪ F)
    (k q : ℕ) : Option ℕ :=
  let B := q / 2^128
  (knownCount k B).orElse fun _ => (RankExecutable.mcaBoundaryWith E labels D k B).map Fin.val

private theorem search_eq [DecidableEq I] [SampleableType F] {len : ℕ} (E : Fin len ≃ I)
    (hn : Fintype.card I = len) (labels : Unit → List F) (hl : ∀ x, x ∈ labels ())
    (D : I ↪ F) (k : ℕ) :
    (RankExecutable.mcaBoundaryWith E labels D k (Fintype.card F / 2^128)).map Fin.val =
      (RankReview.mcaAnswer D (prizeThreshold : ℝ≥0) k).map Fin.val := by
  subst len
  rw [← RankExecutable.prizeBudget F, RankExecutable.mcaBoundaryWith_eq E labels hl]

/-- The production evaluator returns the universal answer, including safety through radius one. -/
theorem answer_correct [DecidableEq I] [SampleableType F] (E : Fin n ≃ I)
    (labels : Unit → List F) (hl : ∀ x, x ∈ labels ()) (D : I ↪ F) [ReedSolomon.Smooth D]
    (k : ℕ) : answer E labels D k (Fintype.card F) =
      (RankReview.mcaAnswer D (prizeThreshold : ℝ≥0) k).map Fin.val := by
  classical
  have hn : Fintype.card I = n := (Fintype.card_congr E).symm.trans (Fintype.card_fin n)
  dsimp only [answer]
  cases h : knownCount k (Fintype.card F / 2^128) with
  | some e => exact (knownCount_correct D hn rfl h).symm
  | none => exact search_eq E hn labels hl D k

#print axioms knownCount_correct
#print axioms answer_correct
end ProximityPrize.SmoothProductionMcaExecutable
