/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAStaircaseRS
import ArkLib.Data.CodingTheory.ProximityGap.UniversalStaircaseCollapse
import ArkLib.Research.ProximityGap.Frontier.FourRateSmoothMca128

/-!
# The two-error MCA boundary on arbitrary Reed–Solomon domains

When three errors fit strictly below the minimum distance, at most two bad
scalars occur below two errors. At two errors the three-spike construction
already exceeds a budget of two scalars. This gives the same strict crossing
at every positive interleaving width and at all four rates of a smooth domain
of length sixteen.
-/

namespace ProximityGap.BudgetTwoMcaBoundary

open Code CoreDefinitions GrandChallenges
open scoped NNReal ENNReal

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
  [Field F] [Fintype F] [DecidableEq F]

/-- All radii and all dimensions with minimum distance at least four.
The two bounds on the threshold express exactly a budget of two field elements. -/
theorem good_iff (D : I ↪ F) {k : ℕ} (room : k + 3 ≤ Fintype.card I)
    {ε : ℝ≥0∞} (safe : 2 / (Fintype.card F : ℝ≥0∞) ≤ ε)
    (overBudget : ε < 3 / (Fintype.card F : ℝ≥0∞)) (δ : ℝ≥0) :
    epsMCA (F := F) (ReedSolomon.code D k : Set (I → F)) δ ≤ ε ↔
      δ < gridPt (ι := I) 2 := by
  classical
  have dist : SpikeFloor.NoWeightLE (ReedSolomon.code D k) 3 :=
    MCAStaircaseRS.rs_noWeightLE D room
  have positive : 0 < (Fintype.card I : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  have three : 3 ≤ Fintype.card I := by omega
  constructor
  · intro good
    by_contra! crossed
    have hδ : (2 : ℝ≥0) ≤ δ * Fintype.card I := (div_le_iff₀ positive).mp crossed
    obtain ⟨pos⟩ : Nonempty (Fin 3 ↪ I) :=
      Function.Embedding.nonempty_of_card_le (by simpa using three)
    have lower := SpikeFloor.epsMCA_ge_j_div_card (ReedSolomon.code D k) dist
      (δ := δ) (by simpa using hδ) (by decide) three pos (pos.trans D) (b := 1) one_ne_zero
    exact (not_lt_of_ge (lower.trans good)) overBudget
  · intro below
    have hδ : δ * Fintype.card I < (2 : ℝ≥0) := (lt_div_iff₀ positive).mp below
    exact (SpikeFloor.epsMCA_le_j_div_card (j := 2) (ReedSolomon.code D k) dist hδ).trans safe

/-- The cutoff in the unrounded canonical affine-line error, at 128-bit security. -/
theorem canonical_good_iff [SampleableType F] (D : I ↪ F) {k : ℕ}
    (room : k + 3 ≤ Fintype.card I) (budget : Fintype.card F / 2^128 = 2) (δ : ℝ≥0) :
    mcaError (AffineLineGenerator F) (ReedSolomon.code D k) (δ : ℝ) ≤
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ↔ δ < gridPt (ι := I) 2 := by
  rw [← epsMCA_eq_mcaError]
  have band := FourRateSmoothMca128.prize_band (Fintype.card F) Fintype.card_pos
  rw [budget] at band
  exact good_iff D room band.1 band.2 δ

/-- Every positive interleaving width has the same open safe-radius interval. -/
theorem interleaved_good_iff (D : I ↪ F) {k : ℕ} (room : k + 3 ≤ Fintype.card I)
    (budget : Fintype.card F / 2^128 = 2) (m : ℕ) [NeZero m] (δ : ℝ≥0) :
    epsMCA (F := F) (A := Fin m → F)
      ((ReedSolomon.code D k : Set (I → F)) ^⋈ (Fin m)) δ ≤
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ↔ δ < gridPt (ι := I) 2 := by
  rw [epsMCA_interleaved_eq]
  have band := FourRateSmoothMca128.prize_band (Fintype.card F) Fintype.card_pos
  rw [budget] at band
  exact good_iff D room band.1 band.2 δ

/-- An adjacent-grid certificate with last safe error count one. -/
def resolution [SampleableType F] (D : I ↪ F) {k : ℕ} (room : k + 3 ≤ Fintype.card I)
    (budget : Fintype.card F / 2^128 = 2) :
    GrandMcaResolution (ReedSolomon.code D k) (prizeThreshold : ℝ≥0) where
  kStar := 1
  lt_card := by omega
  below := (canonical_good_iff D room budget _).2 (by
    unfold gridPt
    exact div_lt_div_of_pos_right (by norm_num) (by exact_mod_cast Fintype.card_pos))
  above := lt_of_not_ge fun bad =>
    (lt_irrefl (gridPt (ι := I) 2)) ((canonical_good_iff D room budget _).1 bad)

/-- On every admissible length-sixteen domain in the budget-two field window,
all four prize dimensions have last safe step one and first unsafe step two. -/
theorem mcaPrize_sixteen [SampleableType F] (D : I ↪ F) [ReedSolomon.Smooth D]
    (size : Fintype.card I = 16) (budget : Fintype.card F / 2^128 = 2) : mcaPrize D := by
  refine ⟨PrizeDomainAdmissible.of_smooth D (by omega), fun j => ?_⟩
  apply (resolution D (k := prizeDimension (ι := I) j) ?_ budget).to_challenge
  fin_cases j <;> norm_num [prizeDimension, prizeDenominator, size]

#print axioms good_iff
#print axioms canonical_good_iff
#print axioms interleaved_good_iff
#print axioms resolution
#print axioms mcaPrize_sixteen

end ProximityGap.BudgetTwoMcaBoundary
