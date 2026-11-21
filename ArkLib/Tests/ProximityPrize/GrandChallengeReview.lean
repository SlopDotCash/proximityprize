/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.FourRateSmoothMca128
import ArkLib.Research.ProximityGap.Frontier.SharpApolarMCA
import ArkLib.Research.ProximityGap.RankReview

/-! Compile-time review of numerical thresholds for affine-line MCA and worst-center lists. -/
set_option autoImplicit false

namespace ProximityPrize.Review
open ProximityGap ProximityGap.GrandChallenges Code
open scoped NNReal ENNReal

/-- The numerical list answers written independently of the library table. -/
theorem lists128 (j : Fin 4) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    (Lambda (interleavedCodeSet (κ := Fin m)
      (ReedSolomon.code FourRateListPrime246.domain
        (prizeDimension (ι := FourRateListPrime246.H) j) :
        Set (FourRateListPrime246.H → FourRateListPrime246.K))) δ : ENNReal) ≤
      ((prizeThreshold : ℝ≥0) : ENNReal) * Fintype.card FourRateListPrime246.K ↔
      δ < ((![63, 97, 113, 121] j : ℕ) : ℝ) / 128 :=
  FourRateListPrime246.list_threshold j m hm δ

/-- The MCA classification at every positive width, rate and nonnegative radius. -/
theorem mca128 (j : Fin 4) (m : ℕ) [NeZero m] (δ : ℝ≥0) :
    epsMCA (F := FourRateListPrime246.K) (A := Fin m → FourRateListPrime246.K)
        ((ReedSolomon.code FourRateListPrime246.domain
          (prizeDimension (ι := FourRateListPrime246.H) j) :
          Set (FourRateListPrime246.H → FourRateListPrime246.K)) ^⋈ (Fin m)) δ ≤
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ↔ j ≠ 0 ∨ δ < 62 / 128 :=
  FourRateSmoothMca128.interleaved_good_iff FourRateListPrime246.domain
    FourRateListPrime246.card_H FourRateSmoothMca128.prime246_window j m δ

open ArkLib.ProximityGap.Frontier

/-- The sharp half-rate window with the predecessor count discharged. -/
theorem halfRateWindow {p : ℕ} [Fact p.Prime] {g : ZMod p}
    (hg : orderOf g = 1073741824) (hlo : 268435458 ≤ p / 2 ^ 128) (hhi : p / 2 ^ 128 ≤ 536870913)
    (width : ℕ) [NeZero width] (δ : ℝ≥0) :
    epsMCA (F := ZMod p) (A := Fin width → ZMod p)
      ((RateHalfApolarThreshold.code g) ^⋈ (Fin width)) δ ≤ (epsStar : ℝ≥0∞) ↔ δ < 1 / 4 :=
  SharpApolarMCA.interleaved_good_iff hg hlo hhi width δ

/-- For a supplied smooth code, compare the two rank predictions directly with the
canonical security inequalities at any radius in the closed unit interval. -/
theorem allRadii {F ι : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    [Fintype ι] [Nonempty ι] (D : ι ↪ F) [ReedSolomon.Smooth D]
    (k m : ℕ) (hm : 0 < m) (ε δ : ℝ≥0) (hδ : δ ≤ 1)
    (hk : 2 * k = Fintype.card ι ∨ 4 * k = Fintype.card ι ∨
      8 * k = Fintype.card ι ∨ 16 * k = Fintype.card ι) :
    (CoreDefinitions.mcaError (CoreDefinitions.AffineLineGenerator F)
        (ReedSolomon.code D k) (δ : ℝ) ≤ (ε : ℝ≥0∞) ↔
      match RankReview.mcaAnswer D ε k with
      | none => True
      | some e => δ < (e.val : ℝ≥0) / Fintype.card ι) ∧
    ((Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (ι → F)))
        (δ : ℝ) : ℝ≥0∞) ≤ (ε : ℝ≥0∞) * Fintype.card F ↔
      match RankReview.listAnswer D ε k m with
      | none => True
      | some e => δ < (e.val : ℝ≥0) / Fintype.card ι) := by
  classical
  obtain ⟨mca, lists⟩ := RankReview.correctForEveryDomain D ε k hk
  constructor
  · cases h : RankReview.mcaAnswer D ε k <;> simpa only [h] using mca δ hδ
  · cases h : RankReview.listAnswer D ε k m <;> simpa only [h] using lists m hm δ hδ

end ProximityPrize.Review
