/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.FourRateSmoothMca128
import ArkLib.Research.ProximityGap.Frontier.SharpApolarMCA
import ArkLib.Research.ProximityGap.RankExecutable

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

/-- The two nonzero points in the field with three elements. -/
private def orderTwo : Fin 2 ↪ ZMod 3 where
  toFun i := if i = 0 then 1 else 2
  inj' := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> revert hab <;> decide

/- At budget one the repetition code has MCA safety throughout and its list first fails
at one error. The two further tests exercise failure at zero and safety at every count. -/
run_cmd do
  let mca := RankExecutable.mcaBoundary (Equiv.refl (Fin 2)) [0, 1, 2] orderTwo 1 1
  let list (budget : ℕ) := (RankExecutable.listBoundary [0, 1] orderTwo 2 1 3 1 budget).map Fin.val
  unless mca.isNone do throwError "The repetition-code MCA evaluator failed the all-safe case"
  unless list 1 == some 1 do throwError "The budget-one list must first fail at one error"
  unless list 0 == some 0 do throwError "The zero-budget list must fail at zero errors"
  unless (list 3).isNone do throwError "The full-field list budget must pass every radius"

/-- All three sites over the field of order three. -/
private def threeSites : Fin 3 ↪ ZMod 3 where
  toFun := ![0, 1, 2]
  inj' := by decide

/- At one error the repetition code has three bad scalars. This exercises the fixed
labels and a free third label, as well as the separate singleton case. -/
run_cmd do
  let mca (budget : ℕ) :=
    (RankExecutable.scan 3 fun e => SimultaneousSupportGaussian.anchoredSafe
      (Equiv.refl (Fin 3)) [0, 1, 2] threeSites 1 budget (3-e.val)).map Fin.val
  unless mca 2 == some 1 do
    throwError "At budget two, the three-site MCA test should first fail at one error."
  unless mca 0 == some 0 do
    throwError "At budget zero, the three-site MCA test should fail at zero errors."

/-- The order-four subgroup of the field of order five. -/
private def orderFour : Fin 4 ↪ ZMod 5 where
  toFun := ![1, 2, 4, 3]
  inj' := by decide

/- The one-error jump has four bad labels and saturates the probability curve. -/
run_cmd do
  let boundary (budget : ℕ) :=
    (RankExecutable.mcaBoundary (Equiv.refl (Fin 4)) [0, 1, 2, 3, 4] orderFour 2 budget).map Fin.val
  unless boundary 0 == some 0 do throwError "The four-site code fails at zero errors for budget zero"
  unless boundary 3 == some 1 do throwError "The four-site code fails at one error for budget three"
  unless (boundary 4).isNone do throwError "The four-site code is safe at every radius for budget four"

/- The numerical certificates reach the published 246-bit code without enumerating the field.
At length eight, the budgets distinguish both interpolation cutoffs and the fallback. -/
run_cmd do
  let q := 65 * 2 ^ 239 + 1
  let B := q / 2 ^ 128
  for (k, firstBad) in [(32, 97), (16, 113), (8, 121)] do
    unless RankExecutable.circuitsCovered 128 k B &&
        (RankExecutable.packingBoundary 128 k q 1 B).map Fin.val == some firstBad do
      throwError "The numerical certificates disagree with the length-128 prize table"
  let small (B : ℕ) := (RankExecutable.packingBoundary 8 2 59 1 B).map Fin.val
  unless [small 8, small 9, small 28] == [none, some 6, some 7] do
    throwError "The list packing threshold was evaluated at the wrong budget"
  unless !RankExecutable.circuitsCovered 8 2 55 && RankExecutable.circuitsCovered 8 2 56 do
    throwError "The circuit bound must include equality"
  unless !RankExecutable.circuitsCovered (2 ^ 30) (2 ^ 29) (2 ^ 30) do
    throwError "The production circuit count exceeds this budget"

end ProximityPrize.Review
