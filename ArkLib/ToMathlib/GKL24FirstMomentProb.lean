/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.GKL24BadWitnessCard
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCount

/-!
# GKL24 first-moment MCA probability bound (#67)

The probability-form statement of the GKL24/GCXK25 first moment, obtained by combining the
count bound `mcaBad_card_le_of_weight` (`GKL24BadWitnessCard.lean`) with the exact probability
identity `Pr_γ[mcaEvent] = mcaBadCount / |F|` (`MCABadCount.lean`):

For `u₁` far from the zero codeword (`wt(u₁) > δ·n`) and any codeword cover `T`,

  **`Pr_{γ ← $F}[mcaEvent C δ u₀ u₁ γ] ≤ (|T| · wt(u₁) / (wt(u₁) - δ·n)) / |F|`.**

This is the paper's first-moment list-decoding estimate, now with its genuinely-mathematical core
(the per-codeword bad-witness cap, reconstructed from scratch via coordinate-injectivity) proven in
full — no residual.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap

open Finset
open scoped NNReal ENNReal ProbabilityTheory BigOperators

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The GKL24 first-moment MCA probability bound.**  For `u₁` far from `0` and a codeword cover
`T`, the MCA event probability over a uniform combining scalar is bounded by the first moment
`|T| · wt(u₁)/(wt(u₁) - δ·n)` divided by `|F|`. -/
theorem pr_mcaEvent_le_of_weight [NoZeroSMulDivisors F A]
    (C : Set (ι → A)) (δ : ℝ≥0) (hδ : δ ≤ 1) (u₀ u₁ : ι → A)
    (T : Finset (ι → A)) (hT : ∀ w ∈ C, w ∈ T)
    (hwt : (δ : ℝ) * Fintype.card ι < (supp₁ u₁).card) :
    Pr_{ let γ ←$ᵖ F }[ mcaEvent C δ u₀ u₁ γ ] ≤
      ENNReal.ofReal
          ((T.card : ℝ) * ((supp₁ u₁).card / ((supp₁ u₁).card - δ * Fintype.card ι)))
        / (Fintype.card F : ℝ≥0∞) := by
  classical
  -- Pr = mcaBadCount / |F|
  rw [pr_mcaEvent_eq_mcaBadCount_div C δ u₀ u₁]
  -- divide-by-|F| is monotone in the numerator
  refine ENNReal.div_le_div_right ?_ _
  -- (mcaBadCount : ℝ≥0∞) ≤ ofReal (first moment), since mcaBadCount = |mcaBad| and the real bound holds
  have hcount : (mcaBadCount (F := F) C δ u₀ u₁ : ℝ) ≤
      (T.card : ℝ) * ((supp₁ u₁).card / ((supp₁ u₁).card - δ * Fintype.card ι)) := by
    -- mcaBadCount = mcaBad.card definitionally
    have heq : (mcaBadCount (F := F) C δ u₀ u₁ : ℝ) = ((mcaBad (F := F) C δ u₀ u₁).card : ℝ) := rfl
    rw [heq]
    exact mcaBad_card_le_of_weight C δ hδ u₀ u₁ T hT hwt
  calc (mcaBadCount (F := F) C δ u₀ u₁ : ℝ≥0∞)
      = ENNReal.ofReal (mcaBadCount (F := F) C δ u₀ u₁ : ℝ) := by
        rw [ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal
          ((T.card : ℝ) * ((supp₁ u₁).card / ((supp₁ u₁).card - δ * Fintype.card ι))) :=
        ENNReal.ofReal_le_ofReal hcount

end ProximityGap
