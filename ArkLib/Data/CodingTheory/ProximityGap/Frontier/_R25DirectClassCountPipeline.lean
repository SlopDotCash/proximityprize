/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R24FullRungAssembly

/-!
# LANE DCOUNT (#466 round 25): direct class-count pipeline for order-d faces

Round 24 packaged the order-d Stepanov consumer through `DStepanovOutput`, an auxiliary-polynomial
existence interface.  Round 25's d = 4 multiplicity brick lands the stronger endpoint actually
needed by the fold: a per-class cardinality bound.  This file records the witness-free adapter.

If every nonzero class fiber of the triple-linear kernel has size at most `B`, then the already
proven fold estimate gives

`‖tripleSum‖ ≤ |T|·B − q + 3`.

Thus any direct per-fiber Stepanov count can feed `TripleLinearHasseC` immediately, without
reconstructing the auxiliary polynomial witnesses.
-/

set_option autoImplicit false
set_option linter.unusedDecidableInType false

open Finset

namespace ArkLib.ProximityGap.Frontier.R25DirectClassCountPipeline

open ArkLib.ProximityGap.Frontier.R21HigherDFaces
open ArkLib.ProximityGap.Frontier.R24FullRungAssembly

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Direct per-class-count consumer.**  A class-value set `T` with unit values summing to zero,
kernel values in `{0} ∪ T`, and a uniform class-fiber cardinality bound `B` gives the
triple-linear Hasse bound with any constant `C` satisfying the displayed fold arithmetic.

This is the witness-free companion to `tripleLinearHasseC_of_dStepanovOutput`: use it when a
Stepanov lane has already discharged the cardinality estimate directly, as in the d = 4 quintic
kernel face. -/
theorem tripleLinearHasseC_of_directClassCount
    (χ : MulChar F ℂ) (G : Finset F) (T : Finset ℂ) {B C : ℝ}
    (hT1 : ∀ c ∈ T, ‖c‖ = 1) (hT0 : (∑ c ∈ T, c) = 0)
    (hvals : ∀ u v w s : F, tripleVal χ u v w s = 0 ∨ tripleVal χ u v w s ∈ T)
    (hB : ∀ u v w : F, ∀ c ∈ T,
      (((Finset.univ.filter fun s : F => tripleVal χ u v w s = c).card : ℝ)) ≤ B)
    (harith : (T.card : ℝ) * B - (Fintype.card F : ℝ) + 3
      ≤ C * Real.sqrt (Fintype.card F)) :
    TripleLinearHasseC χ G C := by
  intro z _hz _hnd
  obtain ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ := z
  set u : F := b₂ - a₁
  set v : F := b₂ - a₂
  set w : F := b₂ - b₁
  have hfold := class_fold_bound (val := fun s => tripleVal χ u v w s) T hT1 hT0
    (fun s => hvals u v w s) (hB u v w) (tripleVal_zero_fiber_card_le_three χ u v w)
  calc ‖tripleSum χ u v w‖
      = ‖∑ s : F, tripleVal χ u v w s‖ := by rw [tripleSum_eq_sum_tripleVal]
    _ ≤ (T.card : ℝ) * B - (Fintype.card F : ℝ) + 3 := hfold
    _ ≤ C * Real.sqrt (Fintype.card F) := harith

/-- Family form of the direct per-class-count consumer, matching the round-24 pipeline's
`FourthMomentTwistBound` output.  The only order-d data required for each character is the direct
class-count bound and the same fold arithmetic. -/
theorem fourthMomentTwistBound_of_directClassCount_family
    (G : Finset F) (X : Finset (MulChar F ℂ))
    (T : MulChar F ℂ → Finset ℂ) (B Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (hT1 : ∀ χ ∈ X, ∀ c ∈ T χ, ‖c‖ = 1)
    (hT0 : ∀ χ ∈ X, (∑ c ∈ T χ, c) = 0)
    (hvals : ∀ χ ∈ X, ∀ u v w s : F,
      tripleVal χ u v w s = 0 ∨ tripleVal χ u v w s ∈ T χ)
    (hB : ∀ χ ∈ X, ∀ u v w : F, ∀ c ∈ T χ,
      (((Finset.univ.filter fun s : F => tripleVal χ u v w s = c).card : ℝ)) ≤ B χ)
    (harith : ∀ χ ∈ X,
      ((T χ).card : ℝ) * B χ - (Fintype.card F : ℝ) + 3
        ≤ Cd χ * Real.sqrt (Fintype.card F))
    (hCd0 : ∀ χ ∈ X, 0 ≤ Cd χ)
    (hCdmax : ∀ χ ∈ X, Cd χ ≤ Cmax)
    (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound
      G X (4 + Cmax) := by
  refine fourthMomentTwistBound_of_tripleLinearHasseC_family G X Cd hCd0 hCdmax
    (fun χ hχ => ?_) hp
  exact tripleLinearHasseC_of_directClassCount χ G (T χ) (hT1 χ hχ) (hT0 χ hχ)
    (hvals χ hχ) (hB χ hχ) (harith χ hχ)

end ArkLib.ProximityGap.Frontier.R25DirectClassCountPipeline

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.R25DirectClassCountPipeline

#print axioms tripleLinearHasseC_of_directClassCount
#print axioms fourthMomentTwistBound_of_directClassCount_family
