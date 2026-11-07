/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Research.ProximityPrize.Frontier._R24FullRungAssembly

/-!
# LANE DCOUNT (#466 round 25): direct class-count pipeline for order-d faces

Round 24 packaged the order-d Stepanov consumer through `DStepanovOutput`, an auxiliary-polynomial
existence interface.  Round 25's d = 4 multiplicity brick lands the stronger endpoint actually
needed by the fold: a per-class cardinality bound.  This file records the witness-free adapter.

If every nonzero class fiber of the triple-linear kernel has size at most `B` **at every tuple
arising from a nondegenerate quadruple of `G⁴`**, then the already proven fold estimate gives

`‖tripleSum‖ ≤ |T|·B − q + 3`

at those tuples.  Thus any direct per-fiber Stepanov count on the nondegenerate shapes can feed
`TripleLinearHasseC` immediately, without reconstructing the auxiliary polynomial witnesses.

**Correction (audit R-136, 2026-10-28).**  An earlier version required the class-fiber bound
for ALL `u, v, w`.  At the degenerate tuple `u = v = w = 0` the kernel is identically `1`, so
that universal bound forces `B ≥ q` and `|T| ≥ 2`, hence `C√q ≥ q + 3`
(`universal_classCount_forces_large`, `universal_classCount_not_two`): no fixed small
constant (in particular not `C = 2`) could ever be fed.  The class-fiber hypothesis is now
guarded by exactly the tuple family and nondegeneracy condition consumed by
`TripleLinearHasseC`; degenerate tuples are left to the separately accounted trivial layer.
The order-4 face in `_R26D4Mirror.lean` (`d4_class_count`, guarded by the three degeneracy
clauses) is a per-class count of exactly this guarded shape.
-/

set_option autoImplicit false
set_option linter.unusedDecidableInType false

open Finset

namespace ArkLib.ProximityGap.Frontier.R25DirectClassCountPipeline

open ArkLib.ProximityGap.Frontier.R18FourthMomentTwist (IsDegenerate)
open ArkLib.ProximityGap.Frontier.R21HigherDFaces
open ArkLib.ProximityGap.Frontier.R24FullRungAssembly

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The universal class-count socket is impossible at small constants (audit R-136).**  If the
class-fiber bound `B` held at EVERY tuple, the degenerate tuple `u = v = w = 0` (constant kernel
`1`) would force `1 ∈ T`, `B ≥ q` and `|T| ≥ 2`, so the fold expression is at least `q + 3`. -/
theorem universal_classCount_forces_large
    (χ : MulChar F ℂ) (T : Finset ℂ) {B : ℝ}
    (hT0 : (∑ c ∈ T, c) = 0)
    (hvals : ∀ u v w s : F, tripleVal χ u v w s = 0 ∨ tripleVal χ u v w s ∈ T)
    (hB : ∀ u v w : F, ∀ c ∈ T,
      (((Finset.univ.filter fun s : F => tripleVal χ u v w s = c).card : ℝ)) ≤ B) :
    (Fintype.card F : ℝ) + 3 ≤ (T.card : ℝ) * B - (Fintype.card F : ℝ) + 3 := by
  have h1T : (1 : ℂ) ∈ T := by
    rcases hvals 0 0 0 0 with h | h
    · rw [tripleVal_zero_zero_zero] at h
      exact absurd h one_ne_zero
    · rwa [tripleVal_zero_zero_zero] at h
  have hfib : (Finset.univ.filter fun s : F => tripleVal χ 0 0 0 s = 1) = Finset.univ :=
    Finset.filter_true_of_mem fun s _ => tripleVal_zero_zero_zero χ s
  have hqB : (Fintype.card F : ℝ) ≤ B := by
    have := hB 0 0 0 1 h1T
    rwa [hfib, Finset.card_univ] at this
  have hcard2 : 2 ≤ T.card := by
    by_contra hlt
    have hle : T.card ≤ 1 := by omega
    have hT : T = {1} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      exact ⟨h1T, fun x hx => Finset.card_le_one.mp hle x hx 1 h1T⟩
    rw [hT, Finset.sum_singleton] at hT0
    exact one_ne_zero hT0
  have hcard2R : (2 : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hcard2
  have hq0 : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  nlinarith

/-- Consequently the universal socket can never be fed at the sharp constant `C = 2`
(indeed `q + 3 > 2√q` for every `q`). -/
theorem universal_classCount_not_two
    (χ : MulChar F ℂ) (T : Finset ℂ) {B : ℝ}
    (hT0 : (∑ c ∈ T, c) = 0)
    (hvals : ∀ u v w s : F, tripleVal χ u v w s = 0 ∨ tripleVal χ u v w s ∈ T)
    (hB : ∀ u v w : F, ∀ c ∈ T,
      (((Finset.univ.filter fun s : F => tripleVal χ u v w s = c).card : ℝ)) ≤ B) :
    ¬ ((T.card : ℝ) * B - (Fintype.card F : ℝ) + 3 ≤ 2 * Real.sqrt (Fintype.card F)) := by
  intro h
  have hlow := universal_classCount_forces_large χ T hT0 hvals hB
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (Fintype.card F : ℝ))
  nlinarith [sq_nonneg (Real.sqrt (Fintype.card F) - 1)]

/-- **Direct per-class-count consumer (guarded).**  A class-value set `T` with unit values
summing to zero, kernel values in `{0} ∪ T`, and a class-fiber cardinality bound `B` at every
tuple `(y₂−x₁, y₂−x₂, y₂−y₁)` of a NONdegenerate quadruple `z ∈ G⁴` gives the triple-linear
Hasse bound with any constant `C` satisfying the displayed fold arithmetic.

This is the witness-free companion to `tripleLinearHasseC_of_dStepanovOutputOn`: use it when a
Stepanov lane has already discharged the cardinality estimate directly on the nondegenerate
shapes, as in the d = 4 quintic kernel face. -/
theorem tripleLinearHasseC_of_directClassCount
    (χ : MulChar F ℂ) (G : Finset F) (T : Finset ℂ) {B C : ℝ}
    (hT1 : ∀ c ∈ T, ‖c‖ = 1) (hT0 : (∑ c ∈ T, c) = 0)
    (hvals : ∀ u v w s : F, tripleVal χ u v w s = 0 ∨ tripleVal χ u v w s ∈ T)
    (hB : ∀ z ∈ (G ×ˢ G) ×ˢ (G ×ˢ G), ¬ IsDegenerate z → ∀ c ∈ T,
      (((Finset.univ.filter fun s : F =>
          tripleVal χ (z.2.2 - z.1.1) (z.2.2 - z.1.2) (z.2.2 - z.2.1) s = c).card : ℝ)) ≤ B)
    (harith : (T.card : ℝ) * B - (Fintype.card F : ℝ) + 3
      ≤ C * Real.sqrt (Fintype.card F)) :
    TripleLinearHasseC χ G C := by
  intro z hz hnd
  have hBz := hB z hz hnd
  obtain ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ := z
  set u : F := b₂ - a₁
  set v : F := b₂ - a₂
  set w : F := b₂ - b₁
  have hfold := class_fold_bound (val := fun s => tripleVal χ u v w s) T hT1 hT0
    (fun s => hvals u v w s) hBz (tripleVal_zero_fiber_card_le_three χ u v w)
  calc ‖tripleSum χ u v w‖
      = ‖∑ s : F, tripleVal χ u v w s‖ := by rw [tripleSum_eq_sum_tripleVal]
    _ ≤ (T.card : ℝ) * B - (Fintype.card F : ℝ) + 3 := hfold
    _ ≤ C * Real.sqrt (Fintype.card F) := harith

/-- Family form of the direct per-class-count consumer, matching the round-24 pipeline's
`FourthMomentTwistBound` output.  The only order-d data required for each character is the direct
class-count bound on the nondegenerate shapes of `G⁴` and the same fold arithmetic. -/
theorem fourthMomentTwistBound_of_directClassCount_family
    (G : Finset F) (X : Finset (MulChar F ℂ))
    (T : MulChar F ℂ → Finset ℂ) (B Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (hT1 : ∀ χ ∈ X, ∀ c ∈ T χ, ‖c‖ = 1)
    (hT0 : ∀ χ ∈ X, (∑ c ∈ T χ, c) = 0)
    (hvals : ∀ χ ∈ X, ∀ u v w s : F,
      tripleVal χ u v w s = 0 ∨ tripleVal χ u v w s ∈ T χ)
    (hB : ∀ χ ∈ X, ∀ z ∈ (G ×ˢ G) ×ˢ (G ×ˢ G), ¬ IsDegenerate z → ∀ c ∈ T χ,
      (((Finset.univ.filter fun s : F =>
          tripleVal χ (z.2.2 - z.1.1) (z.2.2 - z.1.2) (z.2.2 - z.2.1) s = c).card : ℝ)) ≤ B χ)
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
#print axioms universal_classCount_forces_large
#print axioms universal_classCount_not_two
