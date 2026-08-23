/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTraceFlatnessRatioSqrtCancellation

/-!
# EXTEND — the exact range and endpoints of flatness excess (#444)

`_DiffTraceFlatnessRatioSqrtCancellation` introduced the dimensionless excess above the diagonal
square-root-cancellation floor

`flatnessExcess(Rel) = flatnessRatio(Rel) - 1`.

This file records the no-slack endpoint dictionary for that normalization.  Since the ratio lies in
`[0,#Rel]`, the excess lies in `[-1,#Rel-1]`.  The bottom endpoint is perfect cancellation of the
aggregate Jacobi phase sum, while the top endpoint is perfect coherence.  The zero threshold is exactly
square-root cancellation:

* `flatnessExcess ≤ 0` iff `flatnessRatio ≤ 1`;
* `-1 ≤ flatnessExcess ≤ #Rel-1`;
* `flatnessExcess = -1` iff `Σ_T Jphase θ T = 0`;
* `flatnessExcess = #Rel-1` iff `‖Σ_T Jphase θ T‖ = #Rel`.

No CORE / cancellation / completion / moment-saving / capacity claim is made.  These are normalization
and endpoint facts only; proving that the excess is `o(1)` is exactly the open Door-(iv) burden.  #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.DiffTraceFlatnessExcessRange

open Finset ComplexConjugate
open ArkLib.ProximityGap.Frontier.NextDifferenceVariety
open ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatio
open ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioRange
open ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioSqrtCancellation

variable {R : Type*} [AddCommGroup R] {r : ℕ} {θ : R → ℂ} [DecidableEq (Fin r → R)]

/-! ## §1 Zero threshold dictionary -/

/-- **`flatnessExcess_le_zero_iff_flatnessRatio_le_one`** — the excess is nonpositive exactly when the
flatness ratio is at the square-root-cancellation threshold `≤ 1`. -/
theorem flatnessExcess_le_zero_iff_flatnessRatio_le_one (Rel : Finset (Fin r → R)) :
    flatnessExcess θ Rel ≤ 0 ↔ flatnessRatio θ Rel ≤ 1 := by
  unfold flatnessExcess
  constructor <;> intro h <;> linarith

/-- **`flatnessExcess_lt_zero_iff_flatnessRatio_lt_one`** — strict sub-diagonal excess is exactly
`ρ_flat < 1`. -/
theorem flatnessExcess_lt_zero_iff_flatnessRatio_lt_one (Rel : Finset (Fin r → R)) :
    flatnessExcess θ Rel < 0 ↔ flatnessRatio θ Rel < 1 := by
  unfold flatnessExcess
  constructor <;> intro h <;> linarith

/-- **`flatnessExcess_eq_zero_iff_flatnessRatio_eq_one`** — zero excess is exactly diagonal-floor
flatness ratio `ρ_flat = 1`. -/
theorem flatnessExcess_eq_zero_iff_flatnessRatio_eq_one (Rel : Finset (Fin r → R)) :
    flatnessExcess θ Rel = 0 ↔ flatnessRatio θ Rel = 1 := by
  unfold flatnessExcess
  constructor <;> intro h <;> linarith

/-! ## §2 Global range and endpoint dictionary -/

/-- **`flatnessExcess_mem_range`** — for nonempty `Rel`, the excess lies in
`[-1, #Rel - 1]`, the shifted image of the flatness-ratio range `[0,#Rel]`. -/
theorem flatnessExcess_mem_range (hunit : ∀ s, Complex.normSq (θ s) = 1)
    (Rel : Finset (Fin r → R)) (hne : 0 < (Rel.card : ℝ)) :
    -1 ≤ flatnessExcess θ Rel ∧ flatnessExcess θ Rel ≤ (Rel.card : ℝ) - 1 := by
  rcases flatnessRatio_mem_range (θ := θ) hunit Rel hne with ⟨h0, htop⟩
  unfold flatnessExcess
  constructor <;> linarith

/-- **`flatnessExcess_eq_neg_one_iff_sum_eq_zero`** — the bottom endpoint `-1` is attained exactly
when the aggregate Jacobi phase sum perfectly cancels. -/
theorem flatnessExcess_eq_neg_one_iff_sum_eq_zero (Rel : Finset (Fin r → R))
    (hne : 0 < (Rel.card : ℝ)) :
    flatnessExcess θ Rel = -1 ↔ (∑ T ∈ Rel, Jphase θ T) = 0 := by
  constructor
  · intro h
    have hr : flatnessRatio θ Rel = 0 := by
      unfold flatnessExcess at h
      linarith
    exact (flatnessRatio_eq_zero_iff_sum_eq_zero (θ := θ) Rel hne).1 hr
  · intro h
    have hr : flatnessRatio θ Rel = 0 :=
      (flatnessRatio_eq_zero_iff_sum_eq_zero (θ := θ) Rel hne).2 h
    unfold flatnessExcess
    linarith

/-- **`flatnessExcess_eq_card_sub_one_iff_norm_eq_card`** — the top endpoint `#Rel - 1` is attained
exactly when the aggregate Jacobi phase sum is maximally coherent. -/
theorem flatnessExcess_eq_card_sub_one_iff_norm_eq_card (hunit : ∀ s, Complex.normSq (θ s) = 1)
    (Rel : Finset (Fin r → R)) (hne : 0 < (Rel.card : ℝ)) :
    flatnessExcess θ Rel = (Rel.card : ℝ) - 1
      ↔ ‖∑ T ∈ Rel, Jphase θ T‖ = (Rel.card : ℝ) := by
  constructor
  · intro h
    have hr : flatnessRatio θ Rel = (Rel.card : ℝ) := by
      unfold flatnessExcess at h
      linarith
    exact (flatnessRatio_eq_card_iff_norm_eq_card (θ := θ) hunit Rel hne).1 hr
  · intro h
    have hr : flatnessRatio θ Rel = (Rel.card : ℝ) :=
      (flatnessRatio_eq_card_iff_norm_eq_card (θ := θ) hunit Rel hne).2 h
    unfold flatnessExcess
    linarith

end ArkLib.ProximityGap.Frontier.DiffTraceFlatnessExcessRange

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessExcessRange.flatnessExcess_le_zero_iff_flatnessRatio_le_one
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessExcessRange.flatnessExcess_lt_zero_iff_flatnessRatio_lt_one
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessExcessRange.flatnessExcess_eq_zero_iff_flatnessRatio_eq_one
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessExcessRange.flatnessExcess_mem_range
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessExcessRange.flatnessExcess_eq_neg_one_iff_sum_eq_zero
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessExcessRange.flatnessExcess_eq_card_sub_one_iff_norm_eq_card
