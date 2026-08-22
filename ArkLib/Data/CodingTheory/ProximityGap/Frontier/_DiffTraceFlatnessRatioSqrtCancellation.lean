/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTraceFlatnessRatioRange

/-!
# CAPSTONE — the exact square-root-cancellation normalization of the flatness ratio (#444)

`_DiffTraceFlatnessRatio` introduced the dimensionless Door-(iv) variance-core ratio

`ρ_flat(Rel) = ‖Σ_T Jphase θ T‖² / #Rel`.

`_DiffTraceFlatnessRatioRange` pinned its global range `[0,#Rel]` and both extremes.  This file records
one more citable normalization rung: the square-root-cancellation / diagonal-floor target is EXACTLY
`ρ_flat ≤ 1`, with no hidden constants and no slack.

For nonempty `Rel`, dividing by `#Rel` gives the no-slack dictionary

* `ρ_flat ≤ 1` iff `‖Σ_T Jphase θ T‖² ≤ #Rel`;
* `ρ_flat < 1` iff `‖Σ_T Jphase θ T‖² < #Rel`;
* `ρ_flat = 1` iff `‖Σ_T Jphase θ T‖² = #Rel`.

This does NOT prove the left side.  It only names the exact square-root-cancellation target in the
Shaw-value/flatness normalization, so downstream Door-(iv) reductions can cite the diagonal-floor
threshold directly instead of redoing the algebra.  No CORE / cancellation / completion / moment-saving /
capacity claim is made.  #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioSqrtCancellation

open Finset ComplexConjugate
open ArkLib.ProximityGap.Frontier.NextDifferenceVariety
open ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatio

variable {R : Type*} [AddCommGroup R] {r : ℕ} {θ : R → ℂ} [DecidableEq (Fin r → R)]

/-- **`flatnessRatio_le_one_iff_normSq_le_card`** — the dimensionless square-root-cancellation target
`ρ_flat ≤ 1` is exactly the diagonal-floor norm-square budget `‖Σ Jphase‖² ≤ #Rel`. -/
theorem flatnessRatio_le_one_iff_normSq_le_card (Rel : Finset (Fin r → R))
    (hne : 0 < (Rel.card : ℝ)) :
    flatnessRatio θ Rel ≤ 1
      ↔ Complex.normSq (∑ T ∈ Rel, Jphase θ T) ≤ (Rel.card : ℝ) := by
  unfold flatnessRatio
  rw [div_le_iff₀ hne]
  ring_nf

/-- **`flatnessRatio_lt_one_iff_normSq_lt_card`** — the strict sub-diagonal form of the same
normalization: `ρ_flat < 1` iff `‖Σ Jphase‖² < #Rel`. -/
theorem flatnessRatio_lt_one_iff_normSq_lt_card (Rel : Finset (Fin r → R))
    (hne : 0 < (Rel.card : ℝ)) :
    flatnessRatio θ Rel < 1
      ↔ Complex.normSq (∑ T ∈ Rel, Jphase θ T) < (Rel.card : ℝ) := by
  unfold flatnessRatio
  rw [div_lt_iff₀ hne]
  ring_nf

/-- **`flatnessRatio_eq_one_iff_normSq_eq_card`** — the exact diagonal-floor equality form:
`ρ_flat = 1` iff `‖Σ Jphase‖² = #Rel`. -/
theorem flatnessRatio_eq_one_iff_normSq_eq_card (Rel : Finset (Fin r → R))
    (hne : 0 < (Rel.card : ℝ)) :
    flatnessRatio θ Rel = 1
      ↔ Complex.normSq (∑ T ∈ Rel, Jphase θ T) = (Rel.card : ℝ) := by
  unfold flatnessRatio
  rw [div_eq_iff (ne_of_gt hne)]
  ring_nf


/-! ## §2 Arbitrary threshold dictionary -/

/-- **`flatnessRatio_le_const_iff_normSq_le_const_mul_card`** — for any real threshold `C`, the
flatness-ratio budget `ρ_flat ≤ C` is exactly the raw aggregate norm-square budget
`‖Σ Jphase‖² ≤ C * #Rel`.  The square-root target above is the special case `C=1`. -/
theorem flatnessRatio_le_const_iff_normSq_le_const_mul_card (Rel : Finset (Fin r → R)) (C : ℝ)
    (hne : 0 < (Rel.card : ℝ)) :
    flatnessRatio θ Rel ≤ C
      ↔ Complex.normSq (∑ T ∈ Rel, Jphase θ T) ≤ C * (Rel.card : ℝ) := by
  unfold flatnessRatio
  rw [div_le_iff₀ hne]

/-- **`flatnessRatio_lt_const_iff_normSq_lt_const_mul_card`** — strict arbitrary-threshold form:
`ρ_flat < C` iff `‖Σ Jphase‖² < C * #Rel`. -/
theorem flatnessRatio_lt_const_iff_normSq_lt_const_mul_card (Rel : Finset (Fin r → R)) (C : ℝ)
    (hne : 0 < (Rel.card : ℝ)) :
    flatnessRatio θ Rel < C
      ↔ Complex.normSq (∑ T ∈ Rel, Jphase θ T) < C * (Rel.card : ℝ) := by
  unfold flatnessRatio
  rw [div_lt_iff₀ hne]

/-- **`flatnessRatio_eq_const_iff_normSq_eq_const_mul_card`** — equality arbitrary-threshold form:
`ρ_flat = C` iff `‖Σ Jphase‖² = C * #Rel`. -/
theorem flatnessRatio_eq_const_iff_normSq_eq_const_mul_card (Rel : Finset (Fin r → R)) (C : ℝ)
    (hne : 0 < (Rel.card : ℝ)) :
    flatnessRatio θ Rel = C
      ↔ Complex.normSq (∑ T ∈ Rel, Jphase θ T) = C * (Rel.card : ℝ) := by
  unfold flatnessRatio
  rw [div_eq_iff (ne_of_gt hne)]

/-- **`flatnessRatio_le_one_of_normSq_le_card`** — forward-facing consumer wrapper for certificates of
the diagonal-floor norm-square budget. -/
theorem flatnessRatio_le_one_of_normSq_le_card (Rel : Finset (Fin r → R))
    (hne : 0 < (Rel.card : ℝ))
    (h : Complex.normSq (∑ T ∈ Rel, Jphase θ T) ≤ (Rel.card : ℝ)) :
    flatnessRatio θ Rel ≤ 1 :=
  (flatnessRatio_le_one_iff_normSq_le_card Rel hne).2 h

/-- **`normSq_le_card_of_flatnessRatio_le_one`** — reverse-facing consumer wrapper: any proof of
`ρ_flat ≤ 1` has proved the diagonal-floor aggregate norm-square budget. -/
theorem normSq_le_card_of_flatnessRatio_le_one (Rel : Finset (Fin r → R))
    (hne : 0 < (Rel.card : ℝ)) (h : flatnessRatio θ Rel ≤ 1) :
    Complex.normSq (∑ T ∈ Rel, Jphase θ T) ≤ (Rel.card : ℝ) :=
  (flatnessRatio_le_one_iff_normSq_le_card Rel hne).1 h


/-! ## §3 Excess-over-diagonal prize slack -/

/-- **`flatnessExcess`** — the dimensionless excess of the flatness ratio above the diagonal
square-root-cancellation floor `1`.  The prize-scale target is `flatnessExcess = o(1)`. -/
noncomputable def flatnessExcess (θ : R → ℂ) (Rel : Finset (Fin r → R)) : ℝ :=
  flatnessRatio θ Rel - 1

/-- **`flatnessExcess_le_iff_normSq_le_one_add_mul_card`** — the exact excess-slack dictionary:
`ρ_flat - 1 ≤ ε` iff `‖Σ Jphase‖² ≤ (1+ε) * #Rel`. -/
theorem flatnessExcess_le_iff_normSq_le_one_add_mul_card (Rel : Finset (Fin r → R)) (ε : ℝ)
    (hne : 0 < (Rel.card : ℝ)) :
    flatnessExcess θ Rel ≤ ε
      ↔ Complex.normSq (∑ T ∈ Rel, Jphase θ T) ≤ (1 + ε) * (Rel.card : ℝ) := by
  unfold flatnessExcess flatnessRatio
  rw [sub_le_iff_le_add]
  rw [div_le_iff₀ hne]
  ring_nf

/-- **`flatnessExcess_lt_iff_normSq_lt_one_add_mul_card`** — strict excess-slack dictionary:
`ρ_flat - 1 < ε` iff `‖Σ Jphase‖² < (1+ε) * #Rel`. -/
theorem flatnessExcess_lt_iff_normSq_lt_one_add_mul_card (Rel : Finset (Fin r → R)) (ε : ℝ)
    (hne : 0 < (Rel.card : ℝ)) :
    flatnessExcess θ Rel < ε
      ↔ Complex.normSq (∑ T ∈ Rel, Jphase θ T) < (1 + ε) * (Rel.card : ℝ) := by
  unfold flatnessExcess flatnessRatio
  rw [sub_lt_iff_lt_add]
  rw [div_lt_iff₀ hne]
  ring_nf

/-- **`flatnessExcess_eq_iff_normSq_eq_one_add_mul_card`** — equality excess-slack dictionary:
`ρ_flat - 1 = ε` iff `‖Σ Jphase‖² = (1+ε) * #Rel`. -/
theorem flatnessExcess_eq_iff_normSq_eq_one_add_mul_card (Rel : Finset (Fin r → R)) (ε : ℝ)
    (hne : 0 < (Rel.card : ℝ)) :
    flatnessExcess θ Rel = ε
      ↔ Complex.normSq (∑ T ∈ Rel, Jphase θ T) = (1 + ε) * (Rel.card : ℝ) := by
  unfold flatnessExcess flatnessRatio
  rw [sub_eq_iff_eq_add]
  rw [div_eq_iff (ne_of_gt hne)]
  ring_nf

end ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioSqrtCancellation

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioSqrtCancellation.flatnessRatio_le_one_iff_normSq_le_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioSqrtCancellation.flatnessRatio_lt_one_iff_normSq_lt_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioSqrtCancellation.flatnessRatio_eq_one_iff_normSq_eq_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioSqrtCancellation.flatnessRatio_le_const_iff_normSq_le_const_mul_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioSqrtCancellation.flatnessRatio_lt_const_iff_normSq_lt_const_mul_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioSqrtCancellation.flatnessRatio_eq_const_iff_normSq_eq_const_mul_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioSqrtCancellation.flatnessRatio_le_one_of_normSq_le_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioSqrtCancellation.normSq_le_card_of_flatnessRatio_le_one
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioSqrtCancellation.flatnessExcess_le_iff_normSq_le_one_add_mul_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioSqrtCancellation.flatnessExcess_lt_iff_normSq_lt_one_add_mul_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioSqrtCancellation.flatnessExcess_eq_iff_normSq_eq_one_add_mul_card
