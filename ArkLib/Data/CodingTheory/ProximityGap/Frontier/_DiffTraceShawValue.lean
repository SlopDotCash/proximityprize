/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTraceFlatnessRatio

/-!
# EXTEND — the Shaw value attached to the variance-route flatness ratio (#444)

The previous capstone normalized the door-(iv) variance route to the dimensionless flatness ratio

`ρ_flat(Rel) = ‖Σ_T Jphase θ T‖² / #Rel`.

This file packages the square-root normalization, the **Shaw value**

`Sh(Rel) = sqrt(ρ_flat(Rel)) = ‖Σ_T Jphase θ T‖ / sqrt(#Rel)`

at the level needed for a citable reduction chain: bounding the off-diagonal second moment is
*equivalent* to bounding `Sh(Rel)^2` by `1 + S/#Rel`.  Thus the prize-side slack is exactly the excess
of the aggregate Jacobi-phase Shaw value over the orthonormal floor `1`.

NO CORE / cancellation / completion / moment-saving / capacity claim: this is only a normalization and
an iff with the already-open variance-core bound.  The missing analytic content remains the flatness
inequality itself.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.DiffTraceShawValue

open Finset ComplexConjugate
open ArkLib.ProximityGap.Frontier.NextDifferenceVariety
open ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatio

variable {R : Type*} [AddCommGroup R] {r : ℕ} {θ : R → ℂ} [DecidableEq (Fin r → R)]

/-- **`shawValue`** — the square-root-normalized dimensionless aggregate phase value:
`Sh(Rel) = sqrt(ρ_flat(Rel))`.  The prize form asks for `Sh(Rel)^2 ≤ 1 + o(1)`, equivalently
`Sh(Rel) ≤ 1 + o(1)` after a harmless square-root normalization. -/
noncomputable def shawValue (θ : R → ℂ) (Rel : Finset (Fin r → R)) : ℝ :=
  Real.sqrt (flatnessRatio θ Rel)

/-- **`shawValue_nonneg`** — the Shaw value is nonnegative by definition. -/
theorem shawValue_nonneg (Rel : Finset (Fin r → R)) :
    0 ≤ shawValue θ Rel := by
  unfold shawValue
  exact Real.sqrt_nonneg _

/-- **`shawValue_sq_eq_flatnessRatio`** — the Shaw value is exactly the square root of the flatness
ratio, with no loss: `Sh(Rel)^2 = ρ_flat(Rel)`. -/
theorem shawValue_sq_eq_flatnessRatio (Rel : Finset (Fin r → R)) :
    (shawValue θ Rel) ^ 2 = flatnessRatio θ Rel := by
  unfold shawValue
  rw [Real.sq_sqrt (flatnessRatio_nonneg Rel)]


/-- **`shawValue_eq_norm_div_sqrt_card`** — the literal aggregate-normalized form promised by the
notation: for nonempty `Rel`, `Sh(Rel) = ‖Σ_T Jphase θ T‖ / sqrt(#Rel)`.  This exposes the Shaw value
as the normalized size of the single aggregate phase sum, not a new analytic estimate. -/
theorem shawValue_eq_norm_div_sqrt_card (Rel : Finset (Fin r → R)) :
    shawValue θ Rel = ‖(∑ T ∈ Rel, Jphase θ T)‖ / Real.sqrt (Rel.card : ℝ) := by
  unfold shawValue flatnessRatio
  rw [Complex.normSq_eq_norm_sq]
  rw [Real.sqrt_div (sq_nonneg ‖(∑ T ∈ Rel, Jphase θ T)‖)]
  rw [Real.sqrt_sq_eq_abs]
  rw [abs_of_nonneg (norm_nonneg _)]

/-- **`shawValue_sq_le_of_secondMoment_le`** — a variance-core off-diagonal second-moment bound gives
the Shaw-value squared bound `Sh(Rel)^2 ≤ 1 + S/#Rel`.  This is the same open flatness estimate in the
square-root normalization. -/
theorem shawValue_sq_le_of_secondMoment_le (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ)
    (hne : 0 < (Rel.card : ℝ))
    (h : (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re ≤ S) :
    (shawValue θ Rel) ^ 2 ≤ 1 + S / (Rel.card : ℝ) := by
  rw [shawValue_sq_eq_flatnessRatio]
  exact flatnessRatio_le_of_secondMoment_le hmul hone hunit Rel S hne h

/-- **`shawValue_sq_le_iff_secondMoment_le`** — the citable Shaw-value equivalence: for nonempty
`Rel`, bounding `Sh(Rel)^2` by `1 + S/#Rel` is EXACTLY the variance-core off-diagonal second-moment
bound.  This is the kernel-checked form of the reduction to a single Shaw-value flatness statement. -/
theorem shawValue_sq_le_iff_secondMoment_le (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ)
    (hne : 0 < (Rel.card : ℝ)) :
    (shawValue θ Rel) ^ 2 ≤ 1 + S / (Rel.card : ℝ)
      ↔ (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re ≤ S := by
  rw [shawValue_sq_eq_flatnessRatio]
  exact flatnessRatio_le_iff_secondMoment_le hmul hone hunit Rel S hne


/-- **`shawValue_le_sqrt_of_secondMoment_le`** — the linear Shaw-value form: if the normalized
right side is nonnegative, the same variance-core bound gives `Sh(Rel) ≤ sqrt(1 + S/#Rel)`. -/
theorem shawValue_le_sqrt_of_secondMoment_le (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ)
    (hne : 0 < (Rel.card : ℝ)) (hrhs : 0 ≤ 1 + S / (Rel.card : ℝ))
    (h : (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re ≤ S) :
    shawValue θ Rel ≤ Real.sqrt (1 + S / (Rel.card : ℝ)) := by
  unfold shawValue
  rw [Real.sqrt_le_sqrt_iff hrhs]
  exact flatnessRatio_le_of_secondMoment_le hmul hone hunit Rel S hne h

/-- **`shawValue_le_sqrt_iff_secondMoment_le`** — the fully linear citable form of the Shaw-value
capstone: for nonempty `Rel` and nonnegative normalized budget, `Sh(Rel) ≤ sqrt(1 + S/#Rel)` is EXACTLY
the variance-core off-diagonal second-moment bound. -/
theorem shawValue_le_sqrt_iff_secondMoment_le (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ)
    (hne : 0 < (Rel.card : ℝ)) (hrhs : 0 ≤ 1 + S / (Rel.card : ℝ)) :
    shawValue θ Rel ≤ Real.sqrt (1 + S / (Rel.card : ℝ))
      ↔ (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re ≤ S := by
  unfold shawValue
  rw [Real.sqrt_le_sqrt_iff hrhs]
  exact flatnessRatio_le_iff_secondMoment_le hmul hone hunit Rel S hne

end ArkLib.ProximityGap.Frontier.DiffTraceShawValue

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceShawValue.shawValue_nonneg
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceShawValue.shawValue_sq_eq_flatnessRatio
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceShawValue.shawValue_eq_norm_div_sqrt_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceShawValue.shawValue_sq_le_of_secondMoment_le
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceShawValue.shawValue_sq_le_iff_secondMoment_le
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceShawValue.shawValue_le_sqrt_of_secondMoment_le
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceShawValue.shawValue_le_sqrt_iff_secondMoment_le
