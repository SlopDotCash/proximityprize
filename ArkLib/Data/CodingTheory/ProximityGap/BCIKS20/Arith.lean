/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Bundle

/-!
# The closing-arithmetic plumbing for the per-pair numeric edge (#302)

Cast plumbing for `johnsonNumericBound_of_perPairFactorData`'s arithmetic side condition:
the `ℝ≥0∞` inequality follows from the plain real inequality
`(ℓ·max(T,n) : ℝ) ≤ johnsonBoundReal·|F|`, so the fleet's closing-arithmetic obligation is
a clean real-number statement at the GS budgets.

HONEST REGIME NOTE (recorded, not papered over): the in-tree `johnsonBoundReal` is the
[BCHKS25]-strength linear-in-`n` closed form, while the [Hab25]/[BCIKS20] dichotomy
threshold `T` is quadratic in `n` — so the inequality holds only in bounded-`n` regimes at
the Hab25 budgets, or after the [BCHKS25] `O(1)`-`D_Z` interpolant upgrade (per-factor
budgets, in-tree at `BCKHS25/Interpolation.lean`), or against a quadratic-form bound
threaded through the errStar-parametric WHIR keystone.

## References

* [Hab25] ePrint 2025/2110; [BCHKS25] ePrint 2025/2055.
-/

open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

namespace BCIKS20.Claim510Bundle

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **The arithmetic side condition from a plain real inequality**: if
`(B : ℝ) ≤ johnsonBoundReal·|F|` (with the bound nonnegative), then the `ℝ≥0∞` form
consumed by `johnsonNumericBound_of_perPairFactorData` holds. -/
theorem arith_of_real_le (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) (B : ℕ)
    (hpos : 0 ≤ johnsonBoundReal domain k η δ)
    (hreal : (B : ℝ) ≤ johnsonBoundReal domain k η δ * (Fintype.card F₀ : ℝ)) :
    ((B : ℕ) : ℝ≥0∞) / (Fintype.card F₀ : ℝ≥0∞)
      ≤ ENNReal.ofReal (johnsonBoundReal domain k η δ) := by
  have hFpos : (0 : ℝ) < (Fintype.card F₀ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [ENNReal.div_le_iff_le_mul]
  · calc ((B : ℕ) : ℝ≥0∞)
        = ENNReal.ofReal (B : ℝ) := by
          rw [ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (johnsonBoundReal domain k η δ * (Fintype.card F₀ : ℝ)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (johnsonBoundReal domain k η δ)
            * ENNReal.ofReal ((Fintype.card F₀ : ℝ)) := by
          rw [ENNReal.ofReal_mul hpos]
      _ = ENNReal.ofReal (johnsonBoundReal domain k η δ) * (Fintype.card F₀ : ℝ≥0∞) := by
          rw [ENNReal.ofReal_natCast]
  · left
    simp only [ne_eq, Nat.cast_eq_zero]
    exact Fintype.card_ne_zero
  · left
    exact ENNReal.natCast_ne_top _

/-- **The numeric edge from per-pair data + the real arithmetic**: the composition of
`johnsonNumericBound_of_perPairFactorData` with the cast plumbing — the fleet's remaining
obligations are `PerPairFactorData` per pair and ONE real inequality. -/
theorem johnsonNumericBound_of_perPairFactorData_real
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0)
    (hη : 0 < η) (hδ : InJohnsonRange domain k η δ) (ℓ T : ℕ)
    (hdata : ∀ u : Code.WordStack F₀ (Fin 2) ι₀,
      Nonempty (PerPairFactorData domain k δ u ℓ T))
    (hpos : 0 ≤ johnsonBoundReal domain k η δ)
    (hreal : ((ℓ * max T (Fintype.card ι₀) : ℕ) : ℝ)
      ≤ johnsonBoundReal domain k η δ * (Fintype.card F₀ : ℝ)) :
    CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.JohnsonNumericBound domain k η δ :=
  johnsonNumericBound_of_perPairFactorData domain k η δ hη hδ ℓ T hdata
    (arith_of_real_le domain k η δ _ hpos hreal)

end BCIKS20.Claim510Bundle

/-! ## Axiom audit -/
#print axioms BCIKS20.Claim510Bundle.arith_of_real_le
#print axioms BCIKS20.Claim510Bundle.johnsonNumericBound_of_perPairFactorData_real
