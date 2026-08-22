/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTraceVarianceRouteCapstone

/-!
# EXTEND — the dimensionless L²-flatness ratio `‖Σ Jphase‖² / #Rel` of the variance route (#444)

**Frontier-movement extension of `_DiffTraceVarianceRouteCapstone`.**  The capstone reduced the
variance route (slack-free) to `‖Σ_T Jphase θ T‖² ≤ #Rel + S`.  In the prize regime the slack `S`
must be sub-Poisson, `S = o(#Rel)`, so the right normalization is the **dimensionless flatness
ratio**
```
        ρ_flat(Rel)  :=  ‖Σ_T Jphase θ T‖² / #Rel.
```
This file pins that ratio's exact relationship to the variance-core slack: `ρ_flat ≤ 1 + S/#Rel`,
i.e. the prize is exactly the statement that the `#Rel` iterated Jacobi phases sum with the aggregate
L²-mass at the orthonormal floor `#Rel` up to a `1 + o(1)` factor (square-root cancellation in the
aggregate phase).

## The mechanism

For nonempty `Rel` (`#Rel > 0`), dividing the capstone bound `‖Σ Jphase‖² ≤ #Rel + S` by `#Rel`:
```
        ρ_flat(Rel) = ‖Σ Jphase‖²/#Rel  ≤  1 + S/#Rel.
```
And from the Plancherel floor (`fullTrace_re_nonneg`), `ρ_flat ≥ 0` always.  So `ρ_flat ∈ [0, ?]` and
the prize is `ρ_flat ≤ 1 + o(1)`.  The "diagonal main term" `#Rel` becomes the dimensionless `1`; the
entire prize content is the `S/#Rel → 0` excess over the orthonormal floor.

## What this file PROVES (axiom-clean, no `sorry`)

* `flatnessRatio` — the dimensionless ratio `‖Σ Jphase‖² / #Rel`;
* `flatnessRatio_nonneg` — `0 ≤ ρ_flat` (Plancherel non-negativity);
* `flatnessRatio_le_of_secondMoment_le` — `(off-diag 2nd moment).re ≤ S` (#Rel > 0) ⟹
  `ρ_flat ≤ 1 + S/#Rel`;
* `flatnessRatio_le_iff_secondMoment_le` — the iff: for `#Rel > 0`, `ρ_flat ≤ 1 + S/#Rel` ⟺ the
  variance-core bound `(off-diag 2nd moment).re ≤ S`.

NO CORE / cancellation / completion / moment-saving / capacity claim: the flatness inequality is NOT
proved.  This is the dimensionless normalization of the variance-route open core — the prize as
"aggregate Jacobi-phase L²-mass at the orthonormal floor up to `1+o(1)`".  #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatio

open Finset ComplexConjugate
open ArkLib.ProximityGap.Frontier.NextDifferenceVariety
open ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloor
open ArkLib.ProximityGap.Frontier.DiffTraceVarianceRouteCapstone

variable {R : Type*} [AddCommGroup R] {r : ℕ} {θ : R → ℂ} [DecidableEq (Fin r → R)]

/-- **`flatnessRatio`** — the dimensionless L²-flatness ratio of the aggregate iterated Jacobi phase:
`‖Σ_T Jphase θ T‖² / #Rel`.  The prize regime asks this be `≤ 1 + o(1)` (the orthonormal floor). -/
noncomputable def flatnessRatio (θ : R → ℂ) (Rel : Finset (Fin r → R)) : ℝ :=
  Complex.normSq (∑ T ∈ Rel, Jphase θ T) / (Rel.card : ℝ)

/-- **`flatnessRatio_nonneg`** — the flatness ratio is non-negative (Plancherel: the numerator is a
squared modulus, the denominator a cardinality). -/
theorem flatnessRatio_nonneg (Rel : Finset (Fin r → R)) :
    0 ≤ flatnessRatio θ Rel := by
  unfold flatnessRatio
  exact div_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

/-- **`flatnessRatio_le_of_secondMoment_le`** — for nonempty `Rel`, the variance-core off-diagonal
second-moment bound `(off-diag 2nd moment).re ≤ S` gives `ρ_flat ≤ 1 + S/#Rel`.  Via the exact
characterization `secondMoment_re_eq_normSq_sub_card` and dividing by `#Rel > 0`. -/
theorem flatnessRatio_le_of_secondMoment_le (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ)
    (hne : 0 < (Rel.card : ℝ))
    (h : (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re ≤ S) :
    flatnessRatio θ Rel ≤ 1 + S / (Rel.card : ℝ) := by
  unfold flatnessRatio
  rw [secondMoment_re_eq_normSq_sub_card hmul hone hunit Rel] at h
  rw [div_le_iff₀ hne, add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hne)]
  linarith

/-- **`flatnessRatio_le_iff_secondMoment_le`** — the iff: for nonempty `Rel`, `ρ_flat ≤ 1 + S/#Rel`
is EXACTLY the variance-core off-diagonal second-moment bound `(off-diag 2nd moment).re ≤ S`. -/
theorem flatnessRatio_le_iff_secondMoment_le (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ)
    (hne : 0 < (Rel.card : ℝ)) :
    flatnessRatio θ Rel ≤ 1 + S / (Rel.card : ℝ)
      ↔ (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re ≤ S := by
  unfold flatnessRatio
  rw [secondMoment_re_eq_normSq_sub_card hmul hone hunit Rel]
  rw [div_le_iff₀ hne, add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hne)]
  constructor <;> intro h <;> linarith

end ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatio

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatio.flatnessRatio_nonneg
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatio.flatnessRatio_le_of_secondMoment_le
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatio.flatnessRatio_le_iff_secondMoment_le
