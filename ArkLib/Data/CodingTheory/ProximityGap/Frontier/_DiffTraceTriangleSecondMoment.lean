/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTraceTrivialEnvelope
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTraceVarianceRouteCapstone

/-!
# CONSTRAINT — the original off-diagonal second moment has only the triangle corridor (#444)

This is the direct second-moment corollary of the variance-core triangle envelope.  The previous
files pin the exact identity

```
  offdiag₂.re = ‖Σ_T Jphase θ T‖² - #Rel.
```

Together with `0 ≤ ‖Σ Jphase‖² ≤ #Rel²`, this gives the unconditional corridor

```
  -#Rel ≤ offdiag₂.re ≤ #Rel² - #Rel.
```

The upper end is exactly the trivial/square slack already formalized for `DiffTrace`; this file
packages it on the ORIGINAL off-diagonal second-moment expression so downstream variance code can cite
one theorem without detouring through the named first-moment predicate.  No cancellation is proved.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.DiffTraceTriangleSecondMoment

open Finset ComplexConjugate
open ArkLib.ProximityGap.Frontier.NextDifferenceVariety
open ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloor
open ArkLib.ProximityGap.Frontier.DiffTraceTrivialEnvelope
open ArkLib.ProximityGap.Frontier.DiffTraceVarianceRouteCapstone

variable {R : Type*} [AddCommGroup R] {r : ℕ} {θ : R → ℂ} [DecidableEq (Fin r → R)]

/-- **`secondMoment_re_ge_neg_card`** — the original off-diagonal second moment has the same exact
Plancherel floor as `DiffTrace`: it cannot drop below `-#Rel`. -/
theorem secondMoment_re_ge_neg_card (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    -(Rel.card : ℝ) ≤
      (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re := by
  rw [secondMoment_re_eq_normSq_sub_card hmul hone hunit Rel]
  have hnonneg : 0 ≤ Complex.normSq (∑ T ∈ Rel, Jphase θ T) := Complex.normSq_nonneg _
  linarith

/-- **`secondMoment_re_le_card_sq_sub_card`** — direct original-second-moment form of the triangle
ceiling: the off-diagonal pair-correlation real part is at most `#Rel² - #Rel`.  This is only the
trivial square envelope, not the prize cancellation bound. -/
theorem secondMoment_re_le_card_sq_sub_card (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re
      ≤ (Rel.card : ℝ) ^ 2 - (Rel.card : ℝ) := by
  rw [secondMoment_re_eq_normSq_sub_card hmul hone hunit Rel]
  have h := linearPhase_normSq_le_card_sq (θ := θ) hunit Rel
  linarith

/-- **`secondMoment_triangle_corridor`** — the complete unconditional triangle corridor for the
original off-diagonal second moment:
`-#Rel ≤ offdiag₂.re ≤ #Rel² - #Rel`.  Any prize-relevant variance attack must replace the upper
endpoint by a genuine flatness/anti-concentration saving. -/
theorem secondMoment_triangle_corridor (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    -(Rel.card : ℝ) ≤
        (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re
      ∧ (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re
        ≤ (Rel.card : ℝ) ^ 2 - (Rel.card : ℝ) :=
  ⟨secondMoment_re_ge_neg_card hmul hone hunit Rel,
    secondMoment_re_le_card_sq_sub_card hmul hone hunit Rel⟩

end ArkLib.ProximityGap.Frontier.DiffTraceTriangleSecondMoment

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceTriangleSecondMoment.secondMoment_re_ge_neg_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceTriangleSecondMoment.secondMoment_re_le_card_sq_sub_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceTriangleSecondMoment.secondMoment_triangle_corridor
