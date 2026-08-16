/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTraceFlatnessExcessRange

/-!
# CAPSTONE — flatness excess is the normalized off-diagonal second moment (#444)

`_DiffTraceFlatnessRatioSqrtCancellation` introduced

`flatnessExcess(Rel) = flatnessRatio(Rel) - 1`.

This file pins the exact variance-core meaning of that excess.  Under the standard unit-character
hypotheses, the off-diagonal second moment has real part

`secondMomentRe = ‖Σ_T Jphase θ T‖² - #Rel`.

Therefore, for nonempty `Rel`,

`flatnessExcess(Rel) = secondMomentRe / #Rel`.

Equivalently, a dimensionless excess budget `ε` is exactly the raw off-diagonal second-moment budget
`secondMomentRe ≤ ε * #Rel` (and likewise for `<` and `=`).  This is a no-slack normalization bridge,
not an estimate: proving `flatnessExcess = o(1)` is exactly proving the off-diagonal second moment is
`o(#Rel)`.

No CORE / cancellation / completion / moment-saving / capacity claim is made.  #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.DiffTraceFlatnessExcessSecondMoment

open Finset ComplexConjugate
open ArkLib.ProximityGap.Frontier.NextDifferenceVariety
open ArkLib.ProximityGap.Frontier.DiffTraceVarianceRouteCapstone
open ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatio
open ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioSqrtCancellation

variable {R : Type*} [AddCommGroup R] {r : ℕ} {θ : R → ℂ} [DecidableEq (Fin r → R)]

/-- **`flatnessExcess_eq_secondMomentRe_div_card`** — the flatness excess is exactly the normalized
real off-diagonal second moment: `(‖Σ Jphase‖²/#Rel - 1) = secondMomentRe/#Rel`. -/
theorem flatnessExcess_eq_secondMomentRe_div_card (hmul : ∀ a b, θ (a + b) = θ a * θ b)
    (hone : θ 0 = 1) (hunit : ∀ s, Complex.normSq (θ s) = 1)
    (Rel : Finset (Fin r → R)) (hne : 0 < (Rel.card : ℝ)) :
    flatnessExcess θ Rel =
      (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re /
        (Rel.card : ℝ) := by
  unfold flatnessExcess flatnessRatio
  rw [secondMoment_re_eq_normSq_sub_card hmul hone hunit Rel]
  field_simp [ne_of_gt hne]

/-- **`flatnessExcess_le_iff_secondMomentRe_le_mul`** — a dimensionless excess budget `ε` is exactly
the raw second-moment budget `secondMomentRe ≤ ε * #Rel`. -/
theorem flatnessExcess_le_iff_secondMomentRe_le_mul (hmul : ∀ a b, θ (a + b) = θ a * θ b)
    (hone : θ 0 = 1) (hunit : ∀ s, Complex.normSq (θ s) = 1)
    (Rel : Finset (Fin r → R)) (ε : ℝ) (hne : 0 < (Rel.card : ℝ)) :
    flatnessExcess θ Rel ≤ ε ↔
      (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re ≤
        ε * (Rel.card : ℝ) := by
  rw [flatnessExcess_eq_secondMomentRe_div_card hmul hone hunit Rel hne]
  rw [div_le_iff₀ hne]

/-- **`flatnessExcess_lt_iff_secondMomentRe_lt_mul`** — strict version of the normalized/raw
second-moment budget dictionary. -/
theorem flatnessExcess_lt_iff_secondMomentRe_lt_mul (hmul : ∀ a b, θ (a + b) = θ a * θ b)
    (hone : θ 0 = 1) (hunit : ∀ s, Complex.normSq (θ s) = 1)
    (Rel : Finset (Fin r → R)) (ε : ℝ) (hne : 0 < (Rel.card : ℝ)) :
    flatnessExcess θ Rel < ε ↔
      (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re <
        ε * (Rel.card : ℝ) := by
  rw [flatnessExcess_eq_secondMomentRe_div_card hmul hone hunit Rel hne]
  rw [div_lt_iff₀ hne]

/-- **`flatnessExcess_eq_iff_secondMomentRe_eq_mul`** — equality version of the normalized/raw
second-moment budget dictionary. -/
theorem flatnessExcess_eq_iff_secondMomentRe_eq_mul (hmul : ∀ a b, θ (a + b) = θ a * θ b)
    (hone : θ 0 = 1) (hunit : ∀ s, Complex.normSq (θ s) = 1)
    (Rel : Finset (Fin r → R)) (ε : ℝ) (hne : 0 < (Rel.card : ℝ)) :
    flatnessExcess θ Rel = ε ↔
      (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re =
        ε * (Rel.card : ℝ) := by
  rw [flatnessExcess_eq_secondMomentRe_div_card hmul hone hunit Rel hne]
  rw [div_eq_iff (ne_of_gt hne)]

/-! ## §2 Zero-threshold specialization -/

/-- **`flatnessExcess_le_zero_iff_secondMomentRe_nonpos`** — square-root/diagonal-floor cancellation
(`flatnessExcess ≤ 0`) is exactly nonpositive off-diagonal second moment. -/
theorem flatnessExcess_le_zero_iff_secondMomentRe_nonpos (hmul : ∀ a b, θ (a + b) = θ a * θ b)
    (hone : θ 0 = 1) (hunit : ∀ s, Complex.normSq (θ s) = 1)
    (Rel : Finset (Fin r → R)) (hne : 0 < (Rel.card : ℝ)) :
    flatnessExcess θ Rel ≤ 0 ↔
      (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re ≤ 0 := by
  simpa using flatnessExcess_le_iff_secondMomentRe_le_mul hmul hone hunit Rel 0 hne

/-- **`flatnessExcess_lt_zero_iff_secondMomentRe_neg`** — strict sub-diagonal flatness is exactly
negative off-diagonal second moment. -/
theorem flatnessExcess_lt_zero_iff_secondMomentRe_neg (hmul : ∀ a b, θ (a + b) = θ a * θ b)
    (hone : θ 0 = 1) (hunit : ∀ s, Complex.normSq (θ s) = 1)
    (Rel : Finset (Fin r → R)) (hne : 0 < (Rel.card : ℝ)) :
    flatnessExcess θ Rel < 0 ↔
      (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re < 0 := by
  simpa using flatnessExcess_lt_iff_secondMomentRe_lt_mul hmul hone hunit Rel 0 hne

/-- **`flatnessExcess_eq_zero_iff_secondMomentRe_eq_zero`** — exact diagonal-floor equality is exactly
zero off-diagonal second moment. -/
theorem flatnessExcess_eq_zero_iff_secondMomentRe_eq_zero (hmul : ∀ a b, θ (a + b) = θ a * θ b)
    (hone : θ 0 = 1) (hunit : ∀ s, Complex.normSq (θ s) = 1)
    (Rel : Finset (Fin r → R)) (hne : 0 < (Rel.card : ℝ)) :
    flatnessExcess θ Rel = 0 ↔
      (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re = 0 := by
  simpa using flatnessExcess_eq_iff_secondMomentRe_eq_mul hmul hone hunit Rel 0 hne

end ArkLib.ProximityGap.Frontier.DiffTraceFlatnessExcessSecondMoment

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessExcessSecondMoment.flatnessExcess_eq_secondMomentRe_div_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessExcessSecondMoment.flatnessExcess_le_iff_secondMomentRe_le_mul
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessExcessSecondMoment.flatnessExcess_lt_iff_secondMomentRe_lt_mul
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessExcessSecondMoment.flatnessExcess_eq_iff_secondMomentRe_eq_mul
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessExcessSecondMoment.flatnessExcess_le_zero_iff_secondMomentRe_nonpos
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessExcessSecondMoment.flatnessExcess_lt_zero_iff_secondMomentRe_neg
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessExcessSecondMoment.flatnessExcess_eq_zero_iff_secondMomentRe_eq_zero
