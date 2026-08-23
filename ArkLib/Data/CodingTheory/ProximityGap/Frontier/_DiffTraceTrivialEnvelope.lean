/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTraceLinearSumReframe

/-!
# CONSTRAINT — the variance-core linear-sum route has only the triangle envelope (#444)

Continuation of the Door-IV variance-core chain.  The previous files proved the exact endpoint

```
  FirstMomentDiffCancellation θ Rel S  ↔  ‖Σ_T Jphase θ T‖² ≤ #Rel + S.
```

This file pins the unconditional triangle envelope for that single aggregate linear phase sum.  Since
each `Jphase θ T` is a unit, the triangle inequality gives

```
  ‖Σ_T Jphase θ T‖ ≤ #Rel,
  ‖Σ_T Jphase θ T‖² ≤ #Rel²,
  (DiffTrace θ Rel).re ≤ #Rel² - #Rel.
```

So the variance-core reframe by itself supplies only the square/trivial ceiling `S = #Rel² - #Rel`.
The open prize content is exactly the missing anti-concentration/flatness theorem improving this to a
sub-Poisson upper bound.  No CORE/cancellation/completion/moment-saving/capacity claim is made here.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.DiffTraceTrivialEnvelope

open Finset ComplexConjugate
open ArkLib.ProximityGap.Frontier.NextDifferenceVariety
open ArkLib.ProximityGap.Frontier.DiffTraceDiagonalExtraction
open ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloor
open ArkLib.ProximityGap.Frontier.DiffTraceLinearSumReframe

variable {R : Type*} [AddCommGroup R] {r : ℕ} {θ : R → ℂ}

/-! ## §1 Unit phase terms give the triangle envelope -/

/-- **`norm_Jphase_eq_one`** — the normalized Jacobi phase has complex norm `1` whenever the
underlying additive character has norm-square `1` on every input. -/
theorem norm_Jphase_eq_one (hunit : ∀ s, Complex.normSq (θ s) = 1) (T : Fin r → R) :
    ‖Jphase θ T‖ = 1 := by
  have hs : ‖Jphase θ T‖ ^ 2 = (1 : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq, Jphase_normSq_eq_one hunit T]
  have hn : 0 ≤ ‖Jphase θ T‖ := norm_nonneg _
  nlinarith

/-- **`linearPhase_norm_le_card`** — triangle envelope for the aggregate variance-core phase sum:
`‖Σ_T Jphase θ T‖ ≤ #Rel`.  This is the exact trivial ceiling for the single linear sum that remains
after the variance-core Plancherel collapse. -/
theorem linearPhase_norm_le_card (hunit : ∀ s, Complex.normSq (θ s) = 1)
    (Rel : Finset (Fin r → R)) :
    ‖∑ T ∈ Rel, Jphase θ T‖ ≤ (Rel.card : ℝ) := by
  calc
    ‖∑ T ∈ Rel, Jphase θ T‖ ≤ ∑ T ∈ Rel, ‖Jphase θ T‖ := norm_sum_le _ _
    _ = ∑ _T ∈ Rel, (1 : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro T _
        exact norm_Jphase_eq_one hunit T
    _ = (Rel.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **`linearPhase_normSq_le_card_sq`** — squared triangle envelope:
`‖Σ_T Jphase θ T‖² ≤ #Rel²`.  This is the baseline upper side of the shifted square
`(DiffTrace).re + #Rel = ‖Σ Jphase‖²`. -/
theorem linearPhase_normSq_le_card_sq (hunit : ∀ s, Complex.normSq (θ s) = 1)
    (Rel : Finset (Fin r → R)) :
    Complex.normSq (∑ T ∈ Rel, Jphase θ T) ≤ (Rel.card : ℝ) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  have h := linearPhase_norm_le_card (θ := θ) hunit Rel
  have hn : 0 ≤ ‖∑ T ∈ Rel, Jphase θ T‖ := norm_nonneg _
  have hc : 0 ≤ (Rel.card : ℝ) := by positivity
  nlinarith

/-! ## §2 The induced trivial ceiling for the variance-core trace -/

/-- **`diffTrace_re_le_card_sq_sub_card`** — the variance-core off-diagonal first moment has the
unconditional trivial upper envelope `(DiffTrace).re ≤ #Rel² - #Rel`.  Combined with the Plancherel
floor, this places it in `[-#Rel, #Rel²-#Rel]`; the prize-relevant upper saving is exactly what is
NOT proved by triangle inequality. -/
theorem diffTrace_re_le_card_sq_sub_card [DecidableEq (Fin r → R)]
    (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    (DiffTrace θ Rel).re ≤ (Rel.card : ℝ) ^ 2 - (Rel.card : ℝ) := by
  rw [diffTrace_re_eq_normSq_sub_card hmul hone hunit Rel]
  have h := linearPhase_normSq_le_card_sq (θ := θ) hunit Rel
  linarith

/-- **`firstMomentDiffCancellation_trivial_ceiling`** — in the named open-core predicate, the
unconditional triangle inequality discharges only the large square slack `S = #Rel² - #Rel`.  Any
useful Door-IV variance-core attack must replace this by a genuinely nontrivial anti-concentration
bound for the aggregate phase sum. -/
theorem firstMomentDiffCancellation_trivial_ceiling [DecidableEq (Fin r → R)]
    (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    FirstMomentDiffCancellation θ Rel ((Rel.card : ℝ) ^ 2 - (Rel.card : ℝ)) :=
  diffTrace_re_le_card_sq_sub_card hmul hone hunit Rel

end ArkLib.ProximityGap.Frontier.DiffTraceTrivialEnvelope

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceTrivialEnvelope.norm_Jphase_eq_one
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceTrivialEnvelope.linearPhase_norm_le_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceTrivialEnvelope.linearPhase_normSq_le_card_sq
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceTrivialEnvelope.diffTrace_re_le_card_sq_sub_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceTrivialEnvelope.firstMomentDiffCancellation_trivial_ceiling
