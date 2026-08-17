/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTraceSecondMomentEnvelope

/-!
# BRIDGE — sub-ceiling budgets on the named second moment force strict aggregate anti-coherence (#444)

`_DiffTraceSecondMomentEnvelope` moved the variance-core envelope from `DiffTrace` onto the named
off-diagonal second-moment real part

`secondMomentRe θ Rel = (Σ_T Σ_{T'∈Rel.erase T} Jphase θ T * conj (Jphase θ T')).re`.

This file packages the corresponding sub-ceiling obligation directly on that named object: a bound
`secondMomentRe θ Rel ≤ S` with `S < #Rel² - #Rel` exists exactly when the aggregate phase sum has a
strict triangle deficit `‖Σ_T Jphase θ T‖ < #Rel`.  Equivalently, a fully coherent aggregate sum
refutes every strict sub-ceiling second-moment budget.

No CORE / cancellation / completion / moment-saving / capacity claim is made.  This is the named-object
version of the Door-(iv) obligation: any real sub-trivial second-moment estimate must prove genuine
aggregate anti-coherence of the phase sum.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.DiffTraceSecondMomentSubCeiling

open Finset ComplexConjugate
open ArkLib.ProximityGap.Frontier.NextDifferenceVariety
open ArkLib.ProximityGap.Frontier.DiffTraceTrivialEnvelopeAttained
open ArkLib.ProximityGap.Frontier.DiffTraceSecondMomentEnvelope
open ArkLib.ProximityGap.Frontier.DiffTraceVarianceRouteCapstone

variable {R : Type*} [AddCommGroup R] {r : ℕ} {θ : R → ℂ} [DecidableEq (Fin r → R)]

/-- **`norm_lt_card_of_secondMomentRe_le_subceiling`** — any upper bound on the named off-diagonal
second moment that is strictly below the trivial ceiling forces strict aggregate anti-coherence:
`‖Σ Jphase‖ < #Rel`. -/
theorem norm_lt_card_of_secondMomentRe_le_subceiling
    (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ)
    (hS : S < (Rel.card : ℝ) ^ 2 - (Rel.card : ℝ))
    (h : secondMomentRe θ Rel ≤ S) :
    ‖∑ T ∈ Rel, Jphase θ T‖ < (Rel.card : ℝ) := by
  unfold secondMomentRe at h
  rw [secondMoment_re_eq_normSq_sub_card hmul hone hunit Rel, Complex.normSq_eq_norm_sq] at h
  have hn : 0 ≤ ‖∑ T ∈ Rel, Jphase θ T‖ := norm_nonneg _
  have hc : 0 ≤ (Rel.card : ℝ) := by positivity
  nlinarith

/-- **`exists_subceiling_secondMomentRe_bound_iff_norm_lt_card`** — on the named second-moment object,
strict aggregate anti-coherence is exactly the existence of some strict sub-ceiling budget. -/
theorem exists_subceiling_secondMomentRe_bound_iff_norm_lt_card
    (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    (∃ S : ℝ, S < (Rel.card : ℝ) ^ 2 - (Rel.card : ℝ) ∧ secondMomentRe θ Rel ≤ S)
      ↔ ‖∑ T ∈ Rel, Jphase θ T‖ < (Rel.card : ℝ) := by
  constructor
  · rintro ⟨S, hS, h⟩
    exact norm_lt_card_of_secondMomentRe_le_subceiling hmul hone hunit Rel S hS h
  · intro hnorm
    refine ⟨secondMomentRe θ Rel, ?_, le_rfl⟩
    rw [secondMomentRe_eq_diffTrace_re hmul hone hunit Rel]
    exact diffTrace_re_lt_ceiling_of_norm_lt_card hmul hone hunit Rel hnorm

/-- **`not_secondMomentRe_le_subceiling_of_norm_eq_card`** — at full aggregate coherence, no strict
sub-ceiling bound on the named off-diagonal second moment can hold. -/
theorem not_secondMomentRe_le_subceiling_of_norm_eq_card
    (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ)
    (hnorm : ‖∑ T ∈ Rel, Jphase θ T‖ = (Rel.card : ℝ))
    (hS : S < (Rel.card : ℝ) ^ 2 - (Rel.card : ℝ)) :
    ¬ secondMomentRe θ Rel ≤ S := by
  intro h
  have hlt := norm_lt_card_of_secondMomentRe_le_subceiling hmul hone hunit Rel S hS h
  linarith

end ArkLib.ProximityGap.Frontier.DiffTraceSecondMomentSubCeiling

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no extra axioms) -/
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceSecondMomentSubCeiling.norm_lt_card_of_secondMomentRe_le_subceiling
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceSecondMomentSubCeiling.exists_subceiling_secondMomentRe_bound_iff_norm_lt_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceSecondMomentSubCeiling.not_secondMomentRe_le_subceiling_of_norm_eq_card
