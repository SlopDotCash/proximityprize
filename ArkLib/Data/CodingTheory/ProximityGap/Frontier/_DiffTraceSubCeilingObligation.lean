/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTraceEnvelopeCapstone

/-!
# CONSTRAINT — sub-trivial variance budgets are exactly strict aggregate anti-coherence (#444)

This is a small Door-(iv) capstone on top of `_DiffTraceEnvelopeCapstone`.  The prior chain proved
that the variance-core trace is the shifted square

`(DiffTrace θ Rel).re = ‖Σ_T Jphase θ T‖² - #Rel`

and that the trivial ceiling is `#Rel² - #Rel`, attained exactly at maximal aggregate coherence
`‖Σ_T Jphase θ T‖ = #Rel`.  This file packages the corresponding **budget obligation** for the named
open predicate `FirstMomentDiffCancellation`:

* any budget strictly below the trivial ceiling forces strict aggregate anti-coherence
  `‖Σ_T Jphase θ T‖ < #Rel`;
* conversely, strict aggregate anti-coherence is exactly the existence of *some* sub-ceiling first
  moment budget;
* at full aggregate coherence no sub-ceiling budget can hold.

No CORE / cancellation / anti-concentration / completion / moment-saving claim is made: these are exact
reframings of what a successful Door-(iv) sub-ceiling argument would have to prove about the single
aggregate phase sum.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.DiffTraceSubCeilingObligation

open Finset ComplexConjugate
open ArkLib.ProximityGap.Frontier.NextDifferenceVariety
open ArkLib.ProximityGap.Frontier.DiffTraceLinearSumReframe
open ArkLib.ProximityGap.Frontier.DiffTraceTrivialEnvelopeAttained
open ArkLib.ProximityGap.Frontier.DiffTraceEnvelopeCapstone

variable {R : Type*} [AddCommGroup R] {r : ℕ} {θ : R → ℂ} [DecidableEq (Fin r → R)]

/-- **`norm_lt_card_of_firstMomentDiffCancellation_lt_ceiling`** — every named first-moment budget
strictly below the trivial ceiling `#Rel² - #Rel` forces a strict triangle deficit for the aggregate
phase sum.  This is the exact Door-(iv) obligation: a sub-trivial variance estimate must prove
`‖Σ Jphase‖ < #Rel`, i.e. genuine aggregate anti-coherence. -/
theorem norm_lt_card_of_firstMomentDiffCancellation_lt_ceiling
    (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ)
    (hS : S < (Rel.card : ℝ) ^ 2 - (Rel.card : ℝ))
    (h : FirstMomentDiffCancellation θ Rel S) :
    ‖∑ T ∈ Rel, Jphase θ T‖ < (Rel.card : ℝ) := by
  have hmass := normSq_le_of_firstMomentDiffCancellation hmul hone hunit Rel S h
  rw [Complex.normSq_eq_norm_sq] at hmass
  have hn : 0 ≤ ‖∑ T ∈ Rel, Jphase θ T‖ := norm_nonneg _
  have hc : 0 ≤ (Rel.card : ℝ) := by positivity
  nlinarith

/-- **`exists_subceiling_firstMomentDiffCancellation_iff_norm_lt_card`** — for a fixed relation set,
strict aggregate anti-coherence is EXACTLY the existence of a first-moment cancellation budget below
the trivial ceiling.  Forward direction: any such budget forces `‖Σ Jphase‖ < #Rel`.  Reverse
direction: if the aggregate sum has strict triangle deficit, choose the actual trace value as the
sub-ceiling budget. -/
theorem exists_subceiling_firstMomentDiffCancellation_iff_norm_lt_card
    (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    (∃ S : ℝ, S < (Rel.card : ℝ) ^ 2 - (Rel.card : ℝ)
        ∧ FirstMomentDiffCancellation θ Rel S)
      ↔ ‖∑ T ∈ Rel, Jphase θ T‖ < (Rel.card : ℝ) := by
  constructor
  · rintro ⟨S, hS, h⟩
    exact norm_lt_card_of_firstMomentDiffCancellation_lt_ceiling hmul hone hunit Rel S hS h
  · intro hnorm
    refine ⟨(DiffTrace θ Rel).re, ?_, ?_⟩
    · exact diffTrace_re_lt_ceiling_of_norm_lt_card hmul hone hunit Rel hnorm
    · unfold FirstMomentDiffCancellation
      exact le_rfl

/-- **`not_firstMomentDiffCancellation_subceiling_of_norm_eq_card`** — at maximal aggregate
coherence (`‖Σ Jphase‖ = #Rel`), no budget strictly below the trivial ceiling can hold.  Thus a
coherent worst frequency refutes any claimed sub-ceiling Door-(iv) certificate unless the certificate
first proves that this full-coherence case cannot be adversarial. -/
theorem not_firstMomentDiffCancellation_subceiling_of_norm_eq_card
    (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ)
    (hnorm : ‖∑ T ∈ Rel, Jphase θ T‖ = (Rel.card : ℝ))
    (hS : S < (Rel.card : ℝ) ^ 2 - (Rel.card : ℝ)) :
    ¬ FirstMomentDiffCancellation θ Rel S := by
  intro h
  have hlt := norm_lt_card_of_firstMomentDiffCancellation_lt_ceiling hmul hone hunit Rel S hS h
  linarith

end ArkLib.ProximityGap.Frontier.DiffTraceSubCeilingObligation

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no extra axioms) -/
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceSubCeilingObligation.norm_lt_card_of_firstMomentDiffCancellation_lt_ceiling
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceSubCeilingObligation.exists_subceiling_firstMomentDiffCancellation_iff_norm_lt_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceSubCeilingObligation.not_firstMomentDiffCancellation_subceiling_of_norm_eq_card
