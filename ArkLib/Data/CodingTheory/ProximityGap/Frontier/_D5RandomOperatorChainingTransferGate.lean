/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

set_option autoImplicit false

/-!
# D5 random-operator / generic-chaining transfer gate

Issue #464 flagged random-operator square-root cancellation and generic-chaining technology as an
L∞-native way to reach the Paley floor.  The transfer obligation is precise: a theorem about a
randomized coefficient model bounds the fixed smooth-subgroup instance only through a pointwise
domination/coupling, or through a genuine cover of all deterministic bad events by model bad
events.  Without such an input, the random model can be uniformly bounded while the designated
smooth instance spikes.

This file records that gate.  It does not refute chaining itself; it isolates the missing theorem:
deterministic sub-Gaussian increments/tails for the actual Gauss-period process at the Paley
saddle.
-/

namespace ArkLib.ProximityGap.Frontier.D5RandomOperatorChainingTransferGate

/-- A uniform bound for an auxiliary random/operator model transfers to the deterministic prize
statistic only through a pointwise domination map. -/
theorem deterministic_bound_of_pointwise_domination
    {D Ω : Type*} (detStat : D → ℝ) (modelStat : Ω → ℝ) (pull : D → Ω) (B : ℝ)
    (hdom : ∀ d, detStat d ≤ modelStat (pull d))
    (hmodel : ∀ ω, modelStat ω ≤ B) :
    ∀ d, detStat d ≤ B := by
  intro d
  exact le_trans (hdom d) (hmodel (pull d))

/-- If every deterministic bad instance is covered by a model bad event, then excluding all model
bad events excludes deterministic bad instances. -/
theorem no_deterministic_bad_of_bad_event_cover
    {D Ω : Type*} (detBad : D → Prop) (modelBad : Ω → Prop) (covers : D → Ω → Prop)
    (hcover : ∀ d, detBad d → ∃ ω, covers d ω ∧ modelBad ω)
    (hnoModelBad : ¬ ∃ ω, modelBad ω) :
    ¬ ∃ d, detBad d := by
  rintro ⟨d, hd⟩
  rcases hcover d hd with ⟨ω, _hcov, hbad⟩
  exact hnoModelBad ⟨ω, hbad⟩

/-- **No-coupling countermodel.**  The random/operator model can be bounded everywhere while a
designated deterministic smooth instance is arbitrarily large. -/
theorem bounded_random_model_does_not_bound_fixed_instance (B : ℝ) :
    ∃ (modelStat : PUnit → ℝ) (detStat : Bool → ℝ) (smooth : Bool),
      (∀ ω, modelStat ω ≤ B) ∧ B < detStat smooth := by
  refine ⟨fun _ => B - 1, fun d => if d then B - 1 else B + 1, false, ?_, ?_⟩
  · intro _
    simp
  · simp

/-- **No bad-event-cover countermodel.**  A model theorem may exclude every model bad event while
an uncovered deterministic bad event still exists.  This is the logical shape of using random
multiplier/chaining estimates without proving they cover the actual smooth-domain extremum. -/
theorem no_model_bad_does_not_exclude_uncovered_deterministic_bad :
    ∃ (detBad : Bool → Prop) (modelBad : PUnit → Prop) (covers : Bool → PUnit → Prop),
      (¬ ∃ ω, modelBad ω) ∧
      (∃ d, detBad d) ∧
      (∀ d, detBad d → ∀ ω, ¬ covers d ω) := by
  refine ⟨(fun d => d = false), (fun _ => False), (fun _ _ => False), ?_, ?_, ?_⟩
  · rintro ⟨ω, hω⟩
    exact hω
  · exact ⟨false, rfl⟩
  · intro d _hd ω
    simp

/-! ## Axiom audit. -/
#print axioms deterministic_bound_of_pointwise_domination
#print axioms no_deterministic_bad_of_bad_event_cover
#print axioms bounded_random_model_does_not_bound_fixed_instance
#print axioms no_model_bad_does_not_exclude_uncovered_deterministic_bad

end ArkLib.ProximityGap.Frontier.D5RandomOperatorChainingTransferGate
