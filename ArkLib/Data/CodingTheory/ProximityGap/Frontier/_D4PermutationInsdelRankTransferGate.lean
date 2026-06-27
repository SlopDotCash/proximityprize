/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

set_option autoImplicit false

/-!
# D4 permutation/insdel rank-transfer gate

Issue #464 flagged arXiv:2606.22344 as a useful random-Reed-Solomon input: random RS codes over
polynomial-size alphabets can robustly correct adversarial coordinate permutations followed by
insertion/deletion errors, using algebraic rank and Schwartz-Zippel style genericity.

For the plain proximity-prize floor, the domain is not random.  It is the fixed dyadic smooth
subgroup `mu_n`.  A generic-rank theorem transfers only after one proves the fixed smooth domain,
or every actual extremal configuration on that domain, lies inside the generic certificate.  This
file records that transfer obligation and the countermodels showing that random/generic control
alone is compatible with a spike on the designated smooth instance.
-/

namespace ArkLib.ProximityGap.Frontier.D4PermutationInsdelRankTransferGate

/-- If the designated smooth domain is inside the generic-good locus, a generic rank/SZ bound
transfers to it. -/
theorem smooth_bound_of_generic_locus
    {D : Type*} (good : D → Prop) (smooth : D) (stat : D → ℝ) (B : ℝ)
    (hsmooth : good smooth)
    (hgeneric : ∀ d, good d → stat d ≤ B) :
    stat smooth ≤ B :=
  hgeneric smooth hsmooth

/-- **No-domain-membership countermodel.** A rank/SZ bound on every generic-good domain is
compatible with an arbitrarily bad designated smooth domain if membership of the smooth domain in
the generic-good locus is not supplied. -/
theorem generic_bound_does_not_transfer_without_smooth_membership (B : ℝ) :
    ∃ (smooth : Bool) (good : Bool → Prop) (stat : Bool → ℝ),
      (∀ d, good d → stat d ≤ B) ∧ ¬ good smooth ∧ B < stat smooth := by
  refine ⟨false, (fun d => d = true), (fun d => if d then B - 1 else B + 1), ?_, ?_, ?_⟩
  · intro d hd
    cases d <;> simp at hd ⊢
  · simp
  · simp

/-- If every actual smooth-domain configuration is covered by a generic symbolic model, and the
generic model bound dominates the actual statistic pointwise, then the bound transfers to all
actual configurations. -/
theorem actual_bound_of_pointwise_model_cover
    {C Ω : Type*} (actual : C → ℝ) (model : Ω → ℝ) (covers : C → Ω → Prop) (B : ℝ)
    (hcover : ∀ c, ∃ ω, covers c ω)
    (hcompare : ∀ c ω, covers c ω → actual c ≤ model ω)
    (hmodel : ∀ ω, model ω ≤ B) :
    ∀ c, actual c ≤ B := by
  intro c
  rcases hcover c with ⟨ω, hω⟩
  exact le_trans (hcompare c ω hω) (hmodel ω)

/-- **No-configuration-cover countermodel.** Even if every covered symbolic model is bounded, an
uncovered smooth-domain configuration may still spike.  Thus a faulty-index/SZ union bound must
cover the actual extremal smooth-domain configurations, not only a random-domain model class. -/
theorem covered_models_do_not_bound_uncovered_config (B : ℝ) :
    ∃ (actual : Bool → ℝ) (model : Unit → ℝ) (covers : Bool → Unit → Prop)
        (c₀ : Bool),
      (∀ c ω, covers c ω → actual c ≤ model ω) ∧
      (∀ ω, model ω ≤ B) ∧
      (∀ ω, ¬ covers c₀ ω) ∧
      B < actual c₀ := by
  refine ⟨(fun c => if c then B - 1 else B + 1), (fun _ => B),
    (fun c _ => c = true), false, ?_, ?_, ?_, ?_⟩
  · intro c ω hcover
    cases c <;> simp at hcover ⊢
  · intro ω
    rfl
  · intro ω
    simp
  · simp

/-! ## Axiom audit. -/
#print axioms smooth_bound_of_generic_locus
#print axioms generic_bound_does_not_transfer_without_smooth_membership
#print axioms actual_bound_of_pointwise_model_cover
#print axioms covered_models_do_not_bound_uncovered_config

end ArkLib.ProximityGap.Frontier.D4PermutationInsdelRankTransferGate
