/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.Basic

/-!
# Probability-one bind composition (issue #114 — completeness-composition keystone helper)

A small, reusable probabilistic lemma needed to de-launder the sequential-composition completeness
residual (`Reduction.reductionAppendCompletenessResidual`): if the first stage succeeds at its
predicate `p` with probability `1`, and conditioned on `p` the second stage succeeds at `good` with
probability `1`, then the composite succeeds with probability `1`.

This is exactly the error-`0` (perfect-completeness) instance of the two-stage success-probability
union bound that `reduction_append_perfectCompleteness` reduces to once the run is factored via
`Prover.append_run` (+ the `probOutput_bind_bind_swap` commutation). It carries the `prob = 1`
threading through `Pr[ · | mx >>= f]` cleanly, so the framework proof can apply it directly rather
than re-deriving the `tsum`/support bookkeeping.

Proof: `probEvent_bind_eq_tsum` expands `Pr[good | mx >>= f] = ∑' a, Pr[=a|mx] · Pr[good | f a]`;
`probEvent_eq_one_iff` extracts from `Pr[p|mx] = 1` both `Pr[⊥|mx] = 0` (so `∑' a, Pr[=a|mx] = 1`,
via `tsum_probOutput_eq_sub`) and `support mx ⊆ {p}` (so every in-support `a` has `Pr[good|f a] = 1`
by hypothesis); the out-of-support terms vanish.
-/

open scoped ENNReal

namespace OracleComp

universe u v

variable {α β : Type u} {m : Type u → Type v} [Monad m] [HasEvalSPMF m]

/-- **Probability-one bind composition.** If `mx` satisfies `p` with probability `1`, and `f a`
satisfies `good` with probability `1` for every `a` in the support of `mx` (in particular whenever
`p a` holds), then `mx >>= f` satisfies `good` with probability `1`. -/
lemma probEvent_bind_eq_one (mx : m α) (f : α → m β) {p : α → Prop} {good : β → Prop}
    (hmx : Pr[ p | mx] = 1) (hf : ∀ a, p a → Pr[ good | f a] = 1) :
    Pr[ good | mx >>= f] = 1 := by
  obtain ⟨hfail, hsupp⟩ := probEvent_eq_one_iff.mp hmx
  rw [probEvent_bind_eq_tsum]
  rw [show (1 : ℝ≥0∞) = ∑' a, Pr[= a | mx] from by rw [tsum_probOutput_eq_sub, hfail, tsub_zero]]
  refine tsum_congr fun a => ?_
  by_cases h : a ∈ support mx
  · rw [hf a (hsupp a h), mul_one]
  · simp [probOutput_eq_zero_of_not_mem_support h]

end OracleComp
