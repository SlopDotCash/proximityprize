/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ProximityPrize.Compatibility.DiscreteProbability
import ProximityPrize.Extensions.OracleReduction.Security.Basic

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

variable {α β : Type} {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- **Probability-one bind composition.** If `mx` satisfies `p` with probability `1`, and `f a`
satisfies `good` with probability `1` for every `a` in the support of `mx` (in particular whenever
`p a` holds), then `mx >>= f` satisfies `good` with probability `1`. -/
lemma probEvent_bind_eq_one (mx : m α) (f : α → m β) {p : α → Prop} {good : β → Prop}
    (hmx : probEvent (p) (mx) = 1) (hf : ∀ a, p a → probEvent (good) (f a) = 1) :
    probEvent (good) (mx >>= f) = 1 := by
  apply le_antisymm (prEvent_le_one _)
  have h := mul_le_prEvent_bind_of_forall mx f p good (r := 1) (r' := 1)
    hmx.ge (fun a ha => (hf a ha).ge)
  simpa only [one_mul] using h

end OracleComp
