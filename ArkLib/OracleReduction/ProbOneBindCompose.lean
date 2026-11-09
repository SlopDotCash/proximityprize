/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Compatibility.DiscreteProbability
import ArkLib.Extensions.OracleReduction.Security.Basic
import ArkLib.ToMathlib.ProbEventBindOne

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

The generic statement is proved once, as the root-namespace `probEvent_bind_eq_one` in
`ArkLib.ToMathlib.ProbEventBindOne` (explicit predicates); `OracleComp.probEvent_bind_eq_one`
below is a compatibility wrapper with implicit predicates, kept so both argument shapes remain
available without a second proof.
-/

open scoped ENNReal

namespace OracleComp

universe u v

variable {α β : Type} {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- **Probability-one bind composition.** If `mx` satisfies `p` with probability `1`, and `f a`
satisfies `good` with probability `1` whenever `p a` holds, then `mx >>= f` satisfies `good` with
probability `1`. Compatibility wrapper (implicit predicates) around the root-namespace
`probEvent_bind_eq_one`. -/
lemma probEvent_bind_eq_one (mx : m α) (f : α → m β) {p : α → Prop} {good : β → Prop}
    (hmx : probEvent (p) (mx) = 1) (hf : ∀ a, p a → probEvent (good) (f a) = 1) :
    probEvent (good) (mx >>= f) = 1 :=
  _root_.probEvent_bind_eq_one mx f p good hmx hf

end OracleComp
