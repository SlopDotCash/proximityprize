/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRun
import ArkLib.OracleReduction.Completeness

/-!
# Perfect completeness of sequential composition (`Reduction.append`): proof-plan notes

**Status: this module contains no declarations.** It is kept (it is imported by
`AppendPerfectCompletenessProof.lean`) as the record of the support-decomposition proof plan.

The append-completeness theorem in `Append.lean` (`reduction_append_perfectCompleteness`) is
residual-gated: it takes its own conclusion as the hypothesis
`reductionAppendPerfectCompletenessResidual`. For the message-seam case that residual is
**discharged by proved companion theorems** (not by this file), which derive

`(R₁.append R₂).perfectCompleteness` from `R₁.perfectCompleteness` and `R₂.perfectCompleteness`

*without* assuming the conclusion:

* `Reduction.append_perfectCompleteness_message` (`AppendPerfectCompletenessMsg.lean`) and
  `Reduction.append_perfectCompleteness_msg_proof` (`AppendPerfectCompletenessProof.lean`), under
  the message-seam hypotheses `hn`/`hDir`/`hDir₂`, `NeverFail init`, and the oracle-support
  restriction `hImplSupp` (every stateful response support equals the full query support,
  independently of the state); `reductionAppendPerfectCompletenessResidual_of_message` packages
  the former as the residual;
* `OracleReduction.append_perfectCompleteness_msg_proof` (`AppendPerfectCompletenessOracle.lean`)
  transfers this to oracle reductions, additionally assuming the verifier-fusion bridge
  `appendToReductionResidual`;
* `BCS/CompletenessPreservation.lean` consumes `Reduction.append_perfectCompleteness_msg_proof`.

These theorems do not cover other seams or implementations violating `hImplSupp`.

## Proof outline (support-decomposition — no distributional reordering needed)

`(R₁.append R₂).run` runs both provers then both verifiers: order `P₁, P₂, V₁, V₂`. A *distribution*
identity would need to commute `V₁` past `P₂`, but **perfect completeness only needs support
containment** (`probEvent_eq_one_iff`: `Pr[p|mx] = 1 ↔ Pr[⊥|mx] = 0 ∧ ∀ x ∈ support mx, p x`), and
support decomposes through `bind` *without* reordering (`mem_support_bind_iff`). So we never commute
anything; we decompose the support directly:

1. `Prover.append_run_msg` factors the appended prover run into `P₁.run` then `P₂.run`, and
   `Verifier.append_run` (`rfl`) splits the verifier into `V₁.run stmt₁ tr₁` then `V₂.run · tr₂`.
2. Take any outcome in the support. `mem_support_bind_iff` exposes
   `(tr₁,s₂,w₂) ∈ support (P₁.run)`, `sv₂ ∈ support (V₁.run stmt₁ tr₁)`,
   `(tr₂,s₃,w₃) ∈ support (P₂.run s₂ w₂)`, `sv₃ ∈ support (V₂.run sv₂ tr₂)`.
3. `h₁` applied to the `R₁.run` outcome `((tr₁,s₂,w₂), sv₂)` gives `sv₂ = s₂ ∧ (sv₂,w₂) ∈ rel₂`,
   hence `(s₂,w₂) ∈ rel₂` and `sv₂ = s₂`.
4. Rewriting `sv₂ = s₂`, the tail is exactly the `R₂.run s₂ w₂` outcome `((tr₂,s₃,w₃), sv₃)`;
   `h₂` (valid since `(s₂,w₂) ∈ rel₂`) gives `(sv₃,w₃) ∈ rel₃ ∧ sv₃ = s₃` — i.e. the goal.

The `hImplSupp` hypothesis (the appended verifier's stateful oracle queries have state-independent
*support*) is what makes the support decomposition go through despite a stateful `impl`; it is exactly
why the support route works where a naive distributional route would also have to track `σ`-state.

## Historical status (superseded; kept for the record)

The text in this section predates the companion proofs listed above. The "remaining gap" it
describes was later closed there (via the support-faithfulness gate
`Prover.addLift_challenge_support_faithful` of `ChallengeSeamBridge.lean` and the `OptionT`
support-decomposition lemmas), and the named residual it mentions is no longer stated in this
file. Read "unproven" below as the state at the time of writing, not the current state.

The following steps were machine-checked at the time (`lake env lean`, against built deps):
* `rw [perfectCompleteness_eq_prob_one]` reduces `h₁`, `h₂`, and the goal to `Pr[·] = 1`.
* `rw [probEvent_eq_one_iff]; refine ⟨?_, ?_⟩` splits the goal into **no-failure** (`Pr[⊥ | ·] = 0`)
  and **support containment** (`∀ x ∈ support …, good₃ x`).
* `Prover.append_run_msg` (with `hn`, `hDir`, `hDir₂`) factors `(R₁.append R₂).prover.run` into
  `P₁.run` then `P₂.run` (the rewrite fires; closing the explicit `hrun` to a stated RHS is a
  destructuring-vs-`match` defeq).

The remaining gap is the one piece that has kept this keystone unproven library-wide: the support
in the goal sits behind three wrappers — `OptionT.mk`, `StateT.run'` (from `init`), and
`simulateQ (impl.addLift challengeQueryImpl)` — so `support_bind`/`mem_support_bind_iff` do **not**
fire directly (verified: they leave the term intact). Closing it requires unfolding those three
layers and then the *challenge-oracle seam split* — relating the combined
`challengeQueryImpl` over `pSpec₁ ++ₚ pSpec₂` to the component handlers across the seam round `m`
(the building blocks exist: `append_getChallenge_left` / `append_getChallenge_natAdd`,
`range_challenge_append_inl`/`inr`, and vcvio's `simulateQ_add_liftM_left`/`right` /
`simulateQ_liftM_eq_of_query`). With the run decomposed under `simulateQ`, `h₁` pins
`V₁`'s output to `P₁`'s output statement `s₂ ∈ rel₂` and `h₂` lands the result in `rel₃`.

At the time, this obligation was stated below as a named residual. That statement has since been
removed from this file (see the note at the end), because the companion modules above prove the
message-seam keystone outright under the hypotheses listed there.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Reduction

-- NOTE: The placebo `def append_perfectCompleteness_msg : … := (R₁.append R₂).perfectCompleteness …`
-- (which merely restated the goal as a `Prop`-valued def, ignoring its own hypotheses) was removed.
-- The genuine, axiom-clean append perfect-completeness keystone is the *theorem*
-- `Reduction.append_perfectCompleteness_message` (in `AppendPerfectCompletenessMsg.lean`), with the
-- reduction-level companion `Reduction.append_perfectCompleteness_msg_proof`
-- (in `AppendPerfectCompletenessProof.lean`) and the oracle-level wrapper
-- `OracleReduction.append_perfectCompleteness_msg_proof`
-- (in `AppendPerfectCompletenessOracle.lean`, which also assumes `appendToReductionResidual`).
-- Use those.

end Reduction
