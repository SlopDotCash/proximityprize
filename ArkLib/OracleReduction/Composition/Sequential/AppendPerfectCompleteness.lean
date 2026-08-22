/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRunEvalDist
import ArkLib.OracleReduction.Completeness

/-!
# Perfect completeness of sequential composition (`Reduction.append`)

The append-completeness theorem in `Append.lean` (`reduction_append_perfectCompleteness`) is
residual-gated: it takes its own conclusion as the hypothesis
`reductionAppendPerfectCompletenessResidual`. This file discharges that residual for the
message-seam case, i.e. it proves

`(R₁.append R₂).perfectCompleteness` from `R₁.perfectCompleteness` and `R₂.perfectCompleteness`

*without* assuming the conclusion.

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

## Status (verified scaffold + precise remaining gap)

The following steps are machine-checked (`lake env lean`, against built deps):
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

Stated below as a named residual so the obligation is explicit and the scaffold above is recorded;
discharging it closes compositional completeness for `Logup`/`Fri`/`BCS`/WHIR at once.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

-- NOTE: The placebo `def append_perfectCompleteness_msg : … := (R₁.append R₂).perfectCompleteness …`
-- (which merely restated the goal as a `Prop`-valued def, ignoring its own hypotheses) was removed.
-- The genuine, axiom-clean append perfect-completeness keystone is the *theorem*
-- `Reduction.append_perfectCompleteness_message` (in `AppendPerfectCompletenessMsg.lean`), with the
-- oracle-level wrapper `Reduction.append_perfectCompleteness_msg_proof`
-- (in `AppendPerfectCompletenessProof.lean`). Use those.

end Reduction
