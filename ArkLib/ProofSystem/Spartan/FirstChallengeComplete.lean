/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.FirstChallengeCoherent
import ArkLib.ProofSystem.Spartan.ZeroCheckComplete
import ArkLib.ProofSystem.Component.RandomQuery

/-!
# The Spartan `firstChallenge` phase is (unconditionally) perfectly complete (issue #114)

Spartan's `firstChallenge` phase (`oracleReduction.firstChallenge`) is the `liftContext` of the
generic `RandomQuery` oracle reduction onto the virtual zero-check polynomial `𝒢` (compared against
the zero polynomial). This module assembles the **completeness transfer** for that lift.

Unlike the two sum-check phases — whose inner multi-round sum-check completeness is the
sequential-composition keystone still being assembled in the framework layer — the inner
`RandomQuery.oracleReduction_completeness` is already a *closed, unconditional* theorem. Hence this
phase's completeness is **unconditional**: it takes no `h_inner` hypothesis.

* `firstChallengeRelIn` / `firstChallengeRelOut` — the outer relations, both "R1CS is satisfied".
  The challenge `τ` produced by the phase is recorded in the output statement but is irrelevant to
  R1CS satisfiability, so it is carried through unchanged.
* `firstChallengeLensComplete` — the `OracleContext.Lens.IsComplete` instance. Its `proj_complete`
  is exactly `zeroCheckVirtualPolynomial_eq_zero_of_satisfied`: an R1CS-satisfying instance makes the
  zero-check polynomial `𝒢` vanish, so the two `RandomQuery` virtual oracles `(𝒢, 0)` agree
  (`RandomQuery.relIn`). Its `lift_complete` is the R1CS pass-through.
* `firstChallenge_perfectCompleteness` — a direct run proof for the one-round challenge adapter:
  the verifier samples `τ`, the prover records it, and the statement/oracles/witness are carried
  through unchanged.
-/

open MvPolynomial OracleComp OracleSpec ProtocolSpec OracleInterface Function

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  [VCVCompatible R] (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

local instance :
    VerifierOnly (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1) where
  verifier_first' := by simp

/-- **Outer input relation of the `firstChallenge` phase.** The R1CS instance is satisfied: the
public input `𝕩` (the `AfterFirstMessage` statement is exactly `𝕩`) together with the matrix oracles
`A, B, C` and the witness oracle `𝕨` satisfy `(A𝕫)·(B𝕫) = C𝕫`. -/
def firstChallengeRelIn :
    Set ((Statement.AfterFirstMessage R pp ×
        (∀ i, OracleStatement.AfterFirstMessage R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1
      (fun idx => x.1.2 (.inl idx)) (x.1.2 (.inr 0)) }

/-- **Outer output relation of the `firstChallenge` phase.** The same R1CS satisfiability, carried
through: the output statement `(τ, 𝕩)` records the sampled challenge `τ`, but the matrix/witness
oracles and the public input `𝕩 = stmt.2` are unchanged. This is the input relation of the following
first sum-check phase (`firstSumcheckRelIn`). -/
def firstChallengeRelOut :
    Set ((Statement.AfterFirstChallenge R pp ×
        (∀ i, OracleStatement.AfterFirstChallenge R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2
      (fun idx => x.1.2 (.inl idx)) (x.1.2 (.inr 0)) }

/-- **`OracleContext.Lens.IsComplete` for the `firstChallenge` lens.**

* `proj_complete`: an R1CS-satisfying Spartan instance projects to a `RandomQuery` instance whose two
  virtual oracles `(𝒢, 0)` agree, i.e. `𝒢 = 0` — exactly `zeroCheckVirtualPolynomial_eq_zero_of_satisfied`.
* `lift_complete`: the lift carries the matrices/witness/public input unchanged (only `τ` is
  recorded), so R1CS satisfiability transfers verbatim. -/
instance firstChallengeLensComplete :
    (firstChallengeContextLens R pp).toContext.IsComplete
      (firstChallengeRelIn pp)
      (RandomQuery.relIn (MvPolynomial (Fin pp.ℓ_m) R))
      (firstChallengeRelOut pp)
      (RandomQuery.relOut (MvPolynomial (Fin pp.ℓ_m) R))
      ((RandomQuery.oracleReduction oSpec (MvPolynomial (Fin pp.ℓ_m) R)).toReduction.compatContext
        (firstChallengeContextLens R pp).toContext) where
  proj_complete := by
    rintro ⟨𝕩, oStmt⟩ ⟨⟩ hRelIn
    simp only [firstChallengeRelIn, Set.mem_setOf_eq] at hRelIn
    simp only [firstChallengeContextLens, firstChallengeStmtLens, OracleContext.Lens.toContext,
      Context.Lens.proj, RandomQuery.relIn, Set.mem_setOf_eq]
    exact zeroCheckVirtualPolynomial_eq_zero_of_satisfied pp 𝕩 oStmt hRelIn
  lift_complete := by
    rintro ⟨𝕩, oStmt⟩ ⟨⟩ ⟨q, innerO⟩ ⟨⟩ _hCompat hRelIn _hRelOut
    simp only [firstChallengeRelIn, Set.mem_setOf_eq] at hRelIn
    simpa only [firstChallengeRelOut, Set.mem_setOf_eq] using hRelIn

set_option maxHeartbeats 0 in
/-- **`firstChallenge` phase perfect completeness (issue #114), unconditional.** The Spartan
`firstChallenge` oracle reduction is perfectly complete from `firstChallengeRelIn` to
`firstChallengeRelOut`.

The protocol implementation is behaviorally the old `RandomQuery` lift, but the concrete reduction
is now the direct `firstChallengeProver`/`firstChallengeVerifier` pair. Proving completeness against
that run avoids the heavy deep-lens normalization while preserving the same semantic endpoints. -/
theorem firstChallenge_perfectCompleteness
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)} :
    (oracleReduction.firstChallenge R pp oSpec).perfectCompleteness init impl
      (firstChallengeRelIn (R := R) pp) (firstChallengeRelOut (R := R) pp) := by
  simp only [OracleReduction.perfectCompleteness, oracleReduction.firstChallenge,
    firstChallengeRelIn, firstChallengeRelOut]
  simp only [Reduction.perfectCompleteness_eq_prob_one]
  intro ⟨stmt, oStmt⟩ wit hRelIn
  simp only [OracleReduction.toReduction, Reduction.run, Prover.run_of_verifier_first,
    firstChallengeProver, firstChallengeVerifier, OracleVerifier.toVerifier, Verifier.run]
  simp_rw [show (pure : _ → OptionT (OracleComp _) _) = fun x => (pure (some x) :
    OracleComp _ _) from rfl]
  try simp only [← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_pure,
    pure_bind, bind_assoc]
  erw [simulateQ_bind]
  erw [simulateQ_bind]
  simp only [QueryImpl.addLift_def, simulateQ_pure,
    QueryImpl.simulateQ_add_liftComp_right, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_query,
    ← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_pure,
    pure_bind, bind_assoc, map_pure, monadLift_pure, monadLift_bind]
  erw [simulateQ_bind]
  simp only [QueryImpl.addLift_def, simulateQ_pure,
    QueryImpl.simulateQ_add_liftComp_right, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_query,
    ← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_pure,
    pure_bind, bind_assoc, map_pure, monadLift_pure, monadLift_bind,
    OptionT.run_mk, OptionT.run_pure, OptionT.run_bind, OptionT.run,
    Option.getM, Option.bind_some, Option.elimM,
    FullTranscript.challenges, FullTranscript.messages, ChallengeIdx, Challenge]
  try erw [simulateQ_query]
  simp only [Fin.isValue, Fin.vcons_of_one, ChallengeIdx,
    Challenge, ofPFunctor_toPFunctor, QueryImpl.liftTarget_self, MessageIdx,
    Message, bind_map_left, StateT.run'_eq, StateT.run_bind, map_bind, OptionT.mk_bind,
    Set.mem_setOf_eq, probEvent_eq_one_iff, probFailure_bind_eq_zero_iff,
    OptionT.probFailure_liftM, HasEvalPMF.probFailure_eq_zero, OptionT.support_liftM,
    Prod.forall, true_and, support_bind, Set.mem_iUnion, OptionT.mem_support_iff,
    OptionT.run_mk, support_map, Set.mem_image, Prod.exists, exists_and_right,
    exists_eq_right, exists_prop, forall_exists_index, and_imp, Prod.mk.injEq]
  constructor <;> intro <;> intro <;> intro <;> intro
  all_goals try erw [simulateQ_bind]
  all_goals simp only [MonadLift.monadLift, liftM, monadLift, MonadLiftT.monadLift]
  all_goals simp only [OracleComp.liftComp_pure, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_pure, simulateQ_id', pure_bind, bind_assoc, map_pure, monadLift_pure,
    OptionT.run_mk, OptionT.run_pure, OptionT.run_bind, OptionT.run,
    StateT.run'_eq, probFailure_eq_zero,
    support_pure, Set.mem_singleton_iff, Prod.eq_iff_fst_eq_snd_eq]
  all_goals try erw [simulateQ_pure]
  all_goals try simp_all only [simulateQ_pure, pure_bind, map_pure,
    OptionT.run_mk, OptionT.run_pure, OptionT.run_bind, OptionT.run,
    StateT.run'_eq, StateT.run_pure, probFailure_eq_zero,
    support_pure, support_map, Set.mem_singleton_iff, Set.mem_image,
    OptionT.probFailure_eq, probOutput_pure]
  · erw [simulateQ_bind, simulateQ_pure]
    simp only [pure_bind]
    erw [simulateQ_pure]
    simp [map_pure, OptionT.mk, probFailure_pure]
  · intro wOut q2 stmt2 oOut2 sI hsI chalR sC hQuery sV hSupp
    try erw [simulateQ_bind] at hSupp
    try simp only [liftComp_eq_liftM, pure_bind, simulateQ_pure, OptionT.lift,
      OptionT.run_mk, map_pure] at hSupp
    try erw [simulateQ_pure] at hSupp
    simp only [pure_bind, simulateQ_pure, StateT.run_pure, support_pure, StateT.run, StateT.run',
      Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hSupp
    obtain ⟨⟨rfl, ⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, ⟨rfl, rfl⟩, rfl⟩ := hSupp
    refine ⟨?_, ⟨rfl, rfl⟩, rfl⟩
    simpa only [Set.mem_setOf_eq] using hRelIn

end Spartan.Spec
