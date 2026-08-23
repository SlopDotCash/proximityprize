/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRoundFlipImp
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRoundPlainRbr

/-! # Discharging `hIndep` for the single-round sum-check knowledge state function (#13)

`SingleRoundFlipImp.lean` reduced the all-prover-witness-type per-round knowledge-flip bound
(`hKnowFlip`, the last residual of the RBR-knowledge ⇒ RBR-plain soundness weakening) to the single
named hypothesis `hIndep : TranscriptIndependent kSF` — transcript-independence of the single-round
sum-check knowledge state function. That fact was left as a hypothesis only because
`Simple.simpleKnowledgeStateFunction` was `private` and so could not be named from a downstream
file.

It is now public, and its transcript-independence is immediate: its `toFun` is
`fun _ stmtIn _ _ => (stmtIn, ()) ∈ inputRelation R deg D`, which ignores the message index,
transcript, and mid-witness. So the statement-predicate witness is the input-relation membership
and the per-round equivalence is `Iff.rfl`. This closes `hIndep`, hence `hKnowFlip`, hence the
per-round plain round-by-round soundness of the single-round sum-check oracle verifier. -/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Sumcheck.Spec.SingleRound.Simple

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R] {deg : ℕ} {m : ℕ}
  {D : Fin m ↪ R} {ι : Type} {oSpec : OracleSpec ι}

/-- **`hIndep`, discharged.** The single-round sum-check knowledge state function is
transcript-independent: its `toFun` returns only whether the statement lies in the input relation,
ignoring the message index, transcript, and intermediate witness. -/
theorem simpleKnowledgeStateFunction_transcriptIndependent {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    KnowFlip.TranscriptIndependent
      (simpleKnowledgeStateFunction (init := init) (impl := impl) R deg D oSpec) :=
  ⟨fun stmtIn => (stmtIn, ()) ∈ inputRelation R deg D, fun _ _ _ _ => Iff.rfl⟩

/-- **Per-round plain RBR soundness, discharged for the single-round sum-check oracle verifier.**

This closes the downstream `hRound` shape for one generic sum-check round: the plain state function
is induced from `simpleKnowledgeStateFunction`, the all-prover-witness-type knowledge-flip bound is
supplied by transcript-independence, and the flip event is pointwise impossible.  The statement is
valid for any caller-chosen error family, since the actual flip probability is `0`. -/
theorem oracleVerifier_rbrSoundness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    [(oSpec + [(SingleRound.pSpec R deg).Challenge]ₒ'challengeOracleInterface).Fintype]
    [(oSpec + [(SingleRound.pSpec R deg).Challenge]ₒ'challengeOracleInterface).Inhabited]
    (rbrError : (SingleRound.pSpec R deg).ChallengeIdx → ℝ≥0) :
    (oracleVerifier R deg D oSpec).rbrSoundness init impl
      (inputRelation R deg D).language (outputRelation R deg).language rbrError :=
  Verifier.RoundByRound.oracleVerifier_rbrSoundness_of_knowledgeFlip
    (simpleKnowledgeStateFunction (init := init) (impl := impl) R deg D oSpec)
    rbrError
    (oracleVerifier_hKnowFlip_family_of_transcriptIndep
      (simpleKnowledgeStateFunction (init := init) (impl := impl) R deg D oSpec)
      (simpleKnowledgeStateFunction_transcriptIndependent init impl) rbrError)

end Sumcheck.Spec.SingleRound.Simple

#print axioms Sumcheck.Spec.SingleRound.Simple.oracleVerifier_rbrSoundness
