/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.FiatShamir.BasicCompleteness
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.ToVCVio.OracleComp.Coercions.SubSpec

/-!
# Basic Fiat-Shamir State-Restoration Pre-Transport Wrappers (#116)

`FiatShamir/Basic.lean` exposes wrappers that apply a discharged state-restoration transfer
residual and then weaken the Fiat-Shamir conclusion.  This companion file provides the dual
consumer shape: first transport the state-restoration hypothesis with
`Verifier.StateRestoration.*.mono_*`, then apply a transfer residual that is already stated at the
target parameters.

It also exposes the one-message Fiat-Shamir adversary payload as a state-restoration prover payload,
so the eventual coupled `simulateQ` proof can compare both games over the same transcript
derivation surface.

Most declarations here are API plumbing over the existing residual/coupling surfaces.  The
canonical shared-challenge-table soundness residual is discharged below; the knowledge-soundness
and zero-knowledge transfer content remains separate.
-/

noncomputable section

open ProtocolSpec OracleComp OracleSpec
open ArkLib.FiatShamir.CompletenessAux
open scoped NNReal

section TranscriptAliases

namespace ProtocolSpec

/-- The slow Fiat-Shamir challenge oracle is definitionally the state-restoration challenge
oracle. This is the structural coupling used by the #116 soundness-transfer reduction. -/
theorem fsChallengeOracle_eq_srChallengeOracle {Statement : Type} {n : ℕ}
    {pSpec : ProtocolSpec n} :
    fsChallengeOracle Statement pSpec = srChallengeOracle Statement pSpec := by
  rfl

/-- The cached slow Fiat-Shamir challenge query implementation is definitionally the cached
state-restoration challenge query implementation. -/
theorem fsChallengeQueryImpl'_eq_srChallengeQueryImpl' {Statement : Type} {n : ℕ}
    {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)] :
    fsChallengeQueryImpl' (Statement := Statement) (pSpec := pSpec) =
      srChallengeQueryImpl' (Statement := Statement) (pSpec := pSpec) := by
  rfl

/-- Slow Fiat-Shamir challenge query implementation with the cached challenge table state written
directly over the Fiat-Shamir oracle alias.

The existing `fsChallengeQueryImpl'` alias unfolds through the state-restoration oracle name.  This
definition exposes the same cached-table behavior at the `fsChallengeOracle` type, so coupled
soundness proofs can use `QueryImpl.addLift` without asking Lean to lift between the alias-expanded
state monads. -/
@[reducible, inline, specialize, simp]
def fsChallengeQueryImplState {Statement : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)] :
    QueryImpl (fsChallengeOracle Statement pSpec)
      (StateT (QueryImpl (fsChallengeOracle Statement pSpec) Id) ProbComp) :=
  fun | ⟨i, t⟩ => fun f => pure (f ⟨i, t⟩, f)

/-- The FS-state implementation is definitionally the usual cached slow-Fiat-Shamir query
implementation after fixing the target state type to the Fiat-Shamir oracle alias. -/
theorem fsChallengeQueryImplState_eq_fsChallengeQueryImpl' {Statement : Type} {n : ℕ}
    {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)] :
    fsChallengeQueryImplState (Statement := Statement) (pSpec := pSpec) =
      (fsChallengeQueryImpl' (Statement := Statement) (pSpec := pSpec) :
        QueryImpl (fsChallengeOracle Statement pSpec)
          (StateT (QueryImpl (fsChallengeOracle Statement pSpec) Id) ProbComp)) := by
  rfl

/-- The FS-state implementation is also definitionally the cached state-restoration challenge
implementation. This is the normalized shared-table shape used by the canonical coupled soundness
proof below. -/
theorem fsChallengeQueryImplState_eq_srChallengeQueryImpl' {Statement : Type} {n : ℕ}
    {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)] :
    fsChallengeQueryImplState (Statement := Statement) (pSpec := pSpec) =
      srChallengeQueryImpl' (Statement := Statement) (pSpec := pSpec) := by
  rfl

namespace MessagesUpTo

/-- Partial transcript derivation for slow Fiat-Shamir is definitionally the state-restoration
transcript derivation. -/
theorem deriveTranscriptFS_eq_deriveTranscriptSR {n : ℕ} {pSpec : ProtocolSpec n}
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (stmt : StmtIn) (k : Fin (n + 1)) (messages : pSpec.MessagesUpTo k) :
    deriveTranscriptFS (oSpec := oSpec) stmt k messages =
      deriveTranscriptSR (oSpec := oSpec) stmt k messages := by
  rfl

end MessagesUpTo

namespace Messages

/-- Full transcript derivation for slow Fiat-Shamir is definitionally the state-restoration
transcript derivation. -/
theorem deriveTranscriptFS_eq_deriveTranscriptSR {n : ℕ} {pSpec : ProtocolSpec n}
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (stmt : StmtIn) (messages : pSpec.Messages) :
    deriveTranscriptFS (oSpec := oSpec) stmt messages =
      deriveTranscriptSR (oSpec := oSpec) stmt messages := by
  rfl

end Messages

end ProtocolSpec

section TranscriptDeterminism

namespace ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
  [∀ i, SampleableType (pSpec.Challenge i)]

/-- A single challenge-oracle query, simulated through the cached challenge-table state
implementation, is a deterministic read of the table that leaves the table unchanged.

This is the per-query atom underlying the read-only determinism of the slow Fiat-Shamir transcript
derivation: `fsChallengeQueryImplState` answers a challenge query by `fun f => pure (f q, f)`, i.e.
it looks up the cached table without sampling or mutating it, so the shared-oracle implementation
`srImpl` is never consulted. -/
theorem simulateQ_addLift_fsChallenge_query_run
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (q : (fsChallengeOracle StmtIn pSpec).Domain)
    (table : QueryImpl (fsChallengeOracle StmtIn pSpec) Id) :
    StateT.run (simulateQ (srImpl.addLift fsChallengeQueryImplState)
      (query (spec := fsChallengeOracle StmtIn pSpec) q :
        OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
          ((fsChallengeOracle StmtIn pSpec).Range q))) table =
        (pure (table q, table) : ProbComp ((fsChallengeOracle StmtIn pSpec).Range q ×
          QueryImpl (fsChallengeOracle StmtIn pSpec) Id)) := by
  rw [show (query (spec := fsChallengeOracle StmtIn pSpec) q :
        OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
          ((fsChallengeOracle StmtIn pSpec).Range q))
      = liftM (liftM (OracleSpec.query q) :
          OracleQuery (oSpec + fsChallengeOracle StmtIn pSpec)
            ((fsChallengeOracle StmtIn pSpec).Range q)) from rfl,
    simulateQ_query]
  simp only [OracleQuery.liftM_add_right_def, QueryImpl.addLift]
  rfl

namespace MessagesUpTo

/-- Through the cached challenge-table state implementation, the auxiliary slow Fiat-Shamir
transcript derivation is read-only deterministic: running it leaves the table unchanged and returns
a fixed transcript value. This is proved by induction on the round index, using
`simulateQ_addLift_fsChallenge_query_run` at each verifier-challenge step. -/
theorem deriveTranscriptSRAux_simulateQ_run
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (stmtIn : StmtIn) (k : Fin (n + 1)) (messages : pSpec.MessagesUpTo k)
    (j : Fin (k + 1))
    (table : QueryImpl (fsChallengeOracle StmtIn pSpec) Id) :
    ∃ t : pSpec.Transcript (j.castLE (by omega)),
      StateT.run (simulateQ (srImpl.addLift fsChallengeQueryImplState)
        (deriveTranscriptSRAux stmtIn k messages j)) table =
        (pure (t, table) :
          ProbComp (pSpec.Transcript (j.castLE (by omega)) ×
            QueryImpl (fsChallengeOracle StmtIn pSpec) Id)) := by
  induction j using Fin.induction with
  | zero =>
    refine ⟨fun i => i.elim0, ?_⟩
    simp [deriveTranscriptSRAux, simulateQ_pure]
  | succ i ih =>
    obtain ⟨t, ht⟩ := ih
    simp only [deriveTranscriptSRAux] at ht ⊢
    rw [Fin.induction_succ, simulateQ_bind, StateT.run_bind, ht, pure_bind]
    split
    · next _hDir =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_addLift_fsChallenge_query_run,
        pure_bind, simulateQ_pure, StateT.run_pure]
      exact ⟨_, rfl⟩
    · rw [simulateQ_pure]
      refine ⟨_, rfl⟩

/-- Read-only determinism of the slow Fiat-Shamir partial-transcript derivation through the cached
challenge-table state, specialized to the full derivation up to round `k`. -/
theorem deriveTranscriptSR_simulateQ_run
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (stmtIn : StmtIn) (k : Fin (n + 1)) (messages : pSpec.MessagesUpTo k)
    (table : QueryImpl (fsChallengeOracle StmtIn pSpec) Id) :
    ∃ t : pSpec.Transcript k,
      StateT.run (simulateQ (srImpl.addLift fsChallengeQueryImplState)
        (deriveTranscriptSR (oSpec := oSpec) stmtIn k messages)) table =
        (pure (t, table) :
          ProbComp (pSpec.Transcript k × QueryImpl (fsChallengeOracle StmtIn pSpec) Id)) :=
  deriveTranscriptSRAux_simulateQ_run srImpl stmtIn k messages (Fin.last k) table

end MessagesUpTo

namespace Messages

/-- Read-only determinism of the slow Fiat-Shamir full-transcript derivation through the cached
challenge-table state implementation: it leaves the table unchanged and returns a fixed transcript.

This is the keystone used by the knowledge-soundness transfer to collapse the redundant transcript
derivation: the Fiat-Shamir verifier derives the transcript to check the proof, and the
straightline extractor re-derives it from the same proof and table. -/
theorem deriveTranscriptFS_simulateQ_run
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (stmtIn : StmtIn) (messages : pSpec.Messages)
    (table : QueryImpl (fsChallengeOracle StmtIn pSpec) Id) :
    ∃ t : pSpec.FullTranscript,
      StateT.run (simulateQ (srImpl.addLift fsChallengeQueryImplState)
        (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn messages)) table =
        (pure (t, table) :
          ProbComp (pSpec.FullTranscript × QueryImpl (fsChallengeOracle StmtIn pSpec) Id)) :=
  MessagesUpTo.deriveTranscriptSR_simulateQ_run srImpl stmtIn (Fin.last n) messages table

end Messages

end ProtocolSpec

#print axioms ProtocolSpec.simulateQ_addLift_fsChallenge_query_run
#print axioms ProtocolSpec.MessagesUpTo.deriveTranscriptSRAux_simulateQ_run
#print axioms ProtocolSpec.MessagesUpTo.deriveTranscriptSR_simulateQ_run
#print axioms ProtocolSpec.Messages.deriveTranscriptFS_simulateQ_run

end TranscriptDeterminism

namespace Verifier

/-- The basic Fiat-Shamir verifier can be expanded using the state-restoration transcript
derivation, since `deriveTranscriptFS` and `deriveTranscriptSR` are aliases. -/
theorem fiatShamir_verify_eq_deriveTranscriptSR {n : ℕ} {pSpec : ProtocolSpec n}
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type}
    (V : Verifier oSpec StmtIn StmtOut pSpec) (stmtIn : StmtIn)
    (proof : FullTranscript ⟨!v[Direction.P_to_V], !v[pSpec.Messages]⟩) :
    (V.fiatShamir).verify stmtIn proof =
      (do
        let messages : pSpec.Messages := proof 0
        let transcript ← messages.deriveTranscriptSR (oSpec := oSpec) stmtIn
        let v ← (V.verify stmtIn transcript).run
        v.getM) := by
  rfl

namespace StateRestoration

/-- The state-restoration soundness game can be read through the slow Fiat-Shamir transcript
derivation, since both derivations query the same challenge oracle. -/
theorem srSoundnessGame_eq_deriveTranscriptFS {n : ℕ} {pSpec : ProtocolSpec n}
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (P : Prover.StateRestoration.Soundness oSpec StmtIn pSpec) :
    srSoundnessGame P =
      (do
        let ⟨stmtIn, messages⟩ ← P
        let transcript ← messages.deriveTranscriptFS (oSpec := oSpec) stmtIn
        return ⟨transcript, stmtIn⟩) := by
  rfl

/-- The state-restoration knowledge-soundness game can likewise be read through the slow
Fiat-Shamir transcript derivation. -/
theorem srKnowledgeSoundnessGame_eq_deriveTranscriptFS {n : ℕ} {pSpec : ProtocolSpec n}
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitOut : Type}
    (P : Prover.StateRestoration.KnowledgeSoundness oSpec StmtIn WitOut pSpec) :
    srKnowledgeSoundnessGame P =
      (do
        let ⟨stmtIn, messages, witOut⟩ ← P
        let transcript ← messages.deriveTranscriptFS (oSpec := oSpec) stmtIn
        return ⟨transcript, stmtIn, witOut⟩) := by
  rfl

end StateRestoration

end Verifier

#print axioms ProtocolSpec.fsChallengeOracle_eq_srChallengeOracle
#print axioms ProtocolSpec.fsChallengeQueryImpl'_eq_srChallengeQueryImpl'
#print axioms ProtocolSpec.fsChallengeQueryImplState
#print axioms ProtocolSpec.fsChallengeQueryImplState_eq_fsChallengeQueryImpl'
#print axioms ProtocolSpec.fsChallengeQueryImplState_eq_srChallengeQueryImpl'
#print axioms ProtocolSpec.MessagesUpTo.deriveTranscriptFS_eq_deriveTranscriptSR
#print axioms ProtocolSpec.Messages.deriveTranscriptFS_eq_deriveTranscriptSR
#print axioms Verifier.fiatShamir_verify_eq_deriveTranscriptSR
#print axioms Verifier.StateRestoration.srSoundnessGame_eq_deriveTranscriptFS
#print axioms Verifier.StateRestoration.srKnowledgeSoundnessGame_eq_deriveTranscriptFS

end TranscriptAliases

section FiatShamirAdversaryAdapter

namespace Prover

namespace StateRestoration

variable {n : ℕ}
variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
variable {StmtIn WitIn StmtOut WitOut : Type}

/-- View a fixed malicious one-message Fiat-Shamir prover execution as the corresponding
state-restoration soundness prover payload.

The adapter runs the Fiat-Shamir prover's single prover-to-verifier message round and then replays
`P.output`, discarding the result. The replay is needed for the coupled soundness proof: the
one-message Fiat-Shamir `Reduction.run` performs the prover output step before verifier queries,
so the state-restoration adversary must make the same shared-oracle queries to keep the simulated
oracle-table state aligned. -/
def soundnessOfFiatShamirProver
    (P : Prover (oSpec + fsChallengeOracle StmtIn pSpec) StmtIn WitIn StmtOut WitOut
      (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (stmtIn : StmtIn) (witIn : WitIn) :
    Prover.StateRestoration.Soundness oSpec StmtIn pSpec := do
  let state := P.input (stmtIn, witIn)
  let ⟨proof, state⟩ ←
    P.sendMessage ⟨0, by simp⟩ state
  let _ctxOut ← P.output state
  let messages : pSpec.Messages := proof
  return ⟨stmtIn, messages⟩

/-- The state-restoration game for the Fiat-Shamir-prover adapter is exactly the single
Fiat-Shamir proof-message computation, the prover output replay, and the shared state-restoration
transcript derivation. Use `ProtocolSpec.Messages.deriveTranscriptFS_eq_deriveTranscriptSR` to
rewrite the final line through the slow Fiat-Shamir alias. -/
theorem srSoundnessGame_soundnessOfFiatShamirProver
    (P : Prover (oSpec + fsChallengeOracle StmtIn pSpec) StmtIn WitIn StmtOut WitOut
      (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (stmtIn : StmtIn) (witIn : WitIn) :
    srSoundnessGame
        (soundnessOfFiatShamirProver (oSpec := oSpec) (pSpec := pSpec) P stmtIn witIn)
      =
      (do
        let state := P.input (stmtIn, witIn)
        let ⟨proof, state⟩ ←
          P.sendMessage ⟨0, by simp⟩ state
        let _ctxOut ← P.output state
        let messages : pSpec.Messages := proof
        let transcript ← messages.deriveTranscriptSR (oSpec := oSpec) stmtIn
        return ⟨transcript, stmtIn⟩) := by
  simp [srSoundnessGame, soundnessOfFiatShamirProver]

/-- View a fixed malicious one-message Fiat-Shamir prover execution as the corresponding
state-restoration knowledge-soundness prover payload.

The adapter replays the Fiat-Shamir prover's output step after the proof-message round, preserving
the same final-state evolution while retaining only the output witness required by the
state-restoration knowledge game. -/
def knowledgeSoundnessOfFiatShamirProver
    (P : Prover (oSpec + fsChallengeOracle StmtIn pSpec) StmtIn WitIn StmtOut WitOut
      (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (stmtIn : StmtIn) (witIn : WitIn) :
    Prover.StateRestoration.KnowledgeSoundness oSpec StmtIn WitOut pSpec := do
  let state := P.input (stmtIn, witIn)
  let ⟨proof, state⟩ ← P.sendMessage ⟨0, by simp⟩ state
  let ctxOut ← P.output state
  let messages : pSpec.Messages := proof
  return ⟨stmtIn, messages, ctxOut.2⟩

/-- The state-restoration knowledge game for the Fiat-Shamir-prover adapter is exactly the single
Fiat-Shamir proof-message computation, followed by the prover output step and the shared
state-restoration transcript derivation. -/
theorem srKnowledgeSoundnessGame_knowledgeSoundnessOfFiatShamirProver
    (P : Prover (oSpec + fsChallengeOracle StmtIn pSpec) StmtIn WitIn StmtOut WitOut
      (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (stmtIn : StmtIn) (witIn : WitIn) :
    srKnowledgeSoundnessGame
        (knowledgeSoundnessOfFiatShamirProver (oSpec := oSpec) (pSpec := pSpec) P stmtIn witIn)
      =
      (do
        let state := P.input (stmtIn, witIn)
        let ⟨proof, state⟩ ←
          P.sendMessage ⟨0, by simp⟩ state
        let ctxOut ← P.output state
        let messages : pSpec.Messages := proof
        let transcript ← messages.deriveTranscriptSR (oSpec := oSpec) stmtIn
        return ⟨transcript, stmtIn, ctxOut.2⟩) := by
  simp [srKnowledgeSoundnessGame, knowledgeSoundnessOfFiatShamirProver]

end StateRestoration

end Prover

#print axioms Prover.StateRestoration.soundnessOfFiatShamirProver
#print axioms Prover.StateRestoration.srSoundnessGame_soundnessOfFiatShamirProver
#print axioms Prover.StateRestoration.knowledgeSoundnessOfFiatShamirProver
#print axioms Prover.StateRestoration.srKnowledgeSoundnessGame_knowledgeSoundnessOfFiatShamirProver

end FiatShamirAdversaryAdapter

section FiatShamirLiftPath

namespace Reduction

attribute [local instance] Reduction.fiatShamirChallengeOracleInterface

variable {n : ℕ}
variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι} {StmtIn α β : Type}

/-- Directly lifting a base Fiat-Shamir-oracle computation into the appended one-message
Fiat-Shamir protocol oracle spec is the same path as first lifting it into `OptionT` over the base
spec and then lifting that `OptionT` computation to the appended spec.

This names the lift-path coherence exposed by the #116 coupled soundness run expansion, where the
generic one-message `Reduction.run_of_prover_first` chooses the direct source-level path but
hand-written SR-transcript shapes naturally elaborate through the nested `OptionT` path. -/
theorem fiatShamir_liftM_base_to_append_eq_nested
    (oa : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) α) :
    (liftM oa :
        OptionT (OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) +
          [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α)
      =
      (liftM
        ((liftM oa :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) α)) :
        OptionT (OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) +
          [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α) := by
  rfl

/-- The inferred `liftM` path for an `OptionT` computation over the base Fiat-Shamir oracle spec
passes through the right-associated append before landing in the left-associated appended target.

This is the elaboration path exposed by the one-message `deriveTranscriptSR` run-shape expansion. -/
theorem fiatShamir_liftM_base_optionT_to_rightAssoc_to_append
    (oa : OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) α) :
    (liftM oa :
        OptionT (OracleComp
          ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α)
      =
    (liftM
        (liftM oa :
          OptionT (OracleComp
            (oSpec + (fsChallengeOracle StmtIn pSpec +
              [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))) α) :
        OptionT (OracleComp
          ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α) := by
  rfl

/-- Specialization of `OracleComp.liftM_OptionT_add_assoc_right` to the basic Fiat-Shamir appended
challenge spec. It collapses the right-associated lift path into the direct left-associated
`liftComp` path on the underlying `OptionT.run`. -/
theorem fiatShamir_liftM_rightAssoc_to_append_eq_direct
    (oa : OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) α) :
    (liftM
        (liftM oa :
          OptionT (OracleComp
            (oSpec + (fsChallengeOracle StmtIn pSpec +
              [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))) α) :
        OptionT (OracleComp
          ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α)
      =
      OptionT.mk (OracleComp.liftComp oa.run
        ((oSpec + fsChallengeOracle StmtIn pSpec) +
          [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) := by
  exact OracleComp.liftM_OptionT_add_assoc_right (spec₁ := oSpec)
    (spec₂ := fsChallengeOracle StmtIn pSpec)
    (spec₃ := [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)
    oa

/-- Combined Fiat-Shamir lift-path normalization for `OptionT` computations over the base
Fiat-Shamir oracle spec: the inferred append lift is the explicit direct `liftComp` of the
underlying `run`. -/
theorem fiatShamir_liftM_base_optionT_to_append_eq_direct
    (oa : OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) α) :
    (liftM oa :
        OptionT (OracleComp
          ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α)
      =
      OptionT.mk (OracleComp.liftComp oa.run
        ((oSpec + fsChallengeOracle StmtIn pSpec) +
          [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) := by
  rw [fiatShamir_liftM_base_optionT_to_rightAssoc_to_append]
  exact fiatShamir_liftM_rightAssoc_to_append_eq_direct oa

/-- Running the direct append-lift of a base Fiat-Shamir oracle computation is the explicit
`some`-map over the direct `liftComp` path into the appended one-message challenge spec. -/
theorem fiatShamir_liftM_oracleComp_to_append_run
    (oa : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) α) :
    ((liftM oa : OptionT (OracleComp
      ((oSpec + fsChallengeOracle StmtIn pSpec) +
        [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α).run) =
      (some <$> OracleComp.liftComp oa
        ((oSpec + fsChallengeOracle StmtIn pSpec) +
          [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) := by
  rw [fiatShamir_liftM_base_to_append_eq_nested oa]
  rw [fiatShamir_liftM_base_optionT_to_append_eq_direct
    (oa := (liftM oa : OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) α))]
  simp only [OptionT.run_mk]
  change OracleComp.liftComp (some <$> oa)
      ((oSpec + fsChallengeOracle StmtIn pSpec) +
        [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ) =
    some <$> OracleComp.liftComp oa
      ((oSpec + fsChallengeOracle StmtIn pSpec) +
        [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)
  rw [OracleComp.liftComp_map]

/-- Appended-spec lift/getM collapse for a mapped base `OptionT` computation. This is the
right-associated analogue of the completeness helper used by the one-message run-shape proof. -/
theorem fiatShamir_lift_run_map_getM_to_append
    (X : OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) β)
    (f : β → α) :
    ((liftM X.run :
        OptionT (OracleComp
          ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) (Option β)) >>=
        fun o => f <$> (o.getM : OptionT (OracleComp
          ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) β)) =
      (f <$> (liftM X : OptionT (OracleComp
        ((oSpec + fsChallengeOracle StmtIn pSpec) +
          [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) β) :
        OptionT (OracleComp
          ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α) := by
  apply OptionT.ext
  simp only [OptionT.run_bind, OptionT.run_map]
  rw [fiatShamir_liftM_oracleComp_to_append_run (oa := X.run)]
  rw [congrArg OptionT.run (fiatShamir_liftM_base_optionT_to_append_eq_direct X)]
  simp only [OptionT.run_mk, Option.elimM, bind_assoc, map_eq_pure_bind, pure_bind]
  refine bind_congr ?_
  intro x
  cases x <;> rfl

/-- Appended-spec lift/getM collapse for a base `OptionT` computation. -/
theorem fiatShamir_lift_run_bind_getM_to_append
    (X : OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) α) :
    ((liftM X.run :
        OptionT (OracleComp
          ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) (Option α)) >>=
        fun o => (o.getM : OptionT (OracleComp
          ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α)) =
      (liftM X : OptionT (OracleComp
        ((oSpec + fsChallengeOracle StmtIn pSpec) +
          [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α) := by
  apply OptionT.ext
  simp only [OptionT.run_bind]
  rw [fiatShamir_liftM_oracleComp_to_append_run (oa := X.run)]
  rw [congrArg OptionT.run (fiatShamir_liftM_base_optionT_to_append_eq_direct X)]
  simp only [OptionT.run_mk, Option.elimM, bind_assoc, map_eq_pure_bind, pure_bind]
  conv_rhs =>
    rw [← bind_pure (OracleComp.liftComp X.run
      ((oSpec + fsChallengeOracle StmtIn pSpec) +
        [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))]
  congr 1
  funext x
  cases x <;> rfl

/-- Same appended-spec `getM` collapse, with the continuation written as `Option.getM`. -/
theorem fiatShamir_lift_run_Option_getM_to_append
    (X : OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) α) :
    ((liftM X.run :
        OptionT (OracleComp
          ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) (Option α)) >>=
        Option.getM) =
      (liftM X : OptionT (OracleComp
        ((oSpec + fsChallengeOracle StmtIn pSpec) +
          [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) α) := by
  exact fiatShamir_lift_run_bind_getM_to_append X

end Reduction

#print axioms Reduction.fiatShamir_liftM_base_to_append_eq_nested
#print axioms Reduction.fiatShamir_liftM_base_optionT_to_rightAssoc_to_append
#print axioms Reduction.fiatShamir_liftM_rightAssoc_to_append_eq_direct
#print axioms Reduction.fiatShamir_liftM_base_optionT_to_append_eq_direct
#print axioms Reduction.fiatShamir_liftM_oracleComp_to_append_run
#print axioms Reduction.fiatShamir_lift_run_map_getM_to_append
#print axioms Reduction.fiatShamir_lift_run_bind_getM_to_append
#print axioms Reduction.fiatShamir_lift_run_Option_getM_to_append

end FiatShamirLiftPath

section CoupledQueryImpl

namespace Reduction

variable {n : ℕ}
variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
  [∀ i, SampleableType (pSpec.Challenge i)]

/-- The concrete query implementation used by the coupled #116 soundness proof: original oracle
queries are interpreted by the state-restoration implementation, while Fiat-Shamir challenge
queries read the same cached challenge table that state restoration samples as its initial state. -/
def fiatShamirCoupledQueryImpl
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp)) :
    QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec)
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp) :=
  srImpl.addLift (ProtocolSpec.fsChallengeQueryImplState (Statement := StmtIn) (pSpec := pSpec))

/-- Original-oracle queries through the coupled Fiat-Shamir implementation are exactly the
state-restoration implementation queries. -/
@[simp]
theorem fiatShamirCoupledQueryImpl_apply_left
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (q : oSpec.Domain) :
    fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn)
        srImpl (.inl q) =
      srImpl q := by
  rfl

/-- Fiat-Shamir challenge queries through the coupled implementation read the cached challenge
table and leave it unchanged. -/
@[simp]
theorem fiatShamirCoupledQueryImpl_apply_right
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (q : (fsChallengeOracle StmtIn pSpec).Domain) :
    fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn)
        srImpl (.inr q) =
      (fun f => pure (f q, f)) := by
  rfl

/-- The coupled implementation is exactly the original-oracle implementation plus the fixed-state
cached Fiat-Shamir challenge implementation. This is the `addLift` form consumed by generic
simulation lemmas. -/
theorem fiatShamirCoupledQueryImpl_eq_addLift_fsChallengeQueryImplState
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp)) :
    fiatShamirCoupledQueryImpl (pSpec := pSpec) (StmtIn := StmtIn) srImpl =
      srImpl.addLift
        (ProtocolSpec.fsChallengeQueryImplState (Statement := StmtIn) (pSpec := pSpec)) := by
  rfl

/-- Simulating a lifted original-oracle computation through the coupled Fiat-Shamir implementation
projects to the original state-restoration implementation. -/
theorem simulateQ_fiatShamirCoupled_liftComp_left
    {α : Type}
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (oa : OracleComp oSpec α) :
    simulateQ
        (fiatShamirCoupledQueryImpl (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
        (OracleComp.liftComp oa (oSpec + fsChallengeOracle StmtIn pSpec)) =
      simulateQ srImpl oa := by
  simpa [fiatShamirCoupledQueryImpl, QueryImpl.addLift_def] using
    (QueryImpl.simulateQ_add_liftComp_left
      (impl₁' := srImpl)
      (impl₂' := ProtocolSpec.fsChallengeQueryImplState
        (Statement := StmtIn) (pSpec := pSpec))
      (oa := oa))

/-- `liftM` form of `simulateQ_fiatShamirCoupled_liftComp_left`. -/
theorem simulateQ_fiatShamirCoupled_liftM_left
    {α : Type}
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (oa : OracleComp oSpec α) :
    simulateQ
        (fiatShamirCoupledQueryImpl (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
        (liftM oa : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) α) =
      simulateQ srImpl oa := by
  rw [show (liftM oa : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) α) =
      OracleComp.liftComp oa (oSpec + fsChallengeOracle StmtIn pSpec) by
        rw [OracleComp.liftComp_eq_liftM]]
  exact simulateQ_fiatShamirCoupled_liftComp_left srImpl oa

end Reduction

#print axioms Reduction.fiatShamirCoupledQueryImpl
#print axioms Reduction.fiatShamirCoupledQueryImpl_apply_left
#print axioms Reduction.fiatShamirCoupledQueryImpl_apply_right
#print axioms Reduction.fiatShamirCoupledQueryImpl_eq_addLift_fsChallengeQueryImplState
#print axioms Reduction.simulateQ_fiatShamirCoupled_liftComp_left
#print axioms Reduction.simulateQ_fiatShamirCoupled_liftM_left

end CoupledQueryImpl

namespace Reduction

variable {n : ℕ}
variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

attribute [local instance 10000] Reduction.fiatShamirNoChallengeSampleable

section CanonicalSoundness

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {WitIn' WitOut' : Type}

local instance fiatShamirProverOnlyCanonicalSoundness : ProtocolSpec.ProverOnly
    (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)) where
  prover_first' := by simp

private theorem stateT_option_map_elim_some {σ α β : Type}
    (mx : StateT σ ProbComp (Option α)) (f : α → β) :
    (do
        let x ← some <$> mx
        x.elim (pure none) fun x => pure (Option.map f x)) =
      (Option.map f <$> mx) := by
  ext s
  simp only [StateT.run_bind, StateT.run_map]
  rw [map_eq_pure_bind]
  simp only [bind_assoc, pure_bind]
  conv_rhs => rw [map_eq_pure_bind]
  congr 1

private theorem simulateQ_optionT_map_monadLift_run
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {σ α β : Type}
    (impl : QueryImpl (spec₁ + spec₂) (StateT σ ProbComp))
    (X : OptionT (OracleComp spec₁) α) (f : α → β) :
    (do
        let x ← simulateQ impl
          (monadLift
            (some <$> (monadLift X.run : OracleComp (spec₁ + spec₂) (Option α))) :
              OracleComp (spec₁ + spec₂) (Option (Option α)))
        x.elim (pure none) fun x => pure (Option.map f x)) =
      simulateQ impl
        ((f <$> (monadLift X : OptionT (OracleComp (spec₁ + spec₂)) α)).run) := by
  rw [show
      simulateQ impl
          (monadLift
            (some <$> (monadLift X.run : OracleComp (spec₁ + spec₂) (Option α))) :
              OracleComp (spec₁ + spec₂) (Option (Option α))) =
        (some <$> simulateQ impl
          (monadLift X.run : OracleComp (spec₁ + spec₂) (Option α))) by
    rw [← simulateQ_map]
    rfl]
  rw [stateT_option_map_elim_some]
  rw [OptionT.run_map, optionT_monadLift_run, simulateQ_map]

private theorem probEvent_optionT_stateT_init
    {σ α : Type} (init : ProbComp σ) (comp : StateT σ ProbComp (Option α))
    (p : α → Prop) :
    Pr[p | (do
        let s ← OptionT.mk (some <$> init)
        OptionT.mk ((fun x : Option α × σ => x.1) <$> comp.run s) : OptionT ProbComp α)] =
      Pr[fun o : Option α => o.elim False p |
        do
          let s ← init
          (fun x : Option α × σ => x.1) <$> comp.run s] := by
  rw [show
      (do
        let s ← OptionT.mk (some <$> init)
        OptionT.mk ((fun x : Option α × σ => x.1) <$> comp.run s) : OptionT ProbComp α) =
      OptionT.mk (do
        let s ← init
        (fun x : Option α × σ => x.1) <$> comp.run s) by
    apply OptionT.ext
    simp only [OptionT.run_bind, OptionT.run_mk, Option.elimM, bind_assoc, map_bind,
      Option.elim_some, pure_bind]
    rw [map_eq_pure_bind]
    simp only [bind_assoc, pure_bind, Option.elim_some]]
  exact Verifier.StateFunction.probEvent_optionT_mk_eq_elim _ _

private theorem probEvent_payload_option_eq_stmt
    {σ Payload StmtIn StmtOut : Type}
    (stmtIn : StmtIn) (langIn : Set StmtIn) (langOut : Set StmtOut)
    (hstmtIn : stmtIn ∉ langIn)
    (payload : Payload) (mx : StateT σ ProbComp (Option StmtOut)) (s : σ) :
    Pr[fun o : Option (Payload × StmtOut) =>
        o.elim False fun x => x.2 ∈ langOut |
      (fun x : Option (Payload × StmtOut) × σ => x.1) <$>
        ((Option.map (Prod.mk payload) <$> mx).run s)] =
    Pr[(fun x : StmtIn × Option StmtOut =>
        match x with
        | (stmtIn, some stmtOut) => stmtOut ∈ langOut ∧ stmtIn ∉ langIn
        | _ => False) |
      (fun x : Option StmtOut × σ => (stmtIn, x.1)) <$> mx.run s] := by
  simp only [StateT.run_map, probEvent_map, Function.comp_apply]
  rw [probEvent_eq_tsum_indicator, probEvent_eq_tsum_indicator]
  apply tsum_congr
  intro x
  rcases x with ⟨stmtOut?, s'⟩
  cases stmtOut? with
  | none => simp
  | some stmtOut =>
      by_cases hOut : stmtOut ∈ langOut <;> simp [hOut, hstmtIn]

private theorem probEvent_stateT_bind_fst_mono_hetero
    {σ α β γ : Type}
    (mx : StateT σ ProbComp α) (my : α → StateT σ ProbComp (Option β))
    (oc : α → σ → ProbComp γ) (s : σ)
    (p : Option β → Prop) (q : γ → Prop)
    (h : ∀ a s', (a, s') ∈ support (mx.run s) →
      Pr[ p | (fun x : Option β × σ => x.1) <$> (my a).run s'] ≤
        Pr[ q | oc a s']) :
    Pr[ p | (fun x : Option β × σ => x.1) <$> (mx >>= my).run s] ≤
      Pr[ q | do
        let a ← mx.run s
        oc a.1 a.2] := by
  rw [StateT.run_bind, map_bind]
  exact Verifier.StateFunction.probEvent_bind_mono_heteroEvent
    (fun a ha => h a.1 a.2 ha)

/-- Fused-predicate (no projection) variant of the StateT peel: compare two `StateT` computations
sharing a prefix `mx`, with hetero events on the full (value, state) pairs. -/
private theorem probEvent_stateT_bind_mono_hetero
    {σ α β₁ β₂ : Type}
    (mx : StateT σ ProbComp α) (my : α → StateT σ ProbComp β₁)
    (mz : α → StateT σ ProbComp β₂)
    (p : β₁ × σ → Prop) (q : β₂ × σ → Prop) (s : σ)
    (h : ∀ a s', (a, s') ∈ support (mx.run s) →
      Pr[ p | (my a).run s'] ≤ Pr[ q | (mz a).run s']) :
    Pr[ p | (mx >>= my).run s] ≤ Pr[ q | (mx >>= mz).run s] := by
  rw [StateT.run_bind, StateT.run_bind]
  exact Verifier.StateFunction.probEvent_bind_mono_heteroEvent
    (fun a ha => h a.1 a.2 ha)

/-- Explicit one-message Fiat-Shamir adversary execution after the empty transformed challenge
oracle has been collapsed. The payload retains the proof transcript and prover output context so
it can be compared directly with the state-restoration adapter. -/
def fiatShamirAdversaryExecution
    (P : Prover (oSpec + fsChallengeOracle StmtIn pSpec) StmtIn WitIn' StmtOut WitOut'
      (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn') :
    OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
      (((Reduction.FiatShamirProofTranscript (pSpec := pSpec) × StmtOut × WitOut') ×
        StmtOut)) := do
  let state := P.input (stmtIn, witIn)
  let ⟨proofMessages, state⟩ ← P.sendMessage ⟨0, by simp⟩ state
  let ctxOut ← P.output state
  let proof : Reduction.FiatShamirProofTranscript (pSpec := pSpec) := fun
    | ⟨0, _⟩ => proofMessages
  let transcript ←
    (liftM (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn proofMessages) :
      OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) pSpec.FullTranscript)
  let stmtOut ←
    (monadLift (V.verify stmtIn transcript) :
      OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut)
  return ⟨⟨proof, ctxOut⟩, stmtOut⟩

/-- Collapse the one-message transformed Fiat-Shamir reduction run to the explicit adversary
execution over `oSpec + fsChallengeOracle`. -/
theorem fiatShamirAdversary_runCollapse
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (P : Prover (oSpec + fsChallengeOracle StmtIn pSpec) StmtIn WitIn' StmtOut WitOut'
      (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn') :
    simulateQ (QueryImpl.addLift impl challengeQueryImpl)
        (Reduction.run stmtIn witIn { prover := P, verifier := V.fiatShamir }).run =
      simulateQ impl (fiatShamirAdversaryExecution P V stmtIn witIn).run := by
  rw [Reduction.run_of_prover_first
    (pSpec := Reduction.FiatShamirProtocolSpec (pSpec := pSpec))]
  unfold fiatShamirAdversaryExecution
  simp only [Verifier.fiatShamir, Verifier.run,
    liftComp_eq_liftM, bind_assoc, pure_bind, monadLift_bind, monadLift_pure, map_bind,
    bind_pure_comp, liftM_map, liftM_optionT_combined, bind_map_left,
    monadLift_optionT_lift_run_map_getM]
  simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self, liftM_eq_monadLift,
    OptionT.run_bind, OptionT.run_monadLift, OptionT.run_mk, optionT_monadLift_run,
    simulateQ_bind, simulateQ_map, simulateQ_pure, simulateQ_addLift_liftM,
    OptionT.simulateQ_addLift_liftM, Option.getM_map_run, Option.elimM,
    simulateQ_option_elim, bind_assoc, pure_bind, map_bind,
    simulateQ_getM_run_some, OptionT.simulateQ_getM_some, StateT.run_simulateQ_optiont_map,
    StateT.run_pure_some_bind_map, Option.map_comp_lambda, simulateQ_map_monadLift_getM_run,
    optionT_run_simulateQ_liftquery, OptionT.run_monadLift]
  have hVerify (td : pSpec.FullTranscript) :
      simulateQ impl (OptionT.run (simulateQ (fun t : oSpec.Domain =>
          (liftM (OracleSpec.query (spec := oSpec) t) :
            OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (oSpec.Range t)))
          (V.verify stmtIn td))) =
        simulateQ impl (liftM (V.verify stmtIn td).run) := by
    congr 1
  apply bind_congr
  intro proofState?
  cases proofState? with
  | none => rfl
  | some proofState =>
      apply bind_congr
      intro ctxOut?
      cases ctxOut? with
      | none => rfl
      | some ctxOut =>
          apply bind_congr
          intro transcript?
          cases transcript? with
          | none => rfl
          | some transcript =>
              let proof : Reduction.FiatShamirProofTranscript (pSpec := pSpec) := fun
                | ⟨0, _⟩ => proofState.1
              simpa [liftM_eq_monadLift, proof] using
                (simulateQ_optionT_map_monadLift_run
                  (impl := impl)
                  (X := V.verify stmtIn transcript)
                  (f := fun stmtOut : StmtOut =>
                    Prod.mk (Prod.mk proof ctxOut) stmtOut))

set_option linter.flexible false in
/-- Canonical coupled state-restoration soundness implies basic Fiat-Shamir soundness when both
games use the same sampled cached Fiat-Shamir challenge table. -/
theorem fiatShamir_soundnessTransferResidual_canonical
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (soundnessError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    fiatShamir_soundnessTransferResidual srInit srImpl srInit
      (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
      langIn langOut soundnessError V := by
  intro hSR WitIn' WitOut' witIn prover stmtIn hstmtIn
  have h :=
    hSR (Prover.StateRestoration.soundnessOfFiatShamirProver
      (oSpec := oSpec) (pSpec := pSpec) prover stmtIn witIn)
  dsimp only
  rw [fiatShamirAdversary_runCollapse
    (impl := fiatShamirCoupledQueryImpl
      (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
    (P := prover) (V := V) (stmtIn := stmtIn) (witIn := witIn)]
  refine le_trans ?_ h
  simp [Verifier.soundness, Verifier.StateRestoration.soundness,
    fiatShamirAdversaryExecution, fiatShamirCoupledQueryImpl,
    ProtocolSpec.fsChallengeQueryImplState_eq_srChallengeQueryImpl',
    probEvent_optionT_stateT_init,
    probEvent_payload_option_eq_stmt,
    Verifier.StateFunction.probEvent_optionT_mk_eq_elim, hstmtIn,
    probEvent_map, map_bind, Functor.map_map, Function.comp,
    StateT.run_bind, StateT.run_map, liftM_eq_monadLift,
    Prover.StateRestoration.soundnessOfFiatShamirProver,
    Verifier.StateRestoration.srSoundnessGame_eq_deriveTranscriptFS,
    Verifier.fiatShamir_verify_eq,
    Reduction.fiatShamir, Prover.fiatShamir, Verifier.fiatShamir,
    Reduction.run, Prover.run, Prover.runToRound, Prover.processRound]
  refine Verifier.StateFunction.probEvent_bind_mono_heteroEvent (fun table _ => ?_)
  rw [← ProtocolSpec.fsChallengeQueryImplState_eq_srChallengeQueryImpl'
    (Statement := StmtIn) (pSpec := pSpec)]
  refine probEvent_stateT_bind_fst_mono_hetero
    (mx := simulateQ
      (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
      (prover.sendMessage
        (⟨0, by simp⟩ :
          (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).MessageIdx)
        (prover.input (stmtIn, witIn))))
    (my := fun proofState => do
      let ctxOut ← simulateQ
        (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
        (prover.output proofState.2)
      let transcript ← simulateQ
        (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
        (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn proofState.1)
      let proof : Reduction.FiatShamirProofTranscript (pSpec := pSpec) := fun
        | ⟨0, _⟩ => proofState.1
      Option.map (Prod.mk (Prod.mk proof ctxOut)) <$>
        simulateQ
          (fiatShamirCoupledQueryImpl
            (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
          (OptionT.run (simulateQ (fun t : oSpec.Domain =>
            (monadLift (OracleSpec.query (spec := oSpec) t) :
              OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (oSpec.Range t)))
            (V.verify stmtIn transcript))))
    (oc := fun proofState table => do
      let ctxOut ← StateT.run (simulateQ
        (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
        (prover.output proofState.2) :
          StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp
            (StmtOut × WitOut')) table
      let transcript ← StateT.run (simulateQ
        (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
        (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn proofState.1) :
          StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp
            pSpec.FullTranscript) ctxOut.2
      (fun a : Option StmtOut × QueryImpl (fsChallengeOracle StmtIn pSpec) Id =>
          (stmtIn, a.1)) <$>
        StateT.run (simulateQ
          (fiatShamirCoupledQueryImpl
            (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
          (liftM (Verifier.run stmtIn transcript.1 V).run :
            OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut)) :
          StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp
            (Option StmtOut)) transcript.2)
    (p := fun o :
        Option ((Reduction.FiatShamirProofTranscript (pSpec := pSpec) ×
          (StmtOut × WitOut')) × StmtOut) =>
      o.elim False fun x => x.2 ∈ langOut)
    (q := fun x : StmtIn × Option StmtOut =>
      match x with
      | (stmtIn, some stmtOut) => stmtOut ∈ langOut ∧ stmtIn ∉ langIn
      | _ => False)
    (s := table) ?_
  intro proofState table' _
  refine probEvent_stateT_bind_fst_mono_hetero
    (mx := simulateQ
      (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
      (prover.output proofState.2))
    (my := fun ctxOut => do
      let transcript ← simulateQ
        (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
        (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn proofState.1)
      let proof : Reduction.FiatShamirProofTranscript (pSpec := pSpec) := fun
        | ⟨0, _⟩ => proofState.1
      Option.map (Prod.mk (Prod.mk proof ctxOut)) <$>
        simulateQ
          (fiatShamirCoupledQueryImpl
            (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
          (OptionT.run (simulateQ (fun t : oSpec.Domain =>
            (monadLift (OracleSpec.query (spec := oSpec) t) :
              OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (oSpec.Range t)))
            (V.verify stmtIn transcript))))
    (oc := fun _ctxOut table => do
      let transcript ← StateT.run (simulateQ
        (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
        (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn proofState.1) :
          StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp
            pSpec.FullTranscript) table
      (fun a : Option StmtOut × QueryImpl (fsChallengeOracle StmtIn pSpec) Id =>
          (stmtIn, a.1)) <$>
        StateT.run (simulateQ
          (fiatShamirCoupledQueryImpl
            (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
          (liftM (Verifier.run stmtIn transcript.1 V).run :
            OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut)) :
          StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp
            (Option StmtOut)) transcript.2)
    (p := fun o :
        Option ((Reduction.FiatShamirProofTranscript (pSpec := pSpec) ×
          (StmtOut × WitOut')) × StmtOut) =>
      o.elim False fun x => x.2 ∈ langOut)
    (q := fun x : StmtIn × Option StmtOut =>
      match x with
      | (stmtIn, some stmtOut) => stmtOut ∈ langOut ∧ stmtIn ∉ langIn
      | _ => False)
    (s := table') ?_
  intro ctxOut table'' _
  refine probEvent_stateT_bind_fst_mono_hetero
    (mx := simulateQ
      (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
      (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn proofState.1))
    (my := fun transcript => do
      let proof : Reduction.FiatShamirProofTranscript (pSpec := pSpec) := fun
        | ⟨0, _⟩ => proofState.1
      Option.map (Prod.mk (Prod.mk proof ctxOut)) <$>
        simulateQ
          (fiatShamirCoupledQueryImpl
            (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
          (OptionT.run (simulateQ (fun t : oSpec.Domain =>
            (monadLift (OracleSpec.query (spec := oSpec) t) :
              OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (oSpec.Range t)))
            (V.verify stmtIn transcript))))
    (oc := fun transcript table => do
      (fun a : Option StmtOut × QueryImpl (fsChallengeOracle StmtIn pSpec) Id =>
          (stmtIn, a.1)) <$>
        StateT.run (simulateQ
          (fiatShamirCoupledQueryImpl
            (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
          (liftM (Verifier.run stmtIn transcript V).run :
            OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut)) :
          StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp
            (Option StmtOut)) table)
    (p := fun o :
        Option ((Reduction.FiatShamirProofTranscript (pSpec := pSpec) ×
          (StmtOut × WitOut')) × StmtOut) =>
      o.elim False fun x => x.2 ∈ langOut)
    (q := fun x : StmtIn × Option StmtOut =>
      match x with
      | (stmtIn, some stmtOut) => stmtOut ∈ langOut ∧ stmtIn ∉ langIn
      | _ => False)
    (s := table'') ?_
  intro transcript table''' _
  let proof : Reduction.FiatShamirProofTranscript (pSpec := pSpec) := fun
    | ⟨0, _⟩ => proofState.1
  have hVerify :
      (simulateQ
          (fiatShamirCoupledQueryImpl
            (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
          (OptionT.run (simulateQ (fun t : oSpec.Domain =>
            (monadLift (OracleSpec.query (spec := oSpec) t) :
              OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (oSpec.Range t)))
            (V.verify stmtIn transcript))) :
        StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp (Option StmtOut)) =
        (simulateQ
          (fiatShamirCoupledQueryImpl
            (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
          (liftM (Verifier.run stmtIn transcript V).run :
            OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut)) :
        StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp (Option StmtOut)) := by
    congr 1
  exact le_of_eq (by
    simpa [proof, hVerify.symm] using
      (probEvent_payload_option_eq_stmt
        (stmtIn := stmtIn) (langIn := langIn) (langOut := langOut)
        (hstmtIn := hstmtIn) (payload := (proof, ctxOut))
        (mx := simulateQ
          (fiatShamirCoupledQueryImpl
            (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
          (OptionT.run (simulateQ (fun t : oSpec.Domain =>
            (monadLift (OracleSpec.query (spec := oSpec) t) :
              OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (oSpec.Range t)))
            (V.verify stmtIn transcript))))
        (s := table''')))

#print axioms Reduction.fiatShamirAdversary_runCollapse
#print axioms Reduction.fiatShamir_soundnessTransferResidual_canonical

/-- Direct canonical basic Fiat-Shamir soundness transfer for the shared cached challenge table. -/
theorem fiatShamir_soundness_of_stateRestoration_canonical
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (soundnessError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hSR : Verifier.StateRestoration.soundness srInit srImpl
      langIn langOut V soundnessError) :
    Verifier.soundness srInit
      (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
      langIn langOut V.fiatShamir soundnessError := by
  classical
  exact fiatShamir_soundness_of_stateRestoration srInit srImpl srInit
    (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
    langIn langOut soundnessError V
    (fiatShamir_soundnessTransferResidual_canonical srInit srImpl langIn langOut
      soundnessError V)
    hSR

#print axioms Reduction.fiatShamir_soundness_of_stateRestoration_canonical

end CanonicalSoundness

section CanonicalKnowledgeSoundnessSupport

/-- Pop the next challenge response for the expected round from a slow-Fiat-Shamir challenge log.

The parser only checks the challenge-round index.  In the honest verifier log generated by
`Verifier.fiatShamir`, the query payload itself is produced by `deriveTranscriptFS`; checking the
full payload would require unnecessary equality assumptions on messages and statements. -/
private def popFSChallengeFromLog
    (expected : pSpec.ChallengeIdx) :
    StateT (QueryLog (fsChallengeOracle StmtIn pSpec)) Option
      (pSpec.Challenge expected) := fun log =>
  match log with
  | [] => none
  | ⟨⟨idx, _payload⟩, response⟩ :: rest =>
      if h : idx = expected then
        some (by cases h; exact response, rest)
      else
        none

/-- Reconstruct a partial transcript from proof messages and the verifier's logged
Fiat-Shamir-challenge responses. -/
private def transcriptFromFSChallengeLogAux
    (k : Fin (n + 1)) (messages : pSpec.MessagesUpTo k) (j : Fin (k + 1)) :
    StateT (QueryLog (fsChallengeOracle StmtIn pSpec)) Option
      (pSpec.Transcript (j.castLE (by omega))) :=
  Fin.induction
    (pure (fun i => i.elim0))
    (fun i ih => do
      let prevTranscript ← ih
      match hDir : pSpec.dir (i.castLE (by omega)) with
      | .V_to_P =>
          let challenge ← popFSChallengeFromLog
            (StmtIn := StmtIn) (pSpec := pSpec) ⟨i.castLE (by omega), hDir⟩
          pure (prevTranscript.concat challenge)
      | .P_to_V =>
          pure (prevTranscript.concat (messages ⟨i, hDir⟩)))
    j

/-- Reconstruct the underlying public-coin transcript from one-message Fiat-Shamir proof messages
and the verifier-side slow-Fiat-Shamir challenge log.  Malformed logs return `none`. -/
private def transcriptFromFSChallengeLog
    (messages : pSpec.Messages)
    (log : QueryLog (fsChallengeOracle StmtIn pSpec)) :
    Option pSpec.FullTranscript := do
  let parsed ← (transcriptFromFSChallengeLogAux
    (StmtIn := StmtIn) (pSpec := pSpec)
    (k := Fin.last n) messages (Fin.last (Fin.last n))).run' log
  pure (by exact parsed)

private theorem run_simulateQ_loggingOracle_query
    {ι : Type} {spec : OracleSpec ι} (q : spec.Domain) :
    (simulateQ loggingOracle (liftM (OracleSpec.query (spec := spec) q))).run =
      (fun u : spec.Range q =>
          (u, ([⟨q, u⟩] : QueryLog spec))) <$>
        (liftM (OracleSpec.query (spec := spec) q) : OracleComp spec (spec.Range q)) := by
  simpa using
    (OracleComp.run_simulateQ_loggingOracle_query_bind
      (spec := spec) (t := q) (mx := fun u : spec.Range q => pure u))

private theorem queryLog_snd_append
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (log₁ log₂ : QueryLog (spec₁ + spec₂)) :
    (log₁ ++ log₂).snd = log₁.snd ++ log₂.snd := by
  induction log₁ with
  | nil => rfl
  | cons entry tail _ih =>
      cases entry with
      | mk q r =>
          cases q <;> simp [QueryLog.snd]

private theorem queryLog_snd_singleton_inr
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (q : spec₂.Domain) (r : spec₂.Range q) :
    QueryLog.snd
        ([⟨(.inr q : (spec₁ + spec₂).Domain), r⟩] :
          QueryLog (spec₁ + spec₂)) = [⟨q, r⟩] := by
  simp [QueryLog.snd]

private theorem queryLog_snd_singleton_inl
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (q : spec₁.Domain) (r : spec₁.Range q) :
    QueryLog.snd
        ([⟨(.inl q : (spec₁ + spec₂).Domain), r⟩] :
          QueryLog (spec₁ + spec₂)) = ([] : QueryLog spec₂) := by
  simp [QueryLog.snd]

private theorem queryLog_snd_cons_inr
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (q : spec₂.Domain) (r : spec₂.Range q)
    (log : QueryLog (spec₁ + spec₂)) :
    QueryLog.snd (⟨(.inr q : (spec₁ + spec₂).Domain), r⟩ :: log) =
      ⟨q, r⟩ :: log.snd := by
  simp [QueryLog.snd]

private theorem queryLog_snd_cons_inl
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (q : spec₁.Domain) (r : spec₁.Range q)
    (log : QueryLog (spec₁ + spec₂)) :
    QueryLog.snd (⟨(.inl q : (spec₁ + spec₂).Domain), r⟩ :: log) = log.snd := by
  simp [QueryLog.snd]

private theorem queryLog_snd_inl
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (log : QueryLog spec₁) :
    QueryLog.snd (QueryLog.inl (spec₂ := spec₂) log) = ([] : QueryLog spec₂) := by
  induction log with
  | nil => rfl
  | cons entry tail ih =>
      cases entry with
      | mk q r =>
          simp [QueryLog.inl, QueryLog.snd]

private theorem queryLog_snd_inl_append_left
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (leftLog : QueryLog spec₁) (log : QueryLog (spec₁ + spec₂)) :
    QueryLog.snd (QueryLog.inl (spec₂ := spec₂) leftLog ++ log) = log.snd := by
  rw [queryLog_snd_append, queryLog_snd_inl]
  rfl

private theorem queryLog_snd_append_inl_right
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (log : QueryLog (spec₁ + spec₂)) (rightLog : QueryLog spec₁) :
    QueryLog.snd (log ++ QueryLog.inl (spec₂ := spec₂) rightLog) = log.snd := by
  rw [queryLog_snd_append, queryLog_snd_inl]
  simp

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] in
private theorem popFSChallengeFromLog_cons_self
    (idx : pSpec.ChallengeIdx)
    (payload : (challengeOracleInterfaceSR StmtIn pSpec idx).Query)
    (response : pSpec.Challenge idx)
    (tail : QueryLog (fsChallengeOracle StmtIn pSpec)) :
    (popFSChallengeFromLog (StmtIn := StmtIn) (pSpec := pSpec) idx).run
      (⟨⟨idx, payload⟩, response⟩ :: tail) =
        some (response, tail) := by
  unfold popFSChallengeFromLog
  change (if h : idx = idx then some (by cases h; exact response, tail) else none) =
    some (response, tail)
  simp

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Every support point of `deriveTranscriptSRAux.withQueryLog` can be replayed by the
Fiat-Shamir challenge-log parser.  The parser consumes exactly the slow-Fiat-Shamir projection of
the logged derivation and leaves the supplied tail untouched. -/
private theorem transcriptFromFSChallengeLogAux_run_withQueryLog_snd_support
    (stmtIn : StmtIn) (k : Fin (n + 1)) (messages : pSpec.MessagesUpTo k)
    (j : Fin (k + 1)) (tail : QueryLog (fsChallengeOracle StmtIn pSpec))
    {z : pSpec.Transcript (j.castLE (Nat.succ_le_of_lt k.isLt)) ×
      QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)}
    (hz : z ∈ support
      (OracleComp.withQueryLog
        (ProtocolSpec.MessagesUpTo.deriveTranscriptSRAux
          (oSpec := oSpec) stmtIn k messages j))) :
    (transcriptFromFSChallengeLogAux
        (StmtIn := StmtIn) (pSpec := pSpec) k messages j).run (z.2.snd ++ tail) =
      some (z.1, tail) := by
  induction j using Fin.induction generalizing tail with
  | zero =>
      simp only [ProtocolSpec.MessagesUpTo.deriveTranscriptSRAux, Fin.induction_zero,
        OracleComp.withQueryLog_pure, mem_support_pure_iff] at hz
      subst z
      simp [transcriptFromFSChallengeLogAux, QueryLog.snd]
  | succ i ih =>
      simp only [ProtocolSpec.MessagesUpTo.deriveTranscriptSRAux,
        transcriptFromFSChallengeLogAux, Fin.induction_succ] at hz ⊢
      split
      · next hDir =>
          rw [OracleComp.withQueryLog_bind, mem_support_bind_iff] at hz
          obtain ⟨pref, hpref, hcont⟩ := hz
          rw [support_map, Set.mem_image] at hcont
          obtain ⟨contPoint, hcontPoint, houterEq⟩ := hcont
          rcases contPoint with ⟨contTranscript, contLog⟩
          split at hcontPoint
          · next hDir' =>
              have hDirProof : hDir' = hDir := Subsingleton.elim _ _
              cases hDirProof
              let q : (fsChallengeOracle StmtIn pSpec).Domain :=
                ⟨⟨i.castLE (by omega), hDir⟩, (stmtIn, messages.take i.castSucc)⟩
              rw [OracleComp.withQueryLog_bind, mem_support_bind_iff] at hcontPoint
              obtain ⟨challenge, hchallenge, hpure⟩ := hcontPoint
              change challenge ∈ support
                ((liftM (OracleSpec.query
                    (spec := oSpec + fsChallengeOracle StmtIn pSpec) (.inr q)) :
                    OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
                      ((fsChallengeOracle StmtIn pSpec).Range q)).withQueryLog) at hchallenge
              have hqueryEq :
                  ((liftM (OracleSpec.query
                      (spec := oSpec + fsChallengeOracle StmtIn pSpec) (.inr q)) :
                      OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
                        ((fsChallengeOracle StmtIn pSpec).Range q)).withQueryLog)
                    =
                  ((liftM (OracleSpec.query
                      (spec := oSpec + fsChallengeOracle StmtIn pSpec) (.inr q)) :
                      OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
                        ((fsChallengeOracle StmtIn pSpec).Range q)) >>= fun response =>
                    pure (response,
                      [⟨(.inr q :
                          (oSpec + fsChallengeOracle StmtIn pSpec).Domain), response⟩])) := by
                simpa using
                  (OracleComp.withQueryLog_query
                    (spec := oSpec + fsChallengeOracle StmtIn pSpec) (.inr q))
              rw [hqueryEq, mem_support_bind_iff] at hchallenge
              obtain ⟨response, _hresponse, hqueryPure⟩ := hchallenge
              rw [mem_support_pure_iff] at hqueryPure
              obtain ⟨rfl, rfl⟩ := hqueryPure
              rw [support_map, Set.mem_image] at hpure
              obtain ⟨purePoint, hpurePoint, hinnerMap⟩ := hpure
              rw [OracleComp.withQueryLog_pure, mem_support_pure_iff] at hpurePoint
              subst purePoint
              rcases pref with ⟨prevTranscript, prefixLog⟩
              simp only [Prod.map_apply, id_eq, List.append_nil, Prod.mk.injEq] at hinnerMap
              rcases hinnerMap with ⟨rfl, rfl⟩
              subst z
              simp only [Prod.map_apply, id_eq]
              rw [queryLog_snd_append, queryLog_snd_singleton_inr, List.append_assoc]
              change (do
                  let prevTranscript ← transcriptFromFSChallengeLogAux
                    (StmtIn := StmtIn) (pSpec := pSpec) k messages i.castSucc
                  let challenge ← popFSChallengeFromLog
                    (StmtIn := StmtIn) (pSpec := pSpec) ⟨i.castLE (by omega), hDir⟩
                  pure (prevTranscript.concat challenge)).run
                    (prefixLog.snd ++
                      (([⟨q, response⟩] :
                        QueryLog (fsChallengeOracle StmtIn pSpec)) ++ tail)) =
                some (prevTranscript.concat response, tail)
              change (((transcriptFromFSChallengeLogAux
                    (StmtIn := StmtIn) (pSpec := pSpec) k messages i.castSucc).run
                      (prefixLog.snd ++
                        (([⟨q, response⟩] :
                          QueryLog (fsChallengeOracle StmtIn pSpec)) ++ tail))).bind
                  fun p =>
                    (((popFSChallengeFromLog
                      (StmtIn := StmtIn) (pSpec := pSpec)
                      ⟨i.castLE (by omega), hDir⟩).run p.2).bind
                        fun p' => some (p.1.concat p'.1, p'.2))) =
                some (prevTranscript.concat response, tail)
              rw [ih (([⟨q, response⟩] :
                QueryLog (fsChallengeOracle StmtIn pSpec)) ++ tail) hpref]
              simp only [Option.bind_some, List.singleton_append]
              rw [popFSChallengeFromLog_cons_self
                (StmtIn := StmtIn) (pSpec := pSpec) ⟨i.castLE (by omega), hDir⟩
                (stmtIn, messages.take i.castSucc) response tail]
              rfl
          · next hDir' =>
              have hContra : Direction.V_to_P = Direction.P_to_V := hDir.symm.trans hDir'
              cases hContra
      · next hDir =>
          rw [OracleComp.withQueryLog_bind, mem_support_bind_iff] at hz
          obtain ⟨pref, hpref, hcont⟩ := hz
          rw [support_map, Set.mem_image] at hcont
          obtain ⟨contPoint, hcontPoint, houterEq⟩ := hcont
          rcases contPoint with ⟨contTranscript, contLog⟩
          split at hcontPoint
          · next hDir' =>
              have hContra : Direction.V_to_P = Direction.P_to_V := hDir'.symm.trans hDir
              cases hContra
          · next hDir' =>
              have hDirProof : hDir' = hDir := Subsingleton.elim _ _
              cases hDirProof
              rw [OracleComp.withQueryLog_pure, mem_support_pure_iff] at hcontPoint
              cases hcontPoint
              rcases pref with ⟨prevTranscript, prefixLog⟩
              subst z
              simp only [Prod.map_apply, id_eq, List.append_nil]
              change (do
                  let prevTranscript ← transcriptFromFSChallengeLogAux
                    (StmtIn := StmtIn) (pSpec := pSpec) k messages i.castSucc
                  pure (prevTranscript.concat (messages ⟨i, hDir⟩))).run
                    (prefixLog.snd ++ tail) =
                some (prevTranscript.concat (messages ⟨i, hDir⟩), tail)
              change (((transcriptFromFSChallengeLogAux
                    (StmtIn := StmtIn) (pSpec := pSpec) k messages i.castSucc).run
                      (prefixLog.snd ++ tail)).bind
                  fun p => some (p.1.concat (messages ⟨i, hDir⟩), p.2)) =
                some (prevTranscript.concat (messages ⟨i, hDir⟩), tail)
              rw [ih tail hpref]
              rfl

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Full-transcript replay corollary for `deriveTranscriptFS.withQueryLog`: the verifier's
slow-Fiat-Shamir challenge-log projection reconstructs every support transcript.  Extra tail
challenge-log entries are ignored by `transcriptFromFSChallengeLog`, which returns the parsed
transcript and discards the final parser state. -/
private theorem transcriptFromFSChallengeLog_run_withQueryLog_snd_support
    (stmtIn : StmtIn) (messages : pSpec.Messages)
    (tail : QueryLog (fsChallengeOracle StmtIn pSpec))
    {z : pSpec.FullTranscript × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)}
    (hz : z ∈ support
      (OracleComp.withQueryLog
        (ProtocolSpec.Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn messages))) :
    transcriptFromFSChallengeLog
        (StmtIn := StmtIn) (pSpec := pSpec) messages (z.2.snd ++ tail) =
      some z.1 := by
  have haux :=
    transcriptFromFSChallengeLogAux_run_withQueryLog_snd_support
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
      stmtIn (Fin.last n) messages (Fin.last (Fin.last n)) tail (z := z)
      (by
        simpa [ProtocolSpec.Messages.deriveTranscriptFS,
          ProtocolSpec.Messages.deriveTranscriptSR,
          ProtocolSpec.MessagesUpTo.deriveTranscriptFS,
          ProtocolSpec.MessagesUpTo.deriveTranscriptSR] using hz)
  have hrun' :
      (transcriptFromFSChallengeLogAux
        (StmtIn := StmtIn) (pSpec := pSpec)
        (k := Fin.last n) messages (Fin.last (Fin.last n))).run'
          (z.2.snd ++ tail) = some z.1 := by
    unfold StateT.run'
    change (fun x => x.1) <$>
        (transcriptFromFSChallengeLogAux
          (StmtIn := StmtIn) (pSpec := pSpec)
          (k := Fin.last n) messages (Fin.last (Fin.last n))).run
            (z.2.snd ++ tail) =
      some z.1
    rw [haux]
    rfl
  unfold transcriptFromFSChallengeLog
  rw [hrun']
  rfl

private theorem optionT_run_liftM_bind
    {ι : Type} {spec : OracleSpec ι} {α β : Type 0}
    (oa : OracleComp spec α) (X : α → OptionT (OracleComp spec) β) :
    OptionT.run ((liftM oa : OptionT (OracleComp spec) α) >>= X) =
      (oa >>= fun a => (X a).run) := by
  simp only [OptionT.run_bind, OptionT.run_monadLift, Option.elimM]
  rw [map_eq_pure_bind]
  simp only [bind_assoc, pure_bind, Option.elim_some, monadLift_self]

private theorem optionT_run_liftM_bind_getM
    {ι : Type} {spec : OracleSpec ι} {α β : Type 0}
    (oa : OracleComp spec α) (X : α → OptionT (OracleComp spec) β) :
    OptionT.run ((liftM oa : OptionT (OracleComp spec) α) >>= fun a =>
        ((liftM (X a).run : OptionT (OracleComp spec) (Option β)) >>= fun o => o.getM)) =
      (oa >>= fun a => (X a).run) := by
  have hinner :
      ((liftM oa : OptionT (OracleComp spec) α) >>= fun a =>
          ((liftM (X a).run : OptionT (OracleComp spec) (Option β)) >>= fun o => o.getM)) =
        ((liftM oa : OptionT (OracleComp spec) α) >>= X) := by
    apply bind_congr
    intro a
    apply OptionT.ext
    simp only [OptionT.run_bind, OptionT.run_monadLift, Option.elimM]
    rw [map_eq_pure_bind]
    simp only [bind_assoc, pure_bind]
    conv_rhs => rw [← bind_pure (X a).run]
    congr 1
    funext o
    cases o <;> rfl
  rw [hinner]
  exact optionT_run_liftM_bind oa X

private theorem optionT_run_liftM_bind_getM_run
    {ι : Type} {spec : OracleSpec ι} {α β : Type 0}
    (oa : OracleComp spec α) (Y : α → OracleComp spec (Option β)) :
    OptionT.run ((liftM oa : OptionT (OracleComp spec) α) >>= fun a =>
        ((liftM (Y a) : OptionT (OracleComp spec) (Option β)) >>= fun o => o.getM)) =
      (oa >>= fun a => Y a) := by
  simpa only [OptionT.run_mk] using
    optionT_run_liftM_bind_getM oa
      (fun a => (OptionT.mk (Y a) : OptionT (OracleComp spec) β))

private theorem optionT_liftM_run_getM_add
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {α : Type 0} (X : OptionT (OracleComp spec₁) α) :
    ((liftM X.run : OptionT (OracleComp (spec₁ + spec₂)) (Option α)) >>= fun o =>
        (o.getM : OptionT (OracleComp (spec₁ + spec₂)) α)) =
      (monadLift X : OptionT (OracleComp (spec₁ + spec₂)) α) := by
  simpa only [liftM_optionT_combined] using
    (monadLift_optionT_lift_run_getM (spec₂ := spec₂) X)

private theorem optionT_run_liftM_bind_liftOptionT_add
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {α β : Type 0}
    (oa : OracleComp (spec₁ + spec₂) α)
    (X : α → OptionT (OracleComp spec₁) β) :
    OptionT.run ((liftM oa : OptionT (OracleComp (spec₁ + spec₂)) α) >>= fun a =>
        (monadLift (X a) : OptionT (OracleComp (spec₁ + spec₂)) β)) =
      (oa >>= fun a =>
        (liftM (X a).run : OracleComp (spec₁ + spec₂) (Option β))) := by
  simpa only [optionT_monadLift_run, liftM_eq_monadLift] using
    optionT_run_liftM_bind oa
      (fun a => (monadLift (X a) : OptionT (OracleComp (spec₁ + spec₂)) β))

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Run-level normalization for the slow Fiat-Shamir verifier: first derive the transcript from the
one proof message, then run the original verifier on that transcript. -/
theorem fiatShamirVerifier_verify_run_eq_bind
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn)
    (proof : FullTranscript (Reduction.FiatShamirProtocolSpec (pSpec := pSpec))) :
    ((V.fiatShamir).verify stmtIn proof).run =
      (do
        let transcript ← ProtocolSpec.Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (proof 0)
        (liftM (V.verify stmtIn transcript).run :
          OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut))) := by
  rw [Verifier.fiatShamir_verify_eq]
  change OptionT.run
      (((liftM
        (ProtocolSpec.Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (proof 0)) :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
            pSpec.FullTranscript) >>= fun transcript =>
        ((liftM (V.verify stmtIn transcript).run :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
            (Option StmtOut)) >>= fun v =>
          (v.getM :
            OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut)))) =
    (do
      let transcript ← ProtocolSpec.Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (proof 0)
      (liftM (V.verify stmtIn transcript).run :
        OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut)))
  have hnormalize :
      (do
        let transcript ← (liftM
          (ProtocolSpec.Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (proof 0)) :
            OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
              pSpec.FullTranscript)
        let v ← (liftM (V.verify stmtIn transcript).run :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) (Option StmtOut))
        v.getM : OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut) =
      (do
        let transcript ← (liftM
          (ProtocolSpec.Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (proof 0)) :
            OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
              pSpec.FullTranscript)
        (monadLift (V.verify stmtIn transcript) :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut)) := by
    apply bind_congr
    intro transcript
    exact optionT_liftM_run_getM_add
      (spec₂ := fsChallengeOracle StmtIn pSpec) (V.verify stmtIn transcript)
  rw [hnormalize]
  exact optionT_run_liftM_bind_liftOptionT_add
    (ProtocolSpec.Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (proof 0))
    (fun transcript => V.verify stmtIn transcript)

#print axioms Reduction.fiatShamirVerifier_verify_run_eq_bind

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Any support point of the Fiat-Shamir verifier log contains, as a prefix of its
slow-Fiat-Shamir projection, the log produced by the transcript derivation from the proof
messages.  The log-backed parser therefore reconstructs that derived transcript from the whole
verifier log. -/
private theorem fiatShamirVerifier_verify_loggedTranscript_support
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn)
    (proof : FullTranscript (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    {z : Option StmtOut × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)}
    (hz : z ∈ support
      (OracleComp.withQueryLog ((V.fiatShamir).verify stmtIn proof))) :
    ∃ d : pSpec.FullTranscript × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec),
      d ∈ support
        (OracleComp.withQueryLog
          (ProtocolSpec.Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (proof 0))) ∧
      transcriptFromFSChallengeLog
          (StmtIn := StmtIn) (pSpec := pSpec) (proof 0) z.2.snd =
        some d.1 := by
  rw [Verifier.fiatShamir_verify_eq] at hz
  have hcollapse :
      (let messages : pSpec.Messages := proof 0;
        (do
          let transcript ← (liftM
            (ProtocolSpec.Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn messages) :
              OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
                pSpec.FullTranscript)
          let v ← (liftM (V.verify stmtIn transcript).run :
            OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) (Option StmtOut))
          v.getM : OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut).run)
        =
      (do
        let transcript ← ProtocolSpec.Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (proof 0)
        (liftM (V.verify stmtIn transcript).run :
          OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut))) := by
    change OptionT.run
        (((liftM
          (ProtocolSpec.Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (proof 0)) :
            OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
              pSpec.FullTranscript) >>= fun transcript =>
          ((liftM (V.verify stmtIn transcript).run :
            OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
              (Option StmtOut)) >>= fun v =>
            (v.getM :
              OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut)))) =
      (do
        let transcript ← ProtocolSpec.Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (proof 0)
        (liftM (V.verify stmtIn transcript).run :
          OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut)))
    have hnormalize :
        (do
          let transcript ← (liftM
            (ProtocolSpec.Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (proof 0)) :
              OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
                pSpec.FullTranscript)
          let v ← (liftM (V.verify stmtIn transcript).run :
            OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) (Option StmtOut))
          v.getM : OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut) =
        (do
          let transcript ← (liftM
            (ProtocolSpec.Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (proof 0)) :
              OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
                pSpec.FullTranscript)
          (monadLift (V.verify stmtIn transcript) :
            OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut)) := by
      apply bind_congr
      intro transcript
      exact optionT_liftM_run_getM_add
        (spec₂ := fsChallengeOracle StmtIn pSpec) (V.verify stmtIn transcript)
    rw [hnormalize]
    exact optionT_run_liftM_bind_liftOptionT_add
      (ProtocolSpec.Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (proof 0))
      (fun transcript => V.verify stmtIn transcript)
  change z ∈ support (OracleComp.withQueryLog
      (let messages : pSpec.Messages := proof 0;
        (do
          let transcript ← (liftM
            (ProtocolSpec.Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn messages) :
              OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
                pSpec.FullTranscript)
          let v ← (liftM (V.verify stmtIn transcript).run :
            OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) (Option StmtOut))
          v.getM : OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut).run)) at hz
  rw [hcollapse] at hz
  rw [OracleComp.withQueryLog_bind, mem_support_bind_iff] at hz
  obtain ⟨derivePoint, hderive, hcont⟩ := hz
  rw [support_map, Set.mem_image] at hcont
  obtain ⟨contPoint, _hcontPoint, hmap⟩ := hcont
  rcases derivePoint with ⟨transcript, deriveLog⟩
  rcases contPoint with ⟨stmtOut, contLog⟩
  refine ⟨(transcript, deriveLog), hderive, ?_⟩
  subst z
  simp only [Prod.map_apply, id_eq]
  rw [queryLog_snd_append]
  exact transcriptFromFSChallengeLog_run_withQueryLog_snd_support
    (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
    stmtIn (proof 0) contLog.snd hderive

/-- Canonical straightline extractor for the transformed one-message Fiat-Shamir verifier, induced
by a state-restoration extractor for the underlying interactive verifier.

The transformed proof transcript contains exactly the underlying protocol messages.  The adapter
recovers the challenges from the verifier query log, avoiding a second post-verifier query to the
shared Fiat-Shamir table, and then calls the state-restoration extractor with the default query logs
used by the current state-restoration knowledge-soundness game. -/
def fiatShamirStraightlineExtractorOfStateRestoration
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec) :
    Extractor.Straightline (oSpec + fsChallengeOracle StmtIn pSpec)
      StmtIn WitIn WitOut (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)) :=
  fun stmtIn witOut proof _proveQueryLog verifyQueryLog => do
    let messages : pSpec.Messages := proof 0
    let transcript ← OptionT.mk (pure <|
      transcriptFromFSChallengeLog (StmtIn := StmtIn) (pSpec := pSpec)
        messages verifyQueryLog.snd)
    liftM (srExtractor stmtIn witOut transcript default default)

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Unfolding equation for
`fiatShamirStraightlineExtractorOfStateRestoration`, exposing the proof-message replay and
state-restoration extractor call. -/
theorem fiatShamirStraightlineExtractorOfStateRestoration_apply
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec)
    (stmtIn : StmtIn) (witOut : WitOut)
    (proof : FullTranscript (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (proveQueryLog verifyQueryLog :
      QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :
    fiatShamirStraightlineExtractorOfStateRestoration
        (oSpec := oSpec) (pSpec := pSpec) srExtractor
        stmtIn witOut proof proveQueryLog verifyQueryLog =
      (do
        let messages : pSpec.Messages := proof 0
        let transcript ← OptionT.mk (pure <|
          transcriptFromFSChallengeLog (StmtIn := StmtIn) (pSpec := pSpec)
            messages verifyQueryLog.snd)
        liftM (srExtractor stmtIn witOut transcript default default)) := by
  rfl

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] in
/-- On verifier logs produced by a logged slow-Fiat-Shamir transcript derivation, the canonical
log-backed Fiat-Shamir extractor is exactly the underlying state-restoration extractor applied to
the logged transcript. -/
theorem fiatShamirStraightlineExtractorOfStateRestoration_loggedTranscript_support
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec)
    (stmtIn : StmtIn) (witOut : WitOut) (messages : pSpec.Messages)
    (proveQueryLog verifyQueryLog :
      QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))
    (tail : QueryLog (fsChallengeOracle StmtIn pSpec))
    {z : pSpec.FullTranscript × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)}
    (hz : z ∈ support
      (OracleComp.withQueryLog
        (ProtocolSpec.Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn messages)))
    (hVerify : verifyQueryLog.snd = z.2.snd ++ tail) :
    fiatShamirStraightlineExtractorOfStateRestoration
        (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut
        (fun | ⟨0, _⟩ => messages) proveQueryLog verifyQueryLog =
      (liftM (srExtractor stmtIn witOut z.1 default default) :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn) := by
  unfold fiatShamirStraightlineExtractorOfStateRestoration
  rw [hVerify]
  change (do
      let transcript ← OptionT.mk (pure <|
        transcriptFromFSChallengeLog
          (StmtIn := StmtIn) (pSpec := pSpec) messages (z.2.snd ++ tail))
      liftM (srExtractor stmtIn witOut transcript default default)) =
    (liftM (srExtractor stmtIn witOut z.1 default default) :
      OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn)
  rw [transcriptFromFSChallengeLog_run_withQueryLog_snd_support
    (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
    stmtIn messages tail hz]
  rfl

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] in
/-- On verifier logs produced by the one-message slow-Fiat-Shamir verifier, the canonical
log-backed Fiat-Shamir extractor is exactly the state-restoration extractor applied to the
transcript derived during verifier execution. -/
theorem fiatShamirStraightlineExtractorOfStateRestoration_loggedVerifier_support
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec)
    (stmtIn : StmtIn) (witOut : WitOut)
    (proof : FullTranscript (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (proveQueryLog : QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))
    {z : Option StmtOut × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)}
    (hz : z ∈ support
      (OracleComp.withQueryLog ((V.fiatShamir).verify stmtIn proof))) :
    ∃ d : pSpec.FullTranscript × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec),
      d ∈ support
        (OracleComp.withQueryLog
          (ProtocolSpec.Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (proof 0))) ∧
      fiatShamirStraightlineExtractorOfStateRestoration
          (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut
          proof proveQueryLog z.2 =
        (liftM (srExtractor stmtIn witOut d.1 default default) :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn) := by
  obtain ⟨d, hd, hparse⟩ :=
    fiatShamirVerifier_verify_loggedTranscript_support
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
      V stmtIn proof hz
  refine ⟨d, hd, ?_⟩
  unfold fiatShamirStraightlineExtractorOfStateRestoration
  change (do
      let transcript ← OptionT.mk (pure <|
        transcriptFromFSChallengeLog
          (StmtIn := StmtIn) (pSpec := pSpec) (proof 0) z.2.snd)
      liftM (srExtractor stmtIn witOut transcript default default)) =
    (liftM (srExtractor stmtIn witOut d.1 default default) :
      OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn)
  rw [hparse]
  rfl

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] in
private theorem fiatShamirProofTranscript_singleton_eta
    (proof : Reduction.FiatShamirProofTranscript (pSpec := pSpec)) :
    (fun | ⟨0, _⟩ => proof 0) = proof := by
  funext i
  rcases i with ⟨i, hi⟩
  have hi0 : i = 0 := by omega
  subst i
  rfl

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Running the one-message slow-Fiat-Shamir verifier under query logging, filtering for an
accepting verifier output, and then applying the canonical log-backed straightline extractor is
the same `OptionT` computation as deriving the transcript once, running the original verifier on
that transcript, and applying the underlying state-restoration extractor to the same transcript.

This is the continuation-level bridge needed by the canonical knowledge-soundness transfer: the
left side preserves the verifier log long enough for the extractor to replay the verifier's
slow-Fiat-Shamir challenge answers, while the right side is the state-restoration game shape. -/
theorem fiatShamirVerifier_loggedExtractor_eq_direct
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec)
    (stmtIn : StmtIn) (witOut : WitOut)
    (proof : Reduction.FiatShamirProofTranscript (pSpec := pSpec))
    (proveLog : QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :
    (do
      let z ← (liftM (OracleComp.withQueryLog (((V.fiatShamir).verify stmtIn proof).run)) :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
          (Option StmtOut × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))
      let stmtOut ← (OptionT.mk (pure z.1) :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut)
      let witIn ← fiatShamirStraightlineExtractorOfStateRestoration
        (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut proof proveLog z.2
      pure (witIn, stmtOut)) =
    (do
      let messages : pSpec.Messages := proof 0
      let transcript ← (liftM (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn messages) :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) pSpec.FullTranscript)
      let stmtOut ← (OptionT.mk (liftM (V.verify stmtIn transcript).run) :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut)
      let witIn ← (liftM (srExtractor stmtIn witOut transcript default default) :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn)
      pure (witIn, stmtOut)) := by
  change (do
      let z ← (liftM (OracleComp.withQueryLog (((V.fiatShamir).verify stmtIn proof).run)) :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
          (Option StmtOut × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))
      let stmtOut ← (OptionT.mk (pure z.1) :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut)
      let witIn ← fiatShamirStraightlineExtractorOfStateRestoration
        (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut proof proveLog z.2
      pure (witIn, stmtOut)).run =
    (do
      let messages : pSpec.Messages := proof 0
      let transcript ← (liftM (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn messages) :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) pSpec.FullTranscript)
      let stmtOut ← (OptionT.mk (liftM (V.verify stmtIn transcript).run) :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut)
      let witIn ← (liftM (srExtractor stmtIn witOut transcript default default) :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn)
      pure (witIn, stmtOut)).run
  rw [fiatShamirVerifier_verify_run_eq_bind (V := V) (stmtIn := stmtIn) (proof := proof)]
  rw [OracleComp.withQueryLog_bind]
  simp only [OptionT.run_bind, OptionT.run_monadLift, OptionT.run_mk, Option.elimM,
    OptionT.run_pure, map_eq_pure_bind, bind_assoc, pure_bind, Option.elim_some,
    monadLift_self]
  dsimp only [Prod.map]
  rw [← loggingOracle.run_simulateQ_bind_fst
    (oa := Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (proof 0))
    (ob := fun transcript => do
      let stmtOut? ← (liftM (V.verify stmtIn transcript).run :
        OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut))
      stmtOut?.elim (pure none) fun stmtOut => do
        let witIn? ← (liftM (srExtractor stmtIn witOut transcript default default) :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn).run
        witIn?.elim (pure none) fun witIn => pure (some (witIn, stmtOut)))]
  change (do
      let x ← OracleComp.withQueryLog
        (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (proof 0))
      let y ← OracleComp.withQueryLog
        ((liftM (V.verify stmtIn x.1).run :
          OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut)))
      y.1.elim (pure none) fun stmtOut => do
        let witIn? ←
          (fiatShamirStraightlineExtractorOfStateRestoration
              (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut proof proveLog
              (x.2 ++ y.2)).run
        witIn?.elim (pure none) fun witIn => pure (some (witIn, stmtOut))) =
    (do
      let x ← OracleComp.withQueryLog
        (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (proof 0))
      let stmtOut? ← (liftM (V.verify stmtIn x.1).run :
        OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut))
      stmtOut?.elim (pure none) fun stmtOut => do
        let witIn? ← (liftM (srExtractor stmtIn witOut x.1 default default) :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn).run
        witIn?.elim (pure none) fun witIn => pure (some (witIn, stmtOut)))
  apply OracleComp.bind_congr_of_forall_mem_support
  intro x hx
  rw [← loggingOracle.run_simulateQ_bind_fst
    (oa := (liftM (V.verify stmtIn x.1).run :
      OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut)))
    (ob := fun stmtOut? =>
      stmtOut?.elim (pure none) fun stmtOut => do
        let witIn? ← (liftM (srExtractor stmtIn witOut x.1 default default) :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn).run
        witIn?.elim (pure none) fun witIn => pure (some (witIn, stmtOut)))]
  change (do
      let y ← OracleComp.withQueryLog
        ((liftM (V.verify stmtIn x.1).run :
          OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut)))
      y.1.elim (pure none) fun stmtOut => do
        let witIn? ←
          (fiatShamirStraightlineExtractorOfStateRestoration
              (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut proof proveLog
              (x.2 ++ y.2)).run
        witIn?.elim (pure none) fun witIn => pure (some (witIn, stmtOut))) =
    (do
      let y ← OracleComp.withQueryLog
        ((liftM (V.verify stmtIn x.1).run :
          OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut)))
      y.1.elim (pure none) fun stmtOut => do
        let witIn? ← (liftM (srExtractor stmtIn witOut x.1 default default) :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn).run
        witIn?.elim (pure none) fun witIn => pure (some (witIn, stmtOut)))
  apply OracleComp.bind_congr_of_forall_mem_support
  intro y _hy
  cases y.1 with
  | none => rfl
  | some stmtOut =>
      have hExtract :=
        fiatShamirStraightlineExtractorOfStateRestoration_loggedTranscript_support
          (oSpec := oSpec) (pSpec := pSpec)
          srExtractor stmtIn witOut (proof 0) proveLog (x.2 ++ y.2) y.2.snd
          (z := x) hx (by rw [queryLog_snd_append])
      simp only [Option.elim_some]
      rw [← fiatShamirProofTranscript_singleton_eta (pSpec := pSpec) proof]
      have hRun := congrArg OptionT.run hExtract
      exact congrArg
        (fun oa : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option WitIn) =>
          oa >>= fun witIn? : Option WitIn =>
            witIn?.elim (pure none) fun witIn => pure (some (witIn, stmtOut)))
        hRun

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Payload-valued version of `fiatShamirVerifier_loggedExtractor_eq_direct`, specialized to the
knowledge-soundness bad-event tuple. -/
theorem fiatShamirVerifier_loggedExtractor_payload_eq_direct
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec)
    (stmtIn : StmtIn) (witOut : WitOut)
    (proof : Reduction.FiatShamirProofTranscript (pSpec := pSpec))
    (proveLog : QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :
    (do
      let z ← (liftM (OracleComp.withQueryLog (((V.fiatShamir).verify stmtIn proof).run)) :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
          (Option StmtOut × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))
      let stmtOut ← (OptionT.mk (pure z.1) :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut)
      let witIn ← fiatShamirStraightlineExtractorOfStateRestoration
        (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut proof proveLog z.2
      pure (stmtIn, witIn, stmtOut, witOut)) =
    (do
      let messages : pSpec.Messages := proof 0
      let transcript ← (liftM (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn messages) :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) pSpec.FullTranscript)
      let stmtOut ← (OptionT.mk (liftM (V.verify stmtIn transcript).run) :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut)
      let witIn ← (liftM (srExtractor stmtIn witOut transcript default default) :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn)
      pure (stmtIn, witIn, stmtOut, witOut)) := by
  change (do
      let z ← (liftM (OracleComp.withQueryLog (((V.fiatShamir).verify stmtIn proof).run)) :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
          (Option StmtOut × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))
      let stmtOut ← (OptionT.mk (pure z.1) :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut)
      let witIn ← fiatShamirStraightlineExtractorOfStateRestoration
        (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut proof proveLog z.2
      pure (stmtIn, witIn, stmtOut, witOut)).run =
    (do
      let messages : pSpec.Messages := proof 0
      let transcript ← (liftM (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn messages) :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) pSpec.FullTranscript)
      let stmtOut ← (OptionT.mk (liftM (V.verify stmtIn transcript).run) :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut)
      let witIn ← (liftM (srExtractor stmtIn witOut transcript default default) :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn)
      pure (stmtIn, witIn, stmtOut, witOut)).run
  rw [fiatShamirVerifier_verify_run_eq_bind (V := V) (stmtIn := stmtIn) (proof := proof)]
  rw [OracleComp.withQueryLog_bind]
  simp only [OptionT.run_bind, OptionT.run_monadLift, OptionT.run_mk, Option.elimM,
    OptionT.run_pure, map_eq_pure_bind, bind_assoc, pure_bind, Option.elim_some,
    monadLift_self]
  dsimp only [Prod.map]
  rw [← loggingOracle.run_simulateQ_bind_fst
    (oa := Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (proof 0))
    (ob := fun transcript => do
      let stmtOut? ← (liftM (V.verify stmtIn transcript).run :
        OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut))
      stmtOut?.elim (pure none) fun stmtOut => do
        let witIn? ← (liftM (srExtractor stmtIn witOut transcript default default) :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn).run
        witIn?.elim (pure none) fun witIn => pure (some (stmtIn, witIn, stmtOut, witOut)))]
  change (do
      let x ← OracleComp.withQueryLog
        (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (proof 0))
      let y ← OracleComp.withQueryLog
        ((liftM (V.verify stmtIn x.1).run :
          OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut)))
      y.1.elim (pure none) fun stmtOut => do
        let witIn? ←
          (fiatShamirStraightlineExtractorOfStateRestoration
              (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut proof proveLog
              (x.2 ++ y.2)).run
        witIn?.elim (pure none) fun witIn => pure (some (stmtIn, witIn, stmtOut, witOut))) =
    (do
      let x ← OracleComp.withQueryLog
        (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (proof 0))
      let stmtOut? ← (liftM (V.verify stmtIn x.1).run :
        OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut))
      stmtOut?.elim (pure none) fun stmtOut => do
        let witIn? ← (liftM (srExtractor stmtIn witOut x.1 default default) :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn).run
        witIn?.elim (pure none) fun witIn => pure (some (stmtIn, witIn, stmtOut, witOut)))
  apply OracleComp.bind_congr_of_forall_mem_support
  intro x hx
  rw [← loggingOracle.run_simulateQ_bind_fst
    (oa := (liftM (V.verify stmtIn x.1).run :
      OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut)))
    (ob := fun stmtOut? =>
      stmtOut?.elim (pure none) fun stmtOut => do
        let witIn? ← (liftM (srExtractor stmtIn witOut x.1 default default) :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn).run
        witIn?.elim (pure none) fun witIn => pure (some (stmtIn, witIn, stmtOut, witOut)))]
  change (do
      let y ← OracleComp.withQueryLog
        ((liftM (V.verify stmtIn x.1).run :
          OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut)))
      y.1.elim (pure none) fun stmtOut => do
        let witIn? ←
          (fiatShamirStraightlineExtractorOfStateRestoration
              (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut proof proveLog
              (x.2 ++ y.2)).run
        witIn?.elim (pure none) fun witIn => pure (some (stmtIn, witIn, stmtOut, witOut))) =
    (do
      let y ← OracleComp.withQueryLog
        ((liftM (V.verify stmtIn x.1).run :
          OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option StmtOut)))
      y.1.elim (pure none) fun stmtOut => do
        let witIn? ← (liftM (srExtractor stmtIn witOut x.1 default default) :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn).run
        witIn?.elim (pure none) fun witIn => pure (some (stmtIn, witIn, stmtOut, witOut)))
  apply OracleComp.bind_congr_of_forall_mem_support
  intro y _hy
  cases y.1 with
  | none => rfl
  | some stmtOut =>
      have hExtract :=
        fiatShamirStraightlineExtractorOfStateRestoration_loggedTranscript_support
          (oSpec := oSpec) (pSpec := pSpec)
          srExtractor stmtIn witOut (proof 0) proveLog (x.2 ++ y.2) y.2.snd
          (z := x) hx (by rw [queryLog_snd_append])
      simp only [Option.elim_some]
      rw [← fiatShamirProofTranscript_singleton_eta (pSpec := pSpec) proof]
      have hRun := congrArg OptionT.run hExtract
      exact congrArg
        (fun oa : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (Option WitIn) =>
          oa >>= fun witIn? : Option WitIn =>
            witIn?.elim (pure none) fun witIn =>
              pure (some (stmtIn, witIn, stmtOut, witOut)))
        hRun

#print axioms Reduction.fiatShamirStraightlineExtractorOfStateRestoration
#print axioms Reduction.fiatShamirStraightlineExtractorOfStateRestoration_apply
#print axioms Reduction.fiatShamirStraightlineExtractorOfStateRestoration_loggedTranscript_support
#print axioms Reduction.fiatShamirStraightlineExtractorOfStateRestoration_loggedVerifier_support
#print axioms Reduction.fiatShamirVerifier_loggedExtractor_eq_direct
#print axioms Reduction.fiatShamirVerifier_loggedExtractor_payload_eq_direct

end CanonicalKnowledgeSoundnessSupport

/-- Basic Fiat-Shamir soundness from a transfer residual at the target error, after first relaxing
the state-restoration soundness hypothesis to that target error. -/
theorem fiatShamir_soundness_of_stateRestoration_pre_mono_error
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_soundnessTransferResidual srInit srImpl fsInit fsImpl
        langIn langOut soundnessError₂ V)
    (hSR : Verifier.StateRestoration.soundness srInit srImpl
      langIn langOut V soundnessError₁)
    (hle : soundnessError₁ ≤ soundnessError₂) :
    Verifier.soundness fsInit fsImpl langIn langOut V.fiatShamir soundnessError₂ := by
  classical
  exact fiatShamir_soundness_of_stateRestoration srInit srImpl fsInit fsImpl langIn langOut
    soundnessError₂ V hTransfer
    (Verifier.StateRestoration.soundness.mono_error srInit srImpl hSR
      (ENNReal.coe_le_coe.mpr hle))

/-- Basic Fiat-Shamir soundness from a transfer residual at the target languages, after first
transporting the state-restoration soundness hypothesis to those languages. -/
theorem fiatShamir_soundness_of_stateRestoration_pre_mono_languages
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {langIn langIn' : Set StmtIn} {langOut langOut' : Set StmtOut}
    (soundnessError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_soundnessTransferResidual srInit srImpl fsInit fsImpl
        langIn' langOut' soundnessError V)
    (hSR : Verifier.StateRestoration.soundness srInit srImpl
      langIn langOut V soundnessError)
    (hIn : langIn ⊆ langIn') (hOut : langOut' ⊆ langOut) :
    Verifier.soundness fsInit fsImpl langIn' langOut' V.fiatShamir soundnessError := by
  classical
  exact fiatShamir_soundness_of_stateRestoration srInit srImpl fsInit fsImpl langIn' langOut'
    soundnessError V hTransfer
    (Verifier.StateRestoration.soundness.mono_languages srInit srImpl hSR hIn hOut)

/-- Basic Fiat-Shamir soundness from a transfer residual at the target languages/error, after first
transporting the state-restoration soundness hypothesis to those target parameters. -/
theorem fiatShamir_soundness_of_stateRestoration_pre_mono_languages_error
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {langIn langIn' : Set StmtIn} {langOut langOut' : Set StmtOut}
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_soundnessTransferResidual srInit srImpl fsInit fsImpl
        langIn' langOut' soundnessError₂ V)
    (hSR : Verifier.StateRestoration.soundness srInit srImpl
      langIn langOut V soundnessError₁)
    (hIn : langIn ⊆ langIn') (hOut : langOut' ⊆ langOut)
    (hle : soundnessError₁ ≤ soundnessError₂) :
    Verifier.soundness fsInit fsImpl langIn' langOut' V.fiatShamir soundnessError₂ := by
  classical
  exact fiatShamir_soundness_of_stateRestoration srInit srImpl fsInit fsImpl langIn' langOut'
    soundnessError₂ V hTransfer
    (Verifier.StateRestoration.soundness.mono_languages_error srInit srImpl hSR hIn hOut
      (ENNReal.coe_le_coe.mpr hle))

/-- Basic Fiat-Shamir knowledge soundness from a transfer residual at the target error, after first
relaxing the state-restoration knowledge-soundness hypothesis to that target error. -/
theorem fiatShamir_knowledgeSoundness_of_stateRestoration_pre_mono_error
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_knowledgeSoundnessTransferResidual srInit srImpl fsInit fsImpl
        relIn relOut knowledgeError₂ V)
    (hSR : Verifier.StateRestoration.knowledgeSoundness srInit srImpl
      relIn relOut V knowledgeError₁)
    (hle : knowledgeError₁ ≤ knowledgeError₂) :
    Verifier.knowledgeSoundness fsInit fsImpl relIn relOut V.fiatShamir knowledgeError₂ := by
  classical
  exact fiatShamir_knowledgeSoundness_of_stateRestoration srInit srImpl fsInit fsImpl relIn relOut
    knowledgeError₂ V hTransfer
    (Verifier.StateRestoration.knowledgeSoundness.mono_error srInit srImpl hSR
      (ENNReal.coe_le_coe.mpr hle))

/-- Basic Fiat-Shamir knowledge soundness from a transfer residual at the target relations, after
first transporting the state-restoration knowledge-soundness hypothesis to those relations. -/
theorem fiatShamir_knowledgeSoundness_of_stateRestoration_pre_mono_relations
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relIn relIn' : Set (StmtIn × WitIn)} {relOut relOut' : Set (StmtOut × WitOut)}
    (knowledgeError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_knowledgeSoundnessTransferResidual srInit srImpl fsInit fsImpl
        relIn' relOut' knowledgeError V)
    (hSR : Verifier.StateRestoration.knowledgeSoundness srInit srImpl
      relIn relOut V knowledgeError)
    (hIn : relIn ⊆ relIn') (hOut : relOut' ⊆ relOut) :
    Verifier.knowledgeSoundness fsInit fsImpl relIn' relOut' V.fiatShamir knowledgeError := by
  classical
  exact fiatShamir_knowledgeSoundness_of_stateRestoration srInit srImpl fsInit fsImpl relIn' relOut'
    knowledgeError V hTransfer
    (Verifier.StateRestoration.knowledgeSoundness.mono_relations srInit srImpl hSR hIn hOut)

/-- Basic Fiat-Shamir knowledge soundness from a transfer residual at the target relations/error,
after first transporting the state-restoration knowledge-soundness hypothesis to those target
parameters. -/
theorem fiatShamir_knowledgeSoundness_of_stateRestoration_pre_mono_relations_error
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relIn relIn' : Set (StmtIn × WitIn)} {relOut relOut' : Set (StmtOut × WitOut)}
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_knowledgeSoundnessTransferResidual srInit srImpl fsInit fsImpl
        relIn' relOut' knowledgeError₂ V)
    (hSR : Verifier.StateRestoration.knowledgeSoundness srInit srImpl
      relIn relOut V knowledgeError₁)
    (hIn : relIn ⊆ relIn') (hOut : relOut' ⊆ relOut)
    (hle : knowledgeError₁ ≤ knowledgeError₂) :
    Verifier.knowledgeSoundness fsInit fsImpl relIn' relOut' V.fiatShamir
      knowledgeError₂ := by
  classical
  exact fiatShamir_knowledgeSoundness_of_stateRestoration srInit srImpl fsInit fsImpl relIn' relOut'
    knowledgeError₂ V hTransfer
    (Verifier.StateRestoration.knowledgeSoundness.mono_relations_error srInit srImpl hSR hIn hOut
      (ENNReal.coe_le_coe.mpr hle))

/-- Basic Fiat-Shamir soundness with both SR-side pretransport and FS-side posttransport around the
explicit state-restoration transfer residual. -/
theorem fiatShamir_soundness_of_stateRestoration_prepost_mono_languages_error
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {langInSR langInTransfer langInFS : Set StmtIn}
    {langOutSR langOutTransfer langOutFS : Set StmtOut}
    {soundnessErrorSR soundnessErrorTransfer soundnessErrorFS : ℝ≥0}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_soundnessTransferResidual srInit srImpl fsInit fsImpl
        langInTransfer langOutTransfer soundnessErrorTransfer V)
    (hSR : Verifier.StateRestoration.soundness srInit srImpl
      langInSR langOutSR V soundnessErrorSR)
    (hInPre : langInSR ⊆ langInTransfer)
    (hOutPre : langOutTransfer ⊆ langOutSR)
    (hlePre : soundnessErrorSR ≤ soundnessErrorTransfer)
    (hInPost : langInTransfer ⊆ langInFS)
    (hOutPost : langOutFS ⊆ langOutTransfer)
    (hlePost : soundnessErrorTransfer ≤ soundnessErrorFS) :
    Verifier.soundness fsInit fsImpl langInFS langOutFS V.fiatShamir
      soundnessErrorFS := by
  classical
  have hMid :
      Verifier.soundness fsInit fsImpl langInTransfer langOutTransfer V.fiatShamir
        soundnessErrorTransfer :=
    fiatShamir_soundness_of_stateRestoration_pre_mono_languages_error
      srInit srImpl fsInit fsImpl V hTransfer hSR hInPre hOutPre hlePre
  have hLang :
      Verifier.soundness fsInit fsImpl langInFS langOutFS V.fiatShamir
        soundnessErrorTransfer :=
    Verifier.soundness.mono_languages fsInit fsImpl hMid hInPost hOutPost
  exact Verifier.soundness.mono_error fsInit fsImpl hLang hlePost

/-- Basic Fiat-Shamir knowledge soundness with both SR-side pretransport and FS-side posttransport
around the explicit state-restoration transfer residual. -/
theorem fiatShamir_knowledgeSoundness_of_stateRestoration_prepost_mono_relations_error
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relInSR relInTransfer relInFS : Set (StmtIn × WitIn)}
    {relOutSR relOutTransfer relOutFS : Set (StmtOut × WitOut)}
    {knowledgeErrorSR knowledgeErrorTransfer knowledgeErrorFS : ℝ≥0}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_knowledgeSoundnessTransferResidual srInit srImpl fsInit fsImpl
        relInTransfer relOutTransfer knowledgeErrorTransfer V)
    (hSR : Verifier.StateRestoration.knowledgeSoundness srInit srImpl
      relInSR relOutSR V knowledgeErrorSR)
    (hInPre : relInSR ⊆ relInTransfer)
    (hOutPre : relOutTransfer ⊆ relOutSR)
    (hlePre : knowledgeErrorSR ≤ knowledgeErrorTransfer)
    (hInPost : relInTransfer ⊆ relInFS)
    (hOutPost : relOutFS ⊆ relOutTransfer)
    (hlePost : knowledgeErrorTransfer ≤ knowledgeErrorFS) :
    Verifier.knowledgeSoundness fsInit fsImpl relInFS relOutFS V.fiatShamir
      knowledgeErrorFS := by
  classical
  have hMid :
      Verifier.knowledgeSoundness fsInit fsImpl relInTransfer relOutTransfer V.fiatShamir
        knowledgeErrorTransfer :=
    fiatShamir_knowledgeSoundness_of_stateRestoration_pre_mono_relations_error
      srInit srImpl fsInit fsImpl V hTransfer hSR hInPre hOutPre hlePre
  have hRel :
      Verifier.knowledgeSoundness fsInit fsImpl relInFS relOutFS V.fiatShamir
        knowledgeErrorTransfer :=
    Verifier.knowledgeSoundness.mono_relations fsInit fsImpl hMid hInPost hOutPost
  exact Verifier.knowledgeSoundness.mono_error fsInit fsImpl hRel hlePost

#print axioms fiatShamir_soundness_of_stateRestoration_pre_mono_error
#print axioms fiatShamir_soundness_of_stateRestoration_pre_mono_languages
#print axioms fiatShamir_soundness_of_stateRestoration_pre_mono_languages_error
#print axioms fiatShamir_knowledgeSoundness_of_stateRestoration_pre_mono_error
#print axioms fiatShamir_knowledgeSoundness_of_stateRestoration_pre_mono_relations
#print axioms fiatShamir_knowledgeSoundness_of_stateRestoration_pre_mono_relations_error
#print axioms fiatShamir_soundness_of_stateRestoration_prepost_mono_languages_error
#print axioms fiatShamir_knowledgeSoundness_of_stateRestoration_prepost_mono_relations_error

section CanonicalKnowledgeSoundness

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

attribute [local instance] Reduction.fiatShamirChallengeOracleInterface

local instance fiatShamirProverOnlyCanonicalKS : ProtocolSpec.ProverOnly
    (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)) where
  prover_first' := by simp

private theorem stateT_option_elimM_map_eq
    {σ α β γ : Type} (mx : StateT σ ProbComp (Option α)) (f : α → β)
    (k : β → StateT σ ProbComp (Option γ)) :
    Option.elimM mx (pure none) (fun a => k (f a)) =
      Option.elimM (Option.map f <$> mx) (pure none) k := by
  unfold Option.elimM
  apply StateT.ext
  intro s
  simp only [StateT.run_bind, StateT.run_map]
  rw [bind_map_left]
  apply bind_congr
  intro x
  cases x with
  | mk oa _s' =>
      cases oa <;> rfl

private theorem stateT_option_elimM_congr
    {σ α β : Type} (mx : StateT σ ProbComp (Option α))
    (f g : α → StateT σ ProbComp (Option β))
    (h : ∀ a, f a = g a) :
    Option.elimM mx (pure none) f = Option.elimM mx (pure none) g := by
  unfold Option.elimM
  apply bind_congr
  intro oa
  cases oa <;> simp [h]

private theorem stateT_option_elimM_congr₂
    {σ α β : Type} {mx my : StateT σ ProbComp (Option α)}
    {f g : α → StateT σ ProbComp (Option β)}
    (hmx : mx = my) (hfg : ∀ a, f a = g a) :
    Option.elimM mx (pure none) f = Option.elimM my (pure none) g := by
  subst my
  exact stateT_option_elimM_congr mx f g hfg

private theorem stateT_option_elimM_some_map_eq
    {σ α β : Type} (mx : StateT σ ProbComp α)
    (k : α → StateT σ ProbComp (Option β)) :
    Option.elimM (some <$> mx) (pure none) k = (mx >>= k) := by
  unfold Option.elimM
  apply StateT.ext
  intro s
  simp only [StateT.run_bind, StateT.run_map]
  rw [bind_map_left]
  apply bind_congr
  intro x
  cases x
  rfl

private theorem stateT_option_elimM_bind_eq
    {σ α β γ : Type} (mx : StateT σ ProbComp α)
    (my : α → StateT σ ProbComp (Option β))
    (k : β → StateT σ ProbComp (Option γ)) :
    Option.elimM (mx >>= my) (pure none) k =
      (mx >>= fun a => Option.elimM (my a) (pure none) k) := by
  unfold Option.elimM
  rw [bind_assoc]

/-- Bind-form (`simp`-shaped) variant of `stateT_option_elimM_some_map_eq`: a `some`-mapped value
fed into an `Option.elim` continuation collapses to the underlying bind.  Stated with a `Bind.bind`
head so it fires by `simp only` on the unfolded `Option.elimM` produced by the big simulation simp
sets (where re-folding via `change` is blocked by invisible `monadLift` instance differences). -/
@[simp]
private theorem stateT_bind_some_elim_eq
    {σ α β : Type} (mx : StateT σ ProbComp α)
    (k : α → StateT σ ProbComp (Option β)) :
    ((some <$> mx) >>= fun x => Option.elim x (pure none) k) = (mx >>= k) :=
  stateT_option_elimM_some_map_eq mx k

private theorem probEvent_stateT_run_map_congr
    {σ α β : Type} (init : ProbComp σ)
    (mx my : StateT σ ProbComp α) (f : α × σ → β) (p : β → Prop)
    (h : mx = my) :
    probEvent (do
        let s ← init
        f <$> mx.run s) p =
      probEvent (do
        let s ← init
        f <$> my.run s) p := by
  subst my
  rfl

private theorem probEvent_stateT_run_fst_congr
    {σ α : Type} (init : ProbComp σ)
    (mx my : StateT σ ProbComp (Option α)) (p : Option α → Prop)
    (h : mx = my) :
    probEvent (do
        let s ← init
        (fun x : Option α × σ => x.1) <$> mx.run s) p =
      probEvent (do
        let s ← init
        (fun x : Option α × σ => x.1) <$> my.run s) p := by
  exact probEvent_stateT_run_map_congr init mx my (fun x : Option α × σ => x.1) p h

/-- Knowledge-soundness event leaf: aborting on verifier failure and then extracting has the same
bad-event probability as the state-restoration game shape that records an `Option StmtOut` and
still runs the extractor.  The event is false in the `none` branch, so the extractor distribution
there is irrelevant. -/
private theorem probEvent_knowledgePayload_option_eq_stateRestoration
    {σ StmtIn WitIn StmtOut WitOut : Type}
    (stmtIn : StmtIn) (witOut : WitOut)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (mx : StateT σ ProbComp (Option StmtOut))
    (my : StateT σ ProbComp WitIn) (s : σ) :
    Pr[fun o : Option (StmtIn × WitIn × StmtOut × WitOut) =>
        o.elim False fun x => (x.1, x.2.1) ∉ relIn ∧ (x.2.2.1, x.2.2.2) ∈ relOut |
      (fun x : Option (StmtIn × WitIn × StmtOut × WitOut) × σ => x.1) <$>
        (Option.elimM mx (pure none) (fun stmtOut => do
          let witIn ← my
          pure (some (stmtIn, witIn, stmtOut, witOut)))).run s] =
    Pr[(fun x : StmtIn × WitIn × Option StmtOut × WitOut =>
        match x with
        | (stmtIn, witIn, some stmtOut, witOut) =>
            (stmtOut, witOut) ∈ relOut ∧ (stmtIn, witIn) ∉ relIn
        | _ => False) |
      (fun x : (StmtIn × WitIn × Option StmtOut × WitOut) × σ => x.1) <$>
        (do
          let stmtOut? ← mx
          let witIn ← my
          pure (stmtIn, witIn, stmtOut?, witOut)).run s] := by
  classical
  simp only [probEvent_map]
  unfold Option.elimM
  simp only [StateT.run_bind]
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro x
  rcases x with ⟨stmtOut?, s'⟩
  cases stmtOut? with
  | none =>
      have hfalse :
          probEvent (my.run s')
            ((((fun x : StmtIn × WitIn × Option StmtOut × WitOut =>
              match x with
              | (stmtIn, witIn, some stmtOut, witOut) =>
                  (stmtOut, witOut) ∈ relOut ∧ (stmtIn, witIn) ∉ relIn
              | _ => False) ∘ fun x => x.1) ∘
                fun a : WitIn × σ => ((stmtIn, a.1, none, witOut), a.2))) = 0 := by
        rw [probEvent_eq_tsum_indicator]
        simp
      simp only [StateT.run_pure, probEvent_pure, Option.elim_none]
      simp [hfalse]
  | some stmtOut =>
      simp only [Option.elim_some, StateT.run_bind, StateT.run_pure]
      congr 1
      symm
      rw [probEvent_bind_eq_tsum]
      symm
      rw [probEvent_bind_eq_tsum]
      apply tsum_congr
      intro y
      rcases y with ⟨witIn, _s''⟩
      rw [probEvent_pure, probEvent_pure]
      by_cases hOut : (stmtOut, witOut) ∈ relOut <;>
      by_cases hIn : (stmtIn, witIn) ∈ relIn <;>
        simp [hOut, hIn, and_comm]

private theorem simulateQ_optionT_bind_mk_some_run
    {ι : Type} {spec : OracleSpec ι} {σ α β : Type}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec α)
    (k : α → OptionT (OracleComp spec) β) :
    simulateQ impl (OptionT.run (do
        let a ← OptionT.mk (some <$> oa)
        k a)) =
      (do
        let a ← simulateQ impl oa
        simulateQ impl (OptionT.run (k a))) := by
  simp [OptionT.run_bind, OptionT.run_mk, simulateQ_option_elimM, simulateQ_map,
    stateT_option_elimM_some_map_eq]

/-- Simulating an `OptionT` computation that only uses the base Fiat-Shamir oracle is unchanged by
adding the one-message transformed verifier's empty challenge layer. -/
private theorem simulateQ_addLift_fiatShamirChallenge_optionT
    {σ α : Type}
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (oa : OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) α) :
    simulateQ (QueryImpl.addLift impl challengeQueryImpl)
        ((liftM oa :
          OptionT
            (OracleComp
              ((oSpec + fsChallengeOracle StmtIn pSpec) +
                [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))
            α).run) =
      simulateQ impl oa.run := by
  dsimp [QueryImpl.addLift_def]
  change
    simulateQ
        (impl + QueryImpl.liftTarget (StateT σ ProbComp)
          (challengeQueryImpl
            (pSpec := Reduction.FiatShamirProtocolSpec (pSpec := pSpec))))
        (OptionT.run
          ((liftM
            (liftM oa :
              OptionT
                (OracleComp
                  (oSpec + (fsChallengeOracle StmtIn pSpec +
                    [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)))
                α)) :
            OptionT
              (OracleComp
                ((oSpec + fsChallengeOracle StmtIn pSpec) +
                  [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))
              α)) =
      simulateQ impl (OptionT.run oa)
  rw [OracleComp.liftM_OptionT_add_assoc_right
    (spec₁ := oSpec) (spec₂ := fsChallengeOracle StmtIn pSpec)
    (spec₃ := [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)
    (oa := oa)]
  simp only [OptionT.run_mk]
  have hSim :=
    simulateQ_add_liftComp_add_assoc_left
      (impl₁₂ := impl)
      (impl₃ := QueryImpl.liftTarget (StateT σ ProbComp)
        (challengeQueryImpl
          (pSpec := Reduction.FiatShamirProtocolSpec (pSpec := pSpec))))
      (oa := oa.run)
  rw [OracleComp.liftComp_add_assoc_right
    (spec₁ := oSpec) (spec₂ := fsChallengeOracle StmtIn pSpec)
    (spec₃ := [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)
    (oa := oa.run)] at hSim
  exact hSim

/-- Generic bridge: a `Reduction.run`-bind equals the corresponding `runWithLog`-bind whose
continuation only reads the run result.  This is the no-HOU direction (rewrite `run` to
`Prod.fst <$> runWithLog`). -/
theorem bind_run_eq_bind_runWithLog_fst
    {γ : Type} (red : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    (F : ((pSpec.FullTranscript × StmtOut × WitOut) × StmtOut) →
         OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) γ) :
    (Reduction.run stmt wit red >>= F) =
      (Reduction.runWithLog stmt wit red >>= fun d => F d.1) := by
  rw [← Reduction.runWithLog_discard_logs_eq_run (reduction := red)]
  rw [map_eq_pure_bind, bind_assoc]
  simp only [pure_bind]

/-- The canonical Fiat-Shamir straightline extractor induced by a state-restoration extractor does
not depend on the prover-side query log.  It intentionally depends on the verifier-side log, because
that log carries the exact slow-Fiat-Shamir challenges sampled during verification. -/
theorem fiatShamirStraightlineExtractorOfStateRestoration_proveLog_irrel
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec)
    (stmtIn : StmtIn) (witOut : WitOut)
    (proof : FullTranscript (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (pLog pLog' vLog : QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :
    fiatShamirStraightlineExtractorOfStateRestoration
        (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut proof pLog vLog =
      fiatShamirStraightlineExtractorOfStateRestoration
        (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut proof pLog' vLog :=
  rfl

/-- Simp-oriented form of prover-log irrelevance for the canonical Fiat-Shamir straightline
extractor. -/
theorem fiatShamirStraightlineExtractorOfStateRestoration_proveLog_irrel_simp
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec)
    (stmtIn : StmtIn) (witOut : WitOut)
    (proof : FullTranscript (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (pLog vLog : QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :
    fiatShamirStraightlineExtractorOfStateRestoration
        (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut proof pLog vLog =
      fiatShamirStraightlineExtractorOfStateRestoration
        (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut proof default vLog := by
  exact fiatShamirStraightlineExtractorOfStateRestoration_proveLog_irrel
    (srExtractor := srExtractor) (stmtIn := stmtIn) (witOut := witOut)
    (proof := proof) (pLog := pLog) (pLog' := default) (vLog := vLog)

/-- The verifier-side log is used only through its slow-Fiat-Shamir challenge projection.  Original
oracle queries in the verifier log are ignored by the canonical extractor. -/
theorem fiatShamirStraightlineExtractorOfStateRestoration_verifyLog_snd_congr
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec)
    (stmtIn : StmtIn) (witOut : WitOut)
    (proof : FullTranscript (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (pLog verifyLog verifyLog' :
      QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))
    (hVerify : verifyLog.snd = verifyLog'.snd) :
    fiatShamirStraightlineExtractorOfStateRestoration
        (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut proof pLog verifyLog =
      fiatShamirStraightlineExtractorOfStateRestoration
        (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut proof pLog verifyLog' := by
  unfold fiatShamirStraightlineExtractorOfStateRestoration
  simp [hVerify]

/-- Combined log congruence for the canonical extractor: the prover log is ignored, and verifier
logs are interchangeable when their slow-Fiat-Shamir challenge projections agree. -/
theorem fiatShamirStraightlineExtractorOfStateRestoration_log_congr
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec)
    (stmtIn : StmtIn) (witOut : WitOut)
    (proof : FullTranscript (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (pLog pLog' verifyLog verifyLog' :
      QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))
    (hVerify : verifyLog.snd = verifyLog'.snd) :
    fiatShamirStraightlineExtractorOfStateRestoration
        (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut proof pLog verifyLog =
      fiatShamirStraightlineExtractorOfStateRestoration
        (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut proof pLog' verifyLog' := by
  rw [fiatShamirStraightlineExtractorOfStateRestoration_proveLog_irrel
    (srExtractor := srExtractor) (stmtIn := stmtIn) (witOut := witOut)
    (proof := proof) (pLog := pLog) (pLog' := pLog') (vLog := verifyLog)]
  exact fiatShamirStraightlineExtractorOfStateRestoration_verifyLog_snd_congr
    (srExtractor := srExtractor) (stmtIn := stmtIn) (witOut := witOut)
    (proof := proof) (pLog := pLog') (verifyLog := verifyLog)
    (verifyLog' := verifyLog') hVerify

/-- Adding original-oracle-only entries before the verifier log does not affect the canonical
extractor, since only the slow-Fiat-Shamir challenge projection is replayed. -/
theorem fiatShamirStraightlineExtractorOfStateRestoration_verifyLog_inl_left_irrel
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec)
    (stmtIn : StmtIn) (witOut : WitOut)
    (proof : FullTranscript (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (pLog verifyLog : QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))
    (originalLog : QueryLog oSpec) :
    fiatShamirStraightlineExtractorOfStateRestoration
        (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut proof pLog
        (QueryLog.inl (spec₂ := fsChallengeOracle StmtIn pSpec) originalLog ++ verifyLog) =
      fiatShamirStraightlineExtractorOfStateRestoration
        (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut proof pLog
        verifyLog := by
  exact fiatShamirStraightlineExtractorOfStateRestoration_verifyLog_snd_congr
    (srExtractor := srExtractor) (stmtIn := stmtIn) (witOut := witOut)
    (proof := proof) (pLog := pLog)
    (verifyLog :=
      QueryLog.inl (spec₂ := fsChallengeOracle StmtIn pSpec) originalLog ++ verifyLog)
    (verifyLog' := verifyLog)
    (queryLog_snd_inl_append_left originalLog verifyLog)

/-- Adding original-oracle-only entries after the verifier log does not affect the canonical
extractor, since only the slow-Fiat-Shamir challenge projection is replayed. -/
theorem fiatShamirStraightlineExtractorOfStateRestoration_verifyLog_inl_right_irrel
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec)
    (stmtIn : StmtIn) (witOut : WitOut)
    (proof : FullTranscript (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (pLog verifyLog : QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))
    (originalLog : QueryLog oSpec) :
    fiatShamirStraightlineExtractorOfStateRestoration
        (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut proof pLog
        (verifyLog ++ QueryLog.inl (spec₂ := fsChallengeOracle StmtIn pSpec) originalLog) =
      fiatShamirStraightlineExtractorOfStateRestoration
        (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn witOut proof pLog
        verifyLog := by
  exact fiatShamirStraightlineExtractorOfStateRestoration_verifyLog_snd_congr
    (srExtractor := srExtractor) (stmtIn := stmtIn) (witOut := witOut)
    (proof := proof) (pLog := pLog)
    (verifyLog :=
      verifyLog ++ QueryLog.inl (spec₂ := fsChallengeOracle StmtIn pSpec) originalLog)
    (verifyLog' := verifyLog)
    (queryLog_snd_append_inl_right verifyLog originalLog)

#print axioms Reduction.fiatShamirStraightlineExtractorOfStateRestoration_proveLog_irrel
#print axioms Reduction.fiatShamirStraightlineExtractorOfStateRestoration_proveLog_irrel_simp
#print axioms Reduction.fiatShamirStraightlineExtractorOfStateRestoration_verifyLog_snd_congr
#print axioms Reduction.fiatShamirStraightlineExtractorOfStateRestoration_log_congr
#print axioms Reduction.fiatShamirStraightlineExtractorOfStateRestoration_verifyLog_inl_left_irrel
#print axioms Reduction.fiatShamirStraightlineExtractorOfStateRestoration_verifyLog_inl_right_irrel

/-- Knowledge-soundness analogue of `fiatShamirAdversary_runCollapse`: collapse the
`Reduction.runWithLog` of the transformed one-message reduction to an explicit adversary execution
over `oSpec + fsChallengeOracle`. -/
theorem fiatShamir_runWithLog_simulateQ_fst
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (P : Prover (oSpec + fsChallengeOracle StmtIn pSpec) StmtIn WitIn StmtOut WitOut
      (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    (fun o => Option.map Prod.fst o) <$>
        simulateQ (QueryImpl.addLift impl challengeQueryImpl)
          (Reduction.runWithLog stmtIn witIn
            { prover := P, verifier := V.fiatShamir }).run =
      simulateQ impl (fiatShamirAdversaryExecution P V stmtIn witIn).run := by
  rw [← fiatShamirAdversary_runCollapse impl P V stmtIn witIn]
  rw [← Reduction.runWithLog_discard_logs_eq_run (reduction :=
    { prover := P, verifier := V.fiatShamir })]
  rw [OptionT.run_map, simulateQ_map]

#print axioms Reduction.fiatShamir_runWithLog_simulateQ_fst

/-- Collapse the full Fiat-Shamir knowledge-soundness execution, including the straightline
extractor call, from the transformed `runWithLog` game to the explicit adversary execution over
`oSpec + fsChallengeOracle`.

The proof first discards the query logs because
`fiatShamirStraightlineExtractorOfStateRestoration` ignores them, then uses
`fiatShamir_runWithLog_simulateQ_fst` and the generic `simulateQ`/`OptionT` lift-collapse helper to
remove the unused one-message verifier challenge layer around the extractor. -/
theorem fiatShamirKnowledgeExec_runCollapse
    {σ : Type}
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (P : Prover (oSpec + fsChallengeOracle StmtIn pSpec) StmtIn WitIn StmtOut WitOut
      (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    simulateQ (QueryImpl.addLift impl challengeQueryImpl)
        ((do
          let d ← Reduction.runWithLog stmtIn witIn
            { prover := P, verifier := V.fiatShamir }
          let extractedWitIn ←
            liftM do
              let transcript ← OptionT.mk (some <$> Messages.deriveTranscriptFS
                (oSpec := oSpec) stmtIn (d.1.1.1 0))
              liftM (srExtractor stmtIn d.1.1.2.2 transcript default default)
          pure (stmtIn, extractedWitIn, d.1.2, d.1.1.2.2)).run) =
      simulateQ impl
        ((do
          let d ← fiatShamirAdversaryExecution P V stmtIn witIn
          let extractedWitIn ←
            liftM do
              let transcript ← OptionT.mk (some <$> Messages.deriveTranscriptFS
                (oSpec := oSpec) stmtIn (d.1.1 0))
              liftM (srExtractor stmtIn d.1.2.2 transcript default default)
          pure (stmtIn, extractedWitIn, d.2, d.1.2.2)).run) := by
  simp only [OptionT.run_bind, simulateQ_option_elimM, simulateQ_pure]
  let K :
      ((Reduction.FiatShamirProofTranscript (pSpec := pSpec) × (StmtOut × WitOut)) ×
          StmtOut) →
        StateT σ ProbComp (Option (StmtIn × WitIn × StmtOut × WitOut)) := fun d =>
      Option.elimM
        (simulateQ (QueryImpl.addLift impl challengeQueryImpl)
          (OptionT.run
            ((liftM
              (do
                let transcript ← OptionT.mk (some <$> Messages.deriveTranscriptFS
                  (oSpec := oSpec) stmtIn (d.1.1 0))
                liftM (srExtractor stmtIn d.1.2.2 transcript default default) :
                  OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn)) :
                OptionT
                  (OracleComp
                    ((oSpec + fsChallengeOracle StmtIn pSpec) +
                      [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))
                  WitIn)))
        (pure none) fun extractedWitIn =>
          simulateQ (QueryImpl.addLift impl challengeQueryImpl)
            (OptionT.run
              ((pure (stmtIn, extractedWitIn, d.2, d.1.2.2)) :
                OptionT
                  (OracleComp
                    ((oSpec + fsChallengeOracle StmtIn pSpec) +
                      [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))
                  (StmtIn × WitIn × StmtOut × WitOut)))
  change Option.elimM
      (simulateQ (QueryImpl.addLift impl challengeQueryImpl)
        (Reduction.runWithLog stmtIn witIn { prover := P, verifier := V.fiatShamir }).run)
      (pure none) (fun d => K d.1) =
    Option.elimM (simulateQ impl (fiatShamirAdversaryExecution P V stmtIn witIn).run)
      (pure none) (fun d =>
        Option.elimM
          (simulateQ impl
            (OptionT.run
              ((liftM
                (do
                  let transcript ← OptionT.mk (some <$> Messages.deriveTranscriptFS
                    (oSpec := oSpec) stmtIn (d.1.1 0))
                  liftM (srExtractor stmtIn d.1.2.2 transcript default default) :
                    OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn)) :
                  OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn)))
          (pure none) fun extractedWitIn =>
            simulateQ impl
              (OptionT.run
                ((pure (stmtIn, extractedWitIn, d.2, d.1.2.2)) :
                  OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
                    (StmtIn × WitIn × StmtOut × WitOut))))
  rw [stateT_option_elimM_map_eq (f := Prod.fst) (k := K)]
  change Option.elimM
      ((fun o => Option.map Prod.fst o) <$>
        simulateQ (QueryImpl.addLift impl challengeQueryImpl)
          (Reduction.runWithLog stmtIn witIn { prover := P, verifier := V.fiatShamir }).run)
      (pure none) K =
    Option.elimM (simulateQ impl (fiatShamirAdversaryExecution P V stmtIn witIn).run)
      (pure none) (fun d =>
        Option.elimM
          (simulateQ impl
            (OptionT.run
              ((liftM
                (do
                  let transcript ← OptionT.mk (some <$> Messages.deriveTranscriptFS
                    (oSpec := oSpec) stmtIn (d.1.1 0))
                  liftM (srExtractor stmtIn d.1.2.2 transcript default default) :
                    OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn)) :
                  OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn)))
          (pure none) fun extractedWitIn =>
            simulateQ impl
              (OptionT.run
                ((pure (stmtIn, extractedWitIn, d.2, d.1.2.2)) :
                  OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
                    (StmtIn × WitIn × StmtOut × WitOut))))
  have hfst :
      ((fun o => Option.map Prod.fst o) <$>
        simulateQ (QueryImpl.addLift impl challengeQueryImpl)
          (Reduction.runWithLog stmtIn witIn { prover := P, verifier := V.fiatShamir }).run) =
        simulateQ impl (fiatShamirAdversaryExecution P V stmtIn witIn).run :=
    fiatShamir_runWithLog_simulateQ_fst impl P V stmtIn witIn
  rw [hfst]
  have hLift :
      ∀ d : ((Reduction.FiatShamirProofTranscript (pSpec := pSpec) ×
          (StmtOut × WitOut)) × StmtOut),
        simulateQ (impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
          (OptionT.run
            ((liftM
              (do
                let transcript ← OptionT.mk (some <$> Messages.deriveTranscriptFS
                  (oSpec := oSpec) stmtIn (d.1.1 0))
                liftM (srExtractor stmtIn d.1.2.2 transcript default default) :
                  OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn)) :
                OptionT
                  (OracleComp
                    ((oSpec + fsChallengeOracle StmtIn pSpec) +
                      [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))
                  WitIn)) =
        simulateQ impl
          (OptionT.run
            (do
              let transcript ← OptionT.mk (some <$> Messages.deriveTranscriptFS
                (oSpec := oSpec) stmtIn (d.1.1 0))
              liftM (srExtractor stmtIn d.1.2.2 transcript default default) :
                OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn)) := by
    intro d
    let oa :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn :=
      (do
        let transcript ← OptionT.mk (some <$> Messages.deriveTranscriptFS
          (oSpec := oSpec) stmtIn (d.1.1 0))
        liftM (srExtractor stmtIn d.1.2.2 transcript default default) :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn)
    change
      simulateQ
          (impl + QueryImpl.liftTarget (StateT σ ProbComp)
            (challengeQueryImpl
              (pSpec := Reduction.FiatShamirProtocolSpec (pSpec := pSpec))))
          (OptionT.run
            ((liftM
              (liftM oa :
                OptionT
                  (OracleComp
                    (oSpec + (fsChallengeOracle StmtIn pSpec +
                      [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)))
                  WitIn)) :
              OptionT
                (OracleComp
                  ((oSpec + fsChallengeOracle StmtIn pSpec) +
                    [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))
                WitIn)) =
        simulateQ impl (OptionT.run oa)
    rw [OracleComp.liftM_OptionT_add_assoc_right
      (spec₁ := oSpec) (spec₂ := fsChallengeOracle StmtIn pSpec)
      (spec₃ := [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)
      (oa := oa)]
    simp only [OptionT.run_mk]
    have hSim :=
      simulateQ_add_liftComp_add_assoc_left
      (impl₁₂ := impl)
      (impl₃ := QueryImpl.liftTarget (StateT σ ProbComp)
        (challengeQueryImpl
          (pSpec := Reduction.FiatShamirProtocolSpec (pSpec := pSpec))))
      (oa := oa.run)
    rw [OracleComp.liftComp_add_assoc_right
      (spec₁ := oSpec) (spec₂ := fsChallengeOracle StmtIn pSpec)
      (spec₃ := [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)
      (oa := oa.run)] at hSim
    exact hSim
  have hPure :
      ∀ (d : ((Reduction.FiatShamirProofTranscript (pSpec := pSpec) ×
          (StmtOut × WitOut)) × StmtOut)) (extractedWitIn : WitIn),
        simulateQ (impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
          (OptionT.run
            ((pure (stmtIn, extractedWitIn, d.2, d.1.2.2)) :
              OptionT
                (OracleComp
                  ((oSpec + fsChallengeOracle StmtIn pSpec) +
                    [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))
                (StmtIn × WitIn × StmtOut × WitOut))) =
        simulateQ impl
          (OptionT.run
            ((pure (stmtIn, extractedWitIn, d.2, d.1.2.2)) :
              OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
                (StmtIn × WitIn × StmtOut × WitOut))) := by
    intro d extractedWitIn
    simp only [OptionT.run_pure, simulateQ_pure]
  apply stateT_option_elimM_congr
  intro d
  dsimp [K, QueryImpl.addLift_def]
  trans
      Option.elimM
        (simulateQ impl
          (OptionT.run
            (do
              let transcript ← OptionT.mk (some <$> Messages.deriveTranscriptFS
                (oSpec := oSpec) stmtIn (d.1.1 0))
              liftM (srExtractor stmtIn d.1.2.2 transcript default default) :
                OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn)))
        (pure none) fun extractedWitIn =>
          simulateQ impl
            (OptionT.run
              ((pure (stmtIn, extractedWitIn, d.2, d.1.2.2)) :
                OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
                  (StmtIn × WitIn × StmtOut × WitOut)))
  · exact stateT_option_elimM_congr₂ (hLift d) (fun extractedWitIn =>
      hPure d extractedWitIn)
  · rfl

/-- Collapse the one-message transformed Fiat-Shamir prover run to its explicit send/output
execution over `oSpec + fsChallengeOracle`. -/
theorem fiatShamirProver_run_simulateQ_eq_direct
    {σ : Type}
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (P : Prover (oSpec + fsChallengeOracle StmtIn pSpec) StmtIn WitIn StmtOut WitOut
      (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (stmtIn : StmtIn) (witIn : WitIn) :
    simulateQ (QueryImpl.addLift impl challengeQueryImpl)
        (Prover.run stmtIn witIn P) =
      simulateQ impl
        (do
          let state := P.input (stmtIn, witIn)
          let ⟨proofMessages, state⟩ ← P.sendMessage ⟨0, by simp⟩ state
          let ctxOut ← P.output state
          let proof : Reduction.FiatShamirProofTranscript (pSpec := pSpec) := fun
            | ⟨0, _⟩ => proofMessages
          pure ⟨proof, ctxOut⟩) := by
  rw [Prover.run_of_prover_first
    (pSpec := Reduction.FiatShamirProtocolSpec (pSpec := pSpec))]
  simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self, liftComp_eq_liftM,
    bind_assoc, pure_bind, simulateQ_bind, simulateQ_map, simulateQ_pure,
    simulateQ_addLift_liftM, map_bind, bind_pure_comp]
  rfl

/-- Logged prover execution collapses to the explicit send/output execution after projecting away
the query log. -/
theorem fiatShamirProver_runWithLog_simulateQ_fst_eq_direct
    {σ : Type}
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (P : Prover (oSpec + fsChallengeOracle StmtIn pSpec) StmtIn WitIn StmtOut WitOut
      (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (stmtIn : StmtIn) (witIn : WitIn) :
    Prod.fst <$>
        simulateQ (QueryImpl.addLift impl challengeQueryImpl)
          (Prover.runWithLog stmtIn witIn P) =
      simulateQ impl
        (do
          let state := P.input (stmtIn, witIn)
          let ⟨proofMessages, state⟩ ← P.sendMessage ⟨0, by simp⟩ state
          let ctxOut ← P.output state
          let proof : Reduction.FiatShamirProofTranscript (pSpec := pSpec) := fun
            | ⟨0, _⟩ => proofMessages
          pure ⟨proof, ctxOut⟩) := by
  rw [← fiatShamirProver_run_simulateQ_eq_direct
    (impl := impl) (P := P) (stmtIn := stmtIn) (witIn := witIn)]
  rw [← simulateQ_map]
  rw [Prover.runWithLog_discard_log_eq_run]


/-- Collapse the log-backed Fiat-Shamir knowledge-soundness execution to the direct aborting
state-restoration-shaped execution.  The verifier log is preserved until
`fiatShamirVerifier_loggedExtractor_payload_eq_direct` rewrites the verifier/extractor block to a
single transcript derivation, verifier run, and state-restoration extractor call. -/
theorem fiatShamirKnowledgeExec_loggedExtractor_eq_direct
    {σ : Type}
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (P : Prover (oSpec + fsChallengeOracle StmtIn pSpec) StmtIn WitIn StmtOut WitOut
      (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    simulateQ (QueryImpl.addLift impl challengeQueryImpl)
        ((do
          let d ← Reduction.runWithLog stmtIn witIn
            { prover := P, verifier := V.fiatShamir }
          let extractedWitIn ←
            liftM (fiatShamirStraightlineExtractorOfStateRestoration
              (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn d.1.1.2.2
              d.1.1.1 d.2.1.fst d.2.2)
          pure (stmtIn, extractedWitIn, d.1.2, d.1.1.2.2)).run) =
      simulateQ impl
        ((do
          let state := P.input (stmtIn, witIn)
          let ⟨proofMessages, state⟩ ← P.sendMessage ⟨0, by simp⟩ state
          let ctxOut ← P.output state
          let proof : Reduction.FiatShamirProofTranscript (pSpec := pSpec) := fun
            | ⟨0, _⟩ => proofMessages
          let messages : pSpec.Messages := proof 0
          let transcript ← (liftM (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn messages) :
            OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) pSpec.FullTranscript)
          let stmtOut ← (OptionT.mk (liftM (V.verify stmtIn transcript).run) :
            OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut)
          let extractedWitIn ←
            (liftM (srExtractor stmtIn ctxOut.2 transcript default default) :
              OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn)
          pure (stmtIn, extractedWitIn, stmtOut, ctxOut.2) :
            OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
              (StmtIn × WitIn × StmtOut × WitOut)).run) := by
  -- Reassociate the `runWithLog` so the verifier run and the log-backed extractor become adjacent,
  -- then collapse them with the payload bridge, all at the level of `OptionT` computations over the
  -- big spec `(oSpec + fsChallengeOracle) + [Challenge]ₒ`.
  have hbig :
      (do
        let d ← Reduction.runWithLog stmtIn witIn
          { prover := P, verifier := V.fiatShamir }
        let extractedWitIn ←
          liftM (fiatShamirStraightlineExtractorOfStateRestoration
            (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn d.1.1.2.2
            d.1.1.1 d.2.1.fst d.2.2)
        pure (stmtIn, extractedWitIn, d.1.2, d.1.1.2.2) :
          OptionT (OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))
            (StmtIn × WitIn × StmtOut × WitOut)) =
      (do
        let pr ← (liftM (Prover.runWithLog stmtIn witIn P) :
          OptionT (OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))
            ((Reduction.FiatShamirProofTranscript (pSpec := pSpec) × StmtOut × WitOut) ×
              QueryLog ((oSpec + fsChallengeOracle StmtIn pSpec) +
                [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)))
        (liftM
          ((do
            let z ← (liftM (OracleComp.withQueryLog
                (((V.fiatShamir).verify stmtIn pr.1.1).run)) :
              OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
                (Option StmtOut × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))
            let stmtOut ← (OptionT.mk (pure z.1) :
              OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut)
            let witIn ← fiatShamirStraightlineExtractorOfStateRestoration
              (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn pr.1.2.2 pr.1.1 pr.2.fst z.2
            pure (stmtIn, witIn, stmtOut, pr.1.2.2)) :
            OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
              (StmtIn × WitIn × StmtOut × WitOut)))) := by
    unfold Reduction.runWithLog
    simp only [bind_assoc]
    refine bind_congr (fun pr => ?_)
    rw [show (Verifier.run stmtIn pr.1.1 V.fiatShamir) = (V.fiatShamir).verify stmtIn pr.1.1 from rfl]
    simp only [pure_bind]
    rw [show (simulateQ loggingOracle ((V.fiatShamir).verify stmtIn pr.1.1)).run =
        OracleComp.withQueryLog (((V.fiatShamir).verify stmtIn pr.1.1).run) from rfl]
    -- Normalize the right-hand `liftM` of the small-spec block to the explicit `OptionT.mk ∘ liftComp`
    -- path, then prove the residual `OptionT` equality at the `.run` level.
    rw [fiatShamir_liftM_base_optionT_to_append_eq_direct
      (oa := (do
        let z ← (liftM (OracleComp.withQueryLog
            (((V.fiatShamir).verify stmtIn pr.1.1).run)) :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
            (Option StmtOut × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))
        let stmtOut ← (OptionT.mk (pure z.1) :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut)
        let witIn ← fiatShamirStraightlineExtractorOfStateRestoration
          (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn pr.1.2.2 pr.1.1 pr.2.fst z.2
        pure (stmtIn, witIn, stmtOut, pr.1.2.2)))]
    -- Fold the right-hand explicit `OptionT.mk ∘ liftComp` form back into a single `liftM` of the
    -- small-spec bridge block.
    rw [← fiatShamir_liftM_base_optionT_to_append_eq_direct
      (oa := (do
        let z ← (liftM (OracleComp.withQueryLog
            (((V.fiatShamir).verify stmtIn pr.1.1).run)) :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
            (Option StmtOut × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))
        let stmtOut ← (OptionT.mk (pure z.1) :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut)
        let witIn ← fiatShamirStraightlineExtractorOfStateRestoration
          (oSpec := oSpec) (pSpec := pSpec) srExtractor stmtIn pr.1.2.2 pr.1.1 pr.2.fst z.2
        pure (stmtIn, witIn, stmtOut, pr.1.2.2)))]
    have hgm : ∀ (o : Option StmtOut), (monadLift (OptionT.mk (pure o) :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut) :
        OptionT (OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) +
          [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) StmtOut) =
        o.getM := by
      intro o
      rw [show (monadLift (OptionT.mk (pure o) :
            OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut) :
          OptionT (OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) StmtOut) =
          (liftM (OptionT.mk (pure o) :
            OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut) :
          OptionT (OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) StmtOut) from rfl]
      rw [fiatShamir_liftM_base_optionT_to_append_eq_direct]
      apply OptionT.ext
      simp only [OptionT.run_mk, OracleComp.liftComp_pure, Option.getM]
      cases o <;> rfl
    simp only [monadLift_bind, monadLift_pure, hgm, liftM_eq_monadLift]
    apply OptionT.ext
    simp only [OptionT.run_bind, liftM_optionT_combined, optionT_monadLift_run,
      fiatShamir_liftM_base_optionT_to_append_eq_direct,
      OptionT.run_mk, OptionT.run_monadLift, OptionT.run_pure, Option.elimM, Option.getM,
      OracleComp.liftComp_eq_liftM, OracleComp.liftComp_bind, OracleComp.liftComp_map,
      OracleComp.liftComp_pure, monadLift_bind, monadLift_pure,
      map_eq_pure_bind, pure_bind, bind_assoc, Option.elim_some, Option.elim_none,
      monadLift_self]
    congr 1
    induction (V.fiatShamir.verify stmtIn pr.1.1).run.withQueryLog using
        OracleComp.inductionOn with
    | pure x => rfl
    | query_bind t oa ih =>
        rw [monadLift_bind, OracleComp.liftComp_bind]
        congr 1
        · rcases t with t | t <;> rfl
        · funext x; exact ih x
  rw [hbig]
  simp only [fiatShamirVerifier_loggedExtractor_payload_eq_direct]
  conv_lhs => simp only [OptionT.run_bind, simulateQ_option_elimM, simulateQ_pure]
  -- The impl-level (small-spec) verify/extract continuation, lifted through the addLift challenge
  -- layer.  The LHS inner continuation depends only on the prover output `pr.1` (the log `pr.2` is
  -- ignored), so the whole block factors through `Prod.fst`.
  let K :
      (Reduction.FiatShamirProofTranscript (pSpec := pSpec) × StmtOut × WitOut) →
        StateT σ ProbComp (Option (StmtIn × WitIn × StmtOut × WitOut)) := fun c =>
      simulateQ (QueryImpl.addLift impl challengeQueryImpl)
        (OptionT.run
          ((liftM
            (do
              let transcript ← (liftM (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (c.1 0)) :
                OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) pSpec.FullTranscript)
              let stmtOut ← (OptionT.mk (liftM (V.verify stmtIn transcript).run) :
                OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut)
              let witIn ← (liftM (srExtractor stmtIn c.2.2 transcript default default) :
                OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn)
              pure (stmtIn, witIn, stmtOut, c.2.2) :
                OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
                  (StmtIn × WitIn × StmtOut × WitOut))) :
              OptionT
                (OracleComp
                  ((oSpec + fsChallengeOracle StmtIn pSpec) +
                    [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))
                (StmtIn × WitIn × StmtOut × WitOut)))
  change Option.elimM
      (simulateQ (QueryImpl.addLift impl challengeQueryImpl)
        (liftM (Prover.runWithLog stmtIn witIn P) :
          OptionT (OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))
            ((Reduction.FiatShamirProofTranscript (pSpec := pSpec) × StmtOut × WitOut) ×
              QueryLog ((oSpec + fsChallengeOracle StmtIn pSpec) +
                [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))).run)
      (pure none) (fun x => K (Prod.fst x)) = _
  rw [stateT_option_elimM_map_eq (f := Prod.fst) (k := K)]
  -- Discard the prover query log and collapse the lifted logged prover run to the explicit
  -- send/output execution `E_full` over `oSpec + fsChallengeOracle`.
  have hfst :
      (Option.map Prod.fst <$>
        simulateQ (QueryImpl.addLift impl challengeQueryImpl)
          (liftM (Prover.runWithLog stmtIn witIn P) :
            OptionT (OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) +
              [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))
              ((Reduction.FiatShamirProofTranscript (pSpec := pSpec) × StmtOut × WitOut) ×
                QueryLog ((oSpec + fsChallengeOracle StmtIn pSpec) +
                  [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))).run) =
        Option.some <$>
          simulateQ impl
            (do
              let state := P.input (stmtIn, witIn)
              let ⟨proofMessages, state⟩ ← P.sendMessage ⟨0, by simp⟩ state
              let ctxOut ← P.output state
              let proof : Reduction.FiatShamirProofTranscript (pSpec := pSpec) := fun
                | ⟨0, _⟩ => proofMessages
              pure ⟨proof, ctxOut⟩) := by
    rw [show (liftM (Prover.runWithLog stmtIn witIn P) :
          OptionT (OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))
            ((Reduction.FiatShamirProofTranscript (pSpec := pSpec) × StmtOut × WitOut) ×
              QueryLog ((oSpec + fsChallengeOracle StmtIn pSpec) +
                [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))).run =
          Option.some <$> Prover.runWithLog stmtIn witIn P from rfl]
    rw [simulateQ_map]
    rw [← fiatShamirProver_runWithLog_simulateQ_fst_eq_direct
      (impl := impl) (P := P) (stmtIn := stmtIn) (witIn := witIn)]
    simp only [Functor.map_map, Function.comp, Option.map_some]
  rw [hfst]
  rw [stateT_option_elimM_some_map_eq]
  -- Reconcile the composed (addLift) challenge MonadLift instance around the verify/extract block
  -- with the canonical right-associated instance, using only the lemmas that respect that instance.
  have hLift :
      ∀ c : (Reduction.FiatShamirProofTranscript (pSpec := pSpec) × StmtOut × WitOut),
        K c =
        simulateQ impl
          (OptionT.run
            (do
              let transcript ← (liftM (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (c.1 0)) :
                OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) pSpec.FullTranscript)
              let stmtOut ← (OptionT.mk (liftM (V.verify stmtIn transcript).run) :
                OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut)
              let witIn ← (liftM (srExtractor stmtIn c.2.2 transcript default default) :
                OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn)
              pure (stmtIn, witIn, stmtOut, c.2.2) :
                OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
                  (StmtIn × WitIn × StmtOut × WitOut))) := by
    intro c
    dsimp only [K]
    let oa :
        OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
          (StmtIn × WitIn × StmtOut × WitOut) :=
      (do
        let transcript ← (liftM (Messages.deriveTranscriptFS (oSpec := oSpec) stmtIn (c.1 0)) :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) pSpec.FullTranscript)
        let stmtOut ← (OptionT.mk (liftM (V.verify stmtIn transcript).run) :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) StmtOut)
        let witIn ← (liftM (srExtractor stmtIn c.2.2 transcript default default) :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn)
        (pure (stmtIn, witIn, stmtOut, c.2.2) :
          OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
            (StmtIn × WitIn × StmtOut × WitOut)))
    change
      simulateQ
          (impl + QueryImpl.liftTarget (StateT σ ProbComp)
            (challengeQueryImpl
              (pSpec := Reduction.FiatShamirProtocolSpec (pSpec := pSpec))))
          (OptionT.run
            ((liftM
              (liftM oa :
                OptionT
                  (OracleComp
                    (oSpec + (fsChallengeOracle StmtIn pSpec +
                      [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)))
                  (StmtIn × WitIn × StmtOut × WitOut))) :
              OptionT
                (OracleComp
                  ((oSpec + fsChallengeOracle StmtIn pSpec) +
                    [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))
                (StmtIn × WitIn × StmtOut × WitOut))) =
        simulateQ impl (OptionT.run oa)
    rw [OracleComp.liftM_OptionT_add_assoc_right
      (spec₁ := oSpec) (spec₂ := fsChallengeOracle StmtIn pSpec)
      (spec₃ := [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)
      (oa := oa)]
    simp only [OptionT.run_mk]
    have hSim :=
      simulateQ_add_liftComp_add_assoc_left
      (impl₁₂ := impl)
      (impl₃ := QueryImpl.liftTarget (StateT σ ProbComp)
        (challengeQueryImpl
          (pSpec := Reduction.FiatShamirProtocolSpec (pSpec := pSpec))))
      (oa := oa.run)
    rw [OracleComp.liftComp_add_assoc_right
      (spec₁ := oSpec) (spec₂ := fsChallengeOracle StmtIn pSpec)
      (spec₃ := [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)
      (oa := oa.run)] at hSim
    exact hSim
  rw [bind_congr hLift]
  -- Refold the explicit send/output execution and its verify/extract continuation into a single
  -- lifted `OptionT` run, then collapse the trailing `pure` so the whole thing matches the direct
  -- aborting block on the right.
  rw [← simulateQ_bind]
  congr 1
  simp only [bind_assoc, pure_bind, OptionT.run_bind, OptionT.run_monadLift, OptionT.run_mk,
    OptionT.run_pure, optionT_monadLift_run, liftM_eq_monadLift, monadLift_self, Option.elimM,
    Option.elim_some, Option.elim_none, map_eq_pure_bind]

/-- Re-fold the unfolded one-message Fiat-Shamir protocol spec (exposed by `dsimp` of the reducible
abbreviation) back to `FiatShamirProtocolSpec`, so that `simp`/`rw` discrimination-tree keys line up
with lemmas stated against the folded abbreviation. -/
@[simp]
theorem fiatShamirProtocolSpec_fold :
    (⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ : ProtocolSpec 1) =
      FiatShamirProtocolSpec (pSpec := pSpec) := rfl

/-- Peel one shared `StateT` bind under a `probEvent` equality, threading the state. -/
private theorem probEvent_stateT_peel
    {σ α β₁ β₂ : Type} (mx : StateT σ ProbComp α)
    (f : α → StateT σ ProbComp β₁) (g : α → StateT σ ProbComp β₂)
    (p : β₁ → Prop) (q : β₂ → Prop) (s : σ)
    (h : ∀ a s', (a, s') ∈ support (mx.run s) →
      Pr[p | (fun x : β₁ × σ => x.1) <$> (f a).run s'] =
        Pr[q | (fun x : β₂ × σ => x.1) <$> (g a).run s']) :
    Pr[p | (fun x : β₁ × σ => x.1) <$> (mx >>= f).run s] =
      Pr[q | (fun x : β₂ × σ => x.1) <$> (mx >>= g).run s] := by
  rw [StateT.run_bind, StateT.run_bind, map_bind, map_bind]
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr (fun x => ?_)
  rcases x with ⟨a, s'⟩
  by_cases hx : (a, s') ∈ support (mx.run s)
  · rw [h a s' hx]
  · simp [probOutput_eq_zero_of_not_mem_support hx]

/-- The `Verifier.knowledgeSoundness` execution lifts the base-spec straightline extractor into the
appended challenge spec through the reflexive-then-direct `MonadLift` instance, which agrees with
the direct `liftComp` path used by the bridged execution lemma. -/
private theorem fiatShamirKS_goalLift_eq_liftComp
    (e : OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)) WitIn) :
    (@liftM (OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)))
        (OptionT (OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) +
          [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)))
        (instMonadLiftTOfMonadLift
          (OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)))
          (OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)))
          (OptionT (OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) +
            [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))))
        WitIn e) =
      OptionT.mk (OracleComp.liftComp e.run
        ((oSpec + fsChallengeOracle StmtIn pSpec) +
          [(Reduction.FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)) := by
  apply OptionT.ext
  dsimp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift]
  rw [OracleComp.liftComp_def]
  simp only [OptionT.run_mk]
  congr 1
  funext t
  dsimp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift]
  cases t <;> rfl

set_option maxHeartbeats 0 in
set_option linter.flexible false in
/-- Canonical coupled state-restoration knowledge soundness implies basic Fiat-Shamir knowledge
soundness when both games use the same sampled cached Fiat-Shamir challenge table. -/
theorem fiatShamir_knowledgeSoundnessTransferResidual_canonical
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (knowledgeError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    fiatShamir_knowledgeSoundnessTransferResidual srInit srImpl srInit
      (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec)
        (StmtIn := StmtIn) srImpl)
      relIn relOut knowledgeError V := by
  intro hSR
  obtain ⟨srExtractor, hbound⟩ := hSR
  refine ⟨fiatShamirStraightlineExtractorOfStateRestoration
    (oSpec := oSpec) (pSpec := pSpec) srExtractor, ?_⟩
  intro stmtIn witIn prover
  have h :=
    hbound (Prover.StateRestoration.knowledgeSoundnessOfFiatShamirProver
      (oSpec := oSpec) (pSpec := pSpec) prover stmtIn witIn)
  dsimp only [Verifier.knowledgeSoundness]
  rw [Verifier.StateFunction.probEvent_optionT_mk_eq_elim]
  have h_eq := fiatShamirKnowledgeExec_loggedExtractor_eq_direct
    (impl := fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec)
      (StmtIn := StmtIn) srImpl)
    (P := prover) (V := V) (srExtractor := srExtractor) (stmtIn := stmtIn) (witIn := witIn)
  rw [Verifier.StateRestoration.srKnowledgeSoundnessGame_eq_deriveTranscriptFS] at h
  dsimp only [Prover.StateRestoration.knowledgeSoundnessOfFiatShamirProver] at h
  rw [← ProtocolSpec.fsChallengeQueryImplState_eq_srChallengeQueryImpl'] at h
  change probEvent (do let s ← srInit; (simulateQ (fiatShamirCoupledQueryImpl srImpl) _).run' s) _ ≤ _ at h
  -- Now simplify `bind` in `h`, distributing `simulateQ` over the prefix.
  simp only [OptionT.mk_bind, OptionT.run_mk, bind_assoc, pure_bind, StateT.run',
    simulateQ_bind, simulateQ_map, simulateQ_pure] at h
  -- Re-express the goal's reflexive-then-direct extractor lift and `h_eq`'s right-associated lift
  -- through the common direct `liftComp` so the bridge equation applies.
  simp only [fiatShamirKS_goalLift_eq_liftComp,
    fiatShamir_liftM_rightAssoc_to_append_eq_direct,
    fiatShamir_liftM_base_optionT_to_append_eq_direct] at h_eq ⊢
  rw [h_eq]
  refine le_trans ?_ h
  simp only [StateT.run', OptionT.run_bind, OptionT.run_monadLift, OptionT.run_mk,
    optionT_monadLift_run, liftM_eq_monadLift, monadLift_self, simulateQ_map,
    simulateQ_pure, simulateQ_option_elimM, OptionT.run_pure, Verifier.run,
    OracleComp.liftComp_eq_liftM,
    stateT_option_elimM_some_map_eq, bind_assoc, pure_bind, simulateQ_bind,
    StateT.run_bind, StateT.run_map, Functor.map_map, Function.comp]
  refine Verifier.StateFunction.probEvent_bind_mono_heteroEvent (fun table _ => ?_)
  simp [simulateQ_bind, simulateQ_map, simulateQ_pure, simulateQ_option_elimM,
    fiatShamirCoupledQueryImpl, ProtocolSpec.fsChallengeQueryImplState_eq_srChallengeQueryImpl',
    probEvent_map, map_bind, Functor.map_map, Function.comp,
    StateT.run_bind, StateT.run_map, liftM_eq_monadLift, Option.elimM,
    bind_assoc, pure_bind]
  conv_rhs => erw [simulateQ_bind]
  refine probEvent_stateT_bind_mono_hetero _ _ _ _ _ _ (fun x s' _ => ?_)
  conv_rhs => erw [simulateQ_bind]
  refine probEvent_stateT_bind_mono_hetero _ _ _ _ _ _ (fun x1 s2 _ => ?_)
  conv_rhs => erw [simulateQ_bind]
  refine probEvent_stateT_bind_mono_hetero _ _ _ _ _ _ (fun tr s3 _ => ?_)
  conv_rhs => erw [simulateQ_bind]
  refine probEvent_stateT_bind_mono_hetero _ _ _ _ _ _ (fun o s4 _ => ?_)
  cases o with
  | none =>
      refine le_trans (le_of_eq ?_) (zero_le _)
      simp [probEvent_pure]
  | some stmtOut =>
      conv_rhs => erw [simulateQ_map]
      simp only [Option.elim_some]
      have h1 : (monadLift (srExtractor stmtIn x1.2 tr default default) :
          OptionT (OracleComp (oSpec + ProtocolSpec.srChallengeOracle StmtIn pSpec)) WitIn).run
        = OracleComp.liftComp
            ((srExtractor stmtIn x1.2 tr default default) >>= fun a => pure (some a))
            (oSpec + ProtocolSpec.srChallengeOracle StmtIn pSpec) := rfl
      erw [h1]
      have h2 : (monadLift (srExtractor stmtIn x1.2 tr default default) :
          OracleComp (oSpec + ProtocolSpec.srChallengeOracle StmtIn pSpec) WitIn)
        = OracleComp.liftComp (srExtractor stmtIn x1.2 tr default default)
            (oSpec + ProtocolSpec.srChallengeOracle StmtIn pSpec) := rfl
      erw [h2]
      simp only [OracleComp.liftComp_bind, OracleComp.liftComp_pure,
        QueryImpl.simulateQ_add_liftComp_left, simulateQ_bind, simulateQ_pure,
        bind_assoc, pure_bind, Option.elim_some]
      refine le_of_eq ?_
      conv_lhs => erw [simulateQ_bind]
      simp only [simulateQ_pure, bind_assoc, pure_bind, Option.elim_some,
        map_eq_bind_pure_comp, Function.comp]
      rw [StateT.run_bind, StateT.run_bind]
      simp only [probEvent_bind_eq_tsum]
      refine tsum_congr fun y => ?_
      congr 1
      conv_lhs => erw [simulateQ_pure]
      classical
      simp [StateT.run_pure, StateT.run_bind, probEvent_pure,
        Option.elim_some, pure_bind, and_comm]

-- The canonical knowledge-soundness transfer needs a log-replay comparison for the verifier-side
-- Fiat-Shamir challenges.  Re-deriving the transcript after verifier execution is not sound for an
-- arbitrary stateful `srImpl`, because original-oracle verifier queries may mutate the cached
-- challenge table.  The extractor above therefore replays `verifyQueryLog.snd`; the remaining
-- theorem should compare `Reduction.runWithLog` against the state-restoration game using that log.

end CanonicalKnowledgeSoundness

end Reduction
