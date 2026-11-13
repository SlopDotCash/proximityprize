/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.OracleReduction.Basic

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Extensions.OracleReduction.ProtocolSpec.SeqCompose

/-!
### OracleReduction.Basic — reading guide

This file defines the *types* of the parties of a public-coin interactive (oracle) reduction.
The detailed modeling description is the next module docstring ("Interactive (Oracle)
Reductions"); this guide only summarizes the actual definitions (see their docstrings for the
exact signatures) and points to where the rest of the theory lives.

* `ProtocolSpec n` (`ProtocolSpec/`): the fixed sequence of `n` rounds, each either a prover
  message (`P_to_V`) or a verifier challenge (`V_to_P`), with their types.
* `Prover oSpec StmtIn WitIn StmtOut WitOut pSpec`: a stateful prover with
  `input : StmtIn × WitIn → PrvState 0`; per round either `sendMessage` (an `OracleComp oSpec`
  producing the message and next state) or `receiveChallenge` (an `OracleComp oSpec` returning a
  function of the challenge); and `output : PrvState (Fin.last n) → OracleComp oSpec
  (StmtOut × WitOut)`. All three may query the shared, possibly probabilistic, oracle `oSpec`.
  `ProverInteraction` / `ProverInteractionWithOutput` are weaker interfaces for (knowledge)
  soundness adversaries.
* `Verifier oSpec StmtIn StmtOut pSpec`:
  `verify : StmtIn → FullTranscript pSpec → OptionT (OracleComp oSpec) StmtOut`. A plain verifier
  reads the **full transcript** (prover messages in the clear and all challenges), may query
  `oSpec`, and may fail.
* `OracleProver`: a `Prover` whose input/output statements also carry the contents of the oracle
  statements.
* `OracleVerifier`: `verify : StmtIn → pSpec.Challenges →
  OptionT (OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ))) StmtOut`. It receives the
  challenges as input and accesses the input oracle statements and the prover's messages **only
  through oracle queries** (per their `OracleInterface` instances). Its output oracle statements
  are given by `outputOracle`: either an `OracleOutputEmbedding` into the input oracle statements
  and prover messages, or a virtual `OracleOutputSimulation` whose query implementation is proved
  to agree with its materialization. It has no challenge-generation field: challenges are sampled
  by the execution. `OracleVerifier.toVerifier` turns it into a plain `Verifier` by answering the
  queries from the oracle statements and the transcript.
* `Reduction` / `OracleReduction`: a prover paired with a (oracle) verifier.
* `OracleInterface` (`OracleInterface.lean`): a class giving a message type a `Query` type and
  an oracle semantics.

Where the rest lives:

* execution semantics (`OracleReduction/Execution.lean`): running the prover and verifier, with
  challenges sampled through the challenge oracle (`pSpec.getChallenge`, implemented by
  `challengeQueryImpl`) and the shared oracle interpreted by a (possibly stateful) implementation.
  Execution is probabilistic, not a deterministic function of the challenges alone.
* security definitions: `OracleReduction/Completeness.lean` and `OracleReduction/Security/`
  (soundness, knowledge soundness, round-by-round variants, zero knowledge, …).
* composition: `OracleReduction/Composition/Sequential/` (append, `seqCompose`);
  `Composition/Parallel/Basic.lean` is currently a placeholder.
* context lifting (lenses): `OracleReduction/LiftContext/`.
* the BCS transform (commitments to oracle messages): `OracleReduction/BCS/`.
* concrete protocols: `ArkLib/ProofSystem/` (e.g. `Fri/`, `Sumcheck/`, `Binius/`).

(An earlier version of this guide described a different, conceptual API — a verifier that never
reads raw messages, a deterministic execution, challenge-generating verifier fields and a generic
`embed` combinator — and pointed to nonexistent `Protocol/` and `Lifting.lean` paths. It has
been replaced by the summary above, which follows the actual definitions.)
-/


/-!
# Interactive (Oracle) Reductions

This file defines the basic components of a public-coin **Interactive Oracle Reduction** (IOR).
These are interactive protocols between two parties, a prover and a verifier, with the following
format:

  - The protocol proceeds over a number of steps. In each step, either the prover or the verifier
    sends a message to the other. We assume that this sequence of interactions is fixed in advance,
    and is described by a protocol specification (see `ProtocolSpec.lean`).

    Note that we do _not_ require interleaving prover's messages with verifier's challenges, for
    maximum flexibility in defining reductions.

  - Both parties may have access to some shared oracle, which is modeled as an oracle specification
    `OracleSpec`. These are often probabilistic sampling or random oracles.

  - At the beginning, the prover and verifier both take in an input statement `StmtIn`. There are a
    number of input **oracle** statements `OStmtIn` whose underlying content is known to the prover,
    but is only available via an oracle interface to the verifier. The prover also takes in a
    private witness `WitIn`.

  - During the interaction, the verifier is assumed to always send uniformly random challenges to
    the prover. The prover will send messages, which is either available in full to the verifier, or
    received as oracles. Which is which is specified by the protocol specification.

  - At the end of the interaction, the verifier performs a computation that outputs a new statement
    `StmtOut`, and specify a _subset_ of the oracles it has received to be the output oracle
    statements.

Our formulation of IORs can be seen in the literature as **F-IORs**, where `F` denotes an arbitrary
class of oracles. See the blueprint for more details about our modeling choices.

We can then specialize our definition to obtain specific instantiations in the literature:

  - **Interactive Reductions** (IRs) are a special kind of IORs where _all_ of the prover's messages
    are available in full.
  - **Interactive Oracle Proofs** (IOPs) are a special kind of IORs where the output statement is
    Boolean (i.e. `accept/reject`), there is no oracle output statements, and the output witness is
    trivial.
  - Further specialization of IOPs include **Vector IOPs**, **Polynomial IOPs**, and so on, are
    defined in downstream files. Note that vector IOPs is the original definition of IOPs [BCS16],
    while polynomial IOPs were later introduced in [BCG+19] and others.
  - **Interactive Proofs** (IPs) are a combination of IRs and IOPs.
  - **Non-Interactive Reductions** (for example, folding or accumulation schemes) are IRs with a
    single message from the prover.
  - **Non-Interactive Arguments of Knowledge** (NARKs) are IPs with a single message from the
    prover.

We note that this file only defines the type signature of IORs. The semantics of executing an IOR
can be found in `Execution.lean`, while the security notions are found in the `Security` folder.

Note the appearance of the various dependencies in the type signatures:
- `oSpec : OracleSpec ι` comes first, as we expect this to be the ambient (fixed) shared oracle
  specification for the protocol
- `StmtIn` comes next, as the type of the input statement to the protocol
- Then we have `OStmtIn` for the type of the oracle input statements (for oracle reductions),
  followed by `WitIn`, the type of the input witness
- Then we have `StmtOut` for the type of the output statement, followed by `OStmtOut` for the type
  of the output oracle statements, and finally `WitOut` for the type of the output witness
- Finally, we have `pSpec : ProtocolSpec n`, which is the protocol specification for the (oracle)
  reduction

We arrange things in this way for potential future extensions, where later types may depend on
earlier types (i.e. `WitIn`, `StmtOut`, or `pSpec` may depend on `StmtIn`; though we do not expect,
say, `StmtOut` or `pSpec` to depend on the witness types, as that is not available to the (oracle)
verifier).
-/

open OracleComp OracleSpec SubSpec ProtocolSpec

-- Add an indexer?
namespace OracleComp

/-- Replay an oracle computation and return the accumulated query cost.

The result remains an oracle computation over the same specification, so adaptive computations
choose later queries using the same responses they would have seen in the original run. -/
def queryCostTrace {ι : Type} {spec : OracleSpec ι} {α : Type}
    (cost : spec.Domain → ℕ) (oa : OracleComp spec α) : OracleComp spec ℕ :=
  match oa with
  | .pure _ => pure 0
  | .queryBind t k => do
      let u ← liftM (OracleSpec.query (spec := spec) t)
      let n ← queryCostTrace cost (k u)
      pure (cost t + n)

@[simp] theorem queryCostTrace_pure {ι : Type} {spec : OracleSpec ι} {α : Type}
    (cost : spec.Domain → ℕ) (a : α) :
    queryCostTrace cost (pure a : OracleComp spec α) = pure 0 :=
  rfl

@[simp] theorem queryCostTrace_queryBind {ι : Type} {spec : OracleSpec ι} {α : Type}
    (cost : spec.Domain → ℕ) (t : spec.Domain) (k : spec.Range t → OracleComp spec α) :
    queryCostTrace cost (OracleComp.queryBind t k) =
      (do
        let u ← liftM (OracleSpec.query (spec := spec) t)
        let n ← queryCostTrace cost (k u)
        pure (cost t + n)) :=
  rfl

end OracleComp

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)

/-- Construct output oracle statements from input oracle statements and transcript messages by
  routing according to an embedding function. This is the standalone form of the routing inlined
  in `toVerifier`; consumed by the Binius step logic (`BinaryBasefold.ReductionLogic`,
  `RingSwitching.BatchingPhase`).

  Restored after PR 537 (sequential-composition cherry-pick) dropped it while its Binius consumers
  still reference it; it is exactly the `toVerifier` `oStmtOut` routing factored out, taking the
  embedding/typing data as explicit arguments instead of reading them off a `verifier`. -/
def mkVerifierOStmtOut
    (embed : ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIdx)
    (hEq : ∀ i, OStmtOut i = match embed i with
      | Sum.inl j => OStmtIn j
      | Sum.inr j => pSpec.Message j)
    (oStmt : ∀ i, OStmtIn i) (transcript : FullTranscript pSpec) :
    ∀ i, OStmtOut i :=
  fun i => match h : embed i with
    | Sum.inl j => (hEq i ▸ h ▸ oStmt j : OStmtOut i)
    | Sum.inr j => (hEq i ▸ h ▸ transcript.messages j : OStmtOut i)

omit Oₛᵢ Oₘ in
@[simp]
lemma mkVerifierOStmtOut_inl
    (embed : ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIdx)
    (hEq : ∀ i, OStmtOut i = match embed i with
      | Sum.inl j => OStmtIn j
      | Sum.inr j => pSpec.Message j)
    (oStmt : ∀ i, OStmtIn i) (transcript : FullTranscript pSpec)
    (i : ιₛₒ) (j : ιₛᵢ) (h : embed i = Sum.inl j) :
    mkVerifierOStmtOut embed hEq oStmt transcript i = (hEq i ▸ h ▸ oStmt j : OStmtOut i) := by
  simp only [mkVerifierOStmtOut, MessageIdx, Message]
  split
  · rename_i heq
    rw [h] at heq
    simp only [MessageIdx, Sum.inl.injEq] at heq
    subst heq
    rfl
  · rename_i heq
    rw [h] at heq
    simp only [MessageIdx, reduceCtorEq] at heq

omit Oₛᵢ Oₘ in
@[simp]
lemma mkVerifierOStmtOut_inr
    (embed : ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIdx)
    (hEq : ∀ i, OStmtOut i = match embed i with
      | Sum.inl j => OStmtIn j
      | Sum.inr j => pSpec.Message j)
    (oStmt : ∀ i, OStmtIn i) (transcript : FullTranscript pSpec)
    (i : ιₛₒ) (j : pSpec.MessageIdx) (h : embed i = Sum.inr j) :
    mkVerifierOStmtOut embed hEq oStmt transcript i =
      (hEq i ▸ h ▸ transcript.messages j : OStmtOut i) := by
  simp only [mkVerifierOStmtOut, MessageIdx, Message]
  split
  · rename_i heq
    rw [h] at heq
    simp only [MessageIdx, reduceCtorEq] at heq
  · rename_i heq
    rw [h] at heq
    simp only [MessageIdx, Sum.inr.injEq] at heq
    subst heq
    rfl

/-- The number of queries made to the oracle statements and the prover's messages, for a given input
    statement and challenges.

  This is given as an oracle computation itself, since the oracle verifier may be adaptive and has
  different number of queries depending on the prior responses. Shared `oSpec` queries are replayed
  and charged zero; queries to input oracle statements and prover messages are charged one. -/
def numQueries (stmt : StmtIn) (challenges : ∀ i, pSpec.Challenge i)
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
    OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ)) ℕ :=
  OracleComp.queryCostTrace
    (spec := oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ))
    (fun
      | Sum.inl _ => 0
      | Sum.inr _ => 1)
    ((verifier.verify stmt challenges).run)

theorem numQueries_eq_queryCostTrace (stmt : StmtIn) (challenges : ∀ i, pSpec.Challenge i)
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
    verifier.numQueries stmt challenges =
      OracleComp.queryCostTrace
        (spec := oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ))
        (fun
          | Sum.inl _ => 0
          | Sum.inr _ => 1)
        ((verifier.verify stmt challenges).run) :=
  rfl

theorem numQueries_of_verify_pure (stmt : StmtIn) (challenges : ∀ i, pSpec.Challenge i)
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    {stmtOut : StmtOut} (hverify : verifier.verify stmt challenges = pure stmtOut) :
    verifier.numQueries stmt challenges =
      (pure 0 : OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ)) ℕ) := by
  rw [numQueries_eq_queryCostTrace, hverify]
  rfl

namespace NonAdaptive

end NonAdaptive

end OracleVerifier

section Trivial

variable {ι : Type} {oSpec : OracleSpec ι}
    {Statement : Type} {ιₛ : Type} {OStatement : ιₛ → Type} {Witness : Type}
    [Oₛ : ∀ i, OracleInterface (OStatement i)]

end Trivial

section Classes

namespace ProtocolSpec

variable {n : ℕ}

section SingleMessage

variable {pSpec : ProtocolSpec 1}

--  For protocols with a single message, first and last are the same
end SingleMessage

namespace IsSingleRound

variable {pSpec : ProtocolSpec 2}

end IsSingleRound

end ProtocolSpec

section IsPure

variable {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}

end IsPure

end Classes

/-! ## Axiom audit — adaptive oracle-verifier query counting. -/
#print axioms OracleComp.queryCostTrace
#print axioms OracleComp.queryCostTrace_pure
#print axioms OracleComp.queryCostTrace_queryBind
#print axioms OracleVerifier.numQueries
#print axioms OracleVerifier.numQueries_eq_queryCostTrace
#print axioms OracleVerifier.numQueries_of_verify_pure
