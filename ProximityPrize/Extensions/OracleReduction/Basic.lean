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

import ProximityPrize.Extensions.OracleReduction.ProtocolSpec.SeqCompose

/-!
### OracleReduction.Basic — Conceptual Overview

## What is an Oracle Reduction?

An **Interactive Oracle Reduction (IOR)** — called `OracleReduction` here — is an
interactive protocol between a **prover** and a **verifier** where:

- The prover holds a private witness and sends messages round by round.
- The verifier issues random challenges and, at the end, decides to accept or reject.
- Crucially, the verifier does **not** read prover messages in the clear. Instead it
  holds an *oracle* to each message and may query it at chosen points.

This is the information-theoretic core of most modern SNARKs (FRI, PLONK, STARK, …).
The `BCS transform` later replaces each oracle message with a Merkle commitment,
turning an IOR into a non-interactive argument.

### File Scope

`OracleReduction/Basic.lean` defines the **primitive building blocks** from which
all concrete protocol specifications in this library are assembled:

| Concept              | Role in the model                                              |
|----------------------|----------------------------------------------------------------|
| `Prover`             | Stateful interactive machine; sends messages, receives challenges |
| `Verifier`           | Checks the transcript; receives oracle handles, not raw messages |
| `OracleVerifier`     | A verifier that issues typed oracle *queries* to message handles |
| `OracleInterface`    | Specifies the query type and answer type for a message oracle  |
| `embed`              | Lifts a reduction into a larger oracle context                 |
| `Execution`          | The joint transcript produced by running Prover against Verifier |
| `Soundness`          | Security predicate: no cheating prover convinces on false statements |
| `Completeness`       | Honest prover always convinces on true statements              |

---

## The Prover

```
Prover : Statement → Witness → ProverState → Message × ProverState
```

The prover is a **stateful function**. At each round it:
1. Receives the current challenge (or the initial statement + witness at round 0).
2. Computes the next outgoing message.
3. Updates its internal state.

The state threading is explicit so that the prover can accumulate partial results
across rounds (e.g., storing intermediate polynomial evaluations in FRI folding).

## The Verifier

```
Verifier : Statement → OracleHandle[] → Challenge[] → Decision
```

The verifier receives:
- The **public statement** (shared with the prover from the start).
- A list of **oracle handles** — one per prover message per round. It never sees the
  raw message; it can only interact with it through the oracle interface.
- The list of **challenges** it chose during the interaction.

At the end it outputs `accept` or `reject`.

## The Oracle Verifier

`OracleVerifier` is a refinement of `Verifier` that makes the query structure
explicit in the type. Rather than an opaque decision function, it is described as:

```
OracleVerifier : Statement → List (OracleQuery msg_i) → Challenge[] → Decision
```

Each `OracleQuery` is typed by the `OracleInterface` of the corresponding message.
This makes the **query complexity** of the verifier visible at the type level,
which is essential for proving efficiency bounds and for the BCS transform.

### OracleInterface

```lean
structure OracleInterface (Message : Type) where
  Query  : Type       -- what the verifier asks
  Answer : Type       -- what the oracle returns
  oracle : Message → Query → Answer
```

For example, a polynomial oracle might have `Query := 𝔽` (an evaluation point) and
`Answer := 𝔽` (the polynomial's value there), with `oracle f x := f.eval x`.

## The `embed` Mechanism

`embed` is the key **composition primitive**. It lifts an `OracleReduction` defined
over a small oracle context `𝒪_small` into a larger context `𝒪_large` by:

1. Injecting the small oracle interfaces into the larger list via an index map.
2. Translating queries from the larger verifier back to queries in the smaller world.
3. Leaving all prover behavior unchanged.

This lets complex protocols be **built from smaller sub-reductions** without having
to re-prove security from scratch — the composition theorems propagate soundness and
completeness automatically.

## Interaction, Execution, and Security: The Three Layers

This file deliberately separates three concerns:

### 1. Interaction (syntax)
The types `Prover`, `Verifier`, `OracleVerifier`, and `OracleInterface` describe
*what* the parties compute at each step. No probability, no security claim yet.

### 2. Execution (semantics)
`Execution` runs a `Prover` against a `Verifier` on a given statement and witness,
threading state and collecting the transcript. It is a *deterministic* function of
the random challenges (which are sampled by the calling context). This separation
means the security definitions are stated over transcripts, not over the code of
the parties.

### 3. Security (properties)
- **Completeness**: `∀ (x, w) ∈ R, Execution prover verifier x w accepts`.
- **Soundness / Knowledge Soundness**: For every cheating prover strategy, the
  probability of acceptance on a false statement is below some bound ε. In the
  round-by-round variant (used here), this is stated per-round using a *state
  function* that tracks how far the cheater has "committed" to a false path.

Keeping these layers separate makes it possible to state and reuse security theorems
generically (in `OracleReduction/Composition.lean` and `OracleReduction/Lifting.lean`)
without knowing the details of any particular protocol.

---

## Relationship to the Rest of the Library

```
OracleReduction/Basic.lean          ← you are here
        │
        ├── OracleReduction/Composition.lean   sequential composition of reductions
        ├── OracleReduction/Lifting.lean        context embedding / oracle lifting
        │
        └── Protocol/FRI/, Protocol/Sumcheck/  concrete protocol instances
```

Concrete protocols import `Basic.lean`, instantiate `Prover` and `OracleVerifier`
with their specific types, and then invoke the generic completeness/soundness
theorems from `Composition.lean`.

---

## Quick Reference: Key Definitions

Below is a summary of the main definitions exported from this file, with the
intended reading for each type parameter.

```lean
-- A single-round oracle interface for messages of type Msg
structure OracleInterface (Msg : Type u) where
  Query  : Type v
  Answer : Type w
  oracle : Msg → Query → Answer

-- An n-round prover with state type St, message types Msgs, challenge types Chals
structure Prover (Stmt Wit : Type) (n : ℕ)
    (Msgs Chals : Fin n → Type) (St : Type) where
  load      : Stmt → Wit → St
  -- At round i: given current state and challenge, produce message and new state
  prove     : (i : Fin n) → St → Chals i → Msgs i × St

-- An n-round verifier with oracle access to messages
structure OracleVerifier (Stmt : Type) (n : ℕ)
    (Msgs Chals : Fin n → Type)
    (OI : (i : Fin n) → OracleInterface (Msgs i))
    (Decision : Type) where
  -- At each round: produce a challenge (may query earlier oracles)
  challenge : (i : Fin n) → Stmt → List (OI · |>.Answer) → Chals i
  -- Final decision based on all oracle queries
  decide    : Stmt → (∀ i, List (OI i).Query) → Decision

-- Lift a reduction into a larger oracle context
def embed : OracleReduction 𝒪_small → IndexMap 𝒪_small 𝒪_large
          → OracleReduction 𝒪_large
```

*Note: the actual signatures in the file may use universe-polymorphic variants and
additional typeclass constraints (e.g., `DecidableEq`, `Fintype`). The above is
simplified for readability.*

---

## Contributing

If you extend this file, please:
- Keep the three-layer separation (interaction / execution / security) intact.
- Add an `OracleInterface` instance in the relevant `Protocol/` subfolder, not here.
- Reference this module docstring when writing protocol-specific documentation.
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
