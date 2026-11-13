# Oracle Reductions

This page is the KB concept hub for the architecture of ArkLib's interactive (oracle) reduction
layer: the prover/verifier interaction model, what makes a verifier an *oracle* verifier, how an
interaction is executed, how the security notions are stated, and how reductions compose.

It is written conceptually rather than as an API reference, so that it remains useful while the core
layer is being rewritten (see **Status** below). It describes *roles and structure*, and points to
the real modules and declarations for the current signatures.

## Status

The core interactive-oracle-reduction (IOR) layer is being rewritten in upstream PR
[#433](https://github.com/Verified-zkEVM/ArkLib/pull/433). Per the maintainer, conceptual KB
material is the right home for this documentation, rather than docstrings on
`ArkLib/OracleReduction/Basic.lean` directly. This page therefore documents the *concepts and
separation of concerns*, not exact type signatures, which may change. Declaration names cited below
were verified against the current worktree at the time of writing.

## Scope

Use this page when a question is about:

- the prover/verifier interaction model in ArkLib's `OracleReduction` layer;
- why some verifiers are *oracle* verifiers and what the `embed` mechanism does;
- where the *type-level* interaction structure ends and *execution semantics* / *security* begin;
- how reductions compose and why security is phrased reduction-style (relation in → relation out);
- which references back the formalization.

For the relationship to classical IOP terminology and the vector-IOP specialization, see the
companion page [`interactive-oracle-proofs.md`](interactive-oracle-proofs.md).

## What An Interactive Oracle Reduction Is

An **interactive oracle reduction (IOR)** is a public-coin interactive protocol between a *prover*
and a *verifier* that transforms one statement-witness relation into another. ArkLib models the
public-coin, fixed-schedule case: the sequence of who speaks in each step is fixed in advance by a
**protocol specification** rather than chosen adaptively.

ArkLib defines several specializations as thin layers over the general IOR notion. In
`ArkLib/OracleReduction/Basic.lean`:

- `Proof` is an interactive *proof* (output statement `Bool`, trivial output witness);
- `OracleProof` is the *oracle* analogue (`OracleReduction` into `Bool` with trivial oracle/witness
  output);
- `NonInteractiveReduction` is an IOR with a single prover-to-verifier message.

Conceptually, plain IOPs, vector IOPs, and polynomial IOPs are all further specializations of this
general reduction notion.

## The Interaction Model

### Rounds come from a `ProtocolSpec`

The schedule and message types of a protocol are fixed by a `ProtocolSpec n`
(`ArkLib/OracleReduction/ProtocolSpec/Basic.lean`), which carries:

- `dir : Fin n → Direction` — the direction of each of the `n` steps, either `.P_to_V` (prover sends
  a *message*) or `.V_to_P` (verifier sends a *challenge*); `Direction` is defined in
  `ArkLib/OracleReduction/Prelude.lean`;
- `«Type» : Fin n → Type` — the type sent in each step.

Steps are partitioned by direction into `MessageIdx` (prover-to-verifier indices) and `ChallengeIdx`
(verifier-to-prover indices), with `Message` / `Challenge` giving the type at each. The collected
forms `Messages`, `Challenges`, and `FullTranscript` describe an entire run. Importantly, ArkLib does
*not* require prover messages and verifier challenges to interleave; any fixed direction vector is
allowed, which gives flexibility when defining and composing reductions.

### Challenges vs. messages

The split between `MessageIdx` and `ChallengeIdx` is the heart of the public-coin model:

- **Messages** flow prover → verifier and carry the prover's claims.
- **Challenges** flow verifier → prover and are uniformly random. The verifier's randomness is
  modeled by a challenge oracle (`challengeOracleInterface`), so that the verifier's logic only ever
  *reads* a sampled challenge.

### Prover state evolves across rounds

The prover is a *stateful* algorithm whose state type changes round to round. In
`ArkLib/OracleReduction/Basic.lean`:

- `ProverState n` gives a family `PrvState : Fin (n + 1) → Type` — one state type before the first
  message and after each of the `n` steps.
- `ProverInput` initializes the state from the input statement and witness; `ProverRound` provides
  `sendMessage` (produces a message and the next state) and `receiveChallenge` (consumes a challenge
  and produces the next state).
- `ProverOutput` produces the prover's output (statement and witness) from the final state.
- `Prover` bundles these into the honest-prover type. The restricted variants `ProverInteraction`
  and `ProverInteractionWithOutput` drop the input/output requirements; these are used for malicious
  provers in the soundness games, which need only participate in the interaction.

The verifier, by contrast, is *stateless* in shape: `Verifier` is essentially a function from the
input statement and the `FullTranscript` to an output statement (inside an `OracleComp`, allowing
access to the shared oracle `oSpec`).

## What Makes A Verifier An *Oracle* Verifier

In a plain `Reduction`, the verifier sees the entire transcript in the clear. In an
`OracleReduction`, some inputs and prover messages are available to the verifier only through an
*oracle interface*, not as full data. This captures succinctness: the verifier queries large objects
(e.g. committed polynomials or codewords) at a few points instead of reading them.

### Oracle access via `OracleInterface`

The `OracleInterface` class (`ArkLib/OracleReduction/OracleInterface.lean`) equips a type with a
query type and an answering computation. The oracle verifier `OracleVerifier`
(`ArkLib/OracleReduction/Basic.lean`) takes instances `OracleInterface (OStmtIn i)` for each input
oracle statement and `OracleInterface (pSpec.Message i)` for each prover message, and its `verify`
field runs in an `OracleComp` that can query the shared oracle `oSpec`, the input oracle statements,
and the prover's messages. It receives the verifier `Challenges` directly (these are sampled
externally for public-coin protocols).

### The `embed` mechanism for output oracle statements

An oracle verifier may *forward* some of the oracles it has received as its own output oracle
statements, but it cannot fabricate new ones. This constraint is encoded by two fields of
`OracleVerifier`:

- `embed : ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIdx` — an embedding sending each output-oracle index either to an
  input-oracle index (`Sum.inl`) or to a prover-message index (`Sum.inr`);
- `hEq` — a proof that each `OStmtOut i` has the *same type* as the source the embedding selects.

Because `embed` is an embedding (injective), the output oracle statements are exactly a *subset* of
the input oracle statements together with the prover's oracle messages, with the rest dropped. There
is no way for the verifier to do anything more than choose which received oracles to retain. The
identity oracle verifier `OracleVerifier.id` illustrates the trivial case: `embed` is the left
inclusion and `hEq` is `rfl`.

This is exactly what lets an oracle reduction be viewed as a plain reduction: `toVerifier` simulates
the message/oracle queries using the in-the-clear data (via `OracleInterface.simOracle2`) and
materializes the output oracle statements by following `embed` and rewriting along `hEq`.
`OracleReduction.toReduction` lifts this to whole reductions.

A `NonAdaptive` oracle verifier is the special case where the list of queries is fixed up front
(depending only on the statement and challenges, not on earlier responses); it converts to the
general interface via `OracleVerifier.NonAdaptive.toOracleVerifier`.

## Separation Of Concerns

ArkLib deliberately splits the IOR formalization into three layers:

1. **Type-level interaction structure** — `ArkLib/OracleReduction/Basic.lean` and
   `ArkLib/OracleReduction/ProtocolSpec/Basic.lean`. These define *what the pieces are*
   (`ProtocolSpec`, `Prover`, `Verifier`, `OracleVerifier`, `Reduction`, `OracleReduction`) without
   saying how a run unfolds. `Basic.lean` defines only type signatures.

2. **Execution semantics** — `ArkLib/OracleReduction/Execution.lean`. This gives the operational
   meaning as `OracleComp` computations: `Prover.processRound` / `Prover.runToRound` / `Prover.run`
   drive the prover round by round, `Verifier.run` and `OracleVerifier.run` run the verifier, and
   `Reduction.run` / `OracleReduction.run` compose them into a full execution returning the
   transcript and outputs. Logging variants (`runWithLog`) additionally return the query logs used by
   the security games.

3. **Security definitions** — the `Security/` folder. `Security/Basic.lean` defines `completeness`
   (and `perfectCompleteness`), `Verifier.soundness`, and `Verifier.knowledgeSoundness` (with a
   straightline extractor `Extractor.Straightline`). `Security/RoundByRound.lean` defines the
   `StateFunction` / `KnowledgeStateFunction` machinery and the finer `rbrSoundness` /
   `rbrKnowledgeSoundness` notions.

Keeping these apart means the interaction *shape* (layer 1) can be reasoned about independently of
its probabilistic execution (layer 2) and of any particular adversary model (layer 3) — and is why
the rewrite in #433 can change signatures without invalidating the conceptual picture here.

## Reduction-Style Security: Relation In → Relation Out

Because an IOR transforms one relation into another, its security is stated *relative to two
relations*: an input relation and an output relation.

- **Completeness** (`completeness` in `Security/Basic.lean`): for every `(stmtIn, witIn)` in the
  input relation, the honest interaction yields, except with `completenessError`, an output pair in
  the output relation (and the prover's claimed output statement matches the verifier's).
- **Soundness** (`Verifier.soundness`): stated in terms of input/output *languages*; for any
  malicious prover and any input statement outside the input language, the verifier outputs a
  statement in the output language only with probability at most `soundnessError`.
- **Knowledge soundness** (`Verifier.knowledgeSoundness`): there is a straightline extractor that,
  from the transcript and query logs, recovers an input witness; the failure probability is bounded
  by `knowledgeError`.
- **Round-by-round soundness** (`Verifier.rbrSoundness` in `Security/RoundByRound.lean`): a
  `StateFunction` assigns a doomed/not-doomed predicate to each partial transcript such that it is
  false on the empty transcript for statements outside the input language, can only be flipped to
  true by a verifier challenge (not by a prover message), and forces a non-accepting verifier on
  full transcripts where it is false. The per-challenge error `rbrSoundnessError i` bounds the chance
  any single challenge flips a doomed prefix to a live one. `KnowledgeStateFunction` is the analogous
  notion for round-by-round *knowledge* soundness.

All notions are defined for the *verifier*; the honest prover does not appear in the soundness games.

## How Reductions Compose

The point of phrasing security as "relation in → relation out" is composition: chaining a reduction
from relation `R₀` to `R₁` with one from `R₁` to `R₂` should give a reduction from `R₀` to `R₂` whose
security degrades predictably.

- **Two-at-a-time** — `ArkLib/OracleReduction/Composition/Sequential/Append.lean` defines
  `Prover.append`, `Verifier.append`, `OracleVerifier.append`, `Reduction.append`, and
  `OracleReduction.append`, concatenating the protocol specifications and matching the output context
  of the first reduction to the input context of the second. The file's goal is to show the composite
  inherits the completeness and soundness properties of its parts (with extra extractor conditions).
- **Many-at-a-time** — `ArkLib/OracleReduction/Composition/Sequential/General.lean` defines
  `seqCompose` for an arbitrary `m + 1` reductions by iterating `append`, with the empty case
  reducing to the identity (`Prover.id` / `Verifier.id`).

A further structural transformation, the **BCS transform**
(`ArkLib/OracleReduction/BCS/Basic.lean`), turns an oracle reduction into a plain reduction by
replacing oracle messages/statements with commitments and running opening arguments for each of the
oracle verifier's queries; this captures both the original BCS construction and the polynomial-IOP +
polynomial-commitment pattern.

## Module Touchpoints

| Concept | Module |
| --- | --- |
| Protocol schedule, messages, challenges, transcripts | [`../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean`](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean) |
| Prover, verifier, oracle verifier, reduction types; `embed` | [`../../../ArkLib/OracleReduction/Basic.lean`](../../../ArkLib/OracleReduction/Basic.lean) |
| `Direction` and shared prelude | [`../../../ArkLib/OracleReduction/Prelude.lean`](../../../ArkLib/OracleReduction/Prelude.lean) |
| `OracleInterface` class and query simulation | [`../../../ArkLib/OracleReduction/OracleInterface.lean`](../../../ArkLib/OracleReduction/OracleInterface.lean) |
| Execution semantics (`run`, `processRound`, ...) | [`../../../ArkLib/OracleReduction/Execution.lean`](../../../ArkLib/OracleReduction/Execution.lean) |
| Completeness, soundness, knowledge soundness | [`../../../ArkLib/OracleReduction/Security/Basic.lean`](../../../ArkLib/OracleReduction/Security/Basic.lean) |
| State functions, round-by-round (knowledge) soundness | [`../../../ArkLib/OracleReduction/Security/RoundByRound.lean`](../../../ArkLib/OracleReduction/Security/RoundByRound.lean) |
| Sequential composition of two reductions | [`../../../ArkLib/OracleReduction/Composition/Sequential/Append.lean`](../../../ArkLib/OracleReduction/Composition/Sequential/Append.lean) |
| Sequential composition of many reductions | [`../../../ArkLib/OracleReduction/Composition/Sequential/General.lean`](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean) |
| BCS transform (oracle reduction → reduction) | [`../../../ArkLib/OracleReduction/BCS/Basic.lean`](../../../ArkLib/OracleReduction/BCS/Basic.lean) |

## References

- [`../papers/BCS16.md`](../papers/BCS16.md) — *Interactive Oracle Proofs* (Ben-Sasson, Chiesa,
  Spooner, TCC 2016): the original IOP / vector-IOP reference, cited in the core oracle-reduction
  layer and the basis of the BCS transform.
- `ChiesaYogev2024` — *Building Cryptographic Proofs from Hash Functions* (Chiesa, Yogev): the
  textbook ArkLib's formalization mostly follows; recorded in
  [`../../../website/blueprint/src/references.bib`](../../../website/blueprint/src/references.bib) and referenced in
  the Fiat-Shamir layer ([`../../../ArkLib/OracleReduction/FiatShamir/Basic.lean`](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean)).

## Notes

- This is the right entry point for tasks about the IOR *architecture*. For coding-theory proximity
  machinery used inside concrete proof systems, see
  [`reed-solomon-proximity.md`](reed-solomon-proximity.md).
- Detailed paper-to-code matrices belong on audit pages, not here.
