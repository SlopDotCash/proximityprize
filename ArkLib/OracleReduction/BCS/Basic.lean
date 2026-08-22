/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Commitments.Functional.Basic
import ArkLib.OracleReduction.Composition.Sequential.General

set_option linter.style.longFile 1900

open scoped NNReal

/-!
# The Generalized Ben-Sasson–Chiesa–Spooner (BCS) Compiler

This module formalizes the generalized Ben-Sasson–Chiesa–Spooner (BCS) compilation technique
(TCC 2016) at the protocol specification and reduction levels. The BCS transform compiles an
Interactive Oracle Reduction (IOR) into a standard Interactive Reduction (IR) (or interactive proof
system) by replacing oracle messages with cryptographic commitments.

In the compiled protocol, the prover sends commitments to each oracle message, and the verifier
interacts with the prover to receive challenges. Finally, in the opening phase, the prover shows
that the verifier's oracle queries are consistent with the sent commitments using interactive
opening arguments. This compiles oracle-dependent protocols into concrete protocols, capturing both
the classical Merkle-tree compilation of IOPs and modern polynomial commitment compilers
(e.g., Marlin, Plonk) for polynomial IOPs.

The transformation establishes a composition where:
1. Every oracle message type is replaced with a commitment type (via `renameMessage`).
2. An opening phase consisting of the sequential composition of the per-message commitment-opening
   protocol specifications is appended.

  ## What this file states (ArkLib#2: "initial attempt to state the BCS transform")

  This is a *definitional* first attempt at stating the transform; no security proofs are given.

  * `ProtocolSpec.renameMessage` (pre-existing): replace each prover-message type by a new type
    (here, a commitment type), keeping all directions fixed.
  * `ProtocolSpec.BCSOpeningPhase`: the opening phase as the sequential composition
    (`ProtocolSpec.seqCompose`) of the per-message commitment-opening protocol specs.
  * `ProtocolSpec.BCSTransform`: **fully general** at the protocol-spec level — the renamed
    interaction phase appended (`++ₚ`) to the opening phase.
  * `Reduction.bcsMessageOpening`: the per-message opening reduction extracted from a commitment
    `Commitment.Scheme` (this is exactly its `opening` proof).
  * `OracleReduction.BCSTransform`: the reduction-level transform, stated as `Reduction.append` of an
    interaction phase and an opening phase over `ProtocolSpec.BCSTransform`.

  ## What is deferred

  The reduction-level transform takes its two phases (interaction, opening) as inputs rather than
  constructing them from the input oracle reduction plus the commitment schemes. The honest
  constructions — the prover committing via `Scheme.commit` instead of sending each message, and the
  opening phase reading the oracle verifier's (possibly adaptive) query log to decide which openings
  to run and with which witnesses — are the dependent-type-plumbing-over-query-logs parts, and are
  deferred together with all security-preservation results (completeness, the soundness notions,
  HVZK) to the core oracle-reduction rewrite (ArkLib#433). Restricting to
  `OracleVerifier.NonAdaptive` removes the adaptivity blocker but not the type-threading one; see the
  design note at the end of the file. The fully general transform thus depends on #433.

  ## Notes

  The BCS transform has a lot of degrees of freedom. For instance, we can choose to run the opening
  arguments for each verifier's query in any order; here that choice of order is recorded explicitly
  by the ordering equivalence `e : pSpec.MessageIdx ≃ Fin m` passed to the transform.

  There are also a lot of variants and avenues for optimization:

  - We can ``batch'' many opening arguments together (using homomorphic properties of the commitment
    scheme, or via another round of interaction, or via specialized techniques like Merkle capping).

  ## References

  * [Ben-Sasson, E., Chiesa, A., and Spooner, N., *Interactive Oracle Proofs*, TCC 2016][BCS16] —
    the original BCS transform (vector IOPs + Merkle commitments).
  * [Chiesa, A. and Yogev, E., *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024]
    — textbook treatment of the BCS / hash-based-SNARG compilation.
-/

variable {n : ℕ}

namespace ProtocolSpec

/-- Switch the type of prover's messages in a protocol specification. The directions are preserved.
-/
def renameMessage (pSpec : ProtocolSpec n) (NewMessage : pSpec.MessageIdx → Type) :
    ProtocolSpec n :=
  ⟨ pSpec.dir,
    fun i => if h : pSpec.dir i = Direction.P_to_V then NewMessage ⟨i, h⟩ else pSpec.«Type» i⟩

/-! ### The BCS transform on protocol specifications

  The protocol-spec layer of the BCS transform is fully general: it takes the interaction phase of
  the original protocol with every prover message replaced by a commitment to it (via the existing
  `renameMessage`), and appends an opening phase consisting of the sequential composition of the
  per-message commitment-opening protocol specifications.

  The opening phase is the sequential composition (`ProtocolSpec.seqCompose`) of the per-message
  opening specs. Since `seqCompose` composes a `Fin m`-indexed family while the opening specs are
  indexed by `pSpec.MessageIdx`, we take an explicit ordering equivalence
  `e : pSpec.MessageIdx ≃ Fin m` as a parameter. This makes the order of the opening phase
  explicit: as noted in the module docstring, the BCS transform has a genuine degree of freedom in
  the order in which the opening arguments are run, and `e` records that choice. (Taking `e` as a
  parameter rather
  than the canonical `Fintype.equivFin` also keeps the definition computable.) -/

/-- The opening phase of the BCS transform: the sequential composition of the per-message
  commitment-opening protocol specifications, ordered by the equivalence `e : pSpec.MessageIdx ≃
  Fin m`. -/
def BCSOpeningPhase (pSpec : ProtocolSpec n) {m : ℕ}
    {nCom : pSpec.MessageIdx → ℕ} (pSpecCom : ∀ i, ProtocolSpec (nCom i))
    (e : pSpec.MessageIdx ≃ Fin m) :
    ProtocolSpec (Fin.vsum (fun j => nCom (e.symm j))) :=
  ProtocolSpec.seqCompose (fun j => pSpecCom (e.symm j))

/-- The BCS transformation on protocol specifications.

  Given an interaction-phase spec `pSpec`, a type `CommitmentType i` of commitments for each prover
  message `i`, a commitment-opening protocol spec `pSpecCom i` for each prover message, and an
  ordering `e : pSpec.MessageIdx ≃ Fin m` of the messages, the transformed spec is:

  * the interaction phase `pSpec.renameMessage CommitmentType`, in which every prover message is
    replaced by a commitment to it, followed by
  * the opening phase `BCSOpeningPhase`, which runs the per-message opening protocols in sequence.

  This is the faithful statement sketched by composing the renamed interaction phase with the
  per-message opening phase. -/
def BCSTransform (pSpec : ProtocolSpec n) {m : ℕ}
    {nCom : pSpec.MessageIdx → ℕ} (pSpecCom : ∀ i, ProtocolSpec (nCom i))
    (CommitmentType : pSpec.MessageIdx → Type) (e : pSpec.MessageIdx ≃ Fin m) :
    ProtocolSpec (n + Fin.vsum (fun j => nCom (e.symm j))) :=
  (pSpec.renameMessage CommitmentType) ++ₚ (pSpec.BCSOpeningPhase pSpecCom e)

end ProtocolSpec

open Commitment

namespace Reduction

variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]

variable {m : ℕ} {nCom : pSpec.MessageIdx → ℕ} {pSpecCom : ∀ i, ProtocolSpec (nCom i)}
    {Commitment Decommitment ComKey VerifKey : pSpec.MessageIdx → Type}

/-! ### The opening phase of the BCS transform

  The opening phase is fully constructible from the data of the commitment schemes: each scheme's
  `opening` field is a `Proof` (an interactive reduction whose output statement is `Bool`) for the
  evaluation of one committed message. The opening phase runs these one after another via the
  existing `Reduction.seqCompose`, ordered by `e : pSpec.MessageIdx ≃ Fin m`, over the protocol
  spec `ProtocolSpec.BCSOpeningPhase`.

  For a single message `i`, the opening proof proves the relation
  "the response `y` to query `q` against commitment `cm` is correct", with statement type
  `Commitment i × (q : (Oₘ i).Query) × (Oₘ i).Response q` and witness type
  `pSpec.Message i × Decommitment i`. Threading these statement/witness types through the sequential
  composition is what the `Stmt`/`Wit` families below record. -/

/-- The per-message opening reduction obtained from a commitment scheme for message `i`, given the
  committer/verifier keys. This is literally the scheme's `opening` proof, viewed as a `Reduction`
  over the opening protocol spec `pSpecCom i`. -/
def bcsMessageOpening (i : pSpec.MessageIdx)
    (scheme : Scheme oSpec (pSpec.Message i) (Commitment i) (Decommitment i)
      (ComKey i) (VerifKey i) (pSpecCom i))
    (keys : ComKey i × VerifKey i) :
    Reduction oSpec
      (Commitment i × (q : (Oₘ i).Query) × (Oₘ i).Response q)
      (pSpec.Message i × Decommitment i) Bool Unit (pSpecCom i) :=
  scheme.opening keys

end Reduction

namespace OracleReduction

variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]

variable {m : ℕ} {nCom : pSpec.MessageIdx → ℕ} {pSpecCom : ∀ i, ProtocolSpec (nCom i)}
    {Commitment Decommitment ComKey VerifKey : pSpec.MessageIdx → Type}

variable {StmtIn StmtOut WitIn WitOut : Type}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}

/-! ### The BCS transform on (oracle) reductions

  **Scope.** We state the reduction-level BCS transform as the sequential composition (via the
  existing `Reduction.append`) of two phases over the transformed spec
  `ProtocolSpec.BCSTransform pSpecCom CommitmentType e`:

  1. an **interaction phase** `interaction`, an interactive (non-oracle) reduction over
     `pSpec.renameMessage CommitmentType` — morally the original oracle reduction with every prover
     message replaced by a commitment to it — and
  2. an **opening phase** `opening`, an interactive reduction over
     `pSpec.BCSOpeningPhase pSpecCom e` — morally the verifier's evaluation queries discharged by
     the per-message opening proofs (see `Reduction.bcsMessageOpening`), composed in the order `e`.

  The honest construction of the **interaction phase** from the input oracle `reduction` and the
  commitment schemes (the prover commits to each message via `scheme.commit` instead of sending it,
  and the verifier checks the renamed transcript) and the honest construction of the **opening
  phase** from the verifier's query log (which queries to discharge, in which order, with which
  witnesses) are precisely the parts that require the dependent-type plumbing over query logs.
  These, together with the proofs that the transform preserves completeness / soundness / knowledge
  soundness / HVZK, are deferred to the core oracle-reduction rewrite (ArkLib#433). We therefore
  take the two phases as inputs and record the resulting type-level statement of the transform;
  this is the "initial attempt to state the BCS transform" called for by ArkLib#2.

  The fully general transform (no separate-phase inputs) is sketched in the design comment below. -/

/-- The BCS transformation on (interactive) reductions, stated as the sequential composition of the
  interaction phase (messages replaced by commitments) and the opening phase (per-message opening
  proofs run in sequence), over the BCS-transformed protocol spec
  `ProtocolSpec.BCSTransform pSpecCom CommitmentType e`.

  Here `StmtMid`/`WitMid` are the intermediate statement/witness handed from the interaction phase
  to the opening phase (it carries, e.g., the commitments, the queried points, and the openings
  needed
  by the opening phase). -/
def BCSTransform {StmtMid WitMid : Type} {CommitmentType : pSpec.MessageIdx → Type}
    (e : pSpec.MessageIdx ≃ Fin m)
    (interaction :
      Reduction oSpec StmtIn WitIn StmtMid WitMid (pSpec.renameMessage CommitmentType))
    (opening :
      Reduction oSpec StmtMid WitMid StmtOut WitOut (pSpec.BCSOpeningPhase pSpecCom e)) :
    Reduction oSpec StmtIn WitIn StmtOut WitOut
      (pSpec.BCSTransform pSpecCom CommitmentType e) :=
  Reduction.append interaction opening

/-! #### Current compiler-frontier interface

The definition above is the already-buildable reduction-level composition once the two phases are
available.  The compiler work that remains is to construct those phases from an input
`OracleReduction` and commitment schemes.  The structures below make that boundary explicit without
turning it into prose-only debt: callers can pass the phases today, while the future compiler must
replace the two realization fields by proofs produced from the oracle verifier/query-log machinery.
-/

/-- The two concrete phases of a BCS-compiled protocol, plus the two realization obligations that
are not yet constructible by the generic compiler.

`interaction_realizes_oracle_messages` should say that the interaction phase faithfully simulates
the source oracle reduction while replacing each oracle message by a commitment.
`opening_realizes_query_log` should say that the opening phase opens exactly the oracle queries made
by the verifier with the retained `(message, decommitment)` witnesses.  Both are left as `Prop`
fields because their
eventual statement depends on the query-log API being stabilized. -/
structure BCSCompiledPhases {StmtMid WitMid : Type}
    (CommitmentType : pSpec.MessageIdx → Type) (e : pSpec.MessageIdx ≃ Fin m) where
  interaction :
    Reduction oSpec StmtIn WitIn StmtMid WitMid (pSpec.renameMessage CommitmentType)
  opening :
    Reduction oSpec StmtMid WitMid StmtOut WitOut (pSpec.BCSOpeningPhase pSpecCom e)
  interaction_realizes_oracle_messages : Prop
  opening_realizes_query_log : Prop

/-- One verifier query to a committed oracle message, together with the commitment and response
that the BCS opening phase must justify. -/
structure BCSOpeningRequest (CommitmentType : pSpec.MessageIdx → Type) where
  messageIdx : pSpec.MessageIdx
  commitment : CommitmentType messageIdx
  query : (Oₘ messageIdx).Query
  response : (Oₘ messageIdx).Response query

/-- The dependent opening statement for one committed oracle message.

For `CommitmentType = Commitment`, this is exactly the statement type consumed by
`Reduction.bcsMessageOpening` at the message index `i`. -/
abbrev BCSOpeningStatementAt (CommitmentType : pSpec.MessageIdx → Type)
    (i : pSpec.MessageIdx) :=
  CommitmentType i × (q : (Oₘ i).Query) × (Oₘ i).Response q

/-- Convert one typed BCS opening request to the dependent opening statement expected by the
per-message commitment-opening reduction. -/
def BCSOpeningRequest.toOpeningStatement {CommitmentType : pSpec.MessageIdx → Type}
    (request : BCSOpeningRequest (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    BCSOpeningStatementAt (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType request.messageIdx :=
  (request.commitment, ⟨request.query, request.response⟩)

@[simp] theorem BCSOpeningRequest.toOpeningStatement_commitment
    {CommitmentType : pSpec.MessageIdx → Type}
    (request : BCSOpeningRequest (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    request.toOpeningStatement.1 = request.commitment :=
  rfl

@[simp] theorem BCSOpeningRequest.toOpeningStatement_query
    {CommitmentType : pSpec.MessageIdx → Type}
    (request : BCSOpeningRequest (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    request.toOpeningStatement.2.1 = request.query :=
  rfl

@[simp] theorem BCSOpeningRequest.toOpeningStatement_response
    {CommitmentType : pSpec.MessageIdx → Type}
    (request : BCSOpeningRequest (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    request.toOpeningStatement.2.2 = request.response :=
  rfl

/-- The indexed statement emitted by a typed opening request remembers the whole request. -/
theorem BCSOpeningRequest.indexed_toOpeningStatement_injective
    {CommitmentType : pSpec.MessageIdx → Type} :
    Function.Injective
      (fun request : BCSOpeningRequest (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType =>
        (⟨request.messageIdx, request.toOpeningStatement⟩ :
          (i : pSpec.MessageIdx) ×
            BCSOpeningStatementAt (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType i)) := by
  intro request₁ request₂ h
  cases request₁
  cases request₂
  cases h
  rfl

/-- The concrete query/opening schedule consumed by the BCS opening phase.

For a non-adaptive oracle verifier this schedule should be obtained from
`OracleVerifier.NonAdaptive.queryMsg` after the interaction phase has retained the corresponding
commitments and oracle responses.  In the fully adaptive case, the future query-log API should
produce the same shape from the realized verifier execution. -/
abbrev BCSOpeningSchedule (CommitmentType : pSpec.MessageIdx → Type) :=
  List (BCSOpeningRequest (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType)

/-- A schedule as the list of indexed opening statements that the per-message opening reductions
must discharge. -/
def BCSOpeningSchedule.toOpeningStatements {CommitmentType : pSpec.MessageIdx → Type}
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    List ((i : pSpec.MessageIdx) ×
      BCSOpeningStatementAt (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType i) :=
  schedule.map fun request => ⟨request.messageIdx, request.toOpeningStatement⟩

@[simp] theorem BCSOpeningSchedule.toOpeningStatements_nil
    {CommitmentType : pSpec.MessageIdx → Type} :
    (BCSOpeningSchedule.toOpeningStatements (pSpec := pSpec) (Oₘ := Oₘ)
      (CommitmentType := CommitmentType) []) = [] :=
  rfl

@[simp] theorem BCSOpeningSchedule.toOpeningStatements_cons
    {CommitmentType : pSpec.MessageIdx → Type}
    (request : BCSOpeningRequest (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType)
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    BCSOpeningSchedule.toOpeningStatements (request :: schedule) =
      ⟨request.messageIdx, request.toOpeningStatement⟩ ::
        BCSOpeningSchedule.toOpeningStatements schedule :=
  rfl

@[simp] theorem BCSOpeningSchedule.toOpeningStatements_length
    {CommitmentType : pSpec.MessageIdx → Type}
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    schedule.toOpeningStatements.length = schedule.length :=
  List.length_map _

@[simp] theorem BCSOpeningSchedule.toOpeningStatements_append
    {CommitmentType : pSpec.MessageIdx → Type}
    (schedule₁ schedule₂ : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    (schedule₁ ++ schedule₂).toOpeningStatements =
      schedule₁.toOpeningStatements ++ schedule₂.toOpeningStatements := by
  simp [BCSOpeningSchedule.toOpeningStatements]

@[simp] theorem BCSOpeningSchedule.toOpeningStatements_take
    {CommitmentType : pSpec.MessageIdx → Type}
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) (k : ℕ) :
    BCSOpeningSchedule.toOpeningStatements (schedule.take k) =
      schedule.toOpeningStatements.take k := by
  simp [BCSOpeningSchedule.toOpeningStatements]

@[simp] theorem BCSOpeningSchedule.toOpeningStatements_drop
    {CommitmentType : pSpec.MessageIdx → Type}
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) (k : ℕ) :
    BCSOpeningSchedule.toOpeningStatements (schedule.drop k) =
      schedule.toOpeningStatements.drop k := by
  simp [BCSOpeningSchedule.toOpeningStatements]

@[simp] theorem BCSOpeningSchedule.toOpeningStatements_reverse
    {CommitmentType : pSpec.MessageIdx → Type}
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    BCSOpeningSchedule.toOpeningStatements schedule.reverse =
      schedule.toOpeningStatements.reverse := by
  simp [BCSOpeningSchedule.toOpeningStatements]

@[simp] theorem BCSOpeningSchedule.toOpeningStatements_concat
    {CommitmentType : pSpec.MessageIdx → Type}
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType)
    (request : BCSOpeningRequest (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    BCSOpeningSchedule.toOpeningStatements (schedule.concat request) =
      schedule.toOpeningStatements.concat ⟨request.messageIdx, request.toOpeningStatement⟩ := by
  induction schedule with
  | nil => rfl
  | cons head schedule _ =>
      simp [BCSOpeningSchedule.toOpeningStatements]

/-- Projecting the indexed opening statements back to message indices recovers the message-index
projection of the original typed schedule. -/
@[simp] theorem BCSOpeningSchedule.toOpeningStatements_map_messageIdx
    {CommitmentType : pSpec.MessageIdx → Type}
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    schedule.toOpeningStatements.map (fun statement => statement.1) =
      schedule.map (fun request => request.messageIdx) := by
  induction schedule with
  | nil => rfl
  | cons request schedule _ =>
      simp [BCSOpeningSchedule.toOpeningStatements]

/-- Filtering a typed opening schedule by message index commutes with conversion to indexed
opening statements. This is the per-message query-log accounting bridge: grouping the BCS opening
requests for one committed oracle message gives the same indexed statements as filtering the
converted opening-statement view. -/
@[simp] theorem BCSOpeningSchedule.toOpeningStatements_filter_messageIdx
    {CommitmentType : pSpec.MessageIdx → Type} [DecidableEq pSpec.MessageIdx]
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType)
    (i : pSpec.MessageIdx) :
    BCSOpeningSchedule.toOpeningStatements
        (schedule.filter (fun request => request.messageIdx = i)) =
      schedule.toOpeningStatements.filter (fun statement => statement.1 = i) := by
  induction schedule with
  | nil => rfl
  | cons request schedule ih =>
      by_cases hidx : request.messageIdx = i
      · simpa [BCSOpeningSchedule.toOpeningStatements, hidx] using ih
      · simpa [BCSOpeningSchedule.toOpeningStatements, hidx] using ih

/-- Converting a BCS opening schedule to indexed statements preserves the number of requests for
each committed oracle message. -/
theorem BCSOpeningSchedule.toOpeningStatements_filter_messageIdx_length
    {CommitmentType : pSpec.MessageIdx → Type} [DecidableEq pSpec.MessageIdx]
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType)
    (i : pSpec.MessageIdx) :
    (schedule.toOpeningStatements.filter (fun statement => statement.1 = i)).length =
      (schedule.filter (fun request => request.messageIdx = i)).length := by
  rw [← BCSOpeningSchedule.toOpeningStatements_filter_messageIdx (schedule := schedule) i]
  exact BCSOpeningSchedule.toOpeningStatements_length
    (schedule.filter (fun request => request.messageIdx = i))

/-- Summing per-message opening counts over all message indices recovers the total schedule
length. This is the finite-index accounting form of the per-message query-log split. -/
theorem BCSOpeningSchedule.sum_filter_messageIdx_length
    {CommitmentType : pSpec.MessageIdx → Type} [Fintype pSpec.MessageIdx]
    [DecidableEq pSpec.MessageIdx]
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    (∑ i : pSpec.MessageIdx,
      (schedule.filter (fun request => request.messageIdx = i)).length) = schedule.length := by
  induction schedule with
  | nil => simp
  | cons request schedule ih =>
      calc
        (∑ i : pSpec.MessageIdx,
          ((request :: schedule).filter (fun request => request.messageIdx = i)).length)
            = (∑ i : pSpec.MessageIdx,
                ((if request.messageIdx = i then 1 else 0) +
                  (schedule.filter (fun request => request.messageIdx = i)).length)) := by
                refine Finset.sum_congr rfl ?_
                intro i _
                by_cases hidx : request.messageIdx = i
                · simp [hidx, Nat.add_comm]
                · simp [hidx]
        _ = (∑ i : pSpec.MessageIdx, (if request.messageIdx = i then 1 else 0 : ℕ)) +
              ∑ i : pSpec.MessageIdx,
                (schedule.filter (fun request => request.messageIdx = i)).length := by
            rw [Finset.sum_add_distrib]
        _ = 1 + schedule.length := by
            rw [ih, Fintype.sum_ite_eq]
        _ = (request :: schedule).length := by simp [Nat.add_comm]

/-- The indexed opening-statement view has the same finite-message total opening count as the
typed schedule. -/
theorem BCSOpeningSchedule.toOpeningStatements_sum_filter_messageIdx_length
    {CommitmentType : pSpec.MessageIdx → Type} [Fintype pSpec.MessageIdx]
    [DecidableEq pSpec.MessageIdx]
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    (∑ i : pSpec.MessageIdx,
      (schedule.toOpeningStatements.filter (fun statement => statement.1 = i)).length)
      = schedule.length := by
  rw [← BCSOpeningSchedule.sum_filter_messageIdx_length (schedule := schedule)]
  exact Finset.sum_congr rfl fun i _ =>
    BCSOpeningSchedule.toOpeningStatements_filter_messageIdx_length schedule i

/-- Projecting the indexed opening statements back to commitments recovers the indexed commitment
projection of the original typed schedule. -/
@[simp] theorem BCSOpeningSchedule.toOpeningStatements_map_commitment
    {CommitmentType : pSpec.MessageIdx → Type}
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    schedule.toOpeningStatements.map (fun statement =>
      (⟨statement.1, statement.2.1⟩ :
        (i : pSpec.MessageIdx) × CommitmentType i)) =
      schedule.map (fun request =>
        (⟨request.messageIdx, request.commitment⟩ :
          (i : pSpec.MessageIdx) × CommitmentType i)) := by
  simp [BCSOpeningSchedule.toOpeningStatements]

/-- Projecting the indexed opening statements back to queries recovers the indexed query
projection of the original typed schedule. -/
@[simp] theorem BCSOpeningSchedule.toOpeningStatements_map_query
    {CommitmentType : pSpec.MessageIdx → Type}
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    schedule.toOpeningStatements.map (fun statement =>
      (⟨statement.1, statement.2.2.1⟩ :
        (i : pSpec.MessageIdx) × (Oₘ i).Query)) =
      schedule.map (fun request =>
        (⟨request.messageIdx, request.query⟩ :
          (i : pSpec.MessageIdx) × (Oₘ i).Query)) := by
  simp [BCSOpeningSchedule.toOpeningStatements]

/-- Projecting the indexed opening statements back to query responses recovers the indexed response
projection of the original typed schedule. -/
@[simp] theorem BCSOpeningSchedule.toOpeningStatements_map_response
    {CommitmentType : pSpec.MessageIdx → Type}
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    schedule.toOpeningStatements.map (fun statement =>
      (⟨statement.1, statement.2.2⟩ :
        (i : pSpec.MessageIdx) × (q : (Oₘ i).Query) × (Oₘ i).Response q)) =
      schedule.map (fun request =>
        (⟨request.messageIdx, ⟨request.query, request.response⟩⟩ :
          (i : pSpec.MessageIdx) × (q : (Oₘ i).Query) × (Oₘ i).Response q)) := by
  induction schedule with
  | nil => rfl
  | cons request schedule _ =>
      cases request
      simp [BCSOpeningSchedule.toOpeningStatements, BCSOpeningRequest.toOpeningStatement]

/-- Bounded lookup in the indexed opening-statement view is bounded lookup in the typed schedule
followed by the indexed-statement conversion. -/
@[simp] theorem BCSOpeningSchedule.toOpeningStatements_getElem
    {CommitmentType : pSpec.MessageIdx → Type}
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) (idx : ℕ)
    (hidx : idx < schedule.length) :
    schedule.toOpeningStatements[idx]'(by
      simpa [BCSOpeningSchedule.toOpeningStatements_length] using hidx) =
      (⟨(schedule[idx]'hidx).messageIdx, (schedule[idx]'hidx).toOpeningStatement⟩ :
        (i : pSpec.MessageIdx) ×
          BCSOpeningStatementAt (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType i) := by
  induction schedule generalizing idx with
  | nil =>
      cases hidx
  | cons request schedule ih =>
      cases idx with
      | zero => rfl
      | succ idx =>
          simp [BCSOpeningSchedule.toOpeningStatements]

/-- Membership in the indexed opening-statement view is exactly membership in the original typed
schedule, transported through `BCSOpeningRequest.toOpeningStatement`. -/
@[simp] theorem BCSOpeningSchedule.mem_toOpeningStatements_iff
    {CommitmentType : pSpec.MessageIdx → Type}
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType)
    (statement : (i : pSpec.MessageIdx) ×
      BCSOpeningStatementAt (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType i) :
    statement ∈ schedule.toOpeningStatements ↔
      ∃ request ∈ schedule, statement = ⟨request.messageIdx, request.toOpeningStatement⟩ := by
  constructor
  · intro h
    rw [BCSOpeningSchedule.toOpeningStatements] at h
    rcases List.mem_map.mp h with ⟨request, hmem, hstatement⟩
    exact ⟨request, hmem, hstatement.symm⟩
  · rintro ⟨request, hmem, hstatement⟩
    rw [BCSOpeningSchedule.toOpeningStatements]
    exact List.mem_map.mpr ⟨request, hmem, hstatement.symm⟩

/-- Every request in a typed opening schedule contributes its indexed opening statement. -/
theorem BCSOpeningSchedule.mem_toOpeningStatements_of_mem
    {CommitmentType : pSpec.MessageIdx → Type}
    {schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType}
    {request : BCSOpeningRequest (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType}
    (hrequest : request ∈ schedule) :
    ⟨request.messageIdx, request.toOpeningStatement⟩ ∈ schedule.toOpeningStatements :=
  (BCSOpeningSchedule.mem_toOpeningStatements_iff schedule _).2 ⟨request, hrequest, rfl⟩

/-- A statement in the indexed opening-statement view comes from a typed request in the original
schedule. -/
theorem BCSOpeningSchedule.exists_request_of_mem_toOpeningStatements
    {CommitmentType : pSpec.MessageIdx → Type}
    {schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType}
    {statement : (i : pSpec.MessageIdx) ×
      BCSOpeningStatementAt (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType i}
    (hstatement : statement ∈ schedule.toOpeningStatements) :
    ∃ request ∈ schedule, statement = ⟨request.messageIdx, request.toOpeningStatement⟩ :=
  (BCSOpeningSchedule.mem_toOpeningStatements_iff schedule statement).1 hstatement

/-- Universal quantification over indexed opening statements is equivalent to quantification over
the originating typed opening requests. -/
theorem BCSOpeningSchedule.toOpeningStatements_forall
    {CommitmentType : pSpec.MessageIdx → Type}
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType)
    (P : ((i : pSpec.MessageIdx) ×
      BCSOpeningStatementAt (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType i) → Prop) :
    (∀ statement ∈ schedule.toOpeningStatements, P statement) ↔
      ∀ request ∈ schedule,
        P (⟨request.messageIdx, request.toOpeningStatement⟩ :
          (i : pSpec.MessageIdx) ×
            BCSOpeningStatementAt (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType i) := by
  constructor
  · intro h request hrequest
    exact h _ (BCSOpeningSchedule.mem_toOpeningStatements_of_mem hrequest)
  · intro h statement hstatement
    obtain ⟨request, hrequest, hstatement_eq⟩ :=
      BCSOpeningSchedule.exists_request_of_mem_toOpeningStatements hstatement
    simpa [hstatement_eq] using h request hrequest

/-- Existential quantification over indexed opening statements is equivalent to existence of an
originating typed opening request. -/
theorem BCSOpeningSchedule.toOpeningStatements_exists
    {CommitmentType : pSpec.MessageIdx → Type}
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType)
    (P : ((i : pSpec.MessageIdx) ×
      BCSOpeningStatementAt (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType i) → Prop) :
    (∃ statement ∈ schedule.toOpeningStatements, P statement) ↔
      ∃ request ∈ schedule,
        P (⟨request.messageIdx, request.toOpeningStatement⟩ :
          (i : pSpec.MessageIdx) ×
            BCSOpeningStatementAt (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType i) := by
  constructor
  · rintro ⟨statement, hstatement, hp⟩
    obtain ⟨request, hrequest, hstatement_eq⟩ :=
      BCSOpeningSchedule.exists_request_of_mem_toOpeningStatements hstatement
    exact ⟨request, hrequest, by simpa [hstatement_eq] using hp⟩
  · rintro ⟨request, hrequest, hp⟩
    exact ⟨_, BCSOpeningSchedule.mem_toOpeningStatements_of_mem hrequest, hp⟩

/-- If one typed opening schedule is contained in another, then its indexed opening-statement view
is contained in the other indexed view. -/
theorem BCSOpeningSchedule.toOpeningStatements_subset
    {CommitmentType : pSpec.MessageIdx → Type}
    {schedule₁ schedule₂ : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType}
    (hsubset : ∀ request, request ∈ schedule₁ → request ∈ schedule₂) :
    ∀ statement, statement ∈ schedule₁.toOpeningStatements →
      statement ∈ schedule₂.toOpeningStatements := by
  intro statement hstatement
  obtain ⟨request, hrequest, hstatement_eq⟩ :=
    BCSOpeningSchedule.exists_request_of_mem_toOpeningStatements hstatement
  exact (BCSOpeningSchedule.mem_toOpeningStatements_iff schedule₂ statement).2
    ⟨request, hsubset request hrequest, hstatement_eq⟩

/-- The indexed opening-statement view determines the original typed opening schedule. -/
theorem BCSOpeningSchedule.toOpeningStatements_injective
    {CommitmentType : pSpec.MessageIdx → Type} :
    Function.Injective
      (fun schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType =>
        schedule.toOpeningStatements) := by
  intro schedule₁ schedule₂ h
  dsimp [BCSOpeningSchedule.toOpeningStatements] at h
  exact
    (BCSOpeningRequest.indexed_toOpeningStatement_injective
      (pSpec := pSpec) (Oₘ := Oₘ) (CommitmentType := CommitmentType)).list_map h

/-- Duplicate-free typed opening schedules remain duplicate-free after conversion to indexed
opening statements. -/
theorem BCSOpeningSchedule.toOpeningStatements_nodup
    {CommitmentType : pSpec.MessageIdx → Type}
    {schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType}
    (hschedule : schedule.Nodup) :
    schedule.toOpeningStatements.Nodup := by
  rw [BCSOpeningSchedule.toOpeningStatements]
  exact hschedule.map
    (BCSOpeningRequest.indexed_toOpeningStatement_injective
      (pSpec := pSpec) (Oₘ := Oₘ) (CommitmentType := CommitmentType))

/-- Duplicate-freeness is equivalent before and after conversion to indexed opening statements. -/
@[simp] theorem BCSOpeningSchedule.toOpeningStatements_nodup_iff
    {CommitmentType : pSpec.MessageIdx → Type}
    (schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    schedule.toOpeningStatements.Nodup ↔ schedule.Nodup := by
  rw [BCSOpeningSchedule.toOpeningStatements]
  exact List.nodup_map_iff
    (BCSOpeningRequest.indexed_toOpeningStatement_injective
      (pSpec := pSpec) (Oₘ := Oₘ) (CommitmentType := CommitmentType))

/-- The typed opening-log boundary for the not-yet-generic BCS compiler.

The current `BCSCompiledPhases` interface still accepts an abstract opening phase.  This structure
records the concrete schedule that such an opening phase is meant to discharge, plus the two proof
obligations that connect the schedule back to the source oracle verifier and to retained
opening witnesses. -/
structure BCSOpeningLogFrontier (CommitmentType : pSpec.MessageIdx → Type) where
  schedule : BCSOpeningSchedule (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType
  schedule_realizes_query_log : Prop
  schedule_has_retained_witnesses : Prop

/-- The typed opening-log obligations needed before an abstract BCS opening phase can be read as
faithfully discharging the source verifier's oracle queries. -/
def BCSOpeningLogFrontierSatisfied {CommitmentType : pSpec.MessageIdx → Type}
    (log : BCSOpeningLogFrontier (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) : Prop :=
  log.schedule_realizes_query_log ∧ log.schedule_has_retained_witnesses

/-- Package the two opening-log obligations from their independent proof bricks. -/
theorem BCSOpeningLogFrontierSatisfied.intro {CommitmentType : pSpec.MessageIdx → Type}
    {log : BCSOpeningLogFrontier (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType}
    (hQueryLog : log.schedule_realizes_query_log)
    (hWitnesses : log.schedule_has_retained_witnesses) :
    BCSOpeningLogFrontierSatisfied log :=
  ⟨hQueryLog, hWitnesses⟩

/-- Project the query-log realization brick from the typed opening-log frontier. -/
theorem BCSOpeningLogFrontierSatisfied.queryLog {CommitmentType : pSpec.MessageIdx → Type}
    {log : BCSOpeningLogFrontier (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType}
    (h : BCSOpeningLogFrontierSatisfied log) :
    log.schedule_realizes_query_log :=
  h.1

/-- Project the retained-witness brick from the typed opening-log frontier. -/
theorem BCSOpeningLogFrontierSatisfied.retainedWitnesses
    {CommitmentType : pSpec.MessageIdx → Type}
    {log : BCSOpeningLogFrontier (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType}
    (h : BCSOpeningLogFrontierSatisfied log) :
    log.schedule_has_retained_witnesses :=
  h.2

/-- The typed opening-log frontier checklist is exactly its two named fields. -/
theorem BCSOpeningLogFrontierSatisfied.iff_fields {CommitmentType : pSpec.MessageIdx → Type}
    {log : BCSOpeningLogFrontier (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType} :
    BCSOpeningLogFrontierSatisfied log ↔
      log.schedule_realizes_query_log ∧ log.schedule_has_retained_witnesses :=
  Iff.rfl

/-- The remaining bridge from a discharged typed opening log to the abstract opening-phase
realization field carried by `BCSCompiledPhases`.  The eventual generic compiler should prove this
from the query-log API and the construction of the opening phase. -/
def BCSOpeningLogBridge {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    (phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e)
    (log : BCSOpeningLogFrontier (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) : Prop :=
  BCSOpeningLogFrontierSatisfied log → phases.opening_realizes_query_log

/-- Apply a discharged typed opening-log bridge to a satisfied opening-log frontier. -/
theorem BCSOpeningLogBridge.apply {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {log : BCSOpeningLogFrontier (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType}
    (hBridge : BCSOpeningLogBridge phases log)
    (hLog : BCSOpeningLogFrontierSatisfied log) :
    phases.opening_realizes_query_log :=
  hBridge hLog

/-- A phase that already realizes the query log supplies the trivial opening-log bridge. -/
theorem BCSOpeningLogBridge.ofOpeningRealization {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {log : BCSOpeningLogFrontier (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType}
    (hOpening : phases.opening_realizes_query_log) :
    BCSOpeningLogBridge phases log :=
  fun _ => hOpening

/-- Interpret a packaged BCS compiler-frontier object as the currently available transformed
reduction.  This is definitionally the `Reduction.append` composition used by `BCSTransform`. -/
def BCSCompiledPhases.toReduction {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    (phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e) :
    Reduction oSpec StmtIn WitIn StmtOut WitOut
      (pSpec.BCSTransform pSpecCom CommitmentType e) :=
  BCSTransform e phases.interaction phases.opening

/-- The phase-realization half of the BCS compiler frontier: the interaction phase must realize
the original oracle-message flow through commitments, and the opening phase must realize the
verifier's query log through commitment openings. This is deliberately a conjunction of the two
fields already carried by `BCSCompiledPhases`, so downstream files can require the compiler-frontier
content as one named hypothesis while still projecting the two independent bricks. -/
def BCSPhaseRealizationFrontier {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    (phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e) : Prop :=
  phases.interaction_realizes_oracle_messages ∧ phases.opening_realizes_query_log

omit Oₘ in
/-- Package the two phase-realization fields directly. -/
theorem BCSPhaseRealizationFrontier.intro {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    (hInteraction : phases.interaction_realizes_oracle_messages)
    (hOpening : phases.opening_realizes_query_log) :
    BCSPhaseRealizationFrontier phases :=
  ⟨hInteraction, hOpening⟩

/-- Project the interaction-realization brick from the named phase frontier. -/
theorem BCSPhaseRealizationFrontier.interaction {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    (h : BCSPhaseRealizationFrontier phases) :
    phases.interaction_realizes_oracle_messages :=
  h.1

/-- Project the query-log-opening brick from the named phase frontier. -/
theorem BCSPhaseRealizationFrontier.opening {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    (h : BCSPhaseRealizationFrontier phases) :
    phases.opening_realizes_query_log :=
  h.2

/-- A packaged phase-realization frontier supplies the opening-log bridge directly. -/
theorem BCSOpeningLogBridge.ofPhaseRealizationFrontier {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {log : BCSOpeningLogFrontier (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType}
    (hPhase : BCSPhaseRealizationFrontier phases) :
    BCSOpeningLogBridge phases log :=
  fun _ => BCSPhaseRealizationFrontier.opening hPhase

omit Oₘ in
/-- Expand the phase-realization frontier into its two named phase obligations. -/
theorem BCSPhaseRealizationFrontier.iff_fields {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e} :
    BCSPhaseRealizationFrontier phases ↔
      phases.interaction_realizes_oracle_messages ∧ phases.opening_realizes_query_log :=
  Iff.rfl

/-- Build the phase-realization frontier from an interaction-realization proof and a discharged
typed opening-log frontier, provided the remaining opening-log bridge is available. -/
theorem BCSPhaseRealizationFrontier.ofOpeningLogBridge {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {log : BCSOpeningLogFrontier (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType}
    (hInteraction : phases.interaction_realizes_oracle_messages)
    (hLog : BCSOpeningLogFrontierSatisfied log)
    (hBridge : BCSOpeningLogBridge phases log) :
    BCSPhaseRealizationFrontier phases :=
  ⟨hInteraction, hBridge hLog⟩

/-- **Proof-carrying compiled phases** (issue #342, the API-level repair): a
`BCSCompiledPhases` together with *proofs* of its two realization payloads.  The base
structure keeps its `Prop` payload fields (the eventual generic compiler must be able to
*state* the obligations before constructing the proofs, and their final shape depends on
the query-log API), but instances of this extension cannot smuggle vacuous payloads:
whatever propositions the payload fields carry must actually be proved.  Downstream
files that want the realization content as hypotheses should take a
`BCSCompiledPhasesLawful` (or its `realizationFrontier`) instead of a bare
`BCSCompiledPhases`. -/
structure BCSCompiledPhasesLawful {StmtMid WitMid : Type}
    (CommitmentType : pSpec.MessageIdx → Type) (e : pSpec.MessageIdx ≃ Fin m) extends
    BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e where
  /-- The interaction phase's realization payload is proved, not merely stated. -/
  interaction_realization_holds : toBCSCompiledPhases.interaction_realizes_oracle_messages
  /-- The opening phase's realization payload is proved, not merely stated. -/
  opening_realization_holds : toBCSCompiledPhases.opening_realizes_query_log

omit Oₘ in
/-- Lawful compiled phases satisfy the phase-realization frontier outright. -/
theorem BCSCompiledPhasesLawful.realizationFrontier {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    (phases : BCSCompiledPhasesLawful (oSpec := oSpec) (pSpec := pSpec)
      (pSpecCom := pSpecCom) (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut)
      (WitOut := WitOut) (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e) :
    BCSPhaseRealizationFrontier phases.toBCSCompiledPhases :=
  ⟨phases.interaction_realization_holds, phases.opening_realization_holds⟩

/-- Lawful compiled phases supply the opening-log bridge for any typed opening log. -/
theorem BCSCompiledPhasesLawful.openingLogBridge {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    (phases : BCSCompiledPhasesLawful (oSpec := oSpec) (pSpec := pSpec)
      (pSpecCom := pSpecCom) (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut)
      (WitOut := WitOut) (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e)
    (log : BCSOpeningLogFrontier (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType) :
    BCSOpeningLogBridge phases.toBCSCompiledPhases log :=
  fun _ => phases.opening_realization_holds

/-- `BCSCompiledPhases.toReduction` is exactly the appended BCS transform on the packaged
interaction and opening phases. This small bridge lets downstream code unfold the current compiler
frontier through a named theorem rather than through record projections. -/
theorem BCSCompiledPhases.toReduction_eq_BCSTransform {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    (phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e) :
    phases.toReduction = BCSTransform e phases.interaction phases.opening :=
  rfl

omit Oₘ in
/-- Perfect completeness of packaged BCS phases composes through the concrete BCS reduction.

This is the security-preservation statement available before the generic compiler constructs the
phases themselves: once the committed-interaction phase and the opening phase are already supplied,
perfect completeness of the appended `BCSTransform` follows from the existing binary append theorem.
The conclusion is stated with the canonical challenge sampler for the appended spec
`pSpec.renameMessage CommitmentType ++ₚ pSpec.BCSOpeningPhase pSpecCom e`, which is definitionally
`ProtocolSpec.BCSTransform`. -/
theorem BCSCompiledPhases.toReduction_perfectCompleteness_of_append {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    [∀ i, SampleableType ((pSpec.renameMessage CommitmentType).Challenge i)]
    [∀ i, SampleableType ((pSpec.BCSOpeningPhase pSpecCom e).Challenge i)]
    (phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e)
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {relIn : Set (StmtIn × WitIn)} {relMid : Set (StmtMid × WitMid)}
    {relOut : Set (StmtOut × WitOut)}
    (hInteraction :
      phases.interaction.perfectCompleteness init impl relIn relMid)
    (hOpening : phases.opening.perfectCompleteness init impl relMid relOut)
    (hAppend :
      Reduction.reductionAppendPerfectCompletenessResidual
        (oSpec := oSpec) (init := init) (impl := impl)
        phases.interaction phases.opening hInteraction hOpening) :
    @Reduction.perfectCompleteness _ oSpec StmtIn WitIn StmtOut WitOut
      (n + Fin.vsum (fun j => nCom (e.symm j)))
      (pSpec.renameMessage CommitmentType ++ₚ pSpec.BCSOpeningPhase pSpecCom e)
      (fun i => ProtocolSpec.instSampleableTypeChallengeAppend i)
      σ init impl relIn relOut phases.toReduction := by
  simpa [BCSCompiledPhases.toReduction, BCSTransform, ProtocolSpec.BCSTransform] using
    (Reduction.reduction_append_perfectCompleteness
      (oSpec := oSpec) (init := init) (impl := impl)
      phases.interaction phases.opening hInteraction hOpening hAppend)

omit Oₘ in
/-- Additive completeness of packaged BCS phases composes through the concrete BCS reduction.

This exposes a real `Reduction.completeness` bridge for the already-supplied phases while preserving
the known append-completeness residual as the remaining deep dependency. The conclusion uses the
canonical challenge sampler for the appended spec, which is definitionally the BCS-transformed
protocol specification. -/
theorem BCSCompiledPhases.toReduction_completeness_of_append {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    [∀ i, SampleableType ((pSpec.renameMessage CommitmentType).Challenge i)]
    [∀ i, SampleableType ((pSpec.BCSOpeningPhase pSpecCom e).Challenge i)]
    (phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e)
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {relIn : Set (StmtIn × WitIn)} {relMid : Set (StmtMid × WitMid)}
    {relOut : Set (StmtOut × WitOut)} {εInteraction εOpening : ℝ≥0}
    (hInteraction :
      phases.interaction.completeness init impl relIn relMid εInteraction)
    (hOpening : phases.opening.completeness init impl relMid relOut εOpening)
    (hAppend :
      Reduction.reductionAppendCompletenessResidual
        (oSpec := oSpec) (init := init) (impl := impl)
        phases.interaction phases.opening hInteraction hOpening) :
    @Reduction.completeness _ oSpec StmtIn WitIn StmtOut WitOut
      (n + Fin.vsum (fun j => nCom (e.symm j)))
      (pSpec.renameMessage CommitmentType ++ₚ pSpec.BCSOpeningPhase pSpecCom e)
      (fun i => ProtocolSpec.instSampleableTypeChallengeAppend i)
      σ init impl relIn relOut phases.toReduction (εInteraction + εOpening) := by
  simpa [BCSCompiledPhases.toReduction, BCSTransform, ProtocolSpec.BCSTransform] using
    (Reduction.reduction_append_completeness
      (oSpec := oSpec) (init := init) (impl := impl)
      phases.interaction phases.opening hInteraction hOpening hAppend)

omit Oₘ in
/-- Soundness of packaged BCS phases composes through the concrete BCS verifier.

This is the verifier-side analogue of `toReduction_completeness_of_append`: it packages the
already-supplied committed-interaction and opening verifiers with the existing binary append
soundness theorem, while preserving the append soundness residual as the remaining deep dependency.
The conclusion uses the canonical challenge sampler for the appended spec, definitionally the
BCS-transformed protocol specification. -/
theorem BCSCompiledPhases.toReduction_soundness_of_append {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    [∀ i, SampleableType ((pSpec.renameMessage CommitmentType).Challenge i)]
    [∀ i, SampleableType ((pSpec.BCSOpeningPhase pSpecCom e).Challenge i)]
    (phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e)
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {langIn : Set StmtIn} {langMid : Set StmtMid} {langOut : Set StmtOut}
    {εInteraction εOpening : ℝ≥0}
    (hInteraction :
      phases.interaction.verifier.soundness init impl langIn langMid εInteraction)
    (hOpening : phases.opening.verifier.soundness init impl langMid langOut εOpening)
    (hAppend :
      Verifier.appendSoundnessResidual
        (oSpec := oSpec) (init := init) (impl := impl)
        phases.interaction.verifier phases.opening.verifier hInteraction hOpening) :
    @Verifier.soundness _ oSpec StmtIn StmtOut
      (n + Fin.vsum (fun j => nCom (e.symm j)))
      (pSpec.renameMessage CommitmentType ++ₚ pSpec.BCSOpeningPhase pSpecCom e)
      (fun i => ProtocolSpec.instSampleableTypeChallengeAppend i)
      σ init impl langIn langOut phases.toReduction.verifier (εInteraction + εOpening) := by
  simpa [BCSCompiledPhases.toReduction, BCSTransform, ProtocolSpec.BCSTransform] using
    (Verifier.append_soundness
      (oSpec := oSpec) (init := init) (impl := impl)
      phases.interaction.verifier phases.opening.verifier hInteraction hOpening hAppend)

omit Oₘ in
/-- Knowledge soundness of packaged BCS phases composes through the concrete BCS verifier.

This bridge does not prove commitment extractability or the generic query-log compiler; it only
exposes the standard append-composition theorem for the already-supplied BCS phases under the
existing append knowledge-soundness residual. -/
theorem BCSCompiledPhases.toReduction_knowledgeSoundness_of_append {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    [∀ i, SampleableType ((pSpec.renameMessage CommitmentType).Challenge i)]
    [∀ i, SampleableType ((pSpec.BCSOpeningPhase pSpecCom e).Challenge i)]
    (phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e)
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {relIn : Set (StmtIn × WitIn)} {relMid : Set (StmtMid × WitMid)}
    {relOut : Set (StmtOut × WitOut)} {εInteraction εOpening : ℝ≥0}
    (hInteraction :
      phases.interaction.verifier.knowledgeSoundness init impl relIn relMid εInteraction)
    (hOpening :
      phases.opening.verifier.knowledgeSoundness init impl relMid relOut εOpening)
    (hAppend :
      Verifier.appendKnowledgeSoundnessResidual
        (oSpec := oSpec) (init := init) (impl := impl)
        phases.interaction.verifier phases.opening.verifier hInteraction hOpening) :
    @Verifier.knowledgeSoundness _ oSpec StmtIn WitIn StmtOut WitOut
      (n + Fin.vsum (fun j => nCom (e.symm j)))
      (pSpec.renameMessage CommitmentType ++ₚ pSpec.BCSOpeningPhase pSpecCom e)
      (fun i => ProtocolSpec.instSampleableTypeChallengeAppend i)
      σ init impl relIn relOut phases.toReduction.verifier (εInteraction + εOpening) := by
  simpa [BCSCompiledPhases.toReduction, BCSTransform, ProtocolSpec.BCSTransform] using
    (Verifier.append_knowledgeSoundness
      (oSpec := oSpec) (init := init) (impl := impl)
      phases.interaction.verifier phases.opening.verifier hInteraction hOpening hAppend)

/-- Security obligations still required to turn `BCSCompiledPhases.toReduction` into the final
compiler theorem.  These are intentionally named as fields rather than hidden in one opaque
assumption: each field corresponds to a separate proof brick in issue #62.

The intended endgame is to replace this interface by the actual preservation theorems:
completeness from commitment correctness plus phase realization, and soundness / knowledge
soundness from commitment binding or extractability plus the oracle-reduction security theorem. -/
structure BCSSecurityFrontier {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    (_phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e) where
  commitment_correctness_available : Prop
  commitment_binding_or_extractability_available : Prop
  completeness_preservation_target : Prop
  soundness_preservation_target : Prop
  knowledge_soundness_preservation_target : Prop

/-- The explicit checklist that remains before `BCSCompiledPhases.toReduction` can be promoted
from a compositional front door to a genuine BCS compiler theorem.

This is still an interface, not a security proof: each conjunct names one proof brick that the
full compiler must eventually produce from the source oracle reduction, the commitment schemes,
and the query-log API. -/
def BCSCompilerFrontierSatisfied {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    (phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e)
    (frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases) : Prop :=
  phases.interaction_realizes_oracle_messages ∧
  phases.opening_realizes_query_log ∧
  frontier.commitment_correctness_available ∧
  frontier.commitment_binding_or_extractability_available ∧
  frontier.completeness_preservation_target ∧
  frontier.soundness_preservation_target ∧
  frontier.knowledge_soundness_preservation_target

omit Oₘ in
/-- The security-preservation half of the BCS compiler frontier, separated from phase
realization so downstream code can consume the two checklists independently. -/
def BCSSecurityFrontierSatisfied {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    (frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases) : Prop :=
  frontier.commitment_correctness_available ∧
  frontier.commitment_binding_or_extractability_available ∧
  frontier.completeness_preservation_target ∧
  frontier.soundness_preservation_target ∧
  frontier.knowledge_soundness_preservation_target

omit Oₘ in
/-- Package the security-preservation fields directly. -/
theorem BCSSecurityFrontierSatisfied.intro {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (hCorrect : frontier.commitment_correctness_available)
    (hBindingOrExtract : frontier.commitment_binding_or_extractability_available)
    (hComplete : frontier.completeness_preservation_target)
    (hSound : frontier.soundness_preservation_target)
    (hKS : frontier.knowledge_soundness_preservation_target) :
    BCSSecurityFrontierSatisfied frontier :=
  ⟨hCorrect, hBindingOrExtract, hComplete, hSound, hKS⟩

omit Oₘ in
/-- Project commitment correctness from the security-frontier checklist. -/
theorem BCSSecurityFrontierSatisfied.correctness {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSSecurityFrontierSatisfied frontier) :
    frontier.commitment_correctness_available :=
  h.1

omit Oₘ in
/-- Project binding or extractability availability from the security-frontier checklist. -/
theorem BCSSecurityFrontierSatisfied.bindingOrExtract {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSSecurityFrontierSatisfied frontier) :
    frontier.commitment_binding_or_extractability_available :=
  h.2.1

omit Oₘ in
/-- Project the completeness-preservation target from the security-frontier checklist. -/
theorem BCSSecurityFrontierSatisfied.completeness {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSSecurityFrontierSatisfied frontier) :
    frontier.completeness_preservation_target :=
  h.2.2.1

omit Oₘ in
/-- Project the soundness-preservation target from the security-frontier checklist. -/
theorem BCSSecurityFrontierSatisfied.soundness {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSSecurityFrontierSatisfied frontier) :
    frontier.soundness_preservation_target :=
  h.2.2.2.1

omit Oₘ in
/-- Project the knowledge-soundness-preservation target from the security-frontier checklist. -/
theorem BCSSecurityFrontierSatisfied.knowledgeSoundness {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSSecurityFrontierSatisfied frontier) :
    frontier.knowledge_soundness_preservation_target :=
  h.2.2.2.2

omit Oₘ in
/-- Expand the security-frontier checklist into its five named security obligations. -/
theorem BCSSecurityFrontierSatisfied.iff_fields {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases} :
    BCSSecurityFrontierSatisfied frontier ↔
      frontier.commitment_correctness_available ∧
      frontier.commitment_binding_or_extractability_available ∧
      frontier.completeness_preservation_target ∧
      frontier.soundness_preservation_target ∧
      frontier.knowledge_soundness_preservation_target :=
  Iff.rfl

theorem BCSCompilerFrontierSatisfied.interaction_realizes_oracle_messages
    {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierSatisfied phases frontier) :
    phases.interaction_realizes_oracle_messages :=
  h.1

theorem BCSCompilerFrontierSatisfied.opening_realizes_query_log
    {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierSatisfied phases frontier) :
    phases.opening_realizes_query_log :=
  h.2.1

theorem BCSCompilerFrontierSatisfied.commitment_correctness_available
    {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierSatisfied phases frontier) :
    frontier.commitment_correctness_available :=
  h.2.2.1

theorem BCSCompilerFrontierSatisfied.commitment_binding_or_extractability_available
    {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierSatisfied phases frontier) :
    frontier.commitment_binding_or_extractability_available :=
  h.2.2.2.1

theorem BCSCompilerFrontierSatisfied.completeness_preservation_target
    {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierSatisfied phases frontier) :
    frontier.completeness_preservation_target :=
  h.2.2.2.2.1

theorem BCSCompilerFrontierSatisfied.soundness_preservation_target
    {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierSatisfied phases frontier) :
    frontier.soundness_preservation_target :=
  h.2.2.2.2.2.1

theorem BCSCompilerFrontierSatisfied.knowledge_soundness_preservation_target
    {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierSatisfied phases frontier) :
    frontier.knowledge_soundness_preservation_target :=
  h.2.2.2.2.2.2

omit Oₘ in
/-- Expand the full satisfied compiler frontier into all seven named phase/security obligations. -/
theorem BCSCompilerFrontierSatisfied.iff_fields {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases} :
    BCSCompilerFrontierSatisfied phases frontier ↔
      phases.interaction_realizes_oracle_messages ∧
      phases.opening_realizes_query_log ∧
      frontier.commitment_correctness_available ∧
      frontier.commitment_binding_or_extractability_available ∧
      frontier.completeness_preservation_target ∧
      frontier.soundness_preservation_target ∧
      frontier.knowledge_soundness_preservation_target :=
  Iff.rfl

omit Oₘ in
/-- Package the full satisfied BCS compiler frontier directly from its named fields. -/
theorem BCSCompilerFrontierSatisfied.intro {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (hInteraction : phases.interaction_realizes_oracle_messages)
    (hOpening : phases.opening_realizes_query_log)
    (hCorrect : frontier.commitment_correctness_available)
    (hBindingOrExtract : frontier.commitment_binding_or_extractability_available)
    (hComplete : frontier.completeness_preservation_target)
    (hSound : frontier.soundness_preservation_target)
    (hKS : frontier.knowledge_soundness_preservation_target) :
    BCSCompilerFrontierSatisfied phases frontier :=
  ⟨hInteraction, hOpening, hCorrect, hBindingOrExtract, hComplete, hSound, hKS⟩

omit Oₘ in
/-- Build a satisfied BCS compiler frontier from raw phase-realization and security fields. -/
theorem BCSCompilerFrontierSatisfied.ofPhaseFields {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (hInteraction : phases.interaction_realizes_oracle_messages)
    (hOpening : phases.opening_realizes_query_log)
    (hCorrect : frontier.commitment_correctness_available)
    (hBindingOrExtract : frontier.commitment_binding_or_extractability_available)
    (hComplete : frontier.completeness_preservation_target)
    (hSound : frontier.soundness_preservation_target)
    (hKS : frontier.knowledge_soundness_preservation_target) :
    BCSCompilerFrontierSatisfied phases frontier :=
  BCSCompilerFrontierSatisfied.intro
    hInteraction hOpening hCorrect hBindingOrExtract hComplete hSound hKS

omit Oₘ in
/-- Project the phase-realization obligations from a satisfied BCS compiler frontier. -/
theorem BCSCompilerFrontierSatisfied.phase {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierSatisfied phases frontier) :
    BCSPhaseRealizationFrontier phases :=
  ⟨h.1, h.2.1⟩

omit Oₘ in
/-- Project the security-preservation obligations from a satisfied BCS compiler frontier. -/
theorem BCSCompilerFrontierSatisfied.security {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierSatisfied phases frontier) :
    BCSSecurityFrontierSatisfied frontier :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

omit Oₘ in
/-- Rebuild a satisfied BCS compiler frontier from its separated phase and security halves. -/
theorem BCSCompilerFrontierSatisfied.ofPhaseAndSecurity {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (hPhase : BCSPhaseRealizationFrontier phases)
    (hSecurity : BCSSecurityFrontierSatisfied frontier) :
    BCSCompilerFrontierSatisfied phases frontier :=
  ⟨hPhase.1, hPhase.2, hSecurity.1, hSecurity.2.1, hSecurity.2.2.1,
    hSecurity.2.2.2.1, hSecurity.2.2.2.2⟩

omit Oₘ in
/-- A satisfied BCS compiler frontier is exactly the conjunction of the separated
phase-realization and security-preservation frontiers. -/
theorem BCSCompilerFrontierSatisfied.iff_phase_and_security {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases} :
    BCSCompilerFrontierSatisfied phases frontier ↔
      BCSPhaseRealizationFrontier phases ∧ BCSSecurityFrontierSatisfied frontier := by
  constructor
  · intro h
    exact ⟨BCSCompilerFrontierSatisfied.phase h, BCSCompilerFrontierSatisfied.security h⟩
  · intro h
    exact BCSCompilerFrontierSatisfied.ofPhaseAndSecurity h.1 h.2

/-- Build a satisfied BCS compiler frontier from a discharged typed opening log plus the
remaining security-frontier fields. This is the direct adapter for consumers that name the
underlying satisfied predicate rather than the compatibility `Ready` abbrev. -/
theorem BCSCompilerFrontierSatisfied.ofOpeningLogBridge {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    {log : BCSOpeningLogFrontier (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType}
    (hInteraction : phases.interaction_realizes_oracle_messages)
    (hLog : BCSOpeningLogFrontierSatisfied log)
    (hBridge : BCSOpeningLogBridge phases log)
    (hCorrect : frontier.commitment_correctness_available)
    (hBindingOrExtract : frontier.commitment_binding_or_extractability_available)
    (hComplete : frontier.completeness_preservation_target)
    (hSound : frontier.soundness_preservation_target)
    (hKS : frontier.knowledge_soundness_preservation_target) :
    BCSCompilerFrontierSatisfied phases frontier :=
  BCSCompilerFrontierSatisfied.intro
    hInteraction (hBridge hLog) hCorrect hBindingOrExtract hComplete hSound hKS

/-- Build a satisfied BCS compiler frontier from a discharged typed opening log and a packaged
security frontier. This keeps downstream code from unpacking the five security fields when they
have already been assembled as `BCSSecurityFrontierSatisfied`. -/
theorem BCSCompilerFrontierSatisfied.ofOpeningLogBridgeAndSecurity {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    {log : BCSOpeningLogFrontier (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType}
    (hInteraction : phases.interaction_realizes_oracle_messages)
    (hLog : BCSOpeningLogFrontierSatisfied log)
    (hBridge : BCSOpeningLogBridge phases log)
    (hSecurity : BCSSecurityFrontierSatisfied frontier) :
    BCSCompilerFrontierSatisfied phases frontier :=
  BCSCompilerFrontierSatisfied.ofPhaseAndSecurity
    (BCSPhaseRealizationFrontier.ofOpeningLogBridge hInteraction hLog hBridge)
    hSecurity

/-- Compatibility name for the full BCS compiler-frontier checklist. -/
abbrev BCSCompilerFrontierReady {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    (phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e)
    (frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases) : Prop :=
  BCSCompilerFrontierSatisfied phases frontier

/-- Package the named BCS compiler-frontier obligations from their independent proof bricks. -/
theorem BCSCompilerFrontierReady.intro {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (hPhase : BCSPhaseRealizationFrontier phases)
    (hCorrect : frontier.commitment_correctness_available)
    (hBindingOrExtract : frontier.commitment_binding_or_extractability_available)
    (hComplete : frontier.completeness_preservation_target)
    (hSound : frontier.soundness_preservation_target)
    (hKS : frontier.knowledge_soundness_preservation_target) :
    BCSCompilerFrontierReady phases frontier :=
  ⟨hPhase.1, hPhase.2, hCorrect, hBindingOrExtract, hComplete, hSound, hKS⟩

/-- Build the full ready checklist directly from the raw phase-realization and security fields. -/
theorem BCSCompilerFrontierReady.ofPhaseFields {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (hInteraction : phases.interaction_realizes_oracle_messages)
    (hOpening : phases.opening_realizes_query_log)
    (hCorrect : frontier.commitment_correctness_available)
    (hBindingOrExtract : frontier.commitment_binding_or_extractability_available)
    (hComplete : frontier.completeness_preservation_target)
    (hSound : frontier.soundness_preservation_target)
    (hKS : frontier.knowledge_soundness_preservation_target) :
    BCSCompilerFrontierReady phases frontier :=
  BCSCompilerFrontierReady.intro
    (BCSPhaseRealizationFrontier.intro hInteraction hOpening)
    hCorrect hBindingOrExtract hComplete hSound hKS

omit Oₘ in
/-- Expand the ready-frontier compatibility abbrev into all seven named obligations. -/
theorem BCSCompilerFrontierReady.iff_fields {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases} :
    BCSCompilerFrontierReady phases frontier ↔
      phases.interaction_realizes_oracle_messages ∧
      phases.opening_realizes_query_log ∧
      frontier.commitment_correctness_available ∧
      frontier.commitment_binding_or_extractability_available ∧
      frontier.completeness_preservation_target ∧
      frontier.soundness_preservation_target ∧
      frontier.knowledge_soundness_preservation_target :=
  Iff.rfl

/-- Project the phase-realization obligations from a ready BCS compiler frontier. -/
theorem BCSCompilerFrontierReady.phase {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierReady phases frontier) :
    BCSPhaseRealizationFrontier phases :=
  ⟨h.1, h.2.1⟩

omit Oₘ in
/-- Project the security-preservation obligations from a ready BCS compiler frontier. -/
theorem BCSCompilerFrontierReady.security {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierReady phases frontier) :
    BCSSecurityFrontierSatisfied frontier :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- Project interaction-phase realization from a ready BCS compiler frontier. -/
theorem BCSCompilerFrontierReady.interaction_realizes_oracle_messages {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierReady phases frontier) :
    phases.interaction_realizes_oracle_messages :=
  h.1

/-- Project opening-log realization from a ready BCS compiler frontier. -/
theorem BCSCompilerFrontierReady.opening_realizes_query_log {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierReady phases frontier) :
    phases.opening_realizes_query_log :=
  h.2.1

omit Oₘ in
/-- Project commitment correctness from a ready BCS compiler frontier. -/
theorem BCSCompilerFrontierReady.commitment_correctness_available {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierReady phases frontier) :
    frontier.commitment_correctness_available :=
  h.2.2.1

omit Oₘ in
/-- Project binding-or-extractability availability from a ready BCS compiler frontier. -/
theorem BCSCompilerFrontierReady.commitment_binding_or_extractability_available
    {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierReady phases frontier) :
    frontier.commitment_binding_or_extractability_available :=
  h.2.2.2.1

omit Oₘ in
/-- Project completeness preservation from a ready BCS compiler frontier. -/
theorem BCSCompilerFrontierReady.completeness_preservation_target {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierReady phases frontier) :
    frontier.completeness_preservation_target :=
  h.2.2.2.2.1

omit Oₘ in
/-- Project soundness preservation from a ready BCS compiler frontier. -/
theorem BCSCompilerFrontierReady.soundness_preservation_target {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierReady phases frontier) :
    frontier.soundness_preservation_target :=
  h.2.2.2.2.2.1

omit Oₘ in
/-- Project knowledge-soundness preservation from a ready BCS compiler frontier. -/
theorem BCSCompilerFrontierReady.knowledge_soundness_preservation_target {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (h : BCSCompilerFrontierReady phases frontier) :
    frontier.knowledge_soundness_preservation_target :=
  h.2.2.2.2.2.2

omit Oₘ in
/-- Rebuild a ready BCS compiler frontier from its separated phase and security halves. -/
theorem BCSCompilerFrontierReady.ofPhaseAndSecurity {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    (hPhase : BCSPhaseRealizationFrontier phases)
    (hSecurity : BCSSecurityFrontierSatisfied frontier) :
    BCSCompilerFrontierReady phases frontier :=
  ⟨hPhase.1, hPhase.2, hSecurity.1, hSecurity.2.1, hSecurity.2.2.1,
    hSecurity.2.2.2.1, hSecurity.2.2.2.2⟩

omit Oₘ in
/-- The full ready checklist is exactly the conjunction of the separated phase-realization and
security-preservation frontiers. -/
theorem BCSCompilerFrontierReady.iff_phase_and_security {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases} :
    BCSCompilerFrontierReady phases frontier ↔
      BCSPhaseRealizationFrontier phases ∧ BCSSecurityFrontierSatisfied frontier := by
  constructor
  · intro h
    exact
      ⟨⟨h.1, h.2.1⟩,
        ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
          h.2.2.2.2.2.2⟩⟩
  · intro h
    exact
      ⟨h.1.1, h.1.2, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
        h.2.2.2.2.2⟩

/-- Build the full ready checklist from a discharged typed opening log plus the remaining
security-frontier fields. This is the direct adapter expected from the current BCS interface:
`BCSPhaseRealizationFrontier.ofOpeningLogBridge` supplies the phase half, and
`BCSCompilerFrontierReady.intro` adds the commitment/security obligations. -/
theorem BCSCompilerFrontierReady.ofOpeningLogBridge {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    {log : BCSOpeningLogFrontier (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType}
    (hInteraction : phases.interaction_realizes_oracle_messages)
    (hLog : BCSOpeningLogFrontierSatisfied log)
    (hBridge : BCSOpeningLogBridge phases log)
    (hCorrect : frontier.commitment_correctness_available)
    (hBindingOrExtract : frontier.commitment_binding_or_extractability_available)
    (hComplete : frontier.completeness_preservation_target)
    (hSound : frontier.soundness_preservation_target)
    (hKS : frontier.knowledge_soundness_preservation_target) :
    BCSCompilerFrontierReady phases frontier :=
  BCSCompilerFrontierReady.intro
    (BCSPhaseRealizationFrontier.ofOpeningLogBridge hInteraction hLog hBridge)
    hCorrect hBindingOrExtract hComplete hSound hKS

/-- Build the ready checklist from a discharged typed opening log and a packaged security frontier.
This is the compatibility-`Ready` spelling of
`BCSCompilerFrontierSatisfied.ofOpeningLogBridgeAndSecurity`. -/
theorem BCSCompilerFrontierReady.ofOpeningLogBridgeAndSecurity {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    {phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e}
    {frontier : BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) phases}
    {log : BCSOpeningLogFrontier (pSpec := pSpec) (Oₘ := Oₘ) CommitmentType}
    (hInteraction : phases.interaction_realizes_oracle_messages)
    (hLog : BCSOpeningLogFrontierSatisfied log)
    (hBridge : BCSOpeningLogBridge phases log)
    (hSecurity : BCSSecurityFrontierSatisfied frontier) :
    BCSCompilerFrontierReady phases frontier :=
  BCSCompilerFrontierReady.ofPhaseAndSecurity
    (BCSPhaseRealizationFrontier.ofOpeningLogBridge hInteraction hLog hBridge)
    hSecurity
/-! #### Design note: the fully general transform

  In full generality (deferred to ArkLib#433), the transform should take

  * `reduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec`, and
  * for each prover message `i : pSpec.MessageIdx`, a commitment scheme
    `Scheme oSpec (pSpec.Message i) (Commitment i) (Decommitment i) (ComKey i) (VerifKey i)
      (pSpecCom i)`,

  and produce a `Reduction` over `pSpec.BCSTransform pSpecCom Commitment e`, where:

  * the interaction phase is built from `reduction` by having the prover, at each message round,
    compute `(cm, decomm) ← scheme.commit ck msg` and send `cm : Commitment i` (the renamed message
    type) while retaining `(msg, decomm)` in its state; the verifier runs the original oracle
    verifier with each oracle-message query answered against the committed value;
  * the opening phase is `Reduction.seqCompose` of the per-message opening reductions
    `Reduction.bcsMessageOpening i (scheme i) (ck i, vk i)` (reindexed by `e`), where the queried
    points and responses are read off from the oracle verifier's query log and the witnesses are the
    retained `(msg, decomm)` pairs.

  The blocker is reading the (possibly adaptive) oracle verifier's query log to determine which
  openings to run; restricting to `OracleVerifier.NonAdaptive` (whose `queryMsg` is a fixed list)
  removes the adaptivity blocker but the statement/witness threading still depends on the #433
  refactor. -/

end OracleReduction

/-! ## Axiom audit — BCS transform/frontier declarations.

These lines are regression anchors for the current interface boundary only. They do not prove the
generic compiler construction or the completeness/soundness preservation theorems. -/
#print axioms ProtocolSpec.renameMessage
#print axioms ProtocolSpec.BCSOpeningPhase
#print axioms ProtocolSpec.BCSTransform
#print axioms Reduction.bcsMessageOpening
#print axioms OracleReduction.BCSTransform
#print axioms OracleReduction.BCSCompiledPhases
#print axioms OracleReduction.BCSOpeningRequest
#print axioms OracleReduction.BCSOpeningStatementAt
#print axioms OracleReduction.BCSOpeningRequest.toOpeningStatement
#print axioms OracleReduction.BCSOpeningRequest.toOpeningStatement_commitment
#print axioms OracleReduction.BCSOpeningRequest.toOpeningStatement_query
#print axioms OracleReduction.BCSOpeningRequest.toOpeningStatement_response
#print axioms OracleReduction.BCSOpeningRequest.indexed_toOpeningStatement_injective
#print axioms OracleReduction.BCSOpeningSchedule
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_nil
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_cons
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_length
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_append
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_take
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_drop
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_reverse
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_concat
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_map_messageIdx
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_filter_messageIdx
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_filter_messageIdx_length
#print axioms OracleReduction.BCSOpeningSchedule.sum_filter_messageIdx_length
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_sum_filter_messageIdx_length
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_map_commitment
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_map_query
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_map_response
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_getElem
#print axioms OracleReduction.BCSOpeningSchedule.mem_toOpeningStatements_iff
#print axioms OracleReduction.BCSOpeningSchedule.mem_toOpeningStatements_of_mem
#print axioms OracleReduction.BCSOpeningSchedule.exists_request_of_mem_toOpeningStatements
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_forall
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_exists
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_subset
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_injective
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_nodup
#print axioms OracleReduction.BCSOpeningSchedule.toOpeningStatements_nodup_iff
#print axioms OracleReduction.BCSOpeningLogFrontier
#print axioms OracleReduction.BCSOpeningLogFrontierSatisfied
#print axioms OracleReduction.BCSOpeningLogFrontierSatisfied.intro
#print axioms OracleReduction.BCSOpeningLogFrontierSatisfied.queryLog
#print axioms OracleReduction.BCSOpeningLogFrontierSatisfied.retainedWitnesses
#print axioms OracleReduction.BCSOpeningLogFrontierSatisfied.iff_fields
#print axioms OracleReduction.BCSOpeningLogBridge
#print axioms OracleReduction.BCSOpeningLogBridge.apply
#print axioms OracleReduction.BCSOpeningLogBridge.ofOpeningRealization
#print axioms OracleReduction.BCSCompiledPhases.toReduction
#print axioms OracleReduction.BCSPhaseRealizationFrontier
#print axioms OracleReduction.BCSPhaseRealizationFrontier.intro
#print axioms OracleReduction.BCSPhaseRealizationFrontier.interaction
#print axioms OracleReduction.BCSPhaseRealizationFrontier.opening
#print axioms OracleReduction.BCSOpeningLogBridge.ofPhaseRealizationFrontier
#print axioms OracleReduction.BCSPhaseRealizationFrontier.iff_fields
#print axioms OracleReduction.BCSPhaseRealizationFrontier.ofOpeningLogBridge
#print axioms OracleReduction.BCSCompiledPhases.toReduction_eq_BCSTransform
#print axioms OracleReduction.BCSCompiledPhases.toReduction_perfectCompleteness_of_append
#print axioms OracleReduction.BCSCompiledPhases.toReduction_completeness_of_append
#print axioms OracleReduction.BCSCompiledPhases.toReduction_soundness_of_append
#print axioms OracleReduction.BCSCompiledPhases.toReduction_knowledgeSoundness_of_append
#print axioms OracleReduction.BCSSecurityFrontier
#print axioms OracleReduction.BCSSecurityFrontierSatisfied
#print axioms OracleReduction.BCSSecurityFrontierSatisfied.intro
#print axioms OracleReduction.BCSSecurityFrontierSatisfied.correctness
#print axioms OracleReduction.BCSSecurityFrontierSatisfied.bindingOrExtract
#print axioms OracleReduction.BCSSecurityFrontierSatisfied.completeness
#print axioms OracleReduction.BCSSecurityFrontierSatisfied.soundness
#print axioms OracleReduction.BCSSecurityFrontierSatisfied.knowledgeSoundness
#print axioms OracleReduction.BCSSecurityFrontierSatisfied.iff_fields
#print axioms OracleReduction.BCSCompilerFrontierSatisfied
#print axioms OracleReduction.BCSCompilerFrontierSatisfied.interaction_realizes_oracle_messages
#print axioms OracleReduction.BCSCompilerFrontierSatisfied.opening_realizes_query_log
#print axioms OracleReduction.BCSCompilerFrontierSatisfied.commitment_correctness_available
#print axioms
  OracleReduction.BCSCompilerFrontierSatisfied.commitment_binding_or_extractability_available
#print axioms OracleReduction.BCSCompilerFrontierSatisfied.completeness_preservation_target
#print axioms OracleReduction.BCSCompilerFrontierSatisfied.soundness_preservation_target
#print axioms OracleReduction.BCSCompilerFrontierSatisfied.knowledge_soundness_preservation_target
#print axioms OracleReduction.BCSCompilerFrontierSatisfied.iff_fields
#print axioms OracleReduction.BCSCompilerFrontierSatisfied.intro
#print axioms OracleReduction.BCSCompilerFrontierSatisfied.ofPhaseFields
#print axioms OracleReduction.BCSCompilerFrontierSatisfied.phase
#print axioms OracleReduction.BCSCompilerFrontierSatisfied.security
#print axioms OracleReduction.BCSCompilerFrontierSatisfied.ofPhaseAndSecurity
#print axioms OracleReduction.BCSCompilerFrontierSatisfied.iff_phase_and_security
#print axioms OracleReduction.BCSCompilerFrontierSatisfied.ofOpeningLogBridge
#print axioms OracleReduction.BCSCompilerFrontierSatisfied.ofOpeningLogBridgeAndSecurity
#print axioms OracleReduction.BCSCompilerFrontierReady
#print axioms OracleReduction.BCSCompilerFrontierReady.intro
#print axioms OracleReduction.BCSCompilerFrontierReady.ofPhaseFields
#print axioms OracleReduction.BCSCompilerFrontierReady.iff_fields
#print axioms OracleReduction.BCSCompilerFrontierReady.phase
#print axioms OracleReduction.BCSCompilerFrontierReady.security
#print axioms OracleReduction.BCSCompilerFrontierReady.interaction_realizes_oracle_messages
#print axioms OracleReduction.BCSCompilerFrontierReady.opening_realizes_query_log
#print axioms OracleReduction.BCSCompilerFrontierReady.commitment_correctness_available
#print axioms
  OracleReduction.BCSCompilerFrontierReady.commitment_binding_or_extractability_available
#print axioms OracleReduction.BCSCompilerFrontierReady.completeness_preservation_target
#print axioms OracleReduction.BCSCompilerFrontierReady.soundness_preservation_target
#print axioms OracleReduction.BCSCompilerFrontierReady.knowledge_soundness_preservation_target
#print axioms OracleReduction.BCSCompilerFrontierReady.ofPhaseAndSecurity
#print axioms OracleReduction.BCSCompilerFrontierReady.iff_phase_and_security
#print axioms OracleReduction.BCSCompilerFrontierReady.ofOpeningLogBridge
#print axioms OracleReduction.BCSCompilerFrontierReady.ofOpeningLogBridgeAndSecurity
#print axioms OracleReduction.BCSCompiledPhasesLawful.realizationFrontier
#print axioms OracleReduction.BCSCompiledPhasesLawful.openingLogBridge
