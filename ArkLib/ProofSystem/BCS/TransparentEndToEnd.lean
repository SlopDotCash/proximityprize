/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.BCS.CompletenessPreservation
import ArkLib.OracleReduction.BCS.AppendSoundnessMsg
import ArkLib.OracleReduction.Composition.Sequential.ChallengeOracleFintype
import ArkLib.Commitments.Functional.Transparent

/-!
# A concrete BCS end-to-end instance with the transparent commitment scheme (issue #62)

This file constructs **one** concrete nontrivial protocol compiled end-to-end through the BCS API
(`ArkLib.OracleReduction.BCS`) with a concrete commitment/opening scheme (the transparent commitment
scheme of `ArkLib.Commitments.Functional.Transparent`), and instantiates **both** BCS keystones on it:

* perfect completeness, via `OracleReduction.BCSTransform_perfectCompleteness`, and
* (plain) soundness, via `OracleReduction.BCSCompiledPhases.toReduction_soundness_of_append_msg`.

## The protocol

The source interactive protocol is the minimal genuinely-oracle one: a single prover-to-verifier
message of type `Data`, which the verifier treats as an oracle (via `[OracleInterface Data]`) and
queries at a point. Compiling through BCS replaces that oracle message by a commitment to it; for the
transparent scheme the commitment *is* the data and the opening phase is the verifier re-evaluating
the oracle locally.

* `srcPSpec := ⟨!v[.P_to_V], !v[Data]⟩` — one prover oracle message of type `Data`.
* `CommitmentType _ := Data` — transparent commitment = data.
* `nCom _ := 1`, `pSpecCom _ := Commitment.Transparent.openingPSpec` — the one-message opening.

Because the source has exactly one message, `srcPSpec.BCSOpeningPhase pSpecCom e` is *definitionally*
`Commitment.Transparent.openingPSpec`, so the opening phase is exactly the transparent scheme's
opening proof. The **interaction phase** is over `srcPSpec.renameMessage CommitmentType`; we take it
to be a single-message "commit and forward" reduction that sends the commitment (= data) and passes
the opening statement/witness through to the opening phase.

Neither keystone is vacuous here: the input/middle languages and the output relations are honest
sets (`relMid`/`langMid` is "the claimed response is the honest oracle answer on the committed
data", `relOut`/`langOut` is `acceptRejectRel` / `{true}`), so completeness is a real
probability-one statement and soundness a real `≤ ε` statement against arbitrary malicious provers.

The ambient honest-implementation side conditions (`hInit`/`hImplSupp` for completeness and
`himplSP`/`himplNF`/`himplVB` for soundness) are taken as hypotheses, exactly as the analogous
component-level results in this codebase (e.g. `Sumcheck.Spec.reduction_perfectCompleteness`); they
hold for any honest interactive implementation. The cryptographic per-phase content (perfect
completeness and perfect soundness of each phase) is proved here, not assumed.

## What is genuinely proved (no `sorry`, no vacuous hypotheses)

`transparentBCS_perfectCompleteness` and `transparentBCS_soundness` below are the two headline
results; both are axiom-clean (only `propext`/`Classical.choice`/`Quot.sound`).
-/

open OracleSpec OracleComp SubSpec ProtocolSpec Commitment
open scoped NNReal ENNReal

namespace BCSTransparentEndToEnd

/-! ## The ambient data and the source protocol spec -/

variable {ι : Type} [DecidableEq ι] {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
    {Data : Type} [O : OracleInterface Data] [∀ q : O.Query, DecidableEq (O.Response q)]

/-- The source interactive (oracle) protocol spec: a single prover message of type `Data`. -/
abbrev srcPSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[Data]⟩

/-- The single message of `srcPSpec` is `Data`, and it carries the ambient oracle interface `O`. -/
instance instOracleInterfaceSrcMessage :
    ∀ i, OracleInterface ((srcPSpec (Data := Data)).Message i)
  | ⟨0, _⟩ => O

/-- The transparent commitment type: a commitment is the data itself. -/
abbrev CommitmentType : (srcPSpec (Data := Data)).MessageIdx → Type := fun _ => Data

/-- One opening protocol per message. -/
abbrev nCom : (srcPSpec (Data := Data)).MessageIdx → ℕ := fun _ => 1

/-- The per-message opening protocol spec is the transparent opening (one prover message). -/
abbrev pSpecCom : ∀ i, ProtocolSpec ((nCom (Data := Data)) i) :=
  fun _ => Commitment.Transparent.openingPSpec

/-- The unique message index of `srcPSpec` (its only round is a prover message). -/
def srcMsgIdx : (srcPSpec (Data := Data)).MessageIdx := ⟨0, rfl⟩

instance : Unique ((srcPSpec (Data := Data)).MessageIdx) where
  default := srcMsgIdx
  uniq := by
    rintro ⟨i, hi⟩
    have : i = 0 := Fin.eq_zero i
    subst this
    rfl

/-- The ordering equivalence `MessageIdx ≃ Fin 1`: the source has exactly one message. -/
def e : (srcPSpec (Data := Data)).MessageIdx ≃ Fin 1 := Equiv.ofUnique _ _

/-- The opening phase has length `1` (one opening message). -/
theorem vsum_eq_one :
    Fin.vsum (fun j => (nCom (Data := Data)) ((e (Data := Data)).symm j)) = 1 := rfl

/-! ## Statement / witness types and relations

The intermediate statement/witness handed from the interaction phase to the opening phase is exactly
the opening statement `(cm, ⟨q, y⟩)` together with the `(data, decommitment)` witness. For the
transparent scheme `cm : Data`, `decommitment : Unit`. -/

/-- The opening statement carried at the interaction → opening seam: a commitment, a query, and a
claimed response. -/
abbrev OpeningStmt := Data × (q : O.Query) × O.Response q

/-- The opening witness: the underlying data and the (trivial) decommitment. -/
abbrev OpeningWit := Data × Unit

/-- The middle relation: the claimed response is the honest oracle answer on the committed data, and
the witness data is the committed data. This is a genuine (non-vacuous) predicate. -/
def relMid : Set ((OpeningStmt (Data := Data)) × (OpeningWit (Data := Data))) :=
  setOf (fun ⟨⟨cm, q, y⟩, ⟨d, _⟩⟩ => O.answer cm q = y ∧ d = cm)

/-- The middle language: the claimed response is consistent with the commitment (i.e. it is the
honest oracle answer on the committed data). A malicious opening prover cannot make the verifier
accept a statement outside this language — that is the binding content. -/
def langMid : Set (OpeningStmt (Data := Data)) :=
  setOf (fun ⟨cm, q, y⟩ => O.answer cm q = y)

/-- The output language: the verifier accepted. -/
def langOut : Set Bool := setOf (· = true)

/-! ## The interaction phase

A single-message "commit and forward" reduction over `srcPSpec.renameMessage CommitmentType` (whose
unique message type is `Data` — the commitment). The prover commits to the data (transparently, the
identity) and forwards the opening statement/witness to the opening phase; the verifier returns its
input statement unchanged. -/

/-- The interaction-phase prover: commit to the data (= the statement's commitment component) and
forward the input statement/witness. -/
def interactionProver :
    Prover oSpec (OpeningStmt (Data := Data)) (OpeningWit (Data := Data))
      (OpeningStmt (Data := Data)) (OpeningWit (Data := Data))
      ((srcPSpec (Data := Data)).renameMessage (CommitmentType (Data := Data))) where
  PrvState := fun _ => (OpeningStmt (Data := Data)) × (OpeningWit (Data := Data))
  input := fun ctx => ctx
  sendMessage := fun ⟨0, _⟩ => fun st => pure (st.1.1, st)
  receiveChallenge := fun ⟨i, h⟩ => by
    have : i = 0 := Fin.eq_zero i
    subst this
    nomatch h
  output := fun st => pure st

/-- The interaction-phase verifier: return the input statement unchanged. -/
def interactionVerifier :
    Verifier oSpec (OpeningStmt (Data := Data)) (OpeningStmt (Data := Data))
      ((srcPSpec (Data := Data)).renameMessage (CommitmentType (Data := Data))) where
  verify := fun stmt _ => pure stmt

/-- The interaction-phase reduction. -/
def interactionRed :
    Reduction oSpec (OpeningStmt (Data := Data)) (OpeningWit (Data := Data))
      (OpeningStmt (Data := Data)) (OpeningWit (Data := Data))
      ((srcPSpec (Data := Data)).renameMessage (CommitmentType (Data := Data))) where
  prover := interactionProver
  verifier := interactionVerifier

/-- The renamed interaction spec has a single prover message (no verifier challenges). -/
instance instIsEmptyInteractionChallenge :
    IsEmpty (((srcPSpec (Data := Data)).renameMessage
      (CommitmentType (Data := Data))).ChallengeIdx) where
  false := fun ⟨i, h⟩ => by
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    have hdir : ((srcPSpec (Data := Data)).renameMessage
        (CommitmentType (Data := Data))).dir 0 = Direction.P_to_V := rfl
    rw [h] at hdir; exact absurd hdir (by decide)

instance instSampleableInteraction :
    ∀ i, SampleableType (((srcPSpec (Data := Data)).renameMessage
      (CommitmentType (Data := Data))).Challenge i) :=
  fun i => (instIsEmptyInteractionChallenge (Data := Data)).false i |>.elim

instance instProverOnlyInteraction :
    ProverOnly ((srcPSpec (Data := Data)).renameMessage (CommitmentType (Data := Data))) where
  prover_first' := rfl

/-! ## The opening phase

Because the source has exactly one message, `srcPSpec.BCSOpeningPhase pSpecCom e` is *definitionally*
`Commitment.Transparent.openingPSpec`, so the opening phase is exactly `transparentScheme.opening
((), ())`. -/

/-- The opening-phase reduction: the transparent scheme's opening proof, over
`srcPSpec.BCSOpeningPhase pSpecCom e` (definitionally `openingPSpec`). -/
def openingRed :
    Reduction oSpec (OpeningStmt (Data := Data)) (OpeningWit (Data := Data)) Bool Unit
      ((srcPSpec (Data := Data)).BCSOpeningPhase (pSpecCom (Data := Data)) (e (Data := Data))) :=
  (Commitment.Transparent.transparentScheme (oSpec := oSpec) (Data := Data)).opening ((), ())

/-- The opening phase has no verifier challenges (`openingPSpec` is a single prover message), so its
challenge-index type is empty. -/
instance instIsEmptyOpeningChallenge :
    IsEmpty (((srcPSpec (Data := Data)).BCSOpeningPhase (pSpecCom (Data := Data))
      (e (Data := Data))).ChallengeIdx) where
  false := fun ⟨i, h⟩ => by
    have hsum : (Fin.vsum fun j => (nCom (Data := Data)) ((e (Data := Data)).symm j)) = 1 :=
      vsum_eq_one (Data := Data)
    have hi : i.val = 0 := by have := i.isLt; omega
    have hdir : ((srcPSpec (Data := Data)).BCSOpeningPhase (pSpecCom (Data := Data))
        (e (Data := Data))).dir i = Direction.P_to_V := by
      show ((srcPSpec (Data := Data)).BCSOpeningPhase (pSpecCom (Data := Data))
        (e (Data := Data))).dir ⟨i.val, i.isLt⟩ = Direction.P_to_V
      rw [show (⟨i.val, i.isLt⟩ : Fin _) = ⟨0, by omega⟩ from by ext; exact hi]
      rfl
    rw [h] at hdir; exact absurd hdir (by decide)

instance instSampleableOpening :
    ∀ i, SampleableType (((srcPSpec (Data := Data)).BCSOpeningPhase (pSpecCom (Data := Data))
      (e (Data := Data))).Challenge i) :=
  fun i => (instIsEmptyOpeningChallenge (Data := Data)).false i |>.elim

section Security

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

instance instProverOnlyOpening :
    ProverOnly ((srcPSpec (Data := Data)).BCSOpeningPhase (pSpecCom (Data := Data))
      (e (Data := Data))) where
  prover_first' := rfl

set_option maxHeartbeats 800000 in
/-- **Perfect completeness of the opening phase.** For an honest opening statement (the claimed
response is the honest oracle answer on the committed data) the transparent opening verifier returns
`decide (answer cm q = y) = true`, so it accepts with probability one. -/
theorem openingRed_perfectCompleteness :
    (openingRed (oSpec := oSpec) (Data := Data)).perfectCompleteness init impl
      (relMid (Data := Data)) acceptRejectRel := by
  rw [Reduction.perfectCompleteness_eq_prob_one]
  rintro ⟨cm, q, y⟩ ⟨d, u⟩ hmem
  simp only [relMid, Set.mem_setOf_eq] at hmem
  obtain ⟨hans, hd⟩ := hmem
  -- The underlying `OracleComp` (the prover-first run with a constant verdict) has *only* successful
  -- outputs, each of which accepts. This support fact is state-independent (no oracle queries).
  have hsupp : ∀ z ∈ support
      ((openingRed (oSpec := oSpec) (Data := Data)).run (cm, ⟨q, y⟩) (d, u)).run,
      ∃ a, z = some a ∧
        ((a.2, a.1.2.2) ∈ acceptRejectRel ∧ a.1.2.1 = a.2) := by
    intro z hz
    -- `openingRed` is *definitionally* the transparent opening over `openingPSpec`; rewrite its run
    -- via the prover-first lemma (using the `openingPSpec` `ProverOnly` instance).
    haveI : ProverOnly Commitment.Transparent.openingPSpec := { prover_first' := by simp }
    have hrun := Reduction.run_of_prover_first (oSpec := oSpec)
      (pSpec := Commitment.Transparent.openingPSpec)
      (cm, (⟨q, y⟩ : (q : O.Query) × O.Response q)) (d, u)
      ((Commitment.Transparent.transparentScheme (oSpec := oSpec) (Data := Data)).opening ((), ()))
    rw [show ((openingRed (oSpec := oSpec) (Data := Data)).run (cm, ⟨q, y⟩) (d, u)).run
        = (((Commitment.Transparent.transparentScheme (oSpec := oSpec)
            (Data := Data)).opening ((), ())).run (cm, ⟨q, y⟩) (d, u)).run from rfl,
        hrun] at hz
    -- Evaluate the fully deterministic body: each `liftM (pure ·)` is `pure (some ·)`, and each
    -- `Option.elim` on `some` selects the continuation. The verifier's verdict is
    -- `decide (answer cm q = y) = true` by `hans`.
    simp only [Commitment.Transparent.transparentScheme, OptionT.run_pure,
      liftM_pure, pure_bind, Option.getM_some, hans,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨_, rfl, by simp [acceptRejectRel], rfl⟩
  -- Now lift the support fact through `init`-bind, `simulateQ`, and `OptionT`.
  rw [probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, _root_.zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _ hc
    obtain ⟨_, hsome, _⟩ := hsupp none (_root_.support_simulateQ_run'_subset _ _ s hc)
    cases hsome
  · intro x hx
    rw [OptionT.mem_support_iff, OptionT.run_mk] at hx
    simp only [support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    obtain ⟨a, ha, hP⟩ := hsupp (some x) (_root_.support_simulateQ_run'_subset _ _ s hx)
    cases ha
    exact hP

set_option maxHeartbeats 800000 in
/-- **Perfect soundness of the opening phase.** The transparent opening verifier's verdict is the
transcript-independent boolean `decide (answer cm q = y)` (`opening_verify`). Hence for any opening
statement `(cm, ⟨q, y⟩)` *outside* `langMid` (i.e. `answer cm q ≠ y`) the verifier outputs `false`,
which is not in `langOut`; so even an arbitrary malicious prover makes the verifier accept with
probability `0`. This is the binding content of the transparent scheme expressed as verifier
soundness. -/
theorem openingRed_soundness :
    (openingRed (oSpec := oSpec) (Data := Data)).verifier.soundness init impl
      (langMid (Data := Data)) langOut 0 := by
  unfold Verifier.soundness
  intro WitIn WitOut witIn prover stmtIn hstmtIn pImpl
  obtain ⟨cm, q, y⟩ := stmtIn
  simp only [langMid, Set.mem_setOf_eq] at hstmtIn
  -- The bad event `stmtOut ∈ langOut` (= `stmtOut = true`) never holds: the verdict is `false`.
  simp only [ENNReal.coe_zero, nonpos_iff_eq_zero, probEvent_eq_zero_iff]
  intro x hx hev
  rw [OptionT.mem_support_iff, OptionT.run_mk] at hx
  simp only [support_bind, Set.mem_iUnion] at hx
  obtain ⟨s, _, hx⟩ := hx
  -- The verifier's verdict on `(cm, ⟨q, y⟩)` is `decide (answer cm q = y)`, independent of the
  -- transcript; since `answer cm q ≠ y`, the verdict is `false`.
  have hverdict : x.2 = false := by
    have key : ∀ z ∈ support
        (((Reduction.mk prover (openingRed (oSpec := oSpec) (Data := Data)).verifier).run
          (cm, ⟨q, y⟩) witIn)).run, ∀ a, z = some a → a.2 = false := by
      intro z hz a hza
      rw [Reduction.run] at hz
      simp only [OptionT.run_bind, Option.elimM, bind_assoc] at hz
      rw [mem_support_bind_iff] at hz
      obtain ⟨proverResultOpt, _, hz⟩ := hz
      cases proverResultOpt with
      | none =>
        simp only [Option.elim_none, support_pure, Set.mem_singleton_iff] at hz
        rw [hz] at hza; exact absurd hza.symm (by simp)
      | some proverResult =>
        dsimp only [Option.elim_some] at hz
        rw [mem_support_bind_iff] at hz
        obtain ⟨stmtOutOpt, hstmtOut, hz⟩ := hz
        -- The verifier verdict is `decide (answer cm q = y)`, transcript-independent.
        rw [Verifier.run] at hstmtOut
        simp only [openingRed, Commitment.Transparent.transparentScheme, OptionT.run_pure,
          liftM_pure, support_pure, Set.mem_singleton_iff] at hstmtOut
        subst hstmtOut
        simp only [Option.getM_some, Option.elim_some, support_pure,
          Set.mem_singleton_iff] at hz
        subst hz
        simp only [Option.some.injEq] at hza
        subst hza
        simp only [decide_eq_false_iff_not]
        exact hstmtIn
    exact key (some x) (_root_.support_simulateQ_run'_subset _ _ s hx) x rfl
  rw [hverdict] at hev
  simp only [langOut, Set.mem_setOf_eq] at hev
  exact absurd hev (by simp)

set_option maxHeartbeats 800000 in
/-- **Perfect completeness of the interaction phase.** The "commit and forward" reduction sends the
commitment and returns the input statement/witness unchanged; the verifier forwards the statement.
Hence for any `(stmt, wit) ∈ relMid` the output `(stmt, wit)` is again in `relMid`, with probability
one. -/
theorem interactionRed_perfectCompleteness :
    (interactionRed (oSpec := oSpec) (Data := Data)).perfectCompleteness init impl
      (relMid (Data := Data)) (relMid (Data := Data)) := by
  rw [Reduction.perfectCompleteness_eq_prob_one]
  intro stmt wit hmem
  -- The reduction is prover-first; its run forwards the statement/witness deterministically.
  have hsupp : ∀ z ∈ support
      ((interactionRed (oSpec := oSpec) (Data := Data)).run stmt wit).run,
      ∃ a, z = some a ∧ ((a.2, a.1.2.2) ∈ relMid (Data := Data) ∧ a.1.2.1 = a.2) := by
    intro z hz
    rw [Reduction.run_of_prover_first stmt wit
      (interactionRed (oSpec := oSpec) (Data := Data))] at hz
    simp only [interactionRed, interactionProver, interactionVerifier, Verifier.run,
      OptionT.run_pure, liftM_pure, pure_bind, Option.getM_some,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨_, rfl, hmem, rfl⟩
  rw [probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, _root_.zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _ hc
    obtain ⟨_, hsome, _⟩ := hsupp none (_root_.support_simulateQ_run'_subset _ _ s hc)
    cases hsome
  · intro x hx
    rw [OptionT.mem_support_iff, OptionT.run_mk] at hx
    simp only [support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    obtain ⟨a, ha, hP⟩ := hsupp (some x) (_root_.support_simulateQ_run'_subset _ _ s hx)
    cases ha
    exact hP

set_option maxHeartbeats 800000 in
/-- **Perfect soundness of the interaction phase.** The interaction verifier returns its input
statement unchanged, so for any malicious prover and any `stmtIn ∉ langMid` the output statement
equals `stmtIn ∉ langMid`; the bad event has probability `0`. -/
theorem interactionRed_soundness :
    (interactionRed (oSpec := oSpec) (Data := Data)).verifier.soundness init impl
      (langMid (Data := Data)) (langMid (Data := Data)) 0 := by
  unfold Verifier.soundness
  intro WitIn WitOut witIn prover stmtIn hstmtIn pImpl
  simp only [ENNReal.coe_zero, nonpos_iff_eq_zero, probEvent_eq_zero_iff]
  intro x hx hev
  apply hstmtIn
  rw [OptionT.mem_support_iff, OptionT.run_mk] at hx
  simp only [support_bind, Set.mem_iUnion] at hx
  obtain ⟨s, _, hx⟩ := hx
  -- The verifier returns `stmtIn`, so the output statement `x.2` equals `stmtIn`.
  have hverdict : x.2 = stmtIn := by
    have key : ∀ z ∈ support
        (((Reduction.mk prover (interactionRed (oSpec := oSpec) (Data := Data)).verifier).run
          stmtIn witIn)).run, ∀ a, z = some a → a.2 = stmtIn := by
      intro z hz a hza
      rw [Reduction.run] at hz
      simp only [OptionT.run_bind, Option.elimM, bind_assoc] at hz
      rw [mem_support_bind_iff] at hz
      obtain ⟨proverResultOpt, _, hz⟩ := hz
      cases proverResultOpt with
      | none =>
        simp only [Option.elim_none, support_pure, Set.mem_singleton_iff] at hz
        rw [hz] at hza; exact absurd hza.symm (by simp)
      | some proverResult =>
        dsimp only [Option.elim_some] at hz
        rw [mem_support_bind_iff] at hz
        obtain ⟨stmtOutOpt, hstmtOut, hz⟩ := hz
        rw [Verifier.run] at hstmtOut
        simp only [interactionRed, interactionVerifier, OptionT.run_pure, liftM_pure,
          support_pure, Set.mem_singleton_iff] at hstmtOut
        subst hstmtOut
        simp only [Option.getM_some, Option.elim_some, support_pure,
          Set.mem_singleton_iff] at hz
        subst hz
        simp only [Option.some.injEq] at hza
        subst hza
        rfl
    exact key (some x) (_root_.support_simulateQ_run'_subset _ _ s hx) x rfl
  rwa [hverdict] at hev

end Security

/-! ## Structural seam facts

Both keystones consume the same two direction facts: the interaction → opening seam round, and the
opening phase's first round, are prover messages. -/

theorem hn_pos :
    (0 : ℕ) < Fin.vsum (fun j => (nCom (Data := Data)) ((e (Data := Data)).symm j)) := by
  rw [vsum_eq_one]; norm_num

theorem hOpeningFirstDir :
    ((srcPSpec (Data := Data)).BCSOpeningPhase (pSpecCom (Data := Data)) (e (Data := Data))).dir
      (⟨0, hn_pos (Data := Data)⟩ :
        Fin (Fin.vsum (fun j => (nCom (Data := Data)) ((e (Data := Data)).symm j))))
      = .P_to_V := rfl

theorem hSeamDir :
    (((srcPSpec (Data := Data)).renameMessage (CommitmentType (Data := Data))) ++ₚ
        ((srcPSpec (Data := Data)).BCSOpeningPhase (pSpecCom (Data := Data))
          (e (Data := Data)))).dir
      (⟨1, by have := vsum_eq_one (Data := Data); omega⟩ :
        Fin (1 + Fin.vsum (fun j => (nCom (Data := Data)) ((e (Data := Data)).symm j))))
      = .P_to_V := rfl

/-! ## The compiled BCS instance and the two headline results -/

/-- Every challenge type of the renamed interaction spec is `Fintype` (vacuously: no challenges). -/
instance instFintypeInteractionChallenge :
    ∀ i, Fintype (((srcPSpec (Data := Data)).renameMessage
      (CommitmentType (Data := Data))).Challenge i) :=
  fun i => (instIsEmptyInteractionChallenge (Data := Data)).false i |>.elim

instance instInhabitedInteractionChallenge :
    ∀ i, Inhabited (((srcPSpec (Data := Data)).renameMessage
      (CommitmentType (Data := Data))).Challenge i) :=
  fun i => (instIsEmptyInteractionChallenge (Data := Data)).false i |>.elim

/-- Every challenge type of the opening phase is `Fintype` (vacuously: no challenges). -/
instance instFintypeOpeningChallenge :
    ∀ i, Fintype (((srcPSpec (Data := Data)).BCSOpeningPhase (pSpecCom (Data := Data))
      (e (Data := Data))).Challenge i) :=
  fun i => (instIsEmptyOpeningChallenge (Data := Data)).false i |>.elim

instance instInhabitedOpeningChallenge :
    ∀ i, Inhabited (((srcPSpec (Data := Data)).BCSOpeningPhase (pSpecCom (Data := Data))
      (e (Data := Data))).Challenge i) :=
  fun i => (instIsEmptyOpeningChallenge (Data := Data)).false i |>.elim

/-- `SampleableType` for the fully BCS-transformed spec's challenges: definitionally the append
of the two phases' challenges, both vacuously sampleable (no verifier challenges anywhere). -/
instance instSampleableBCSTransform :
    ∀ i, SampleableType (((srcPSpec (Data := Data)).BCSTransform (pSpecCom (Data := Data))
      (CommitmentType (Data := Data)) (e (Data := Data))).Challenge i) :=
  fun i => inferInstanceAs (SampleableType
    ((((srcPSpec (Data := Data)).renameMessage (CommitmentType (Data := Data))) ++ₚ
      ((srcPSpec (Data := Data)).BCSOpeningPhase (pSpecCom (Data := Data))
        (e (Data := Data)))).Challenge i))

/-- Concrete realization obligation for the transparent interaction phase: the prover's unique
message is the source commitment and the phase forwards the original statement/witness pair. -/
def interactionRealizesOracleMessages : Prop :=
  ∀ (stmt : OpeningStmt (Data := Data)) (wit : OpeningWit (Data := Data)),
    (interactionProver (oSpec := oSpec) (Data := Data)).sendMessage
        (srcMsgIdx (Data := Data)) (stmt, wit)
      = pure (stmt.1, (stmt, wit))

theorem interactionRealizesOracleMessages_holds :
    interactionRealizesOracleMessages (oSpec := oSpec) (Data := Data) := by
  intro stmt wit
  rfl

/-- Concrete realization obligation for the transparent opening phase: the verifier accepts exactly
when the claimed response matches the transparent oracle answer at the queried point. -/
def openingRealizesQueryLog : Prop :=
  ∀ (cm : Data) (q : O.Query) (y : O.Response q)
    (tr : ((srcPSpec (Data := Data)).BCSOpeningPhase (pSpecCom (Data := Data))
      (e (Data := Data))).FullTranscript),
    (openingRed (oSpec := oSpec) (Data := Data)).verifier.verify (cm, ⟨q, y⟩) tr
      = (pure (decide (O.answer cm q = y)) : OptionT (OracleComp oSpec) Bool)

theorem openingRealizesQueryLog_holds :
    openingRealizesQueryLog (oSpec := oSpec) (Data := Data) := by
  intro cm q y tr
  rfl

/-- The BCS-compiled phases of the transparent end-to-end instance: the "commit and forward"
interaction phase and the transparent opening phase, carrying concrete realization obligations for
the message and query-log behavior. -/
def phases :
    OracleReduction.BCSCompiledPhases (oSpec := oSpec) (pSpec := srcPSpec (Data := Data))
      (pSpecCom := pSpecCom (Data := Data))
      (StmtIn := OpeningStmt (Data := Data)) (WitIn := OpeningWit (Data := Data))
      (StmtOut := Bool) (WitOut := Unit)
      (StmtMid := OpeningStmt (Data := Data)) (WitMid := OpeningWit (Data := Data))
      (CommitmentType (Data := Data)) (e (Data := Data)) where
  interaction := interactionRed
  opening := openingRed
  interaction_realizes_oracle_messages := interactionRealizesOracleMessages (oSpec := oSpec)
    (Data := Data)
  opening_realizes_query_log := openingRealizesQueryLog (oSpec := oSpec) (Data := Data)

theorem phases_realizationFrontier :
    OracleReduction.BCSPhaseRealizationFrontier
      (phases (oSpec := oSpec) (Data := Data)) := by
  exact ⟨interactionRealizesOracleMessages_holds (oSpec := oSpec) (Data := Data),
    openingRealizesQueryLog_holds (oSpec := oSpec) (Data := Data)⟩

/-- The transparent end-to-end phases in **proof-carrying** form (issue #342): the semantic
realization payloads (`interactionRealizesOracleMessages` / `openingRealizesQueryLog`) come
packaged with their proofs, so no consumer can treat them as unconstrained payload data. -/
def phasesLawful :
    OracleReduction.BCSCompiledPhasesLawful (oSpec := oSpec) (pSpec := srcPSpec (Data := Data))
      (pSpecCom := pSpecCom (Data := Data))
      (StmtIn := OpeningStmt (Data := Data)) (WitIn := OpeningWit (Data := Data))
      (StmtOut := Bool) (WitOut := Unit)
      (StmtMid := OpeningStmt (Data := Data)) (WitMid := OpeningWit (Data := Data))
      (CommitmentType (Data := Data)) (e (Data := Data)) where
  toBCSCompiledPhases := phases (oSpec := oSpec) (Data := Data)
  interaction_realization_holds :=
    interactionRealizesOracleMessages_holds (oSpec := oSpec) (Data := Data)
  opening_realization_holds := openingRealizesQueryLog_holds (oSpec := oSpec) (Data := Data)

/-- The lawful packaging projects back to the original phases (sanity seam). -/
theorem phasesLawful_toBCSCompiledPhases :
    (phasesLawful (oSpec := oSpec) (Data := Data)).toBCSCompiledPhases
      = phases (oSpec := oSpec) (Data := Data) := rfl

section Final

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Headline (a): perfect completeness of the compiled transparent BCS protocol.**

The BCS transform of the "commit and forward" interaction phase and the transparent opening phase is
perfectly complete (input relation `relMid`, output relation `acceptRejectRel`), instantiating the
general keystone `OracleReduction.BCSTransform_perfectCompleteness`. The per-phase perfect
completeness is `interactionRed_perfectCompleteness` / `openingRed_perfectCompleteness`; the
structural seam facts are `hn_pos` / `hSeamDir` / `hOpeningFirstDir`. `hInit` / `hImplSupp` are the
honest-implementation side conditions (held by any honest interactive `impl`). -/
theorem transparentBCS_perfectCompleteness
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (OracleReduction.BCSTransform (e (Data := Data))
        (interactionRed (oSpec := oSpec) (Data := Data))
        (openingRed (oSpec := oSpec) (Data := Data))).perfectCompleteness init impl
      (relMid (Data := Data)) acceptRejectRel := by
  -- All challenge-augmented oracle specs are finite/inhabited: every challenge family is empty.
  haveI : (oSpec + [(((srcPSpec (Data := Data)).renameMessage (CommitmentType (Data := Data))) ++ₚ
      ((srcPSpec (Data := Data)).BCSOpeningPhase (pSpecCom (Data := Data))
        (e (Data := Data)))).Challenge]ₒ).Fintype :=
    ProtocolSpec.appendCombinedOracle_fintype oSpec _ _
  haveI : (oSpec + [(((srcPSpec (Data := Data)).renameMessage (CommitmentType (Data := Data))) ++ₚ
      ((srcPSpec (Data := Data)).BCSOpeningPhase (pSpecCom (Data := Data))
        (e (Data := Data)))).Challenge]ₒ).Inhabited :=
    ProtocolSpec.appendCombinedOracle_inhabited oSpec _ _
  haveI : (oSpec + [((srcPSpec (Data := Data)).renameMessage
      (CommitmentType (Data := Data))).Challenge]ₒ).Fintype :=
    haveI := ProtocolSpec.challengeOracle_fintype ((srcPSpec (Data := Data)).renameMessage
      (CommitmentType (Data := Data))); inferInstance
  haveI : (oSpec + [((srcPSpec (Data := Data)).renameMessage
      (CommitmentType (Data := Data))).Challenge]ₒ).Inhabited :=
    haveI := ProtocolSpec.challengeOracle_inhabited ((srcPSpec (Data := Data)).renameMessage
      (CommitmentType (Data := Data))); inferInstance
  haveI : (oSpec + [((srcPSpec (Data := Data)).BCSOpeningPhase (pSpecCom (Data := Data))
      (e (Data := Data))).Challenge]ₒ).Fintype :=
    haveI := ProtocolSpec.challengeOracle_fintype ((srcPSpec (Data := Data)).BCSOpeningPhase
      (pSpecCom (Data := Data)) (e (Data := Data))); inferInstance
  haveI : (oSpec + [((srcPSpec (Data := Data)).BCSOpeningPhase (pSpecCom (Data := Data))
      (e (Data := Data))).Challenge]ₒ).Inhabited :=
    haveI := ProtocolSpec.challengeOracle_inhabited ((srcPSpec (Data := Data)).BCSOpeningPhase
      (pSpecCom (Data := Data)) (e (Data := Data))); inferInstance
  exact OracleReduction.BCSTransform_perfectCompleteness (e (Data := Data))
    (interactionRed (oSpec := oSpec) (Data := Data)) (openingRed (oSpec := oSpec) (Data := Data))
    (relIn := relMid (Data := Data)) (relMid := relMid (Data := Data)) (relOut := acceptRejectRel)
    interactionRed_perfectCompleteness openingRed_perfectCompleteness
    (hn_pos (Data := Data)) (hSeamDir (Data := Data)) (hOpeningFirstDir (Data := Data))
    hInit hImplSupp

/-- **Headline (b): soundness of the compiled transparent BCS protocol.**

The compiled BCS verifier is sound with error `0 + 0 = 0` (input language `langMid`, output language
`langOut`), instantiating the unconditional message-seam keystone
`OracleReduction.BCSCompiledPhases.toReduction_soundness_of_append_msg`. The per-phase soundness is
`interactionRed_soundness` / `openingRed_soundness`; the structural seam facts are `hn_pos` /
`hSeamDir` / `hOpeningFirstDir`. `himplSP` / `himplNF` / `himplVB` are the honest-implementation
side conditions (held by any honest interactive `impl`). -/
theorem transparentBCS_soundness [Inhabited Data] [Inhabited O.Query]
    [∀ q, Inhabited (O.Response q)]
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    @Verifier.soundness _ oSpec (OpeningStmt (Data := Data)) Bool
      (1 + Fin.vsum (fun j => (nCom (Data := Data)) ((e (Data := Data)).symm j)))
      ((srcPSpec (Data := Data)).renameMessage (CommitmentType (Data := Data)) ++ₚ
        (srcPSpec (Data := Data)).BCSOpeningPhase (pSpecCom (Data := Data)) (e (Data := Data)))
      (fun i => ProtocolSpec.instSampleableTypeChallengeAppend i)
      σ init impl (langMid (Data := Data)) langOut
      (phases (oSpec := oSpec) (Data := Data)).toReduction.verifier (0 + 0) :=
  OracleReduction.BCSCompiledPhases.toReduction_soundness_of_append_msg
    (phases (oSpec := oSpec) (Data := Data))
    (langIn := langMid (Data := Data)) (langMid := langMid (Data := Data)) (langOut := langOut)
    interactionRed_soundness openingRed_soundness
    (hn_pos (Data := Data)) (hSeamDir (Data := Data)) (hOpeningFirstDir (Data := Data))
    himplSP himplNF himplVB

end Final

end BCSTransparentEndToEnd

#print axioms BCSTransparentEndToEnd.phases_realizationFrontier
#print axioms BCSTransparentEndToEnd.phasesLawful
#print axioms BCSTransparentEndToEnd.transparentBCS_perfectCompleteness
#print axioms BCSTransparentEndToEnd.transparentBCS_soundness
