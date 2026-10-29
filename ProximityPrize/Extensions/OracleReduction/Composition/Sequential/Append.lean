/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.OracleReduction.Composition.Sequential.Append

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ProximityPrize.Extensions.OracleReduction.ProtocolSpec.SeqCompose
import ArkLib.OracleReduction.ProtocolSpec.TranscriptRecompose
import ProximityPrize.Extensions.OracleReduction.Security.RoundByRound

/-!
  # Sequential Composition of Two (Oracle) Reductions

  This file gives the definition & properties of the sequential composition of two (oracle)
  reductions. For composition to be valid, we need that the output context (statement + oracle
  statement + witness) for the first (oracle) reduction is the same as the input context for the
  second (oracle) reduction.

  We have refactored the composition logic for `ProtocolSpec` and its associated structures into
  `ProtocolSpec.lean`, and we will use the definitions from there.

  We will prove that the composition of reductions preserve all completeness & soundness properties
  of the reductions being composed (with extra conditions on the extractor).
-/

set_option linter.style.longFile 4500

open OracleComp OracleSpec SubSpec

universe u v

section find_home

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α β : Type}
    (oa : OracleComp spec α)

end find_home

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

section OracleProtocol

variable [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
  {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]

namespace OracleVerifier.Append

/-! ### Oracle-query routing infrastructure for `OracleVerifier.append`

The composite oracle verifier runs `V₁` then `V₂`, but each `Vᵢ` queries its own oracle context
`oSpec + ([OStmtᵢ]ₒ + [pSpecᵢ.Message]ₒ)`, whereas the composite verifier lives in
`oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ)`. The two `QueryImpl` routers below re-route
each verifier's queries into that composite context (cf. the `routeOSpec/routeMsg/...` routers in
`LiftContext/OracleReduction.lean` and the `castMessageImpl` router in `Cast.lean`).

The `pSpec₁`/`pSpec₂` message oracles are carried into the appended message oracle at
`MessageIdx.inl`/`MessageIdx.inr`; the transport across the message-type equality is justified by
the heterogeneous agreement of the appended-message `OracleInterface` instance with `Oₘ₁`/`Oₘ₂`
(`instAppend_inl_heq`/`instAppend_inr_heq`). -/

/-- The appended message type at `MessageIdx.inl k` is `pSpec₁`'s message type at `k`. -/
theorem Message_inl (k : pSpec₁.MessageIdx) :
    (pSpec₁ ++ₚ pSpec₂).Message (MessageIdx.inl k) = pSpec₁.Message k := by
  unfold ProtocolSpec.Message MessageIdx.inl
  simp [Fin.vappend_eq_append, Fin.append_left]

/-- The appended message type at `MessageIdx.inr k` is `pSpec₂`'s message type at `k`. -/
theorem Message_inr (k : pSpec₂.MessageIdx) :
    (pSpec₁ ++ₚ pSpec₂).Message (MessageIdx.inr k) = pSpec₂.Message k := by
  unfold ProtocolSpec.Message MessageIdx.inr
  simp [Fin.vappend_eq_append, Fin.append_right]

/-- The appended-message `OracleInterface` instance at `MessageIdx.inl k` agrees, heterogeneously,
with `Oₘ₁ k`. -/
theorem instAppend_inl_heq (k : pSpec₁.MessageIdx) :
    HEq (instOracleInterfaceMessageAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
            (MessageIdx.inl k)) (Oₘ₁ k) := by
  obtain ⟨⟨k, hk⟩, hdir⟩ := k
  show HEq (instOracleInterfaceMessageAppend (MessageIdx.inl ⟨⟨k, hk⟩, hdir⟩)) _
  unfold instOracleInterfaceMessageAppend MessageIdx.inl
  simp only []
  rw [Fin.fappend₂_left]
  refine dcongr_heq (f₂ := fun h => Oₘ₁ (⟨⟨k, hk⟩, h⟩ : pSpec₁.MessageIdx))
    (proof_irrel_heq _ hdir) (fun t₁ t₂ _ => ?_) (fun _ _ => cast_heq _ _)
  congr 1
  show (pSpec₁.Type ++ᵛ pSpec₂.Type) (Fin.castAdd n ⟨k, hk⟩) = pSpec₁.Type ⟨k, hk⟩
  rw [Fin.vappend_left]

/-- The appended-message `OracleInterface` instance at `MessageIdx.inr k` agrees, heterogeneously,
with `Oₘ₂ k`. -/
theorem instAppend_inr_heq (k : pSpec₂.MessageIdx) :
    HEq (instOracleInterfaceMessageAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
            (MessageIdx.inr k)) (Oₘ₂ k) := by
  obtain ⟨⟨k, hk⟩, hdir⟩ := k
  show HEq (instOracleInterfaceMessageAppend (MessageIdx.inr ⟨⟨k, hk⟩, hdir⟩)) _
  unfold instOracleInterfaceMessageAppend MessageIdx.inr
  simp only []
  rw [Fin.fappend₂_right]
  refine dcongr_heq (f₂ := fun h => Oₘ₂ (⟨⟨k, hk⟩, h⟩ : pSpec₂.MessageIdx))
    (proof_irrel_heq _ hdir) (fun t₁ t₂ _ => ?_) (fun _ _ => cast_heq _ _)
  congr 1
  show (pSpec₁.Type ++ᵛ pSpec₂.Type) (Fin.natAdd m ⟨k, hk⟩) = pSpec₂.Type ⟨k, hk⟩
  rw [Fin.vappend_right]

/-- `cast`-form of `instAppend_inl_heq`, matching the `hO` shape required by `emitMessageQuery`. -/
theorem instAppend_inl_cast (k : pSpec₁.MessageIdx) :
    (Oₘ₁ k) = _root_.cast (congrArg OracleInterface (Message_inl k))
      (instOracleInterfaceMessageAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
        (MessageIdx.inl k)) := by
  apply eq_of_heq
  refine HEq.trans (instAppend_inl_heq (pSpec₂ := pSpec₂) k).symm ?_
  exact (cast_heq _ _).symm

/-- `cast`-form of `instAppend_inr_heq`, matching the `hO` shape required by `emitMessageQuery`. -/
theorem instAppend_inr_cast (k : pSpec₂.MessageIdx) :
    (Oₘ₂ k) = _root_.cast (congrArg OracleInterface (Message_inr k))
      (instOracleInterfaceMessageAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
        (MessageIdx.inr k)) := by
  apply eq_of_heq
  refine HEq.trans (instAppend_inr_heq (pSpec₁ := pSpec₁) k).symm ?_
  exact (cast_heq _ _).symm

/-- Per-query body emitting a query to the source message interface `O₁` (which agrees, up to the
message-type equality `hMsg`, with the appended-spec interface at the appended message index `j`)
into the appended-spec message oracle. Modelled on `OracleVerifier.castMessageQuery`. -/
def emitMessageQuery
    {T₁ : Type} (O₁ : OracleInterface T₁)
    (j : (pSpec₁ ++ₚ pSpec₂).MessageIdx) (hMsg : (pSpec₁ ++ₚ pSpec₂).Message j = T₁)
    (hO : O₁ = _root_.cast (congrArg OracleInterface hMsg)
      (instOracleInterfaceMessageAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) j))
    (q : O₁.Query) :
    OracleComp (oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ)) (O₁.Response q) := by
  subst hMsg
  subst hO
  exact query (spec := oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ))
    (Sum.inr (Sum.inr ⟨j, q⟩))

/-- Emit a `pSpec₁`-message query into the appended message oracle at `MessageIdx.inl`. -/
def emitMessageInl (i : pSpec₁.MessageIdx) (q : (Oₘ₁ i).Query) :
    OracleComp (oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ)) ((Oₘ₁ i).Response q) :=
  emitMessageQuery (oSpec := oSpec) (OStmt₁ := OStmt₁)
    (Oₘ₁ i) (MessageIdx.inl i) (Message_inl i) (instAppend_inl_cast (pSpec₂ := pSpec₂) i) q

/-- Emit a `pSpec₂`-message query into the appended message oracle at `MessageIdx.inr`. -/
private def emitMessageInr (i : pSpec₂.MessageIdx) (q : (Oₘ₂ i).Query) :
    OracleComp (oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ)) ((Oₘ₂ i).Response q) :=
  emitMessageQuery (oSpec := oSpec) (OStmt₁ := OStmt₁)
    (Oₘ₂ i) (MessageIdx.inr i) (Message_inr i) (instAppend_inr_cast (pSpec₁ := pSpec₁) i) q

/-- Router carrying `V₁`'s oracle context into the appended-spec oracle context: `oSpec` and the
input oracle statements `[OStmt₁]ₒ` pass through unchanged; `pSpec₁`-message queries are emitted at
`MessageIdx.inl`. -/
def router₁ : QueryImpl (oSpec + ([OStmt₁]ₒ + [pSpec₁.Message]ₒ))
    (OracleComp (oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ))) :=
  fun q => match q with
    | Sum.inl t =>
        query (spec := oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ)) (Sum.inl t)
    | Sum.inr (Sum.inl t) =>
        query (spec := oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ)) (Sum.inr (Sum.inl t))
    | Sum.inr (Sum.inr ⟨i, q⟩) => emitMessageInl (pSpec₂ := pSpec₂) i q

/-- Canonical routing of the second phase, including virtual output oracles. The first-phase
challenge transcript is explicit because a virtual output implementation may depend on it. -/
abbrev router₂ (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (challenges : pSpec₁.Challenges) :=
  secondQueryImpl (pSpec₂ := pSpec₂) V₁ challenges

/-- The authoritative append verifier, exposed under the historical helper name. -/
abbrev verify
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂) :=
  (OracleVerifier.append V₁ V₂).verify

/-! ### `toVerifier` / `append` bridge infrastructure -/

lemma simulateQ_simOracle2_leftQuery {ιₒ : Type} {spec : OracleSpec ιₒ}
    {κ₁ : Type} {U₁ : κ₁ → Type} [∀ i, OracleInterface (U₁ i)]
    {κ₂ : Type} {U₂ : κ₂ → Type} [∀ i, OracleInterface (U₂ i)]
    (u₁ : ∀ i, U₁ i) (u₂ : ∀ i, U₂ i) (qs : ([U₁]ₒ).Domain) :
    simulateQ (OracleInterface.simOracle2 spec u₁ u₂)
      (query (spec := spec + ([U₁]ₒ + [U₂]ₒ)) (Sum.inr (Sum.inl qs)))
      = (pure (OracleInterface.answer (u₁ qs.1) qs.2) : OracleComp spec _) := by
  change simulateQ (OracleInterface.simOracle2 spec u₁ u₂)
      (liftM ((spec + ([U₁]ₒ + [U₂]ₒ)).query (Sum.inr (Sum.inl qs)))) = _
  rw [simulateQ_spec_query]
  simp only [OracleInterface.simOracle2, QueryImpl.addLift_def, QueryImpl.add_apply_inr,
    QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply]
  change liftM (OracleInterface.simOracle0 U₁ u₁ qs) = _
  simp only [OracleInterface.simOracle0]
  rfl

lemma simulateQ_simOracle2_rightQuery {ιₒ : Type} {spec : OracleSpec ιₒ}
    {κ₁ : Type} {U₁ : κ₁ → Type} [∀ i, OracleInterface (U₁ i)]
    {κ₂ : Type} {U₂ : κ₂ → Type} [∀ i, OracleInterface (U₂ i)]
    (u₁ : ∀ i, U₁ i) (u₂ : ∀ i, U₂ i) (qm : ([U₂]ₒ).Domain) :
    simulateQ (OracleInterface.simOracle2 spec u₁ u₂)
      (query (spec := spec + ([U₁]ₒ + [U₂]ₒ)) (Sum.inr (Sum.inr qm)))
      = (pure (OracleInterface.answer (u₂ qm.1) qm.2) : OracleComp spec _) := by
  change simulateQ (OracleInterface.simOracle2 spec u₁ u₂)
      (liftM ((spec + ([U₁]ₒ + [U₂]ₒ)).query (Sum.inr (Sum.inr qm)))) = _
  rw [simulateQ_spec_query]
  simp only [OracleInterface.simOracle2, QueryImpl.addLift_def, QueryImpl.add_apply_inr,
    QueryImpl.liftTarget_apply]
  change liftM (OracleInterface.simOracle0 U₂ u₂ qm) = _
  simp only [OracleInterface.simOracle0]
  rfl

theorem messages_fst_heq (tr : FullTranscript (pSpec₁ ++ₚ pSpec₂)) (k : pSpec₁.MessageIdx) :
    HEq (tr.fst.messages k) (tr.messages (MessageIdx.inl k)) := by
  show HEq (tr.fst k.val) (tr (MessageIdx.inl k).val)
  unfold FullTranscript.fst
  simp only [MessageIdx.inl]
  exact cast_heq _ _

theorem messages_snd_heq (tr : FullTranscript (pSpec₁ ++ₚ pSpec₂)) (k : pSpec₂.MessageIdx) :
    HEq (tr.snd.messages k) (tr.messages (MessageIdx.inr k)) := by
  show HEq (tr.snd k.val) (tr (MessageIdx.inr k).val)
  unfold FullTranscript.snd
  simp only [MessageIdx.inr]
  exact cast_heq _ _

theorem challenges_fst_heq (tr : FullTranscript (pSpec₁ ++ₚ pSpec₂)) (i : ChallengeIdx pSpec₁) :
    HEq (tr.fst.challenges i) (tr.challenges (ChallengeIdx.inl i)) := by
  show HEq (tr.fst i.val) (tr (ChallengeIdx.inl i).val)
  unfold FullTranscript.fst
  simp only [ChallengeIdx.inl]
  exact cast_heq _ _

theorem challenges_snd_heq (tr : FullTranscript (pSpec₁ ++ₚ pSpec₂)) (i : ChallengeIdx pSpec₂) :
    HEq (tr.snd.challenges i) (tr.challenges (ChallengeIdx.inr i)) := by
  show HEq (tr.snd i.val) (tr (ChallengeIdx.inr i).val)
  unfold FullTranscript.snd
  simp only [ChallengeIdx.inr]
  exact cast_heq _ _

theorem emitMessageQuery_simulateQ (oStmt : ∀ i, OStmt₁ i)
    (msgs : ∀ j, (pSpec₁ ++ₚ pSpec₂).Message j)
    {T₁ : Type} (O₁ : OracleInterface T₁) (j : (pSpec₁ ++ₚ pSpec₂).MessageIdx)
    (hMsg : (pSpec₁ ++ₚ pSpec₂).Message j = T₁)
    (hO : O₁ = _root_.cast (congrArg OracleInterface hMsg)
      (instOracleInterfaceMessageAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) j))
    (q : O₁.Query) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs) (emitMessageQuery O₁ j hMsg hO q)
      = pure (O₁.answer (hMsg ▸ msgs j) q) := by
  subst hMsg; subst hO
  simp only [emitMessageQuery, simulateQ_query]
  rfl

theorem simulateQ_emitMessageInl (oStmt : ∀ i, OStmt₁ i)
    (tr : FullTranscript (pSpec₁ ++ₚ pSpec₂)) (i : pSpec₁.MessageIdx) (q : (Oₘ₁ i).Query) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt tr.messages) (emitMessageInl i q)
      = pure ((Oₘ₁ i).answer (tr.fst.messages i) q) := by
  rw [emitMessageInl, emitMessageQuery_simulateQ]
  congr 1 <;> exact eq_of_heq ((eqRec_heq _ _).trans (messages_fst_heq tr i).symm)

lemma router1_collapse (oStmt : ∀ i, OStmt₁ i) (tr : FullTranscript (pSpec₁ ++ₚ pSpec₂)) :
    (OracleInterface.simOracle2 oSpec oStmt tr.messages) ∘ₛ router₁
      = OracleInterface.simOracle2 oSpec oStmt tr.fst.messages := by
  funext q
  rw [QueryImpl.apply_compose]
  rcases q with t | (t | ⟨i, q⟩) <;> dsimp only [router₁]
  · rfl
  · rfl
  · exact simulateQ_emitMessageInl oStmt tr i q

theorem simulateQ_emitMessageInr (oStmt : ∀ i, OStmt₁ i)
    (tr : FullTranscript (pSpec₁ ++ₚ pSpec₂)) (i : pSpec₂.MessageIdx) (q : (Oₘ₂ i).Query) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt tr.messages) (emitMessageInr i q)
      = pure ((Oₘ₂ i).answer (tr.snd.messages i) q) := by
  rw [emitMessageInr, emitMessageQuery_simulateQ]
  congr 1 <;> exact eq_of_heq ((eqRec_heq _ _).trans (messages_snd_heq tr i).symm)

/-- Materializing the appended virtual output is the composition of the two canonical
materializations. This replaces the obsolete embedding-index equation. -/
theorem append_materializeOutput
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    (oStmt : ∀ i, OStmt₁ i) (tr : FullTranscript (pSpec₁ ++ₚ pSpec₂)) :
    (OracleVerifier.append V₁ V₂).materializeOutput tr.challenges oStmt tr.messages =
      V₂.materializeOutput tr.snd.challenges
        (V₁.materializeOutput tr.fst.challenges oStmt tr.fst.messages) tr.snd.messages := rfl

end OracleVerifier.Append

end OracleProtocol

/-! Sequential composition of extractors and state functions

These have the following form: they needs to know the first verifier, and derive the intermediate
statement from running the first verifier on the first statement.

This leads to complications: the verifier is assumed to be a general `OracleComp oSpec`, and so
we also need to have the extractors and state functions to be similarly `OracleComp`s.

The alternative is to consider a fully deterministic (and non-failing) verifier. The non-failing
part is somewhat problematic as we write our verifiers to be able to fail (i.e. implicit failing
via `guard` statements).

As such, the definitions below isolate the extractor composition interface. -/

namespace Extractor

end Extractor

section Security

open scoped NNReal

section Protocol

variable {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
    {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)}
    {rel₃ : Set (Stmt₃ × Wit₃)}

namespace Reduction

/-- **NAMED RESIDUAL — reduces to the single keystone `Prover.append_run`.** Unlike the soundness
theorems (which quantify over arbitrary malicious provers), completeness uses the *honest* composite
prover `(R₁.prover).append (R₂.prover)`, so the run factoring is exactly `Prover.append_run` (the
deep keystone in this file, whose per-round seam/interior reductions are all proven; only the
right-block
run induction + output assembly remain). Once `Prover.append_run` is available, the proof is:
1. rewrite `(R₁.append R₂).run` via `Prover.append_run` (prover side) + `Verifier.append_run`
   (proven, `rfl`, verifier side) into the sequential `R₁.run >>= R₂.run` shape;
2. push the success-probability through the bind: the phase-1 output `(stmt₂, wit₂) ∈ rel₂` holds
   except w.p. `completenessError₁` (by `h₁`), and conditioned on it the phase-2 output is in `rel₃`
   except w.p. `completenessError₂` (by `h₂`);
3. union bound ⇒ total error `completenessError₁ + completenessError₂`.
The genuinely-deep dependency is therefore *only* `Prover.append_run`; the probabilistic step is the
standard two-stage success-probability union bound. -/
def reductionAppendCompletenessResidual
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    {completenessError₁ completenessError₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ completenessError₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ completenessError₂) : Prop :=
  (R₁.append R₂).completeness init impl rel₁ rel₃ (completenessError₁ + completenessError₂)

theorem reduction_append_completeness
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    {completenessError₁ completenessError₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ completenessError₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ completenessError₂)
    (hResidual : reductionAppendCompletenessResidual R₁ R₂ h₁ h₂) :
      (R₁.append R₂).completeness init impl
        rel₁ rel₃ (completenessError₁ + completenessError₂) :=
  hResidual

def reductionAppendPerfectCompletenessResidual
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃) : Prop :=
  (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃

theorem reduction_append_perfectCompleteness
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hResidual : reductionAppendPerfectCompletenessResidual R₁ R₂ h₁ h₂) :
      (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ :=
  hResidual

end Reduction

namespace Verifier

/-- **NAMED RESIDUAL (deep, arbitrary-prover seam decomposition).** Sequential composition preserves
soundness with the additive error `soundnessError₁ + soundnessError₂`.

The remaining obstruction is *not* `Prover.append_run` (which only factors an *honest*
`P₁.append P₂`): soundness quantifies over an *arbitrary malicious* prover `P` over
`pSpec₁ ++ₚ pSpec₂`, so the proof must decompose `P` at the seam round `m` into a `pSpec₁`-phase
malicious prover `P↾₁` (running rounds
`0..m-1`, with `P`'s round-`m` output context as its `output`) and a `pSpec₂`-phase malicious prover
`P↾₂` (resuming from that context). Then:
1. `Verifier.append_run` (proven, `rfl`) splits
   `(V₁.append V₂).run = V₁.run tr.fst >>= V₂.run tr.snd`.
2. The bad event `stmtOut ∈ lang₃` decomposes through the intermediate statement `stmt₂`:
   either `stmt₂ ∉ lang₂` (bounded by `h₁` applied to `P↾₁`, since `stmt₁ ∉ lang₁`) or
   `stmt₂ ∈ lang₂` and `stmtOut ∈ lang₃` (bounded by `h₂` applied to `P↾₂`).
3. A union bound over these two events gives `soundnessError₁ + soundnessError₂`.
The genuinely new content is the malicious-prover seam decomposition (no analogue of the honest
`Prover.append` exists in the codebase yet) plus the probabilistic union bound; both are deep. -/
def appendSoundnessResidual {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ soundnessError₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ soundnessError₂) : Prop :=
  (V₁.append V₂).soundness init impl lang₁ lang₃ (soundnessError₁ + soundnessError₂)

/-- **NAMED RESIDUAL (deep, arbitrary-prover seam decomposition + extractor composition).**
Sequential composition preserves straightline knowledge soundness with additive error.

The composite straightline extractor is `Extractor.Straightline.append` (proven, above): it runs
`V₁` to derive the intermediate statement, then `E₂` then `E₁`. The remaining obstruction mirrors
`append_soundness`: the malicious prover `P` over `pSpec₁ ++ₚ pSpec₂` must be seam-decomposed into
phase-1 / phase-2 malicious provers so that `h₁`/`h₂` (the per-phase extractor guarantees) apply,
and the bad knowledge event `(stmtIn, witIn') ∉ relIn ∧ (stmtOut, witOut) ∈ relOut` must be
union-bounded
through the intermediate `(stmt₂, wit₂)` pair. The extractor query-log routing across the seam
(`proveQueryLog.fst` / `verifyQueryLog`) is the additional new content over `append_soundness`. -/
def appendKnowledgeSoundnessResidual
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (h₁ : V₁.knowledgeSoundness init impl rel₁ rel₂ knowledgeError₁)
    (h₂ : V₂.knowledgeSoundness init impl rel₂ rel₃ knowledgeError₂) : Prop :=
  (V₁.append V₂).knowledgeSoundness init impl rel₁ rel₃ (knowledgeError₁ + knowledgeError₂)

/-- **NAMED RESIDUAL (deep) + DOCUMENTED STATEMENT GAP (missing side conditions).**
Sequential composition preserves round-by-round soundness, with the per-round error obtained by
routing through `ChallengeIdx.sumEquiv`.

The composite state function is intended to be `Verifier.StateFunction.append` (proven, above). -/
def appendRbrSoundnessResidual {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rbrSoundnessError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrSoundnessError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrSoundness init impl lang₁ lang₂ rbrSoundnessError₁)
    (h₂ : V₂.rbrSoundness init impl lang₂ lang₃ rbrSoundnessError₂) : Prop :=
  (V₁.append V₂).rbrSoundness init impl lang₁ lang₃
    (Sum.elim rbrSoundnessError₁ rbrSoundnessError₂ ∘ ChallengeIdx.sumEquiv.symm)

/-- **NAMED RESIDUAL (deep) + DOCUMENTED STATEMENT GAP (missing side conditions).**
Sequential composition preserves round-by-round knowledge soundness.

The composite knowledge state function / round-by-round extractor are intended to be the proven
`Verifier.StateFunction.append` (for the state-function leg) and `Extractor.RoundByRound.append`
(the round-by-round extractor, proven above, which threads the intermediate statement via a
deterministic
`verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂`). As with `append_rbrSoundness`, the statement is
missing the two side hypotheses that the intended state-function construction requires:
  * `hVerify` (V₁ deterministic & non-failing) — also supplies the very `verify` function that
    `Extractor.RoundByRound.append` consumes; without it neither the state-function nor the
    extractor leg can be instantiated;
  * `hInit : ∃ s, s ∈ support init`.
With those added, the residue is the per-round knowledge bound: case on phase-1 vs phase-2 of the
appended challenge index, defer to `h₁`/`h₂`, and identify the composite `extractMid`/`extractOut`
(per `Extractor.RoundByRound.append`'s construction) with the per-phase extractors across the
seam. -/
def appendRbrKnowledgeSoundnessResidual
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂) : Prop :=
  (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
    (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm)

end Verifier

end Protocol

section OracleProtocol

variable {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type}
    [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
    {Wit₁ : Type}
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type}
    [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
    {Wit₂ : Type}
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type}
    [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
    {Wit₃ : Type}
    {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [Oₘ₁ : ∀ i, OracleInterface ((pSpec₁.Message i))]
    [Oₘ₂ : ∀ i, OracleInterface ((pSpec₂.Message i))]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

namespace OracleReduction

def appendCompletenessResidual
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)

    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    {completenessError₁ completenessError₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ completenessError₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ completenessError₂) : Prop :=
  (R₁.append R₂).completeness init impl rel₁ rel₃ (completenessError₁ + completenessError₂)

theorem append_completeness
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)

    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    {completenessError₁ completenessError₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ completenessError₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ completenessError₂)
    (hResidual : appendCompletenessResidual R₁ R₂ h₁ h₂) :
      (R₁.append R₂).completeness init impl
        rel₁ rel₃ (completenessError₁ + completenessError₂) :=
  hResidual

def appendPerfectCompletenessResidual
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)

    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃) : Prop :=
  (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃

theorem append_perfectCompleteness
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)

    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hResidual : appendPerfectCompletenessResidual R₁ R₂ h₁ h₂) :
      (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ :=
  hResidual

end OracleReduction

namespace OracleVerifier

variable {lang₁ : Set (Stmt₁ × (∀ i, OStmt₁ i))}
    {lang₂ : Set (Stmt₂ × (∀ i, OStmt₂ i))}
    {lang₃ : Set (Stmt₃ × (∀ i, OStmt₃ i))}

def appendSoundnessResidual
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)

    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ soundnessError₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ soundnessError₂) : Prop :=
  (V₁.append V₂).soundness init impl lang₁ lang₃ (soundnessError₁ + soundnessError₂)

def appendKnowledgeSoundnessResidual
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)

    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (h₁ : V₁.knowledgeSoundness init impl rel₁ rel₂ knowledgeError₁)
    (h₂ : V₂.knowledgeSoundness init impl rel₂ rel₃ knowledgeError₂) : Prop :=
  (V₁.append V₂).knowledgeSoundness init impl rel₁ rel₃ (knowledgeError₁ + knowledgeError₂)

def appendRbrSoundnessResidual (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)

    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {rbrSoundnessError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrSoundnessError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrSoundness init impl lang₁ lang₂ rbrSoundnessError₁)
    (h₂ : V₂.rbrSoundness init impl lang₂ lang₃ rbrSoundnessError₂) : Prop :=
  (V₁.append V₂).rbrSoundness init impl lang₁ lang₃
    (Sum.elim rbrSoundnessError₁ rbrSoundnessError₂ ∘ ChallengeIdx.sumEquiv.symm)

def appendRbrKnowledgeSoundnessResidual
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)

    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂) : Prop :=
  (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
    (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm)

end OracleVerifier

end OracleProtocol

end Security

namespace Verifier

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}

/-! ### Entry-level HEq lemmas for appended-transcript projections

Each projection (`Transcript.fst`/`snd`, `FullTranscript.fst`/`snd`) entry is a `cast` of an entry
of the underlying transcript, hence heterogeneously equal to it. Together with `fin_app_heq`
(same dependent function at value-equal indices), these discharge the pointwise obligations of the
`Function.hfunext` steps in `StateFunction.append` below. -/

/-- A dependent function on `Fin d` sends value-equal indices to `HEq` outputs. -/
private theorem fin_app_heq {d : ℕ} {α : Fin d → Sort*} (f : (i : Fin d) → α i)
    {i j : Fin d} (h : (i : ℕ) = (j : ℕ)) : HEq (f i) (f j) := by
  cases Fin.ext h
  exact HEq.rfl

/-- Entry-level unfolding of the partial first-half projection. -/
private theorem transcriptFst_heq_entry {k : Fin (m + n + 1)}
    (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) (i : Fin (min (k : ℕ) m)) :
    HEq (Transcript.fst T i) (T ⟨(i : ℕ), lt_of_lt_of_le i.isLt (min_le_left _ _)⟩) := by
  unfold Transcript.fst
  exact cast_heq _ _

/-- Entry-level unfolding of the partial second-half projection (past the phase boundary). -/
private theorem transcriptSnd_heq_entry {k : Fin (m + n + 1)}
    (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) (hk : ¬ (k : ℕ) ≤ m) (i : Fin ((k : ℕ) - m)) :
    HEq (Transcript.snd T i) (T ⟨m + (i : ℕ), by omega⟩) := by
  unfold Transcript.snd
  exact cast_heq _ _

/-- Entry-level unfolding of the full first-half projection. -/
private theorem fullTranscriptFst_heq_entry (T : (pSpec₁ ++ₚ pSpec₂).FullTranscript) (i : Fin m) :
    HEq (T.fst i) (T (Fin.castAdd n i)) := by
  rw [← congrFun (FullTranscript.fst_append_snd T) (Fin.castAdd n i)]
  refine HEq.trans ?_ (Fin.happend_heq_left T.fst T.snd (Fin.castAdd n i)
    (by simp only [Fin.val_castAdd]; omega)).symm
  exact fin_app_heq T.fst (by simp only [Fin.val_castAdd, Fin.val_mk])

/-- Entry-level unfolding of the full second-half projection. -/
private theorem fullTranscriptSnd_heq_entry (T : (pSpec₁ ++ₚ pSpec₂).FullTranscript) (i : Fin n) :
    HEq (T.snd i) (T (Fin.natAdd m i)) := by
  rw [← congrFun (FullTranscript.fst_append_snd T) (Fin.natAdd m i)]
  refine HEq.trans ?_ (Fin.happend_heq_right T.fst T.snd (Fin.natAdd m i)
    (by simp only [Fin.val_natAdd]; omega)).symm
  exact fin_app_heq T.snd (by simp only [Fin.val_natAdd, Fin.val_mk]; omega)

/-- Entry of an `Eq.mp`-transported transcript is heterogeneously the original entry (the two
round indices being equal). -/
private theorem eqMp_transcript_heq_entry {p : ℕ} {pSpec : ProtocolSpec p} {k k' : Fin (p + 1)}
    (hkk : k = k') (e : pSpec.Transcript k = pSpec.Transcript k')
    (f : pSpec.Transcript k) {i : Fin (k : ℕ)} {i' : Fin (k' : ℕ)} (hii : (i : ℕ) = (i' : ℕ)) :
    HEq (e.mp f i') (f i) := by
  subst hkk
  cases Fin.ext hii
  exact HEq.rfl

/-- **Doomed-ness crosses the language.** For a *deterministic* first verifier `V₁ = pure ∘ verify`
with a reachable initial state (`∃ s, s ∈ support init`), if its state function `S₁` is false on a
full transcript, then the intermediate statement `verify stmt tr` lies *outside* `lang₂`.

This is the bridge that makes the un-conjoined composite state function work: it converts the
probabilistic `S₁.toFun_full` (`Pr[… ∈ lang₂ | …] = 0`) into the pointwise membership fact needed to
fire `S₂.toFun_empty` at the phase crossing. -/
private theorem StateFunction.verify_not_mem_lang_of_toFun_full_neg
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁}
    (S₁ : V₁.StateFunction init impl lang₁ lang₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init)
    (stmt : Stmt₁) (tr : pSpec₁.FullTranscript)
    (hNeg : ¬ S₁ (Fin.last m) stmt tr) :
    verify stmt tr ∉ lang₂ := by
  have hPr := S₁.toFun_full stmt tr hNeg
  rw [ProximityPrize.Compatibility.DiscreteSupportSemantics.prEvent_eq_zero_iff] at hPr
  -- `V₁.run stmt tr = pure (verify stmt tr)`, so `verify stmt tr` is a reachable output; the
  -- `Pr = 0` hypothesis then forbids it from lying in `lang₂`.
  obtain ⟨s, hs⟩ := hInit
  refine hPr (verify stmt tr) ?_
  rw [OptionT.mem_support_iff]
  simp only [OptionT.run_mk, support_bind, Set.mem_iUnion]
  refine ⟨s, hs, ?_⟩
  have hrun : (V₁.run stmt tr) = (pure (verify stmt tr) : OptionT (OracleComp oSpec) Stmt₂) := by
    subst hVerify; rfl
  rw [hrun]
  change some (verify stmt tr) ∈ MonadAttach.support
    (StateT.run' (simulateQ impl (pure (some (verify stmt tr)) :
      OracleComp oSpec (Option Stmt₂))) s)
  rw [simulateQ_pure]
  change some (verify stmt tr) ∈ MonadAttach.support
    (Prod.fst <$> (pure (some (verify stmt tr)) : StateT σ ProbComp _).run s)
  rw [StateT.run_pure]
  simp [map_pure]

end Verifier

section Execution

namespace Prover

variable {P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}
    {stmt : Stmt₁} {wit : Wit₁}

/-- The challenge type at index `i` of the left protocol coincides with the challenge type at the
  embedded index `ChallengeIdx.inl i` of the appended protocol. This is the response-type equality
  underlying the `SubSpec` inclusion of the left challenge oracle into the appended one. -/
private theorem range_challenge_append_inl (i : pSpec₁.ChallengeIdx) :
    [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.Range ⟨ChallengeIdx.inl i, ()⟩
      = [pSpec₁.Challenge]ₒ.Range ⟨i, ()⟩ := by
  show (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i) = pSpec₁.Challenge i
  simp [ChallengeIdx.inl, ProtocolSpec.append]

/-- The challenge type at index `i` of the right protocol coincides with the challenge type at the
  embedded index `ChallengeIdx.inr i` of the appended protocol. This is the response-type equality
  underlying the `SubSpec` inclusion of the right challenge oracle into the appended one. -/
private theorem range_challenge_append_inr (i : pSpec₂.ChallengeIdx) :
    [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.Range ⟨ChallengeIdx.inr i, ()⟩
      = [pSpec₂.Challenge]ₒ.Range ⟨i, ()⟩ := by
  show (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i) = pSpec₂.Challenge i
  simp [ChallengeIdx.inr, ProtocolSpec.append]

/-- The left protocol's challenge oracle is a sub-spec of the appended protocol's challenge oracle:
  a query to challenge round `i` of `pSpec₁` is forwarded to round `ChallengeIdx.inl i` of
  `pSpec₁ ++ₚ pSpec₂`, with responses transported back along `range_challenge_append_inl`. -/
instance : [(pSpec₁).Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ where
  monadLift := fun q => ⟨⟨ChallengeIdx.inl q.input.1, ()⟩,
    q.cont ∘ (fun r => (range_challenge_append_inl q.input.1) ▸ r)⟩
  onQuery := fun t => ⟨ChallengeIdx.inl t.1, ()⟩
  onResponse := fun t r => (range_challenge_append_inl t.1) ▸ r

/-- The right protocol's challenge oracle is a sub-spec of the appended protocol's challenge oracle:
  a query to challenge round `i` of `pSpec₂` is forwarded to round `ChallengeIdx.inr i` of
  `pSpec₁ ++ₚ pSpec₂`, with responses transported back along `range_challenge_append_inr`. -/
instance : [(pSpec₂).Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ where
  monadLift := fun q => ⟨⟨ChallengeIdx.inr q.input.1, ()⟩,
    q.cont ∘ (fun r => (range_challenge_append_inr q.input.1) ▸ r)⟩
  onQuery := fun t => ⟨ChallengeIdx.inr t.1, ()⟩
  onResponse := fun t r => (range_challenge_append_inr t.1) ▸ r

/-! ### Left-block run characterization support

The following support lemmas (proven by `Fin.induction` + the HEq transport toolkit) establish that
running the appended prover `P₁.append P₂` up to a *left-half* round `j ≤ m` is heterogeneously the
`liftM` (along the left challenge `SubSpec`) of running `P₁` up to round `j`.  The keystone is
`append_runToRound_left`; its seam specialization `append_runToRound_seam` (target round `m`) is the
entry point for `append_run`. -/

/-- Support lemma: PrvState of the appended prover matches `P₁`'s on the left half. -/
theorem append_PrvState_castLE (j : Fin (m + 1)) :
    (P₁.append P₂).PrvState (j.castLE (by omega)) = P₁.PrvState j := by
  unfold Prover.append
  dsimp only [Function.comp_apply]
  rw [show (Fin.cast (by omega) (j.castLE (by omega)) : Fin (m + 1 + n)) = Fin.castAdd n j from by
        ext; simp]
  rw [Fin.append_left]

/-- Support lemma `append_Transcript_castLE`: the appended-protocol transcript type at a left-half
round equals `pSpec₁`'s transcript type. -/
theorem append_Transcript_castLE (j : Fin (m + 1)) :
    (pSpec₁ ++ₚ pSpec₂).Transcript (j.castLE (by omega)) = pSpec₁.Transcript j := by
  show ((pSpec₁ ++ₚ pSpec₂).take _ _).FullTranscript = (pSpec₁.take _ _).FullTranscript
  unfold ProtocolSpec.FullTranscript ProtocolSpec.take
  apply pi_congr
  intro i
  have hi : (i : ℕ) < m := by
    have h1 := i.isLt
    have h2 := j.isLt
    simp only [Fin.val_castLE] at h1
    omega
  simp only [Fin.take_apply, Fin.vappend_eq_append]
  rw [show (Fin.castLE (by omega) i : Fin (m + n)) = Fin.castAdd n ⟨i, hi⟩ from by ext; simp]
  rw [Fin.append_left]
  congr 1

/-- Support lemma `append_input_heq`: the appended prover's `input` is heterogeneously equal to
`P₁`'s `input`. -/
theorem append_input_heq :
    HEq ((P₁.append P₂).input (stmt, wit)) (P₁.input (stmt, wit)) := by
  unfold Prover.append
  dsimp only
  exact HEq.rfl

/-- Support lemma `prodMk_heq`: heterogeneous congruence for pairs whose component types vary. -/
theorem prodMk_heq {α α' β β' : Type _} {a : α} {a' : α'} {b : β} {b' : β'}
    (hα : α = α') (hβ : β = β') (ha : HEq a a') (hb : HEq b b') :
    HEq (Prod.mk a b) (Prod.mk a' b') := by
  subst hα hβ
  rw [eq_of_heq ha, eq_of_heq hb]

/-- Support lemma `pure_heq_pure`: heterogeneous congruence for `pure` in `OracleComp`, lifting a
HEq of values (over equal element types) to a HEq of the pure computations. -/
theorem pure_heq_pure {ι : Type} {spec : OracleSpec ι} {α α' : Type _} {a : α} {a' : α'}
    (hα : α = α') (ha : HEq a a') :
    HEq (pure a : OracleComp spec α) (pure a' : OracleComp spec α') := by
  subst hα
  rw [eq_of_heq ha]

/-- HEq congruence for `sendMessage`: equal message index and HEq state imply HEq results. -/
theorem sendMessage_heq_congr {P : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {idx₁ idx₂ : pSpec₁.MessageIdx} (hidx : idx₁ = idx₂)
    {s₁ : P.PrvState idx₁.1.castSucc} {s₂ : P.PrvState idx₂.1.castSucc} (hs : HEq s₁ s₂) :
    HEq (P.sendMessage idx₁ s₁) (P.sendMessage idx₂ s₂) := by
  subst hidx
  rw [eq_of_heq hs]

/-- HEq congruence for `receiveChallenge`: equal challenge index and HEq state imply HEq results. -/
theorem receiveChallenge_heq_congr {P : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {idx₁ idx₂ : pSpec₁.ChallengeIdx} (hidx : idx₁ = idx₂)
    {s₁ : P.PrvState idx₁.1.castSucc} {s₂ : P.PrvState idx₂.1.castSucc} (hs : HEq s₁ s₂) :
    HEq (P.receiveChallenge idx₁ s₁) (P.receiveChallenge idx₂ s₂) := by
  subst hidx
  rw [eq_of_heq hs]

/-- Split a HEq of pairs (over componentwise-equal types) into HEqs of the components. -/
theorem prod_heq_split {α α' β β' : Type _} (hα : α = α') (hβ : β = β')
    {a : α} {a' : α'} {b : β} {b' : β'} (h : HEq (Prod.mk a b) (Prod.mk a' b')) :
    HEq a a' ∧ HEq b b' := by
  subst hα hβ
  rw [heq_iff_eq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
  exact ⟨HEq.rfl, HEq.rfl⟩

/-- HEq congruence for monadic `bind` in `OracleComp` where the element types may differ
propositionally.  If the bound computations are HEq (over equal element types) and the
continuations send HEq inputs to HEq outputs, the binds are HEq. -/
theorem bind_heq_congr {ι : Type} {spec : OracleSpec ι} {α α' β β' : Type _}
    (hα : α = α') (hβ : β = β')
    {ma : OracleComp spec α} {ma' : OracleComp spec α'}
    {f : α → OracleComp spec β} {f' : α' → OracleComp spec β'}
    (hma : HEq ma ma') (hf : ∀ (a : α) (a' : α'), HEq a a' → HEq (f a) (f' a')) :
    HEq (ma >>= f) (ma' >>= f') := by
  subst hα hβ
  rw [eq_of_heq hma]
  have : f = f' := funext fun a => eq_of_heq (hf a a HEq.rfl)
  rw [this]

/-- HEq congruence for `OracleComp.liftComp` (along the canonical query-level `MonadLiftT`): HEq
inputs (over equal element types) give HEq lifts.  Unlike `liftM_heq_congr`, `liftComp` depends only
on the *query-level* `MonadLiftT (OracleQuery spec) (OracleQuery superSpec)`, which is canonical, so
this avoids the OracleComp-level `MonadLiftT` instance diamond. -/
theorem liftComp_heq_congr {ι ι' : Type} {spec : OracleSpec ι} {superSpec : OracleSpec ι'}
    [MonadLiftT (OracleQuery spec) (OracleQuery superSpec)] {α α' : Type}
    (hα : α = α') {ma : OracleComp spec α} {ma' : OracleComp spec α'} (hma : HEq ma ma') :
    HEq (OracleComp.liftComp ma superSpec) (OracleComp.liftComp ma' superSpec) := by
  subst hα
  rw [eq_of_heq hma]


/-- HEq congruence for `liftM` (along a fixed transitive `MonadLiftT` of `OracleComp`s): HEq inputs
(over equal element types) give HEq lifts. -/
theorem liftM_heq_congr {ι ι' : Type} {spec : OracleSpec ι} {superSpec : OracleSpec ι'}
    [MonadLiftT (OracleComp spec) (OracleComp superSpec)] {α α' : Type}
    (hα : α = α') {ma : OracleComp spec α} {ma' : OracleComp spec α'} (hma : HEq ma ma') :
    HEq (liftM ma : OracleComp superSpec α) (liftM ma' : OracleComp superSpec α') := by
  subst hα
  rw [eq_of_heq hma]

/-- HEq congruence: `liftM` (the `OracleQuery → OracleComp` embedding over the SAME spec) of HEq
queries (over equal response types) gives HEq computations. -/
theorem liftM_query_heq {ιs : Type} {spec : OracleSpec ιs} {α α' : Type}
    (hα : α = α') {q : OracleQuery spec α} {q' : OracleQuery spec α'} (hq : HEq q q') :
    HEq (liftM q : OracleComp spec α) (liftM q' : OracleComp spec α') := by
  subst hα; rw [eq_of_heq hq]

/-- HEq of two oracle queries over the same spec whose inputs agree and whose response types are
propositionally equal, with HEq continuations. -/
theorem oracleQuery_heq {ιs : Type} {spec : OracleSpec ιs} {α α' : Type}
    {t t' : spec.Domain} (ht : t = t')
    {f : spec.Range t → α} {f' : spec.Range t' → α'} (hα : α = α') (hf : HEq f f') :
    HEq (OracleQuery.mk t f) (OracleQuery.mk t' f') := by
  subst ht; subst hα; rw [eq_of_heq hf]

/-- **OracleComp-level lift-coherence.**  Lifting `mx : OracleComp spec` first through an
intermediate spec `midSpec` and then to `superSpec` agrees, as a *function*, with lifting it
directly to
`superSpec`, provided the two query-level `MonadLiftT`s cohere
(`OracleQuery.liftM_eq_liftM_liftM`, which is `rfl` for the canonical `+`/transitive instances).
Proved by induction on `mx`: the `query_bind` head reduces both sides to `q.cont <$> liftM (...)`
where the inner lifts coincide by `hquery`.

This is the bridge that defuses the `OracleComp`-level `MonadLiftT` instance diamond: the
*transitive* instance `instMonadLiftTOfMonadLift spec midSpec superSpec` lifts as
`liftComp (liftComp mx midSpec) superSpec`, while the *direct* instance lifts as
`liftComp mx superSpec`. -/
theorem liftComp_liftComp {ι₁ ι₂ ι₃ : Type} {spec : OracleSpec ι₁} {midSpec : OracleSpec ι₂}
    {superSpec : OracleSpec ι₃}
    [MonadLiftT (OracleQuery spec) (OracleQuery midSpec)]
    [MonadLiftT (OracleQuery midSpec) (OracleQuery superSpec)]
    [hsd : MonadLiftT (OracleQuery spec) (OracleQuery superSpec)]
    (hquery : ∀ (t : spec.Domain),
      OracleComp.liftComp
          (liftM (spec.query t) : OracleComp midSpec (spec.Range t)) superSpec
        = (liftM (spec.query t) : OracleComp superSpec (spec.Range t)))
    {α : Type} (mx : OracleComp spec α) :
    OracleComp.liftComp (OracleComp.liftComp mx midSpec) superSpec
      = OracleComp.liftComp mx superSpec := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    -- Distribute both `liftComp`s through the outer bind; the tails match by `ih`.
    rw [OracleComp.liftComp_bind, OracleComp.liftComp_bind, OracleComp.liftComp_bind]
    rw [show (fun x => OracleComp.liftComp (OracleComp.liftComp (k x) midSpec) superSpec)
          = (fun x => OracleComp.liftComp (k x) superSpec) from funext ih]
    -- Reduce the (single-query) head on both sides; the inner lift coheres by `hquery`.
    congr 1
    rw [OracleComp.liftComp_query, OracleComp.liftComp_map]
    simp only [OracleQuery.cont_query, id_map, OracleQuery.input_query]
    rw [hquery t, OracleComp.liftComp_query]
    simp only [OracleQuery.cont_query, id_map, OracleQuery.input_query]

/-- **Diamond collapse for nested `liftM` over `OracleComp`.**  Two composed lifts
`spec → midSpec → superSpec` collapse to the single direct lift (expressed as `liftComp X
superSpec`), given the per-query coherence `hco` (`fun _ => rfl` for the canonical `+`
oracle-spec injections).  This discharges the "multiple coercion paths for the same lifted
computation" obstruction: a goal term `liftM (liftM X)` — e.g. from unfolding `Prover.run`'s
internal output lift, or a Fiat-Shamir empty-challenge-layer embedding — rewrites to the direct
`liftComp X superSpec`, matching a single-lifted occurrence (which is `liftComp X superSpec` by
`liftComp_eq_liftM`).  Proven by converting both `liftM`s to `liftComp` and applying
`liftComp_liftComp`. -/
theorem liftM_liftM_via_comp {ιs ιm ιp : Type} {spec : OracleSpec ιs} {midSpec : OracleSpec ιm}
    {superSpec : OracleSpec ιp}
    [MonadLift (OracleQuery spec) (OracleQuery midSpec)]
    [MonadLift (OracleQuery midSpec) (OracleQuery superSpec)]
    [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    {α : Type} (X : OracleComp spec α)
    (hco : ∀ t, OracleComp.liftComp
        (liftM (spec.query t) : OracleComp midSpec (spec.Range t)) superSpec
      = (liftM (spec.query t) : OracleComp superSpec (spec.Range t))) :
    (liftM (liftM X : OracleComp midSpec α) : OracleComp superSpec α)
      = OracleComp.liftComp X superSpec := by
  rw [show (liftM X : OracleComp midSpec α) = OracleComp.liftComp X midSpec
      from (liftComp_eq_liftM X).symm]
  rw [show (liftM (OracleComp.liftComp X midSpec) : OracleComp superSpec α)
      = OracleComp.liftComp (OracleComp.liftComp X midSpec) superSpec
      from (liftComp_eq_liftM _).symm]
  exact liftComp_liftComp hco X



/-- Collapse the transitive `liftM` path that lifts an `oSpec` computation through the left
challenge layer before the appended challenge layer.  This is the instance shape produced by
`liftM_bind` after splitting the seam `P₁.output >>= P₂.sendMessage` block, while
the right-block round normalizers use the direct `liftComp` path. -/
theorem liftM_via_leftChallenge_eq_liftComp
    {α : Type} (X : OracleComp oSpec α) :
    (@liftM (OracleComp oSpec)
        (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
        (instMonadLiftTOfMonadLift (OracleComp oSpec) (OracleComp (oSpec + [pSpec₁.Challenge]ₒ))
          (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)))
        α X)
      = OracleComp.liftComp X (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) := by
  change (liftM (liftM X : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) α) :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)
    = OracleComp.liftComp X (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
  exact liftM_liftM_via_comp (spec := oSpec) (midSpec := oSpec + [pSpec₁.Challenge]ₒ)
    (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) X (fun _ => rfl)


/-- `processRound` resolved at a message (`P_to_V`) round (mirror of the library's
`processRound_challenge`). -/
theorem processRound_message {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
    {N : ℕ} {pSpec : ProtocolSpec N}
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (j : Fin N)
    (hDir : pSpec.dir j = .P_to_V)
    (currentResult : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × prover.PrvState j.castSucc)) :
    prover.processRound j currentResult = (do
      let ⟨transcript, state⟩ ← currentResult
      let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
      return ⟨transcript.concat msg, newState⟩) := by
  rw [Prover.processRound_def]
  apply bind_congr
  rintro ⟨transcript, state⟩
  dsimp only
  split <;> rename_i hDir'
  · exact absurd (hDir.symm.trans hDir') (by decide)
  · rfl

/-- Generic HEq congruence for `Fin.snoc` over dependent codomain families.  If the lengths agree,
the codomain families are HEq, the tuples are HEq and the appended elements are HEq, the two snocs
are HEq. -/
theorem Fin_snoc_heq {N N' : ℕ} (hN : N = N')
    {β : Fin (N + 1) → Type _} {β' : Fin (N' + 1) → Type _} (hβ : HEq β β')
    {T : (j : Fin N) → β j.castSucc} {T' : (j : Fin N') → β' j.castSucc} (hT : HEq T T')
    {x : β (Fin.last N)} {x' : β' (Fin.last N')} (hx : HEq x x') :
    HEq (Fin.snoc T x) (Fin.snoc T' x') := by
  subst hN
  obtain rfl : β = β' := eq_of_heq hβ
  rw [eq_of_heq hT, eq_of_heq hx]

/-- Dependent function-application HEq congruence: HEq functions (over equal domain and HEq
codomain families) applied to HEq arguments give HEq results. -/
theorem heq_app {α α' : Type _} {β : α → Type _} {β' : α' → Type _}
    (hα : α = α') (hβ : HEq β β')
    {f : (a : α) → β a} {g : (a : α') → β' a} (hfg : HEq f g)
    {a : α} {a' : α'} (haa : HEq a a') :
    HEq (f a) (g a') := by
  subst hα
  obtain rfl : β = β' := eq_of_heq hβ
  rw [eq_of_heq hfg, eq_of_heq haa]

/-- The appended-protocol message type at a left round equals `pSpec₁`'s. -/
theorem append_Message_castLE (i : Fin m)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (i.castLE (by omega)) = .P_to_V) (hDir₁ : pSpec₁.dir i = .P_to_V) :
    (pSpec₁ ++ₚ pSpec₂).Message ⟨i.castLE (by omega), hDir⟩ = pSpec₁.Message ⟨i, hDir₁⟩ := by
  show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (i.castLE (by omega)) = pSpec₁.«Type» i
  rw [Fin.vappend_eq_append,
    show (i.castLE (show m ≤ m + n by omega)) = Fin.castAdd n i from by ext; simp, Fin.append_left]

/-- HEq congruence for `Transcript.concat` across left-round transcripts of the appended and the
`pSpec₁` protocols.  `Transcript.concat = Fin.snoc`; compared as dependent functions on
`Fin (·.succ)`
via `Function.hfunext`, splitting each index into the appended `msg` (last) or an interior entry
read from the transcript. -/
theorem concat_heq (i : Fin m)
    {t : (pSpec₁ ++ₚ pSpec₂).Transcript (i.castLE (by omega)).castSucc}
    {t' : pSpec₁.Transcript i.castSucc}
    {msg : (pSpec₁ ++ₚ pSpec₂).«Type» (i.castLE (by omega))} {msg' : pSpec₁.«Type» i}
    (ht : HEq t t') (hm : HEq msg msg') :
    HEq (Transcript.concat msg t) (Transcript.concat msg' t') := by
  unfold Transcript.concat
  have hlenC : (↑(i.castLE (show m ≤ m + n by omega)).castSucc : ℕ) = ↑i.castSucc := by simp
  -- The two `Fin.snoc`s differ only in (equal) length, (HEq) codomain family, tuple and element.
  refine Fin_snoc_heq hlenC ?_ ht ?_
  · -- codomain families agree: for `j < m`, the appended `«Type»` coincides with `pSpec₁`'s.
    have hsucc : (↑(i.castLE (show m ≤ m + n by omega)).succ : ℕ) = ↑i.succ := by simp
    apply Function.hfunext (by congr 1)
    intro b b' hbb
    have hbv : (b : ℕ) = (b' : ℕ) :=
      Fin.heq_ext_iff hsucc |>.mp hbb
    apply heq_of_eq
    show (pSpec₁ ++ₚ pSpec₂).«Type» _ = pSpec₁.«Type» _
    -- Both indices have value `< m` (or, for the last, `= m`), but only `< m` codomain entries
    -- are read; in all cases the appended `«Type»` at a left index equals `pSpec₁`'s.
    rcases lt_or_eq_of_le (show (↑b : ℕ) ≤ m by
        have := b.isLt; simp only [Fin.val_succ] at this; omega) with hbm | hbm
    · rw [show (Fin.castLE (by omega) b : Fin (m + n)) = Fin.castAdd n ⟨b, hbm⟩ from by ext; simp]
      show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (Fin.castAdd n _) = _
      rw [Fin.vappend_eq_append, Fin.append_left]
      congr 1
      ext; simpa using hbv
    · -- `b = m` only when `b` is the last index of the snoc domain; the families still agree there
      -- because both sides evaluate the message type, equal by `append_Message_castLE`.
      exfalso
      have := b.isLt
      simp only [Fin.val_succ, Fin.val_castSucc] at this
      omega
  · -- the appended message ≍ `pSpec₁`'s message (`hm`).
    exact hm

/-- The appended protocol's direction at a left-half round matches `pSpec₁`'s. -/
theorem append_dir_castLE (i : Fin m) :
    (pSpec₁ ++ₚ pSpec₂).dir (i.castLE (by omega)) = pSpec₁.dir i := by
  show Fin.vappend pSpec₁.dir pSpec₂.dir (i.castLE (by omega)) = pSpec₁.dir i
  rw [Fin.vappend_eq_append,
    show (i.castLE (show m ≤ m + n by omega)) = Fin.castAdd n i from by ext; simp, Fin.append_left]

variable {P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}

/-- State-type equality used to transport the appended prover's state into `P₁`'s state at the
`castSucc` of a left round. -/
theorem append_PrvState_castSucc (i : Fin m) :
    (P₁.append P₂).PrvState (i.castLE (by omega)).castSucc = P₁.PrvState i.castSucc := by
  rw [show (i.castLE (by omega)).castSucc = (i.castSucc).castLE (by omega) from by ext; simp,
    append_PrvState_castLE i.castSucc]

/-- State-type equality at the `succ` of a left round. -/
theorem append_PrvState_succ (i : Fin m) :
    (P₁.append P₂).PrvState (i.castLE (by omega)).succ = P₁.PrvState i.succ := by
  rw [show (i.castLE (by omega)).succ = (i.succ).castLE (by omega) from by ext; simp,
    append_PrvState_castLE i.succ]

/-- Transcript-type equality at the `castSucc` of a left round. -/
theorem append_Transcript_castSucc (i : Fin m) :
    (pSpec₁ ++ₚ pSpec₂).Transcript (i.castLE (by omega)).castSucc = pSpec₁.Transcript i.castSucc := by
  rw [show (i.castLE (by omega)).castSucc = (i.castSucc).castLE (by omega) from by ext; simp]
  exact append_Transcript_castLE i.castSucc

/-- Transcript-type equality at the `succ` of a left round. -/
theorem append_Transcript_succ (i : Fin m) :
    (pSpec₁ ++ₚ pSpec₂).Transcript (i.castLE (by omega)).succ = pSpec₁.Transcript i.succ := by
  rw [show (i.castLE (by omega)).succ = (i.succ).castLE (by omega) from by ext; simp]
  exact append_Transcript_castLE i.succ

/-- **Left-round `sendMessage` reduction.**  The appended prover's `sendMessage` at a left round
`i < m` reduces (heterogeneously) to `P₁`'s `sendMessage`. -/
theorem append_sendMessage_left (i : Fin m)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (i.castLE (by omega)) = .P_to_V)
    (hDir₁ : pSpec₁.dir i = .P_to_V)
    (state : (P₁.append P₂).PrvState (i.castLE (by omega)).castSucc) :
    HEq ((P₁.append P₂).sendMessage ⟨i.castLE (by omega), hDir⟩ state)
        (P₁.sendMessage ⟨i, hDir₁⟩ (cast (append_PrvState_castSucc i) state)) := by
  unfold Prover.append
  dsimp only [Fin.vappend_eq_append]
  have hlt : (↑(i.castLE (show m ≤ m + n by omega)) : ℕ) < m := by simp
  erw [id_eq, dite_eq_left hlt]
  have hidxeq : (⟨⟨↑(i.castLE (show m ≤ m + n by omega)), hlt⟩, by exact hDir₁⟩
      : pSpec₁.MessageIdx) = ⟨i, hDir₁⟩ := by ext; simp
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  apply HEq.trans (cast_heq _ _)
  exact sendMessage_heq_congr hidxeq ((cast_heq _ _).trans (cast_heq _ _).symm)

/-- **Left-round `receiveChallenge` reduction.**  The appended prover's `receiveChallenge` at a
left round `i < m` reduces (heterogeneously) to `P₁`'s `receiveChallenge`. -/
theorem append_receiveChallenge_left (i : Fin m)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (i.castLE (by omega)) = .V_to_P)
    (hDir₁ : pSpec₁.dir i = .V_to_P)
    (state : (P₁.append P₂).PrvState (i.castLE (by omega)).castSucc) :
    HEq ((P₁.append P₂).receiveChallenge ⟨i.castLE (by omega), hDir⟩ state)
        (P₁.receiveChallenge ⟨i, hDir₁⟩ (cast (append_PrvState_castSucc i) state)) := by
  unfold Prover.append
  dsimp only [Fin.vappend_eq_append]
  have hlt : (↑(i.castLE (show m ≤ m + n by omega)) : ℕ) < m := by simp
  rw [dif_pos hlt]
  have hidxeq : (⟨⟨↑(i.castLE (show m ≤ m + n by omega)), hlt⟩, by exact hDir₁⟩
      : pSpec₁.ChallengeIdx) = ⟨i, hDir₁⟩ := by ext; simp
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  apply HEq.trans (cast_heq _ _)
  exact receiveChallenge_heq_congr hidxeq ((cast_heq _ _).trans (cast_heq _ _).symm)

/-- **Left-round `getChallenge` reduction.**  The appended protocol's `getChallenge` at a left
challenge round `i < m` is heterogeneously equal to the `liftM` (along the left challenge `SubSpec`
`[pSpec₁.Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ`) of `pSpec₁`'s `getChallenge`.  The two
single queries coincide on the (value-equal) challenge index `i.castLE = ChallengeIdx.inl ⟨i,_⟩`;
the response types differ only by the propositional `range_challenge_append_inl` transport carried
by the SubSpec `onResponse`, so the queries are HEq. -/
theorem append_getChallenge_left (i : Fin m)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (i.castLE (by omega)) = .V_to_P)
    (hDir₁ : pSpec₁.dir i = .V_to_P) :
    HEq ((pSpec₁ ++ₚ pSpec₂).getChallenge ⟨i.castLE (by omega), hDir⟩)
        (liftM (pSpec₁.getChallenge ⟨i, hDir₁⟩) :
          OracleComp [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ _) := by
  unfold ProtocolSpec.getChallenge
  have hChalEq : (pSpec₁ ++ₚ pSpec₂).Challenge ⟨i.castLE (by omega), hDir⟩
      = pSpec₁.Challenge ⟨i, hDir₁⟩ := by
    show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (i.castLE (by omega)) = pSpec₁.«Type» i
    rw [Fin.vappend_eq_append,
      show (i.castLE (show m ≤ m + n by omega)) = Fin.castAdd n i from by ext; simp, Fin.append_left]
  show HEq (liftM (OracleSpec.query (spec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        ⟨⟨i.castLE (by omega), hDir⟩, ()⟩))
      (liftM (OracleSpec.query (spec := [pSpec₁.Challenge]ₒ) ⟨⟨i, hDir₁⟩, ()⟩) :
        OracleComp [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ _)
  -- Make the OracleQuery-level lift explicit so both sides are `liftM (· : OracleQuery superSpec)`.
  rw [show (liftM (OracleSpec.query (spec := [pSpec₁.Challenge]ₒ) ⟨⟨i, hDir₁⟩, ()⟩) :
          OracleComp [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ _)
        = liftM (liftM (OracleSpec.query (spec := [pSpec₁.Challenge]ₒ) ⟨⟨i, hDir₁⟩, ()⟩)
            : OracleQuery [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ _) from rfl]
  refine liftM_query_heq hChalEq ?_
  rw [OracleSpec.query_def]
  show HEq (OracleQuery.mk (spec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) ⟨⟨i.castLE (by omega), hDir⟩, ()⟩ id)
      (MonadLift.monadLift (OracleSpec.query (spec := [pSpec₁.Challenge]ₒ) ⟨⟨i, hDir₁⟩, ()⟩))
  rw [SubSpec.liftM_eq_lift]
  refine oracleQuery_heq ?_ hChalEq ?_
  · -- inputs agree: `⟨i.castLE, hDir⟩ = onQuery ⟨i,hDir₁⟩ = ⟨ChallengeIdx.inl ⟨i,hDir₁⟩, ()⟩`.
    show (⟨⟨i.castLE (by omega), hDir⟩, ()⟩ : [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.Domain)
      = ⟨ChallengeIdx.inl ⟨i, hDir₁⟩, ()⟩
    congr 1
  · -- continuations: `id ≍ onResponse ⟨i,hDir₁⟩`, which is the `range_challenge_append_inl`
    -- transport.
    simp only [OracleQuery.cont_query, OracleQuery.input_query, Function.id_comp]
    have hdom : [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.Range ⟨⟨i.castLE (by omega), hDir⟩, ()⟩
        = [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.Range
            ((inferInstance : [(pSpec₁).Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).onQuery
              ⟨⟨i, hDir₁⟩, ()⟩) := by
      show (pSpec₁ ++ₚ pSpec₂).Challenge ⟨i.castLE (by omega), hDir⟩
        = (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl ⟨i, hDir₁⟩)
      congr 1
    refine Function.hfunext hdom (fun a a' haa => ?_)
    refine haa.trans ?_
    -- `a' ≍ onResponse ⟨i,hDir₁⟩ a'`; `onResponse` is a type-level `▸` (= `cast`) transport.
    dsimp only [SubSpec.onResponse]
    refine HEq.symm ?_
    generalize_proofs h
    exact cast_heq h a'

/-- `processRound` resolved at a challenge (`V_to_P`) round (mirror of `processRound_message`). -/
theorem processRound_challenge' {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} {N : ℕ} {pSpec : ProtocolSpec N}
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (j : Fin N)
    (hDir : pSpec.dir j = .V_to_P)
    (currentResult : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × prover.PrvState j.castSucc)) :
    prover.processRound j currentResult = (do
      let ⟨transcript, state⟩ ← currentResult
      let challenge ← pSpec.getChallenge ⟨j, hDir⟩
      letI newState := (← prover.receiveChallenge ⟨j, hDir⟩ state) challenge
      return ⟨transcript.concat challenge, newState⟩) := by
  rw [Prover.processRound_def]
  apply bind_congr
  rintro ⟨transcript, state⟩
  dsimp only
  split <;> rename_i hDir'
  · rfl
  · exact absurd (hDir.symm.trans hDir') (by decide)

/-- **Left-round `processRound` compatibility (message branch).**  Working scratch lemma to inspect
the message-round goal shape. -/
theorem append_processRound_left_message (i : Fin m) (hDir₁ : pSpec₁.dir i = .P_to_V)
    (curA : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      ((pSpec₁ ++ₚ pSpec₂).Transcript (i.castLE (by omega)).castSucc
        × (P₁.append P₂).PrvState (i.castLE (by omega)).castSucc))
    (cur₁ : OracleComp (oSpec + [pSpec₁.Challenge]ₒ)
      (pSpec₁.Transcript i.castSucc × P₁.PrvState i.castSucc))
    (hcur : HEq curA (liftAppendLeft pSpec₂ cur₁ :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)) :
    HEq ((P₁.append P₂).processRound (i.castLE (by omega)) curA)
      (liftAppendLeft pSpec₂ (P₁.processRound i cur₁) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := by
  have hDir : (pSpec₁ ++ₚ pSpec₂).dir (i.castLE (by omega)) = .P_to_V := by
    rw [append_dir_castLE]; exact hDir₁
  rw [processRound_message (P₁.append P₂) (i.castLE (by omega)) hDir curA,
    processRound_message P₁ i hDir₁ cur₁]
  -- Push the outer `liftM` through the RHS `do`-block (keep binds explicit, no `map` rewrite).
  simp only [liftM_bind, liftM_pure]
  -- Outer bind over the (HEq) input results.
  refine bind_heq_congr
    (by rw [append_Transcript_castSucc i, append_PrvState_castSucc i])
    (by rw [append_Transcript_succ i, append_PrvState_succ i]) hcur ?_
  rintro ⟨t, s⟩ ⟨t', s'⟩ hr
  obtain ⟨ht, hs⟩ := prod_heq_split (append_Transcript_castSucc i) (append_PrvState_castSucc i) hr
  dsimp only
  -- Collapse the double `liftM` on the RHS (composition of lifts oSpec → appended spec).
  have hcollapse : (liftM (liftM (P₁.sendMessage ⟨i, hDir₁⟩ s') :
        OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
      = liftM (P₁.sendMessage ⟨i, hDir₁⟩ s' : OracleComp oSpec _) := by
    simpa only [liftComp_eq_liftM] using
      (liftM_liftM_via_comp (spec := oSpec) (midSpec := oSpec + [pSpec₁.Challenge]ₒ)
        (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _ (fun _ => rfl))
  erw [hcollapse]
  -- Normalize the RHS continuation `liftM (pure _) = pure _`.
  simp only [liftM_pure]
  -- Bind over the (HEq) `sendMessage` computations, then `pure (concat, newState)`.
  apply bind_heq_congr (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
    (β := (pSpec₁ ++ₚ pSpec₂).Transcript (i.castLE (by omega)).succ
      × (P₁.append P₂).PrvState (i.castLE (by omega)).succ)
    (β' := pSpec₁.Transcript i.succ × P₁.PrvState i.succ)
    (α := (pSpec₁ ++ₚ pSpec₂).Message ⟨i.castLE (by omega), hDir⟩
      × (P₁.append P₂).PrvState (i.castLE (by omega)).succ)
    (α' := pSpec₁.Message ⟨i, hDir₁⟩ × P₁.PrvState i.succ)
    (by rw [append_Message_castLE i hDir hDir₁, append_PrvState_succ i])
    (by rw [append_Transcript_succ i, append_PrvState_succ i])
  · -- `sendMessage` HEq (lifted): both sides are oSpec→S lifts (direct vs transitive, defeq) of
    -- HEq-equal `sendMessage` computations (`append_sendMessage_left` + `s ≍ s'`).
    have hαeq : ((pSpec₁ ++ₚ pSpec₂).Message ⟨i.castLE (by omega), hDir⟩
          × (P₁.append P₂).PrvState (i.castLE (by omega)).succ)
        = (pSpec₁.Message ⟨i, hDir₁⟩ × P₁.PrvState i.succ) := by
      rw [append_Message_castLE i hDir hDir₁, append_PrvState_succ i]
    have hbase : HEq ((P₁.append P₂).sendMessage ⟨i.castLE (by omega), hDir⟩ s)
        (P₁.sendMessage ⟨i, hDir₁⟩ s') :=
      (append_sendMessage_left i hDir hDir₁ s).trans
        (sendMessage_heq_congr rfl ((cast_heq _ _).trans hs))
    -- Lift the base `sendMessage` HEq (`hbase`) through the lift to `S`.
    --
    -- The goal's two `liftM`s both lift `OracleComp oSpec → S`, but via DIFFERENT `MonadLiftT`
    -- instances: the goal's RHS (`liftM_bind`-pushed `P₁.processRound` side) uses the *transitive*
    -- instance `instMonadLiftTOfMonadLift oSpec (oSpec + [pSpec₁.Challenge]ₒ) S`, whereas the
    -- appended-prover side and `liftM_heq_congr` use the *direct* instance
    -- `instMonadLiftTOfMonadLift oSpec oSpec S`.  These two `monadLift`s are EQUAL as functions
    -- (`liftComp_liftComp`: the transitive lift `liftComp (liftComp · mid) super` equals the direct
    -- `liftComp · super`, the single-query coherence being `rfl` for the canonical `+` instances),
    -- but they are NOT defeq at the `OracleComp` structure level.  We bridge them via
    -- `liftComp_liftComp` and then apply `liftM_heq_congr` on the (common) direct instance.
    -- The goal is `liftM (appended.sendMessage ..) ≍ liftM (P₁.sendMessage ..)`, where the LHS
    -- lifts `OracleComp oSpec → S` via the DIRECT instance and the RHS via the TRANSITIVE instance
    -- `oSpec → oSpec+[pSpec₁.Challenge]ₒ → S`.  Definitionally the transitive RHS unfolds to the
    -- nested `liftComp (liftComp (P₁.sendMessage ..) (oSpec+[pSpec₁.Challenge]ₒ)) S`; expose that
    -- via
    -- `show`, collapse it to the direct `liftComp (P₁.sendMessage ..) S` via `liftComp_liftComp`,
    -- and likewise expose the LHS as the direct `liftComp (appended.sendMessage ..) S`.
    exact liftM_heq_congr (spec := oSpec)
      (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) hαeq hbase
  · rintro ⟨msg, ns⟩ ⟨msg', ns'⟩ hmsg
    refine pure_heq_pure (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      (by rw [append_Transcript_succ i, append_PrvState_succ i]) ?_
    obtain ⟨hm, hns⟩ :=
      prod_heq_split (append_Message_castLE i hDir hDir₁) (append_PrvState_succ i) hmsg
    refine prodMk_heq (append_Transcript_succ i) (append_PrvState_succ i) ?_ hns
    -- `Transcript.concat msg t ≍ Transcript.concat msg' t'`
    exact concat_heq i ht hm

/-- **Left-round `processRound` compatibility (challenge branch).**  The `V_to_P` analogue of
`append_processRound_left_message`: at a left challenge round `i < m`, the appended prover's
`processRound` (heterogeneously) equals the `liftM` of `P₁`'s, assuming the run-up-to inputs are
HEq.  Mirrors the message branch, with `getChallenge` (`append_getChallenge_left`) and
`receiveChallenge` (`append_receiveChallenge_left`) in place of `sendMessage`, plus the extra
function-application of the `receiveChallenge` result to the sampled challenge. -/
theorem append_processRound_left_challenge (i : Fin m) (hDir₁ : pSpec₁.dir i = .V_to_P)
    (curA : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      ((pSpec₁ ++ₚ pSpec₂).Transcript (i.castLE (by omega)).castSucc
        × (P₁.append P₂).PrvState (i.castLE (by omega)).castSucc))
    (cur₁ : OracleComp (oSpec + [pSpec₁.Challenge]ₒ)
      (pSpec₁.Transcript i.castSucc × P₁.PrvState i.castSucc))
    (hcur : HEq curA (liftAppendLeft pSpec₂ cur₁ :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)) :
    HEq ((P₁.append P₂).processRound (i.castLE (by omega)) curA)
      (liftAppendLeft pSpec₂ (P₁.processRound i cur₁) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := by
  have hDir : (pSpec₁ ++ₚ pSpec₂).dir (i.castLE (by omega)) = .V_to_P := by
    rw [append_dir_castLE]; exact hDir₁
  rw [processRound_challenge' (P₁.append P₂) (i.castLE (by omega)) hDir curA,
    processRound_challenge' P₁ i hDir₁ cur₁]
  simp only [liftM_bind, liftM_pure]
  refine bind_heq_congr
    (by rw [append_Transcript_castSucc i, append_PrvState_castSucc i])
    (by rw [append_Transcript_succ i, append_PrvState_succ i]) hcur ?_
  rintro ⟨t, s⟩ ⟨t', s'⟩ hr
  obtain ⟨ht, hs⟩ := prod_heq_split (append_Transcript_castSucc i) (append_PrvState_castSucc i) hr
  dsimp only
  -- Collapse the RHS double-lifts (oSpec'-level transitive ⇒ direct) of the challenge-oracle
  -- computations.  Here both `getChallenge` and `receiveChallenge` already live in the appended
  -- challenge oracle on the RHS after the inner `liftM`; the outer `liftM` to the full spec is the
  -- challenge `SubSpec` lift, common to both sides.
  -- Challenge value type equality.
  have hChalEq : (pSpec₁ ++ₚ pSpec₂).Challenge ⟨i.castLE (by omega), hDir⟩
      = pSpec₁.Challenge ⟨i, hDir₁⟩ := by
    show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (i.castLE (by omega)) = pSpec₁.«Type» i
    rw [Fin.vappend_eq_append,
      show (i.castLE (show m ≤ m + n by omega)) = Fin.castAdd n i from by ext; simp, Fin.append_left]
  -- Bind over the (HEq) `getChallenge` computations.
  refine bind_heq_congr (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
    hChalEq
    (by rw [append_Transcript_succ i, append_PrvState_succ i]) ?_ ?_
  · -- `getChallenge` HEq, lifted to the full spec.  Both sides lift the appended challenge oracle
    -- `[(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ` into the full spec via the same `+`-right `SubSpec`; the
    -- underlying `getChallenge` HEq is `append_getChallenge_left`.
    exact liftM_heq_congr (spec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) hChalEq
      (append_getChallenge_left i hDir hDir₁)
  · -- continuation: bind over `receiveChallenge`, then `pure (concat, f challenge)`.
    rintro chalA chal₁ hchal
    -- Collapse the RHS double-lift of `receiveChallenge` (transitive oSpec→S ⇒ direct).
    have hcollapse : (liftM (liftM (P₁.receiveChallenge ⟨i, hDir₁⟩ s') :
          OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
        = liftM (P₁.receiveChallenge ⟨i, hDir₁⟩ s' : OracleComp oSpec _) := by
      simpa only [liftComp_eq_liftM] using
        (liftM_liftM_via_comp (spec := oSpec) (midSpec := oSpec + [pSpec₁.Challenge]ₒ)
          (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _ (fun _ => rfl))
    erw [hcollapse]
    -- `receiveChallenge` returns `Challenge → State`; the bind result `f` is applied to the
    -- challenge.  HEq of the receiveChallenge computations:
    have hrecvBase : HEq ((P₁.append P₂).receiveChallenge ⟨i.castLE (by omega), hDir⟩ s)
        (P₁.receiveChallenge ⟨i, hDir₁⟩ s') :=
      (append_receiveChallenge_left i hDir hDir₁ s).trans
        (receiveChallenge_heq_congr rfl ((cast_heq _ _).trans hs))
    refine bind_heq_congr (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      (α := (pSpec₁ ++ₚ pSpec₂).Challenge ⟨i.castLE (by omega), hDir⟩
        → (P₁.append P₂).PrvState (i.castLE (by omega)).succ)
      (α' := pSpec₁.Challenge ⟨i, hDir₁⟩ → P₁.PrvState i.succ)
      (β := (pSpec₁ ++ₚ pSpec₂).Transcript (i.castLE (by omega)).succ
        × (P₁.append P₂).PrvState (i.castLE (by omega)).succ)
      (β' := pSpec₁.Transcript i.succ × P₁.PrvState i.succ)
      (by rw [hChalEq, append_PrvState_succ i])
      (by rw [append_Transcript_succ i, append_PrvState_succ i]) ?_ ?_
    · -- lifted `receiveChallenge` HEq, transitive RHS ⇒ direct via `liftComp_liftComp`.
      have hαeq : ((pSpec₁ ++ₚ pSpec₂).Challenge ⟨i.castLE (by omega), hDir⟩
            → (P₁.append P₂).PrvState (i.castLE (by omega)).succ)
          = (pSpec₁.Challenge ⟨i, hDir₁⟩ → P₁.PrvState i.succ) := by
        rw [hChalEq, append_PrvState_succ i]
      exact liftM_heq_congr (spec := oSpec)
        (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) hαeq hrecvBase
    · -- `pure (concat chal t, f chal)`: concat + function-application HEq.
      rintro fA f₁ hf
      refine pure_heq_pure (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        (by rw [append_Transcript_succ i, append_PrvState_succ i]) ?_
      refine prodMk_heq (append_Transcript_succ i) (append_PrvState_succ i) ?_ ?_
      · -- `concat chalA t ≍ concat chal₁ t'`
        exact concat_heq i ht hchal
      · -- `fA chalA ≍ f₁ chal₁`: application of HEq (non-dependent) functions to HEq arguments.
        refine heq_app hChalEq ?_ hf hchal
        -- codomain families are the constant `fun _ => PrvState succ`; HEq via the state equality.
        rw [hChalEq, append_PrvState_succ i]

/-- **The corrected well-founded `append_runToRound_left`.**  Running the appended prover up to a
left-half round `j ≤ m` (embedded as `j.castLE` into `Fin (m + n + 1)`) is heterogeneously equal to
the `liftM` (along the left challenge `SubSpec`) of running `P₁` up to round `j`. -/
theorem append_runToRound_left (j : Fin (m + 1)) :
    HEq ((P₁.append P₂).runToRound (j.castLE (by omega)) stmt wit)
      (liftAppendLeft pSpec₂ (P₁.runToRound j stmt wit) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := by
  induction j using Fin.induction with
  | zero =>
    rw [show ((0 : Fin (m + 1)).castLE (by omega) : Fin (m + n + 1)) = 0 from by ext; simp]
    rw [Prover.runToRound_zero_of_prover_first, Prover.runToRound_zero_of_prover_first]
    simp only [liftAppendLeft, liftM_pure]
    have hT : Transcript 0 (pSpec₁ ++ₚ pSpec₂) = Transcript 0 pSpec₁ := by
      unfold ProtocolSpec.Transcript ProtocolSpec.FullTranscript
      apply pi_congr; intro i; exact absurd i.isLt (by simp)
    have hS : (P₁.append P₂).PrvState 0 = P₁.PrvState 0 := append_PrvState_castLE 0
    apply pure_heq_pure
    · rw [hT, hS]
    · apply prodMk_heq
      · exact hT
      · exact hS
      · exact Subsingleton.helim hT _ _
      · exact append_input_heq
  | succ i ih =>
    -- Express the left-embedded successor index as a successor in `Fin (m + n)`.
    have hidx : ((i.succ).castLE (show m + 1 ≤ m + n + 1 by omega) : Fin (m + n + 1))
        = (i.castLE (show m ≤ m + n by omega)).succ := by ext; simp
    rw [hidx, Prover.runToRound_succ]
    rw [Prover.runToRound_succ]
    -- Goal: `processRound (i.castLE) appended (runToRound (i.castLE).castSucc appended)
    --        ≍ liftM (processRound i P₁ (runToRound i.castSucc P₁))`.
    -- `ih` carries the run up to the seam-predecessor round:
    -- `runToRound (i.castSucc.castLE) appended
    --   ≍ liftM (runToRound i.castSucc P₁)`.  Normalize its index to `(i.castLE).castSucc`.
    have hcur : HEq ((P₁.append P₂).runToRound (i.castLE (by omega)).castSucc stmt wit)
        (liftAppendLeft pSpec₂ (P₁.runToRound i.castSucc stmt wit) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := by
      have hcastSucc : (i.castSucc.castLE (show m + 1 ≤ m + n + 1 by omega) : Fin (m + n + 1))
          = (i.castLE (show m ≤ m + n by omega)).castSucc := by ext; simp
      rw [← hcastSucc]; exact ih
    -- Case-split on the direction of the left round `i`.
    cases hd : pSpec₁.dir i with
    | V_to_P => ?_
    | P_to_V => ?_
    · -- `V_to_P` (challenge round): close via the proven challenge-branch lemma.
      exact append_processRound_left_challenge i hd
        ((P₁.append P₂).runToRound (i.castLE (by omega)).castSucc stmt wit)
        (P₁.runToRound i.castSucc stmt wit) hcur
    · -- `P_to_V` (message round): close directly via the proven message-branch lemma.
      exact append_processRound_left_message i hd
        ((P₁.append P₂).runToRound (i.castLE (by omega)).castSucc stmt wit)
        (P₁.runToRound i.castSucc stmt wit) hcur

/-- **Seam specialization of `append_runToRound_left`.**  Running the appended prover up to the
*seam* round `m` (the last round of `pSpec₁`, embedded as `(Fin.last m).castLE` into the appended
protocol) is heterogeneously equal to the `liftM` of running `P₁` to its last round — i.e. the full
honest run of `P₁`'s message phase.  This is the entry point for assembling `Prover.append_run`:
after the seam, the continuation runs `P₂` (rounds `m+1 .. m+n`) starting from `P₁.output`-fed
`P₂.input`. -/
theorem append_runToRound_seam :
    HEq ((P₁.append P₂).runToRound ((Fin.last m).castLE (by omega)) stmt wit)
      (liftAppendLeft pSpec₂ (P₁.runToRound (Fin.last m) stmt wit) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) :=
  append_runToRound_left (Fin.last m)

/-! ### Right-block run characterization support (in progress)

The right block mirrors the left, but the appended prover's right half is indexed through
`Fin.natAdd (m + 1)` (interior rounds `m+1 .. m+n`) and—crucially—the **seam round** `m`
(`Prover.append`'s `i = m` branch) is *not* a uniform right round: it threads
`P₁.output >>= P₂.input`
before `P₂`'s round-`0` step.  We record here the proven right-half state transport; the remaining
right reductions and the seam-merge lemma are the documented obstruction of `append_run`. -/

/-- PrvState of the appended prover at a *right interior* round `m + 1 + k` (`k : Fin n`) equals
`P₂`'s state at round `k + 1`.  Mirror of `append_PrvState_castLE` via `Fin.append_right`/`Fin.tail`
(here `Fin.tail P₂.PrvState ∘ Fin.cast` reduces to `P₂.PrvState ∘ Fin.succ` on the right). -/
theorem append_PrvState_natAdd_succ (k : Fin n) :
    (P₁.append P₂).PrvState (Fin.natAdd (m + 1) k |>.cast (by omega)) = P₂.PrvState k.succ := by
  unfold Prover.append
  dsimp only [Function.comp_apply]
  rw [show (Fin.cast (by omega) (Fin.natAdd (m + 1) k |>.cast (by omega)) : Fin (m + 1 + n))
        = Fin.natAdd (m + 1) k from by ext; simp]
  rw [Fin.append_right]
  rfl

/-- The appended protocol's direction at a *right interior* round `Fin.natAdd m k` (`k : Fin n`)
matches `pSpec₂`'s direction at `k`.  Mirror of `append_dir_castLE` via `Fin.append_right`. -/
theorem append_dir_natAdd (k : Fin n) :
    (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = pSpec₂.dir k := by
  show Fin.vappend pSpec₁.dir pSpec₂.dir (Fin.natAdd m k) = pSpec₂.dir k
  rw [Fin.vappend_eq_append, Fin.append_right]

/-- The appended-protocol message type at a right interior round equals `pSpec₂`'s. -/
theorem append_Message_natAdd (k : Fin n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .P_to_V) (hDir₂ : pSpec₂.dir k = .P_to_V) :
    (pSpec₁ ++ₚ pSpec₂).Message ⟨Fin.natAdd m k, hDir⟩ = pSpec₂.Message ⟨k, hDir₂⟩ := by
  show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (Fin.natAdd m k) = pSpec₂.«Type» k
  rw [Fin.vappend_eq_append, Fin.append_right]

/-- The appended-protocol challenge type at a right interior round equals `pSpec₂`'s. -/
theorem append_Challenge_natAdd (k : Fin n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .V_to_P) (hDir₂ : pSpec₂.dir k = .V_to_P) :
    (pSpec₁ ++ₚ pSpec₂).Challenge ⟨Fin.natAdd m k, hDir⟩ = pSpec₂.Challenge ⟨k, hDir₂⟩ := by
  show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (Fin.natAdd m k) = pSpec₂.«Type» k
  rw [Fin.vappend_eq_append, Fin.append_right]

/-- **Right interior-round `getChallenge` reduction.**  The `inr` analogue of
`append_getChallenge_left`: the appended protocol's `getChallenge` at a right challenge round
`Fin.natAdd m k` (`k : Fin n`) is heterogeneously equal to the `liftM` (along the right challenge
`SubSpec` `[pSpec₂.Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ`) of `pSpec₂`'s
`getChallenge`. -/
theorem append_getChallenge_natAdd (k : Fin n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .V_to_P)
    (hDir₂ : pSpec₂.dir k = .V_to_P) :
    HEq ((pSpec₁ ++ₚ pSpec₂).getChallenge ⟨Fin.natAdd m k, hDir⟩)
        (liftM (pSpec₂.getChallenge ⟨k, hDir₂⟩) :
          OracleComp [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ _) := by
  unfold ProtocolSpec.getChallenge
  have hChalEq : (pSpec₁ ++ₚ pSpec₂).Challenge ⟨Fin.natAdd m k, hDir⟩
      = pSpec₂.Challenge ⟨k, hDir₂⟩ := by
    show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (Fin.natAdd m k) = pSpec₂.«Type» k
    rw [Fin.vappend_eq_append, Fin.append_right]
  show HEq (liftM (OracleSpec.query (spec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        ⟨⟨Fin.natAdd m k, hDir⟩, ()⟩))
      (liftM (OracleSpec.query (spec := [pSpec₂.Challenge]ₒ) ⟨⟨k, hDir₂⟩, ()⟩) :
        OracleComp [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ _)
  rw [show (liftM (OracleSpec.query (spec := [pSpec₂.Challenge]ₒ) ⟨⟨k, hDir₂⟩, ()⟩) :
          OracleComp [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ _)
        = liftM (liftM (OracleSpec.query (spec := [pSpec₂.Challenge]ₒ) ⟨⟨k, hDir₂⟩, ()⟩)
            : OracleQuery [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ _) from rfl]
  refine liftM_query_heq hChalEq ?_
  rw [OracleSpec.query_def]
  show HEq (OracleQuery.mk (spec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) ⟨⟨Fin.natAdd m k, hDir⟩, ()⟩ id)
      (MonadLift.monadLift (OracleSpec.query (spec := [pSpec₂.Challenge]ₒ) ⟨⟨k, hDir₂⟩, ()⟩))
  rw [SubSpec.liftM_eq_lift]
  refine oracleQuery_heq ?_ hChalEq ?_
  · show (⟨⟨Fin.natAdd m k, hDir⟩, ()⟩ : [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.Domain)
      = ⟨ChallengeIdx.inr ⟨k, hDir₂⟩, ()⟩
    congr 1
  · simp only [OracleQuery.cont_query, OracleQuery.input_query, Function.id_comp]
    have hdom : [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.Range ⟨⟨Fin.natAdd m k, hDir⟩, ()⟩
        = [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.Range
            ((inferInstance : [(pSpec₂).Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).onQuery
              ⟨⟨k, hDir₂⟩, ()⟩) := by
      show (pSpec₁ ++ₚ pSpec₂).Challenge ⟨Fin.natAdd m k, hDir⟩
        = (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr ⟨k, hDir₂⟩)
      congr 1
    refine Function.hfunext hdom (fun a a' haa => ?_)
    refine haa.trans ?_
    dsimp only [SubSpec.onResponse]
    refine HEq.symm ?_
    generalize_proofs h
    exact cast_heq h a'

/-! ### Seam-round reductions

The seam round `m` is the genuinely-new monadic-interleaving step of `Prover.append` (the `i = m`
branch): it threads `P₁.output state >>= P₂.input` before `P₂`'s round-`0` step.  We characterize
the two seam shapes (`sendMessage`/`receiveChallenge`) heterogeneously in terms of `P₁.output` /
`P₂.input` / `P₂`'s round-0 step.  These feed the seam-round `processRound` in the right-block
run. -/

/-- State-type equality: the appended prover's state at the seam-round `castSucc` index `m`
(the state going INTO the seam round) equals `P₁`'s last state. -/
theorem append_PrvState_seam_castSucc (hn : 0 < n) :
    (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc = P₁.PrvState (Fin.last m) := by
  have := append_PrvState_castLE (P₁ := P₁) (P₂ := P₂) (Fin.last m)
  rw [show ((Fin.last m).castLE (show m + 1 ≤ m + n + 1 by omega) : Fin (m + n + 1))
        = (⟨m, by omega⟩ : Fin (m + n)).castSucc from by ext; simp] at this
  exact this

/-- **Seam-round `sendMessage` reduction.**  At the seam round `m` (the `i = m` branch of
`Prover.append.sendMessage`), the appended prover's `sendMessage` is heterogeneously equal to
`P₁.output state >>= fun ctx => P₂.sendMessage ⟨0,_⟩ (P₂.input ctx)`. -/
theorem append_sendMessage_seam (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir ⟨m, by omega⟩ = .P_to_V)
    (hDir₂ : pSpec₂.dir ⟨0, hn⟩ = .P_to_V)
    (state : (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc) :
    HEq ((P₁.append P₂).sendMessage ⟨⟨m, by omega⟩, hDir⟩ state)
      (do
        let ctxIn₂ ← P₁.output (cast (append_PrvState_seam_castSucc hn) state)
        P₂.sendMessage ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctxIn₂) : OracleComp oSpec _) := by
  unfold Prover.append
  dsimp only [Fin.vappend_eq_append]
  have hnlt : ¬ (↑(⟨m, by omega⟩ : Fin (m + n)) : ℕ) < m := by simp
  erw [id_eq, dite_eq_right hnlt]
  have heqm : (↑(⟨m, by omega⟩ : Fin (m + n)) : ℕ) = m := by simp
  rw [dif_pos heqm]
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  apply HEq.trans (cast_heq _ _)
  -- Both sides are `P₁.output (·) >>= fun ctx => P₂.sendMessage ⟨0,_⟩ (P₂.input ctx)` over oSpec;
  -- the seam's internally-cast `state` and our `cast _ state` target the same
  -- `P₁.PrvState (last m)`.
  refine bind_heq_congr (α := Stmt₂ × Wit₂) (α' := Stmt₂ × Wit₂) rfl
    (by congr 1) ?_ ?_
  · apply heq_of_eq; congr 1
  · rintro c c' rfl; rfl

/-- **Seam-round `receiveChallenge` reduction.**  The `V_to_P` analogue of
`append_sendMessage_seam`:
at the seam round `m`, the appended prover's `receiveChallenge` is heterogeneously equal to
`P₁.output state >>= fun ctx => P₂.receiveChallenge ⟨0,_⟩ (P₂.input ctx)`. -/
theorem append_receiveChallenge_seam (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir ⟨m, by omega⟩ = .V_to_P)
    (hDir₂ : pSpec₂.dir ⟨0, hn⟩ = .V_to_P)
    (state : (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc) :
    HEq ((P₁.append P₂).receiveChallenge ⟨⟨m, by omega⟩, hDir⟩ state)
      (do
        let ctxIn₂ ← P₁.output (cast (append_PrvState_seam_castSucc hn) state)
        P₂.receiveChallenge ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctxIn₂) : OracleComp oSpec _) := by
  unfold Prover.append
  dsimp only [Fin.vappend_eq_append]
  have hnlt : ¬ (↑(⟨m, by omega⟩ : Fin (m + n)) : ℕ) < m := by simp
  rw [dif_neg hnlt]
  have heqm : (↑(⟨m, by omega⟩ : Fin (m + n)) : ℕ) = m := by simp
  rw [dif_pos heqm]
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  apply HEq.trans (cast_heq _ _)
  refine bind_heq_congr (α := Stmt₂ × Wit₂) (α' := Stmt₂ × Wit₂) rfl
    (by congr 1) ?_ ?_
  · apply heq_of_eq; congr 1
  · rintro c c' rfl; rfl

/-- State-type equality: the appended prover's state at the seam-round `succ` index `m + 1`
(the state going OUT of the seam round) equals `P₂`'s state at round `1` (`= ⟨0,_⟩.succ`).  Derived
from `append_PrvState_natAdd_succ` at the right interior offset `k = 0`. -/
theorem append_PrvState_seam_succ (hn : 0 < n) :
    (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ
      = P₂.PrvState (⟨0, hn⟩ : Fin n).succ := by
  have h := append_PrvState_natAdd_succ (P₁ := P₁) (P₂ := P₂) (⟨0, hn⟩ : Fin n)
  rw [show ((Fin.natAdd (m + 1) (⟨0, hn⟩ : Fin n)).cast (by omega) : Fin (m + n + 1))
        = (⟨m, by omega⟩ : Fin (m + n)).succ from by ext; simp] at h
  exact h

/-- The appended-protocol message type at the seam round `m` equals `pSpec₂`'s round-`0` message
type.  The `i = m` (`= Fin.append_right` at offset `0`) analogue of `append_Message_castLE`. -/
theorem append_Message_seam (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V) :
    (pSpec₁ ++ₚ pSpec₂).Message ⟨⟨m, by omega⟩, hDir⟩ = pSpec₂.Message ⟨⟨0, hn⟩, hDir₂⟩ := by
  show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (⟨m, by omega⟩ : Fin (m + n)) = pSpec₂.«Type» ⟨0, hn⟩
  rw [Fin.vappend_eq_append,
    show (⟨m, by omega⟩ : Fin (m + n)) = Fin.natAdd m (⟨0, hn⟩ : Fin n) from by ext; simp,
    Fin.append_right]

/-- Seam-specialized `appendRight_concat` for the message branch.  This packages the transcript
reconciliation used by the right-block seam base: growing the carried `pSpec₁` prefix by `pSpec₂`'s
round-0 message is the same as growing the appended seam transcript by the cast seam message. -/
theorem appendRight_concat_seam_message (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (T₁ : FullTranscript pSpec₁)
    (msg : pSpec₂.Message ⟨⟨0, hn⟩, hDir₂⟩) :
    HEq
      (Transcript.appendRight T₁
        (Transcript.concat msg (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))))
      (Transcript.concat
        (m := (⟨m, by omega⟩ : Fin (m + n)))
        (cast (append_Message_seam hn hDir hDir₂).symm msg)
        (Transcript.appendRight T₁
          (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))))) := by
  exact ProtocolSpec.Transcript.appendRight_concat
    (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) T₁
    (k := (⟨0, hn⟩ : Fin n)) msg
    (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))

/-- **Seam-round `processRound` bridge (message branch).**  The seam-round counterpart of
`append_processRound_left_message`: resolving the appended prover's `processRound` at the seam round
`m` applied to the (`pure`d) seam start `rSeam` is heterogeneously equal to the `liftM` of the
`P₁.output >>= P₂.input`-threaded message boundary `do let ctx ← P₁.output (cast _ rSeam.2);
let ⟨msg,ns⟩ ← P₂.sendMessage ⟨0,_⟩ (P₂.input ctx); pure ⟨rSeam.1.concat (cast _ msg), cast _ ns⟩`.

The output transcript stays in the *appended* protocol (`rSeam.1.concat`, the genuine new content —
the `pSpec₁` prefix carried inside `rSeam.1`), so the seam-round message `msg` and post-state `ns`
produced by `P₂` are transported back along `append_Message_seam` / `append_PrvState_seam_succ`.

Proof shape: resolve the appended `processRound` via `processRound_message`, collapse the leading
`pure rSeam` bind, then bridge the (implicitly `liftM`-wrapped) appended `sendMessage` against the
`liftM`-pushed boundary.  Unlike the left analogue, the seam `sendMessage` and the boundary both
already live in `OracleComp oSpec`, so the two outer lifts agree on the SINGLE direct `MonadLift
oSpec → oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ` (no transitive `liftComp_liftComp` diamond); the
base HEq is `append_sendMessage_seam`. -/
theorem append_processRound_seam_message (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (rSeam : (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).castSucc
      × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc) :
    HEq ((P₁.append P₂).processRound ⟨m, by omega⟩ (pure rSeam))
      (Bind.bind
        (liftM (do
            let ctxIn₂ ← P₁.output (cast (append_PrvState_seam_castSucc hn) rSeam.2)
            P₂.sendMessage ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctxIn₂) :
            OracleComp oSpec (pSpec₂.Message ⟨⟨0, hn⟩, hDir₂⟩ × P₂.PrvState (⟨0, hn⟩ : Fin n).succ)) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            (pSpec₂.Message ⟨⟨0, hn⟩, hDir₂⟩ × P₂.PrvState (⟨0, hn⟩ : Fin n).succ))
        (fun p => (pure (rSeam.1.concat (cast (append_Message_seam hn hDir hDir₂).symm p.1),
            cast (append_PrvState_seam_succ hn).symm p.2) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              ((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).succ
                × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ)))) := by
  -- Resolve the appended `processRound` at the (message) seam round, then collapse `pure rSeam`.
  rw [processRound_message (P₁.append P₂) ⟨m, by omega⟩ hDir (pure rSeam)]
  simp only [pure_bind]
  -- Both sides: `(lifted seam sendMessage) >>= fun p => pure (concat p.1, p.2)` over the SAME
  -- (appended) output type; the seam `sendMessage` result type differs (appended vs `pSpec₂`).
  refine bind_heq_congr
    (α := (pSpec₁ ++ₚ pSpec₂).Message ⟨⟨m, by omega⟩, hDir⟩
      × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ)
    (α' := pSpec₂.Message ⟨⟨0, hn⟩, hDir₂⟩ × P₂.PrvState (⟨0, hn⟩ : Fin n).succ)
    (β := (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).succ
      × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ)
    (β' := (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).succ
      × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ)
    (by rw [append_Message_seam hn hDir hDir₂, append_PrvState_seam_succ hn]) rfl ?_ ?_
  · -- the (lifted) seam `sendMessage` HEq.  The LHS lifts `OracleComp oSpec → appended` via the
    -- DIRECT instance; the RHS via the TRANSITIVE instance `oSpec → oSpec+[pSpec₁.Challenge]ₒ →
    -- appended` (the default `MonadLiftT`).  Bridge the diamond via `liftComp_liftComp` (the two
    -- are equal as functions, `rfl` single-query coherence), then close with `liftComp_heq_congr`
    -- on the
    -- (HEq) base `sendMessage` computations (`append_sendMessage_seam`).
    have hαeq : ((pSpec₁ ++ₚ pSpec₂).Message ⟨⟨m, by omega⟩, hDir⟩
          × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ)
        = (pSpec₂.Message ⟨⟨0, hn⟩, hDir₂⟩ × P₂.PrvState (⟨0, hn⟩ : Fin n).succ) := by
      rw [append_Message_seam hn hDir hDir₂, append_PrvState_seam_succ hn]
    exact liftM_heq_congr (spec := oSpec)
      (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) hαeq
      (append_sendMessage_seam hn hDir hDir₂ rSeam.2)
  · -- trailing `pure (concat p.1, p.2)`: the appended seam `msg`/`ns` and the back-cast `pSpec₂`
    -- ones agree, so the appended-world output pairs are HEq (here in fact equal-typed).
    rintro ⟨msg, ns⟩ ⟨msg', ns'⟩ hmsg
    obtain ⟨hm, hns⟩ :=
      prod_heq_split (append_Message_seam hn hDir hDir₂) (append_PrvState_seam_succ hn) hmsg
    refine pure_heq_pure (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) rfl ?_
    refine prodMk_heq rfl rfl ?_ ?_
    · -- `rSeam.1.concat msg = rSeam.1.concat (cast _ msg')`: same transcript, HEq-equal messages.
      have : msg = cast (append_Message_seam hn hDir hDir₂).symm msg' :=
        eq_of_heq (hm.trans (cast_heq _ _).symm)
      rw [this]
    · -- `ns = cast _ ns'`: HEq-equal states over the (equal) appended state type.
      apply heq_of_eq
      exact eq_of_heq (hns.trans (cast_heq _ _).symm)

/-- The appended-protocol challenge type at the seam round `m` equals `pSpec₂`'s round-`0` challenge
type.  The `i = m` (`= Fin.append_right` at offset `0`) analogue of `append_Challenge_natAdd`. -/
theorem append_Challenge_seam (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P) :
    (pSpec₁ ++ₚ pSpec₂).Challenge ⟨⟨m, by omega⟩, hDir⟩ = pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩ := by
  show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (⟨m, by omega⟩ : Fin (m + n)) = pSpec₂.«Type» ⟨0, hn⟩
  rw [Fin.vappend_eq_append,
    show (⟨m, by omega⟩ : Fin (m + n)) = Fin.natAdd m (⟨0, hn⟩ : Fin n) from by ext; simp,
    Fin.append_right]

/-- Seam-specialized `appendRight_concat` for the challenge branch. -/
theorem appendRight_concat_seam_challenge (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (T₁ : FullTranscript pSpec₁)
    (challenge : pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩) :
    HEq
      (Transcript.appendRight T₁
        (Transcript.concat challenge (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))))
      (Transcript.concat
        (m := (⟨m, by omega⟩ : Fin (m + n)))
        (cast (append_Challenge_seam hn hDir hDir₂).symm challenge)
        (Transcript.appendRight T₁
          (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))))) := by
  exact ProtocolSpec.Transcript.appendRight_concat
    (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) T₁
    (k := (⟨0, hn⟩ : Fin n)) challenge
    (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))

/-- **Seam-round `getChallenge` reduction.**  At the seam round `m` (`= Fin.natAdd m ⟨0,_⟩`), the
appended protocol's `getChallenge` is heterogeneously equal to the `liftM` (along the right
challenge `SubSpec`) of `pSpec₂`'s round-`0` `getChallenge`.  Re-index of
`append_getChallenge_natAdd`. -/
theorem append_getChallenge_seam (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P) :
    HEq ((pSpec₁ ++ₚ pSpec₂).getChallenge ⟨⟨m, by omega⟩, hDir⟩)
        (liftM (pSpec₂.getChallenge ⟨⟨0, hn⟩, hDir₂⟩) :
          OracleComp [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ _) := by
  have hidx : (⟨m, by omega⟩ : Fin (m + n)) = Fin.natAdd m (⟨0, hn⟩ : Fin n) := by ext; simp
  -- Generalize the seam index to the `natAdd` form; the direction proof rides along.
  have hgen : ∀ (j : Fin (m + n)) (hj : j = Fin.natAdd m (⟨0, hn⟩ : Fin n))
      (hDirj : (pSpec₁ ++ₚ pSpec₂).dir j = .V_to_P),
      HEq ((pSpec₁ ++ₚ pSpec₂).getChallenge ⟨j, hDirj⟩)
        (liftM (pSpec₂.getChallenge ⟨⟨0, hn⟩, hDir₂⟩) :
          OracleComp [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ _) := by
    rintro j rfl hDirj
    exact append_getChallenge_natAdd (⟨0, hn⟩ : Fin n) hDirj hDir₂
  exact hgen (⟨m, by omega⟩ : Fin (m + n)) hidx hDir

/-- **Seam-round `processRound` bridge (challenge branch).**  The `V_to_P` analogue of
`append_processRound_seam_message`, and the seam-round counterpart of
`append_processRound_left_challenge`: resolving the appended prover's `processRound` at the seam
challenge round `m` applied to the (`pure`d) seam start `rSeam` is heterogeneously equal to the
boundary that samples the seam challenge (`pSpec₂`'s round-`0` `getChallenge`, lifted along the
right challenge `SubSpec`), then threads `P₁.output >>= P₂.input` into `P₂`'s round-`0`
`receiveChallenge`,
applies the resulting state-update to the sampled challenge, and grows the *appended* transcript
`rSeam.1` by the (back-cast) challenge.

Proof shape (mirrors the left challenge branch): resolve via `processRound_challenge'`, collapse
`pure rSeam`, then `bind_heq_congr` over the (lifted) `getChallenge` (`append_getChallenge_seam`),
then over the (lifted) `receiveChallenge` — whose `oSpec → appended` lift carries the same
transitive `MonadLift` diamond as the message branch, bridged by `liftComp_liftComp` against the
direct seam
`receiveChallenge` HEq (`append_receiveChallenge_seam`) — closing with the `concat` + function
application (`heq_app`) of the state-update to the challenge. -/
theorem append_processRound_seam_challenge (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (rSeam : (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).castSucc
      × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc) :
    HEq ((P₁.append P₂).processRound ⟨m, by omega⟩ (pure rSeam))
      (Bind.bind
        (liftM (pSpec₂.getChallenge ⟨⟨0, hn⟩, hDir₂⟩) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩))
        (fun challenge =>
          Bind.bind
            (liftM (do
                let ctxIn₂ ← P₁.output (cast (append_PrvState_seam_castSucc hn) rSeam.2)
                P₂.receiveChallenge ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctxIn₂) :
                OracleComp oSpec
                  (pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩ → P₂.PrvState (⟨0, hn⟩ : Fin n).succ)) :
              OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                (pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩ → P₂.PrvState (⟨0, hn⟩ : Fin n).succ))
            (fun f => (pure
              (rSeam.1.concat (cast (append_Challenge_seam hn hDir hDir₂).symm challenge),
                cast (append_PrvState_seam_succ hn).symm (f challenge)) :
              OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                ((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).succ
                  × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ))))) := by
  -- Resolve the appended `processRound` at the (challenge) seam round, then collapse `pure rSeam`.
  rw [processRound_challenge' (P₁.append P₂) ⟨m, by omega⟩ hDir (pure rSeam)]
  simp only [pure_bind]
  -- Challenge value-type equality.
  have hChalEq : (pSpec₁ ++ₚ pSpec₂).Challenge ⟨⟨m, by omega⟩, hDir⟩
      = pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩ := append_Challenge_seam hn hDir hDir₂
  -- Outer bind over the (HEq) `getChallenge` computations.
  refine bind_heq_congr (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
    hChalEq rfl ?_ ?_
  · -- `getChallenge` HEq, lifted to the full spec (same right `+`-`SubSpec` on both sides).
    exact liftM_heq_congr (spec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) hChalEq
      (append_getChallenge_seam hn hDir hDir₂)
  · -- continuation: bind over `receiveChallenge`, then `pure (concat, f challenge)`.
    rintro chalA chal₂ hchal
    -- Inner bind over the (lifted) `receiveChallenge`; result type `Challenge → State`.
    refine bind_heq_congr (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      (α := (pSpec₁ ++ₚ pSpec₂).Challenge ⟨⟨m, by omega⟩, hDir⟩
        → (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ)
      (α' := pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩ → P₂.PrvState (⟨0, hn⟩ : Fin n).succ)
      (β := (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).succ
        × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ)
      (β' := (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).succ
        × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ)
      (by rw [hChalEq, append_PrvState_seam_succ hn]) rfl ?_ ?_
    · -- the (lifted) seam `receiveChallenge` HEq: direct LHS lift vs transitive RHS lift, bridged
      -- by `liftComp_liftComp`; base HEq `append_receiveChallenge_seam`.
      have hαeq : ((pSpec₁ ++ₚ pSpec₂).Challenge ⟨⟨m, by omega⟩, hDir⟩
            → (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ)
          = (pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩ → P₂.PrvState (⟨0, hn⟩ : Fin n).succ) := by
        rw [hChalEq, append_PrvState_seam_succ hn]
      exact liftM_heq_congr (spec := oSpec)
        (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) hαeq
        (append_receiveChallenge_seam hn hDir hDir₂ rSeam.2)
    · -- `pure (concat chal, f chal)`: concat + function-application HEq.
      rintro fA f₂ hf
      refine pure_heq_pure (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) rfl ?_
      refine prodMk_heq rfl rfl ?_ ?_
      · -- `rSeam.1.concat chalA = rSeam.1.concat (cast _ chal₂)`: same transcript, HEq challenges.
        have : chalA = cast (append_Challenge_seam hn hDir hDir₂).symm chal₂ :=
          eq_of_heq (hchal.trans (cast_heq _ _).symm)
        rw [this]
      · -- `fA chalA = cast _ (f₂ chal₂)`: HEq function applied to HEq challenge.
        apply heq_of_eq
        refine eq_of_heq (HEq.trans ?_ (cast_heq _ _).symm)
        exact heq_app hChalEq (by rw [hChalEq, append_PrvState_seam_succ hn]) hf hchal

/-! ### Right interior-round reductions

The right *interior* rounds `m+1 .. m+n-1` are the `i > m` branch of `Prover.append`: uniform `P₂`
rounds.  These mirror the left-block reductions (`append_sendMessage_left` etc.), now indexed
through `Fin.natAdd m k` (`k : Fin n`, `k > 0`); the appended step reduces heterogeneously to
`P₂`'s step at
round `k`, with the state transported by `append_PrvState_natAdd_castSucc`. -/

/-- State-type equality: the appended prover's state at the interior right round `Fin.natAdd m k`'s
`castSucc` (state going INTO interior round `k`, where `k > 0`) equals `P₂`'s state at `k`. -/
theorem append_PrvState_natAdd_castSucc (k : Fin n) (hk : 0 < (k : ℕ)) :
    (P₁.append P₂).PrvState (Fin.natAdd m k).castSucc = P₂.PrvState k.castSucc := by
  have hpred : (⟨(k : ℕ) - 1, by omega⟩ : Fin n).succ = k.castSucc := by ext; simp; omega
  have := append_PrvState_natAdd_succ (P₁ := P₁) (P₂ := P₂) ⟨(k : ℕ) - 1, by omega⟩
  rw [hpred] at this
  rw [show ((Fin.natAdd m k).castSucc : Fin (m + n + 1))
        = (Fin.natAdd (m + 1) (⟨(k : ℕ) - 1, by omega⟩ : Fin n)).cast (by omega) from by
        ext; simp; omega]
  exact this

/-- State-type equality at the interior right round `succ` index (state AFTER interior round `k`,
`k > 0`).  Equals `P₂.PrvState k.succ`. -/
theorem append_PrvState_natAdd_interior_succ (k : Fin n) (hk : 0 < (k : ℕ)) :
    (P₁.append P₂).PrvState (Fin.natAdd m k).succ = P₂.PrvState k.succ := by
  have := append_PrvState_natAdd_succ (P₁ := P₁) (P₂ := P₂) k
  rw [show ((Fin.natAdd m k).succ : Fin (m + n + 1))
        = (Fin.natAdd (m + 1) k).cast (by omega) from by ext; simp; omega]
  exact this

/-- **State-type equality at the final appended round.**  For a non-empty right block (`0 < n`), the
appended prover's state type at the last round `Fin.last (m + n)` is `P₂`'s state at its own last
round `Fin.last n`.  Specialisation of `append_PrvState_natAdd_succ` at `k = ⟨n-1, _⟩`
(`(natAdd (m+1) ⟨n-1,_⟩).cast = Fin.last (m+n)`, `⟨n-1,_⟩.succ = Fin.last n`); mirror of
`append_PrvState_natAdd_castSucc`.  The state transport needed by the right-block `output` assembly. -/
theorem append_PrvState_last (hn : 0 < n) :
    (P₁.append P₂).PrvState (Fin.last (m + n)) = P₂.PrvState (Fin.last n) := by
  have hpred : (⟨n - 1, by omega⟩ : Fin n).succ = Fin.last n := by ext; simp; omega
  have h := append_PrvState_natAdd_succ (P₁ := P₁) (P₂ := P₂) (⟨n - 1, by omega⟩ : Fin n)
  rw [hpred] at h
  rw [show (Fin.last (m + n) : Fin (m + n + 1))
        = (Fin.natAdd (m + 1) (⟨n - 1, by omega⟩ : Fin n)).cast (by omega) from by
        ext; simp; omega]
  exact h

/-- **Output assembly at the final appended round.**  For a non-empty right block (`0 < n`), the
appended prover's `output` at the last round is `P₂`'s `output` applied to the final state
transported by `append_PrvState_last` — exactly `Prover.append`'s `output` branch for `n ≠ 0`.  This
is the `output`-assembly step of the right-block characterization of `append_run`.  (The `DCast.dcast`
of the definition is reconciled to `_root_.cast` via `dcast_eq_root_cast`; the residual transport is
closed by `cast_heq`/proof-irrelevance.) -/
theorem append_output_last (hn : 0 < n)
    (state : (P₁.append P₂).PrvState (Fin.last (m + n))) :
    (P₁.append P₂).output state = P₂.output (cast (append_PrvState_last hn) state) := by
  exact Prover.append_output_pos (P₁ := P₁) (P₂ := P₂) (by omega) state
    (cast (append_PrvState_last hn) state) (cast_heq _ _).symm

/-- **Right interior-round `sendMessage` reduction.**  At an interior right round `Fin.natAdd m k`
(`k : Fin n`, `k > 0`, the `i > m` branch of `Prover.append.sendMessage`), the appended prover's
`sendMessage` is heterogeneously equal to `P₂`'s `sendMessage` at round `k`. -/
theorem append_sendMessage_natAdd (k : Fin n) (hk : 0 < (k : ℕ))
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .P_to_V)
    (hDir₂ : pSpec₂.dir k = .P_to_V)
    (state : (P₁.append P₂).PrvState (Fin.natAdd m k).castSucc) :
    HEq ((P₁.append P₂).sendMessage ⟨Fin.natAdd m k, hDir⟩ state)
      (P₂.sendMessage ⟨k, hDir₂⟩ (cast (append_PrvState_natAdd_castSucc k hk) state)) := by
  unfold Prover.append
  dsimp only [Fin.vappend_eq_append]
  have hnlt : ¬ (↑(Fin.natAdd m k) : ℕ) < m := by simp
  erw [id_eq, dite_eq_right hnlt]
  have hne : (↑(Fin.natAdd m k) : ℕ) ≠ m := by simp; omega
  rw [dif_neg hne]
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  apply HEq.trans (cast_heq _ _)
  have hkeq : (⟨(↑(Fin.natAdd m k) : ℕ) - m, by simp⟩ : Fin n) = k := by ext; simp
  have hdir₂' : pSpec₂.dir ⟨(↑(Fin.natAdd m k) : ℕ) - m, by simp⟩ = .P_to_V := by
    rw [hkeq]; exact hDir₂
  have hidx : (⟨⟨(↑(Fin.natAdd m k) : ℕ) - m, by simp⟩, hdir₂'⟩ : pSpec₂.MessageIdx)
      = ⟨k, hDir₂⟩ := by ext; simp
  refine sendMessage_heq_congr hidx ?_
  exact (cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm)

/-- **Right interior-round `receiveChallenge` reduction.**  Mirror of `append_sendMessage_natAdd`
for the `V_to_P` direction. -/
theorem append_receiveChallenge_natAdd (k : Fin n) (hk : 0 < (k : ℕ))
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .V_to_P)
    (hDir₂ : pSpec₂.dir k = .V_to_P)
    (state : (P₁.append P₂).PrvState (Fin.natAdd m k).castSucc) :
    HEq ((P₁.append P₂).receiveChallenge ⟨Fin.natAdd m k, hDir⟩ state)
      (P₂.receiveChallenge ⟨k, hDir₂⟩ (cast (append_PrvState_natAdd_castSucc k hk) state)) := by
  unfold Prover.append
  dsimp only [Fin.vappend_eq_append]
  have hnlt : ¬ (↑(Fin.natAdd m k) : ℕ) < m := by simp
  rw [dif_neg hnlt]
  have hne : (↑(Fin.natAdd m k) : ℕ) ≠ m := by simp; omega
  rw [dif_neg hne]
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  apply HEq.trans (cast_heq _ _)
  have hkeq : (⟨(↑(Fin.natAdd m k) : ℕ) - m, by simp⟩ : Fin n) = k := by ext; simp
  have hdir₂' : pSpec₂.dir ⟨(↑(Fin.natAdd m k) : ℕ) - m, by simp⟩ = .V_to_P := by
    rw [hkeq]; exact hDir₂
  have hidx : (⟨⟨(↑(Fin.natAdd m k) : ℕ) - m, by simp⟩, hdir₂'⟩ : pSpec₂.ChallengeIdx)
      = ⟨k, hDir₂⟩ := by ext; simp
  refine receiveChallenge_heq_congr hidx ?_
  exact (cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm)

/-! ### Right-block `processRound` reductions (prefix-carrying)

The right-block run carries the left transcript `transcript₁` as a prefix.  Unlike the left block
(where `append_processRound_left_*` matched a clean `liftAppendLeft pSpec₂ (P₁.processRound ..)`), the right block's
transcript is `happend transcript₁ tr₂`: the appended `processRound` at a right round grows the
*outer* `happend`-prefixed transcript by a `concat`, while the factored `P₂.processRound` grows the
*inner* `pSpec₂` transcript `tr₂` by a `concat`.  These are identified by `concat_append_right`
(`= Fin.happend_hconcat_eq`).

`append_getChallenge_natAdd` (the `inr`-SubSpec analogue of the proven `append_getChallenge_left`)
supplies the missing per-round handle for right *challenge* rounds, completing the round-local
reduction set for the right block (`{send,receive}Message_natAdd`, `{send,receive}_seam`,
`getChallenge_natAdd`). -/


/-- **Right interior-round `processRound` reduction (message branch).**  At an interior right round
`Fin.natAdd m k` (`k : Fin n`, `k > 0` — the `i > m` branch, *not* the seam), the appended prover's
`processRound` on a `pure` input reduces (heterogeneously) to `P₂`'s message step on the
state-transported input, concatenated onto the appended transcript `rInt.1`.  Mirror of the proven
seam reduction `append_processRound_seam_message`, but *simpler*: no `P₁.output >>= P₂.input`
threading (that only happens at the seam).  The transcript-prefix is *not* handled here — it enters
only at the right-block run-induction assembly (via `concat_append_right`); at the round level the
appended transcript `rInt.1` is grown directly. -/
theorem append_processRound_natAdd_message (k : Fin n) (hk : 0 < (k : ℕ))
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .P_to_V)
    (hDir₂ : pSpec₂.dir k = .P_to_V)
    (rInt : (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m k).castSucc
      × (P₁.append P₂).PrvState (Fin.natAdd m k).castSucc) :
    HEq ((P₁.append P₂).processRound (Fin.natAdd m k) (pure rInt))
      (Bind.bind
        (liftM (P₂.sendMessage ⟨k, hDir₂⟩
            (cast (append_PrvState_natAdd_castSucc (P₁ := P₁) (P₂ := P₂) k hk) rInt.2)) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            (pSpec₂.Message ⟨k, hDir₂⟩ × P₂.PrvState k.succ))
        (fun p => (pure
            (rInt.1.concat (cast (append_Message_natAdd k hDir hDir₂).symm p.1),
              cast (append_PrvState_natAdd_interior_succ (P₁ := P₁) (P₂ := P₂) k hk).symm p.2) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              ((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m k).succ
                × (P₁.append P₂).PrvState (Fin.natAdd m k).succ)))) := by
  rw [processRound_message (P₁.append P₂) (Fin.natAdd m k) hDir (pure rInt)]
  simp only [pure_bind]
  refine bind_heq_congr
    (α := (pSpec₁ ++ₚ pSpec₂).Message ⟨Fin.natAdd m k, hDir⟩
      × (P₁.append P₂).PrvState (Fin.natAdd m k).succ)
    (α' := pSpec₂.Message ⟨k, hDir₂⟩ × P₂.PrvState k.succ)
    (β := (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m k).succ
      × (P₁.append P₂).PrvState (Fin.natAdd m k).succ)
    (β' := (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m k).succ
      × (P₁.append P₂).PrvState (Fin.natAdd m k).succ)
    (by rw [append_Message_natAdd k hDir hDir₂, append_PrvState_natAdd_interior_succ k hk]) rfl ?_ ?_
  · have hαeq : ((pSpec₁ ++ₚ pSpec₂).Message ⟨Fin.natAdd m k, hDir⟩
          × (P₁.append P₂).PrvState (Fin.natAdd m k).succ)
        = (pSpec₂.Message ⟨k, hDir₂⟩ × P₂.PrvState k.succ) := by
      rw [append_Message_natAdd k hDir hDir₂, append_PrvState_natAdd_interior_succ k hk]
    exact liftM_heq_congr (spec := oSpec)
      (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) hαeq
      (append_sendMessage_natAdd k hk hDir hDir₂ rInt.2)
  · rintro ⟨msg, ns⟩ ⟨msg', ns'⟩ hmsg
    obtain ⟨hm, hns⟩ :=
      prod_heq_split (append_Message_natAdd k hDir hDir₂)
        (append_PrvState_natAdd_interior_succ k hk) hmsg
    refine pure_heq_pure (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) rfl ?_
    refine prodMk_heq rfl rfl ?_ ?_
    · have : msg = cast (append_Message_natAdd k hDir hDir₂).symm msg' :=
        eq_of_heq (hm.trans (cast_heq _ _).symm)
      rw [this]
    · apply heq_of_eq
      exact eq_of_heq (hns.trans (cast_heq _ _).symm)

/-- **Right interior-round `processRound` reduction (challenge branch).**  The `V_to_P` analogue of
`append_processRound_natAdd_message`: at an interior right challenge round, the appended
`processRound` on a `pure` input reduces to `P₂`'s `getChallenge`/`receiveChallenge` on the
state-transported input.  Mirror of `append_processRound_seam_challenge`, simpler (no `P₁.output`). -/
theorem append_processRound_natAdd_challenge (k : Fin n) (hk : 0 < (k : ℕ))
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .V_to_P)
    (hDir₂ : pSpec₂.dir k = .V_to_P)
    (rInt : (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m k).castSucc
      × (P₁.append P₂).PrvState (Fin.natAdd m k).castSucc) :
    HEq ((P₁.append P₂).processRound (Fin.natAdd m k) (pure rInt))
      (Bind.bind
        (liftM (pSpec₂.getChallenge ⟨k, hDir₂⟩) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (pSpec₂.Challenge ⟨k, hDir₂⟩))
        (fun challenge =>
          Bind.bind
            (liftM (P₂.receiveChallenge ⟨k, hDir₂⟩
                (cast (append_PrvState_natAdd_castSucc (P₁ := P₁) (P₂ := P₂) k hk) rInt.2)) :
              OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                (pSpec₂.Challenge ⟨k, hDir₂⟩ → P₂.PrvState k.succ))
            (fun f => (pure
                (rInt.1.concat (cast (append_Challenge_natAdd k hDir hDir₂).symm challenge),
                  cast (append_PrvState_natAdd_interior_succ (P₁ := P₁) (P₂ := P₂) k hk).symm
                    (f challenge)) :
                OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                  ((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m k).succ
                    × (P₁.append P₂).PrvState (Fin.natAdd m k).succ))))) := by
  rw [processRound_challenge' (P₁.append P₂) (Fin.natAdd m k) hDir (pure rInt)]
  simp only [pure_bind]
  have hChalEq : (pSpec₁ ++ₚ pSpec₂).Challenge ⟨Fin.natAdd m k, hDir⟩
      = pSpec₂.Challenge ⟨k, hDir₂⟩ := append_Challenge_natAdd k hDir hDir₂
  refine bind_heq_congr (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) hChalEq rfl ?_ ?_
  · exact liftM_heq_congr (spec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) hChalEq
      (append_getChallenge_natAdd k hDir hDir₂)
  · rintro chalA chal₂ hchal
    refine bind_heq_congr (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      (α := (pSpec₁ ++ₚ pSpec₂).Challenge ⟨Fin.natAdd m k, hDir⟩
        → (P₁.append P₂).PrvState (Fin.natAdd m k).succ)
      (α' := pSpec₂.Challenge ⟨k, hDir₂⟩ → P₂.PrvState k.succ)
      (β := (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m k).succ
        × (P₁.append P₂).PrvState (Fin.natAdd m k).succ)
      (β' := (pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m k).succ
        × (P₁.append P₂).PrvState (Fin.natAdd m k).succ)
      (by rw [hChalEq, append_PrvState_natAdd_interior_succ k hk]) rfl ?_ ?_
    · have hαeq : ((pSpec₁ ++ₚ pSpec₂).Challenge ⟨Fin.natAdd m k, hDir⟩
            → (P₁.append P₂).PrvState (Fin.natAdd m k).succ)
          = (pSpec₂.Challenge ⟨k, hDir₂⟩ → P₂.PrvState k.succ) := by
        rw [hChalEq, append_PrvState_natAdd_interior_succ k hk]
      exact liftM_heq_congr (spec := oSpec)
        (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) hαeq
        (append_receiveChallenge_natAdd k hk hDir hDir₂ rInt.2)
    · rintro fA f₂ hf
      refine pure_heq_pure (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) rfl ?_
      refine prodMk_heq rfl rfl ?_ ?_
      · have : chalA = cast (append_Challenge_natAdd k hDir hDir₂).symm chal₂ :=
          eq_of_heq (hchal.trans (cast_heq _ _).symm)
        rw [this]
      · apply heq_of_eq
        refine eq_of_heq (HEq.trans ?_ (cast_heq _ _).symm)
        exact heq_app hChalEq (by rw [hChalEq, append_PrvState_natAdd_interior_succ k hk]) hf hchal

/-- Computation-input version of `append_processRound_natAdd_message`: the appended interior-round
`processRound` on an arbitrary computation `curA` threads each result through `P₂.sendMessage`. -/
theorem append_processRound_natAdd_message_comp (k : Fin n) (hk : 0 < (k : ℕ))
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .P_to_V)
    (hDir₂ : pSpec₂.dir k = .P_to_V)
    (curA : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      ((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m k).castSucc
        × (P₁.append P₂).PrvState (Fin.natAdd m k).castSucc)) :
    HEq ((P₁.append P₂).processRound (Fin.natAdd m k) curA)
      (curA >>= fun rInt =>
        (Bind.bind
          (liftM (P₂.sendMessage ⟨k, hDir₂⟩
              (cast (append_PrvState_natAdd_castSucc (P₁ := P₁) (P₂ := P₂) k hk) rInt.2)) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              (pSpec₂.Message ⟨k, hDir₂⟩ × P₂.PrvState k.succ))
          (fun p => (pure
            (rInt.1.concat (cast (append_Message_natAdd k hDir hDir₂).symm p.1),
              cast (append_PrvState_natAdd_interior_succ (P₁ := P₁) (P₂ := P₂) k hk).symm p.2) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              ((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m k).succ
                × (P₁.append P₂).PrvState (Fin.natAdd m k).succ))))) := by
  rw [processRound_eq_bind]
  refine bind_heq_congr rfl rfl HEq.rfl (fun r r' hrr => ?_)
  obtain rfl := eq_of_heq hrr
  exact append_processRound_natAdd_message k hk hDir hDir₂ r

theorem append_processRound_natAdd_challenge_comp (k : Fin n) (hk : 0 < (k : ℕ))
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .V_to_P)
    (hDir₂ : pSpec₂.dir k = .V_to_P)
    (curA : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      ((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m k).castSucc
        × (P₁.append P₂).PrvState (Fin.natAdd m k).castSucc)) :
    HEq ((P₁.append P₂).processRound (Fin.natAdd m k) curA)
      (curA >>= fun rInt =>
        (Bind.bind
          (liftM (pSpec₂.getChallenge ⟨k, hDir₂⟩) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (pSpec₂.Challenge ⟨k, hDir₂⟩))
          (fun challenge =>
            Bind.bind
              (liftM (P₂.receiveChallenge ⟨k, hDir₂⟩
                  (cast (append_PrvState_natAdd_castSucc (P₁ := P₁) (P₂ := P₂) k hk) rInt.2)) :
                OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                  (pSpec₂.Challenge ⟨k, hDir₂⟩ → P₂.PrvState k.succ))
              (fun f => (pure
                  (rInt.1.concat (cast (append_Challenge_natAdd k hDir hDir₂).symm challenge),
                    cast (append_PrvState_natAdd_interior_succ (P₁ := P₁) (P₂ := P₂) k hk).symm
                      (f challenge)) :
                  OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                    ((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.natAdd m k).succ
                      × (P₁.append P₂).PrvState (Fin.natAdd m k).succ)))))) := by
  rw [processRound_eq_bind]
  refine bind_heq_congr rfl rfl HEq.rfl (fun r r' hrr => ?_)
  obtain rfl := eq_of_heq hrr
  exact append_processRound_natAdd_challenge k hk hDir hDir₂ r

/-- **Threaded right interior-round `processRound` (message branch).**  The keystone per-round brick
for the right-block run characterization: the appended interior `processRound` applied to the
`appendRight`-bridged image (under `T₁`, the seam/`pSpec₁` prefix) of a `P₂` partial run `cur₂`
equals the `appendRight`-bridged image of `P₂`'s own `processRound`.  Crucially `cur₂` is kept under
a SINGLE `liftComp` and the appended transcript is reconciled by `appendRight_concat`, so every lift
is the canonical `oSpec → appended` one (collapsed via `liftComp_liftComp`) — there is no
challenge-block (`pSpec₂.Challenge → appended`) coherence to discharge.  This is exactly the
invariant the right-block `Fin.induction` folds. -/
theorem append_processRound_natAdd_message_threaded (k : Fin n) (hk : 0 < (k : ℕ))
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .P_to_V)
    (hDir₂ : pSpec₂.dir k = .P_to_V)
    (T₁ : FullTranscript pSpec₁)
    (cur₂ : OracleComp (oSpec + [pSpec₂.Challenge]ₒ)
      (pSpec₂.Transcript k.castSucc × P₂.PrvState k.castSucc)) :
    HEq ((P₁.append P₂).processRound (Fin.natAdd m k)
          ((fun p => (Transcript.appendRight T₁ p.1,
              cast (append_PrvState_natAdd_castSucc (P₁ := P₁) (P₂ := P₂) k hk).symm p.2)) <$>
            (liftComp cur₂ (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))))
      ((fun p => (Transcript.appendRight T₁ p.1,
              cast (append_PrvState_natAdd_interior_succ (P₁ := P₁) (P₂ := P₂) k hk).symm p.2)) <$>
            (liftComp (P₂.processRound k cur₂) (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))) := by
  refine HEq.trans (append_processRound_natAdd_message_comp k hk hDir hDir₂ _) ?_
  rw [processRound_message P₂ k hDir₂ cur₂]
  simp only [bind_map_left, Function.comp, map_bind, liftComp_bind, liftComp_pure, bind_assoc,
    pure_bind, map_pure, bind_pure_comp]
  refine bind_heq_congr rfl rfl HEq.rfl (fun a a' haa => ?_)
  obtain rfl := eq_of_heq haa
  simp only [liftComp_map, Functor.map_map, Function.comp, cast_cast, ← liftComp_eq_liftM]
  rw [Prover.liftComp_liftComp (spec := oSpec) (midSpec := oSpec + [pSpec₂.Challenge]ₒ)
    (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (fun t => rfl)]
  apply heq_of_eq
  simp only [cast_eq]
  congr 1
  · funext a_1
    refine Prod.ext ?_ rfl
    exact (eq_of_heq (ProtocolSpec.Transcript.appendRight_concat T₁ a_1.1 a.1)).symm
/-- **Threaded right interior-round `processRound` (challenge branch).**  The `V_to_P` analogue of
`append_processRound_natAdd_message_threaded`: same `appendRight`-bridge invariant, via the challenge
comp brick `append_processRound_natAdd_challenge_comp` + `processRound_challenge'`.  The shared
`getChallenge` lift collapses by `liftComp_liftComp` (`[pSpec₂.Challenge]ₒ → oSpec+[pSpec₂.Challenge]ₒ
→ appended`) and the per-round transcript growth is reconciled by `appendRight_concat`. -/
theorem append_processRound_natAdd_challenge_threaded (k : Fin n) (hk : 0 < (k : ℕ))
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .V_to_P)
    (hDir₂ : pSpec₂.dir k = .V_to_P)
    (T₁ : FullTranscript pSpec₁)
    (cur₂ : OracleComp (oSpec + [pSpec₂.Challenge]ₒ)
      (pSpec₂.Transcript k.castSucc × P₂.PrvState k.castSucc)) :
    HEq ((P₁.append P₂).processRound (Fin.natAdd m k)
          ((fun p => (Transcript.appendRight T₁ p.1,
              cast (append_PrvState_natAdd_castSucc (P₁ := P₁) (P₂ := P₂) k hk).symm p.2)) <$>
            (liftComp cur₂ (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))))
      ((fun p => (Transcript.appendRight T₁ p.1,
              cast (append_PrvState_natAdd_interior_succ (P₁ := P₁) (P₂ := P₂) k hk).symm p.2)) <$>
            (liftComp (P₂.processRound k cur₂) (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))) := by
  refine HEq.trans (append_processRound_natAdd_challenge_comp k hk hDir hDir₂ _) ?_
  rw [processRound_challenge' P₂ k hDir₂ cur₂]
  simp only [bind_map_left, Function.comp, map_bind, liftComp_bind, liftComp_pure, bind_assoc,
    pure_bind, map_pure, bind_pure_comp]
  refine bind_heq_congr rfl rfl HEq.rfl (fun a a' haa => ?_)
  obtain rfl := eq_of_heq haa
  simp only [liftComp_map, Functor.map_map, Function.comp, cast_cast, ← liftComp_eq_liftM]
  rw [Prover.liftComp_liftComp (spec := [pSpec₂.Challenge]ₒ)
        (midSpec := oSpec + [pSpec₂.Challenge]ₒ)
        (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (fun t => rfl)]
  refine bind_heq_congr rfl rfl ?_ (fun ch ch' hch => ?_)
  · apply heq_of_eq
    exact Prover.liftComp_liftComp (spec := [pSpec₂.Challenge]ₒ)
      (midSpec := oSpec + [pSpec₂.Challenge]ₒ)
      (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (fun t => rfl)
      (pSpec₂.getChallenge ⟨k, hDir₂⟩)
  · obtain rfl := eq_of_heq hch
    rw [Prover.liftComp_liftComp (spec := oSpec) (midSpec := oSpec + [pSpec₂.Challenge]ₒ)
      (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (fun t => rfl)]
    apply heq_of_eq
    simp only [cast_eq]
    congr 1
    · funext a_1
      refine Prod.ext ?_ rfl
      exact (eq_of_heq (ProtocolSpec.Transcript.appendRight_concat T₁ ch a.1)).symm
/-- **Right-block interior run characterization (folded).**  The appended prover's `continueFromTo`
over the *interior* right rounds (`k₀ .. k₀+j`, `k₀ ≥ 1`, no seam) is the `appendRight`-bridged image
(under the seam/`pSpec₁` prefix `T₁`) of `P₂`'s own `continueFromTo`.  Proven by `Fin.induction` on
`j`: base `continueFromTo_self`; step peels one round (`continueFromTo_succ_of_ne`), applies the IH,
and folds via the threaded per-round lemmas (`append_processRound_natAdd_{message,challenge}_threaded`)
matched to `P₂.continueFromTo_succ_of_ne`.  This is the bulk of the right-block run assembly. -/
theorem append_continueFromTo_right_interior
    (T₁ : FullTranscript pSpec₁) (k₀ : Fin n) (hk₀ : 0 < (k₀ : ℕ)) (j : ℕ) (hjn : (k₀ : ℕ) + j ≤ n)
    (stmt₂ : Stmt₂) (wit₂ : Wit₂)
    (r₂ : pSpec₂.Transcript k₀.castSucc × P₂.PrvState k₀.castSucc) :
    HEq ((P₁.append P₂).continueFromTo stmt wit (Fin.natAdd m k₀).castSucc
          ⟨m + ((k₀ : ℕ) + j), by omega⟩
          (Transcript.appendRight T₁ r₂.1,
            cast (append_PrvState_natAdd_castSucc (P₁ := P₁) (P₂ := P₂) k₀ hk₀).symm r₂.2))
      (liftComp (P₂.continueFromTo stmt₂ wit₂ k₀.castSucc ⟨(k₀ : ℕ) + j, by omega⟩ r₂)
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) >>= fun p =>
        pure (Transcript.appendRight T₁ p.1,
          cast (by
            have hK : 0 < (k₀ : ℕ) + j := by omega
            rw [show (⟨(k₀ : ℕ) + j, by omega⟩ : Fin (n+1))
                  = (⟨(k₀ : ℕ) + j - 1, by omega⟩ : Fin n).succ from by ext; simp; omega,
              show (⟨m + ((k₀ : ℕ) + j), by omega⟩ : Fin (m+n+1))
                  = (Fin.natAdd (m + 1) (⟨(k₀ : ℕ) + j - 1, by omega⟩ : Fin n)).cast (by omega) from by
                ext; simp; omega]
            exact (append_PrvState_natAdd_succ (⟨(k₀ : ℕ) + j - 1, by omega⟩ : Fin n)).symm
            : P₂.PrvState ⟨(k₀ : ℕ) + j, by omega⟩
            = (P₁.append P₂).PrvState ⟨m + ((k₀ : ℕ) + j), by omega⟩) p.2)) := by
  induction j with
  | zero =>
    have hL : ((P₁.append P₂).continueFromTo stmt wit (Fin.natAdd m k₀).castSucc
          ⟨m + ((k₀ : ℕ) + 0), by omega⟩
          (Transcript.appendRight T₁ r₂.1,
            cast (append_PrvState_natAdd_castSucc (P₁ := P₁) (P₂ := P₂) k₀ hk₀).symm r₂.2))
        = pure (Transcript.appendRight T₁ r₂.1,
            cast (append_PrvState_natAdd_castSucc (P₁ := P₁) (P₂ := P₂) k₀ hk₀).symm r₂.2) := by
      exact Prover.continueFromTo_self _ _ _ _ _
    have hR : (P₂.continueFromTo stmt₂ wit₂ k₀.castSucc ⟨(k₀ : ℕ) + 0, by omega⟩ r₂)
        = pure r₂ := Prover.continueFromTo_self _ _ _ _ _
    rw [hL, hR]
    simp only [OracleComp.liftComp_pure, pure_bind]
    apply heq_of_eq
    congr 1
  | succ i ih =>
    have hki : 0 < (k₀ : ℕ) + i := by omega
    have hround : (⟨m + ((k₀ : ℕ) + i), by omega⟩ : Fin (m + n))
        = Fin.natAdd m (⟨(k₀ : ℕ) + i, by omega⟩ : Fin n) := by ext; simp
    have hne : ((Fin.natAdd m k₀).castSucc : Fin (m + n + 1))
        ≠ (⟨m + ((k₀ : ℕ) + i), by omega⟩ : Fin (m + n)).succ := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    have hstep : (P₁.append P₂).continueFromTo stmt wit (Fin.natAdd m k₀).castSucc
          ⟨m + ((k₀ : ℕ) + (i + 1)), by omega⟩
          (Transcript.appendRight T₁ r₂.1,
            cast (append_PrvState_natAdd_castSucc (P₁ := P₁) (P₂ := P₂) k₀ hk₀).symm r₂.2)
        = (P₁.append P₂).processRound (⟨m + ((k₀ : ℕ) + i), by omega⟩ : Fin (m + n))
            ((P₁.append P₂).continueFromTo stmt wit (Fin.natAdd m k₀).castSucc
              (⟨m + ((k₀ : ℕ) + i), by omega⟩ : Fin (m + n + 1))
              (Transcript.appendRight T₁ r₂.1,
                cast (append_PrvState_natAdd_castSucc (P₁ := P₁) (P₂ := P₂) k₀ hk₀).symm r₂.2)) := by
      have h := Prover.continueFromTo_succ_of_ne (P₁.append P₂) stmt wit (Fin.natAdd m k₀).castSucc
        (⟨m + ((k₀ : ℕ) + i), by omega⟩ : Fin (m + n)) hne
        (Transcript.appendRight T₁ r₂.1,
          cast (append_PrvState_natAdd_castSucc (P₁ := P₁) (P₂ := P₂) k₀ hk₀).symm r₂.2)
      convert h using 1 <;> congr 1 <;> omega
    rw [hstep]
    have ihi := ih (by omega)
    rw [eq_of_heq ihi]
    -- LHS arg is `liftComp cur₂ >>= pure∘bridge` = bridge <$> liftComp cur₂; convert to map form
    rw [bind_pure_comp]
    -- P₂.processRound (k₀+i) (P₂.cont to ⟨k₀+i⟩) = P₂.continueFromTo to ⟨k₀+(i+1)⟩
    have hP2 : P₂.continueFromTo stmt₂ wit₂ k₀.castSucc ⟨(k₀:ℕ)+(i+1), by omega⟩ r₂
        = P₂.processRound (⟨(k₀:ℕ)+i, by omega⟩ : Fin n)
            (P₂.continueFromTo stmt₂ wit₂ k₀.castSucc (⟨(k₀:ℕ)+i, by omega⟩ : Fin n).castSucc r₂) := by
      have hne2 : (k₀.castSucc : Fin (n+1)) ≠ (⟨(k₀:ℕ)+i, by omega⟩ : Fin n).succ := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      have h := Prover.continueFromTo_succ_of_ne P₂ stmt₂ wit₂ k₀.castSucc
        (⟨(k₀:ℕ)+i, by omega⟩ : Fin n) hne2 r₂
      convert h using 1 <;> congr 1 <;> omega
    rw [hP2, bind_pure_comp]
    have hdir0 : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m (⟨(k₀:ℕ)+i, by omega⟩ : Fin n))
        = pSpec₂.dir (⟨(k₀:ℕ)+i, by omega⟩ : Fin n) := append_dir_natAdd _
    rcases hd : pSpec₂.dir (⟨(k₀:ℕ)+i, by omega⟩ : Fin n) with _ | _
    · -- P_to_V : message threaded lemma
      have hD : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m (⟨(k₀:ℕ)+i, by omega⟩ : Fin n)) = .P_to_V := by
        rw [hdir0]; exact hd
      exact append_processRound_natAdd_message_threaded (P₁ := P₁) (P₂ := P₂)
        (⟨(k₀:ℕ)+i, by omega⟩ : Fin n) (by simp; omega) hD hd T₁
        (P₂.continueFromTo stmt₂ wit₂ k₀.castSucc (⟨(k₀:ℕ)+i, by omega⟩ : Fin n).castSucc r₂)
    · -- V_to_P : challenge threaded lemma
      have hD : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m (⟨(k₀:ℕ)+i, by omega⟩ : Fin n)) = .V_to_P := by
        rw [hdir0]; exact hd
      exact append_processRound_natAdd_challenge_threaded (P₁ := P₁) (P₂ := P₂)
        (⟨(k₀:ℕ)+i, by omega⟩ : Fin n) (by simp; omega) hD hd T₁
        (P₂.continueFromTo stmt₂ wit₂ k₀.castSucc (⟨(k₀:ℕ)+i, by omega⟩ : Fin n).castSucc r₂)

/-- **Seam-peel of the right-block continuation (structural step).**  Continuing the appended
prover's run from the seam-round state index `m` (`= (⟨m,_⟩ : Fin (m+n)).castSucc`, the state going
INTO the seam round) to the next index `m+1` (`= (⟨m,_⟩ : Fin (m+n)).succ`) is exactly one
`processRound` of the seam round `⟨m,_⟩` applied to the (`pure`d) seam start.

This is the once-up-front *peel* the right-block run induction needs: it cannot run a uniform
`Fin.induction` over `k : Fin (n+1)` directly because the seam round `m` (`= pSpec₂` round `0`)
threads `P₁.output >>= P₂.input` INSIDE the `k = 0 → k = 1` `processRound` (so at base `k = 0` the
continuation is `continueFromTo_self = pure rSeam`, carrying NO `P₁.output` bind, and cannot be HEq
to a fixed shape that already does).  Peeling this single seam round (here, as a plain `OracleComp`
equality) exposes the seam `processRound`; the seam-direction reductions
`append_sendMessage_seam` / `append_receiveChallenge_seam` then surface the `P₁.output >>= P₂.input`
bind, after which the interior `k : Fin n` is uniform. -/
theorem append_continueFromTo_seam_peel (hn : 0 < n)
    (rSeam : (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).castSucc
      × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc) :
    Prover.continueFromTo (P₁.append P₂) stmt wit
        (⟨m, by omega⟩ : Fin (m + n)).castSucc (⟨m, by omega⟩ : Fin (m + n)).succ rSeam
      = (P₁.append P₂).processRound ⟨m, by omega⟩ (pure rSeam) := by
  rw [Prover.continueFromTo_succ_of_ne (P₁.append P₂) stmt wit
        (⟨m, by omega⟩ : Fin (m + n)).castSucc (⟨m, by omega⟩ : Fin (m + n))
        (by intro h; exact absurd (congrArg Fin.val h) (by simp)) rSeam]
  rw [Prover.continueFromTo_self]

/-- **Seam base of the right-block continuation induction (message round).**  Combines
`append_continueFromTo_seam_peel` (continuing from the seam state index `m` for one round equals
`processRound ⟨m,_⟩` on a `pure` input) with the proven seam reduction
`append_processRound_seam_message`: at a `P_to_V` seam round, the one-round continuation surfaces
`P₁.output >>= P₂.sendMessage (P₂.input ·)` — the `P₁.output >>= P₂.input` threading that happens
*only* at the seam — concatenated onto the appended transcript `rSeam.1`.  This is the base case
(`k = 0 → 1`) of the right-block continuation induction whose interior steps are
`append_processRound_natAdd_{message,challenge}`. -/
theorem append_continueFromTo_seam_step_message (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (rSeam : (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).castSucc
      × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc) :
    HEq (Prover.continueFromTo (P₁.append P₂) stmt wit (⟨m, by omega⟩ : Fin (m + n)).castSucc
          (⟨m, by omega⟩ : Fin (m + n)).succ rSeam)
      (Bind.bind
        (liftM (do
            let ctxIn₂ ← P₁.output (cast (append_PrvState_seam_castSucc hn) rSeam.2)
            P₂.sendMessage ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctxIn₂) :
            OracleComp oSpec (pSpec₂.Message ⟨⟨0, hn⟩, hDir₂⟩ × P₂.PrvState (⟨0, hn⟩ : Fin n).succ)) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            (pSpec₂.Message ⟨⟨0, hn⟩, hDir₂⟩ × P₂.PrvState (⟨0, hn⟩ : Fin n).succ))
        (fun p => (pure (rSeam.1.concat (cast (append_Message_seam hn hDir hDir₂).symm p.1),
            cast (append_PrvState_seam_succ hn).symm p.2) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              ((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).succ
                × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ)))) := by
  rw [append_continueFromTo_seam_peel hn rSeam]
  exact append_processRound_seam_message hn hDir hDir₂ rSeam

/-- **Seam base of the right-block continuation induction (challenge round).**  The `V_to_P`
analogue of `append_continueFromTo_seam_step_message`, via `append_processRound_seam_challenge`. -/
theorem append_continueFromTo_seam_step_challenge (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (rSeam : (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).castSucc
      × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc) :
    HEq (Prover.continueFromTo (P₁.append P₂) stmt wit (⟨m, by omega⟩ : Fin (m + n)).castSucc
          (⟨m, by omega⟩ : Fin (m + n)).succ rSeam)
      (Bind.bind
        (liftM (pSpec₂.getChallenge ⟨⟨0, hn⟩, hDir₂⟩) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩))
        (fun challenge =>
          Bind.bind
            (liftM (do
                let ctxIn₂ ← P₁.output (cast (append_PrvState_seam_castSucc hn) rSeam.2)
                P₂.receiveChallenge ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctxIn₂) :
                OracleComp oSpec
                  (pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩ → P₂.PrvState (⟨0, hn⟩ : Fin n).succ)) :
              OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                (pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩ → P₂.PrvState (⟨0, hn⟩ : Fin n).succ))
            (fun f => (pure
              (rSeam.1.concat (cast (append_Challenge_seam hn hDir hDir₂).symm challenge),
                cast (append_PrvState_seam_succ hn).symm (f challenge)) :
              OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                ((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).succ
                  × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ))))) := by
  rw [append_continueFromTo_seam_peel hn rSeam]
  exact append_processRound_seam_challenge hn hDir hDir₂ rSeam


/-- If the carried seam transcript is the `appendRight` image of a `pSpec₁` full transcript and
the empty `pSpec₂` prefix, then adding a seam message is the same as adding the message inside the
right transcript and re-appending it. -/
theorem appendRight_concat_seam_message_of_eq (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (T₁ : FullTranscript pSpec₁)
    (rSeamT : (pSpec₁ ++ₚ pSpec₂).Transcript
      (⟨m, by omega⟩ : Fin (m + n)).castSucc)
    (hT : rSeamT =
      Transcript.appendRight T₁
        (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))))
    (msg : pSpec₂.Message ⟨⟨0, hn⟩, hDir₂⟩) :
    HEq
      (rSeamT.concat (cast (append_Message_seam hn hDir hDir₂).symm msg))
      (Transcript.appendRight T₁
        (Transcript.concat msg
          (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))))) := by
  subst hT
  exact (appendRight_concat_seam_message hn hDir hDir₂ T₁ msg).symm

/-- Pair-level version of `appendRight_concat_seam_message_of_eq`, carrying the seam successor
state cast unchanged. -/
theorem appendRight_pair_seam_message_of_eq (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (T₁ : FullTranscript pSpec₁)
    (rSeamT : (pSpec₁ ++ₚ pSpec₂).Transcript
      (⟨m, by omega⟩ : Fin (m + n)).castSucc)
    (hT : rSeamT =
      Transcript.appendRight T₁
        (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))))
    (msg : pSpec₂.Message ⟨⟨0, hn⟩, hDir₂⟩)
    (ns : P₂.PrvState (⟨0, hn⟩ : Fin n).succ) :
    HEq
      (rSeamT.concat (cast (append_Message_seam hn hDir hDir₂).symm msg),
        cast (append_PrvState_seam_succ (P₁ := P₁) (P₂ := P₂) hn).symm ns)
      (Transcript.appendRight T₁
          (Transcript.concat msg
            (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))),
        cast (append_PrvState_seam_succ (P₁ := P₁) (P₂ := P₂) hn).symm ns) := by
  refine prodMk_heq rfl rfl ?_ HEq.rfl
  exact appendRight_concat_seam_message_of_eq hn hDir hDir₂ T₁ rSeamT hT msg

/-- Challenge analogue of `appendRight_concat_seam_message_of_eq`. -/
theorem appendRight_concat_seam_challenge_of_eq (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (T₁ : FullTranscript pSpec₁)
    (rSeamT : (pSpec₁ ++ₚ pSpec₂).Transcript
      (⟨m, by omega⟩ : Fin (m + n)).castSucc)
    (hT : rSeamT =
      Transcript.appendRight T₁
        (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))))
    (challenge : pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩) :
    HEq
      (rSeamT.concat (cast (append_Challenge_seam hn hDir hDir₂).symm challenge))
      (Transcript.appendRight T₁
        (Transcript.concat challenge
          (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))))) := by
  subst hT
  exact (appendRight_concat_seam_challenge hn hDir hDir₂ T₁ challenge).symm

/-- Pair-level challenge analogue of `appendRight_pair_seam_message_of_eq`. -/
theorem appendRight_pair_seam_challenge_of_eq (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (T₁ : FullTranscript pSpec₁)
    (rSeamT : (pSpec₁ ++ₚ pSpec₂).Transcript
      (⟨m, by omega⟩ : Fin (m + n)).castSucc)
    (hT : rSeamT =
      Transcript.appendRight T₁
        (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))))
    (challenge : pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩)
    (ns : P₂.PrvState (⟨0, hn⟩ : Fin n).succ) :
    HEq
      (rSeamT.concat (cast (append_Challenge_seam hn hDir hDir₂).symm challenge),
        cast (append_PrvState_seam_succ (P₁ := P₁) (P₂ := P₂) hn).symm ns)
      (Transcript.appendRight T₁
          (Transcript.concat challenge
            (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))),
        cast (append_PrvState_seam_succ (P₁ := P₁) (P₂ := P₂) hn).symm ns) := by
  refine prodMk_heq rfl rfl ?_ HEq.rfl
  exact appendRight_concat_seam_challenge_of_eq hn hDir hDir₂ T₁ rSeamT hT challenge

/-- `appendRight`-threaded message-branch seam step.  This repackages
`append_continueFromTo_seam_step_message` so the transcript produced by the seam round is already in
the same `appendRight T₁ (...)` shape used by the right-block interior induction. -/
theorem append_continueFromTo_seam_step_message_appendRight (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (T₁ : FullTranscript pSpec₁)
    (rSeam : (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).castSucc
      × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc)
    (hT : rSeam.1 =
      Transcript.appendRight T₁
        (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))) :
    HEq (Prover.continueFromTo (P₁.append P₂) stmt wit
          (⟨m, by omega⟩ : Fin (m + n)).castSucc
          (⟨m, by omega⟩ : Fin (m + n)).succ rSeam)
      (Bind.bind
        (liftM (do
            let ctxIn₂ ← P₁.output (cast (append_PrvState_seam_castSucc hn) rSeam.2)
            P₂.sendMessage ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctxIn₂) :
            OracleComp oSpec
              (pSpec₂.Message ⟨⟨0, hn⟩, hDir₂⟩ ×
                P₂.PrvState (⟨0, hn⟩ : Fin n).succ)) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            (pSpec₂.Message ⟨⟨0, hn⟩, hDir₂⟩ ×
              P₂.PrvState (⟨0, hn⟩ : Fin n).succ))
        (fun p => (pure
            (Transcript.appendRight T₁
                (Transcript.concat p.1
                  (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))),
              cast (append_PrvState_seam_succ (P₁ := P₁) (P₂ := P₂) hn).symm p.2) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              ((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).succ
                × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ)))) := by
  refine HEq.trans (append_continueFromTo_seam_step_message
    (P₁ := P₁) (P₂ := P₂) (stmt := stmt) (wit := wit) hn hDir hDir₂ rSeam) ?_
  refine bind_heq_congr rfl rfl HEq.rfl ?_
  rintro ⟨msg, ns⟩ ⟨msg', ns'⟩ hp
  cases eq_of_heq hp
  refine pure_heq_pure (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) rfl ?_
  exact appendRight_pair_seam_message_of_eq
    (P₁ := P₁) (P₂ := P₂) hn hDir hDir₂ T₁ rSeam.1 hT msg ns

/-- Challenge-branch analogue of `append_continueFromTo_seam_step_message_appendRight`. -/
theorem append_continueFromTo_seam_step_challenge_appendRight (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (T₁ : FullTranscript pSpec₁)
    (rSeam : (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).castSucc
      × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc)
    (hT : rSeam.1 =
      Transcript.appendRight T₁
        (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))) :
    HEq (Prover.continueFromTo (P₁.append P₂) stmt wit
          (⟨m, by omega⟩ : Fin (m + n)).castSucc
          (⟨m, by omega⟩ : Fin (m + n)).succ rSeam)
      (Bind.bind
        (liftM (pSpec₂.getChallenge ⟨⟨0, hn⟩, hDir₂⟩) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            (pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩))
        (fun challenge =>
          Bind.bind
            (liftM (do
                let ctxIn₂ ← P₁.output (cast (append_PrvState_seam_castSucc hn) rSeam.2)
                P₂.receiveChallenge ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctxIn₂) :
                OracleComp oSpec
                  (pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩ →
                    P₂.PrvState (⟨0, hn⟩ : Fin n).succ)) :
              OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                (pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩ →
                  P₂.PrvState (⟨0, hn⟩ : Fin n).succ))
            (fun f => (pure
              (Transcript.appendRight T₁
                  (Transcript.concat challenge
                    (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))),
                cast (append_PrvState_seam_succ (P₁ := P₁) (P₂ := P₂) hn).symm
                  (f challenge)) :
              OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                ((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).succ
                  × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ))))) := by
  refine HEq.trans (append_continueFromTo_seam_step_challenge
    (P₁ := P₁) (P₂ := P₂) (stmt := stmt) (wit := wit) hn hDir hDir₂ rSeam) ?_
  refine bind_heq_congr rfl rfl HEq.rfl ?_
  intro challenge challenge' hChallenge
  obtain rfl := eq_of_heq hChallenge
  refine bind_heq_congr rfl rfl HEq.rfl ?_
  intro f f' hf
  obtain rfl := eq_of_heq hf
  refine pure_heq_pure (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) rfl ?_
  exact appendRight_pair_seam_challenge_of_eq
    (P₁ := P₁) (P₂ := P₂) hn hDir hDir₂ T₁ rSeam.1 hT challenge (f challenge)

/-- Message-branch normalization for direct lifted `P₂.processRound 0` at the seam base.  It
unfolds the empty-transcript round, pushes `liftComp` through the round bind, and collapses the
nested `oSpec → oSpec + [pSpec₂.Challenge]ₒ → appended` lift. -/
theorem liftComp_processRound_zero_message_appendRight (hn : 0 < n)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (T₁ : FullTranscript pSpec₁) (ctxIn₂ : Stmt₂ × Wit₂) :
    (OracleComp.liftComp
        (P₂.processRound (⟨0, hn⟩ : Fin n)
          (pure
            ((default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))),
              P₂.input ctxIn₂)))
        (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) >>= fun p =>
      (pure
        (Transcript.appendRight T₁ p.1,
          cast (append_PrvState_seam_succ (P₁ := P₁) (P₂ := P₂) hn).symm p.2) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
          ((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).succ
            × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ)))
      =
    (OracleComp.liftComp
        (P₂.sendMessage ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctxIn₂))
        (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) >>= fun p =>
      (pure
        (Transcript.appendRight T₁
          (Transcript.concat p.1
            (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))),
          cast (append_PrvState_seam_succ (P₁ := P₁) (P₂ := P₂) hn).symm p.2) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
          ((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).succ
            × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ))) := by
  rw [processRound_message P₂ (⟨0, hn⟩ : Fin n) hDir₂
    (pure ((default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))), P₂.input ctxIn₂))]
  simp only [pure_bind, OracleComp.liftComp_bind, OracleComp.liftComp_pure, bind_assoc]
  rw [show (liftM (P₂.sendMessage ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctxIn₂)) :
        OracleComp (oSpec + [pSpec₂.Challenge]ₒ)
          (pSpec₂.Message ⟨⟨0, hn⟩, hDir₂⟩ ×
            P₂.PrvState (⟨0, hn⟩ : Fin n).succ))
      = OracleComp.liftComp (P₂.sendMessage ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctxIn₂))
        (oSpec + [pSpec₂.Challenge]ₒ) from
          (OracleComp.liftComp_eq_liftM (superSpec := oSpec + [pSpec₂.Challenge]ₒ) _).symm]
  rw [liftComp_liftComp (spec := oSpec) (midSpec := oSpec + [pSpec₂.Challenge]ₒ)
    (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (fun t => rfl)]

/-- Challenge-branch analogue of `liftComp_processRound_zero_message_appendRight`. -/
theorem liftComp_processRound_zero_challenge_appendRight (hn : 0 < n)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (T₁ : FullTranscript pSpec₁) (ctxIn₂ : Stmt₂ × Wit₂) :
    (OracleComp.liftComp
        (P₂.processRound (⟨0, hn⟩ : Fin n)
          (pure
            ((default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))),
              P₂.input ctxIn₂)))
        (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) >>= fun p =>
      (pure
        (Transcript.appendRight T₁ p.1,
          cast (append_PrvState_seam_succ (P₁ := P₁) (P₂ := P₂) hn).symm p.2) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
          ((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).succ
            × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ)))
      =
    (Bind.bind
      (liftM (pSpec₂.getChallenge ⟨⟨0, hn⟩, hDir₂⟩) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
          (pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩))
      (fun challenge =>
        OracleComp.liftComp
          (P₂.receiveChallenge ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctxIn₂))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) >>= fun f =>
        (pure
          (Transcript.appendRight T₁
            (Transcript.concat challenge
              (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))),
            cast (append_PrvState_seam_succ (P₁ := P₁) (P₂ := P₂) hn).symm
              (f challenge)) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            ((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).succ
              × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ)))) := by
  rw [processRound_challenge' P₂ (⟨0, hn⟩ : Fin n) hDir₂
    (pure ((default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))), P₂.input ctxIn₂))]
  simp only [pure_bind, OracleComp.liftComp_bind, OracleComp.liftComp_pure, bind_assoc]
  rw [show (liftM (pSpec₂.getChallenge ⟨⟨0, hn⟩, hDir₂⟩) :
        OracleComp (oSpec + [pSpec₂.Challenge]ₒ)
          (pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩))
      = OracleComp.liftComp (pSpec₂.getChallenge ⟨⟨0, hn⟩, hDir₂⟩)
        (oSpec + [pSpec₂.Challenge]ₒ) from
          (OracleComp.liftComp_eq_liftM (superSpec := oSpec + [pSpec₂.Challenge]ₒ) _).symm]
  rw [liftComp_liftComp (spec := [pSpec₂.Challenge]ₒ)
    (midSpec := oSpec + [pSpec₂.Challenge]ₒ)
    (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (fun t => rfl)]
  congr 1
  funext challenge
  rw [show (liftM (P₂.receiveChallenge ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctxIn₂)) :
        OracleComp (oSpec + [pSpec₂.Challenge]ₒ)
          (pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩ →
            P₂.PrvState (⟨0, hn⟩ : Fin n).succ))
      = OracleComp.liftComp (P₂.receiveChallenge ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctxIn₂))
        (oSpec + [pSpec₂.Challenge]ₒ) from
          (OracleComp.liftComp_eq_liftM (superSpec := oSpec + [pSpec₂.Challenge]ₒ) _).symm]
  rw [liftComp_liftComp (spec := oSpec) (midSpec := oSpec + [pSpec₂.Challenge]ₒ)
    (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (fun t => rfl)]

/-- Message-branch seam start in the same lifted `P₂.processRound 0` shape consumed by the
right-block interior fold.  This composes the appendRight-threaded one-round seam step with
`liftComp_processRound_zero_message_appendRight`, and also collapses the transitive left-challenge
lift introduced by splitting `P₁.output >>= P₂.sendMessage`. -/
theorem append_continueFromTo_seam_start_message_processRound (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (T₁ : FullTranscript pSpec₁)
    (rSeam : (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).castSucc
      × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc)
    (hT : rSeam.1 =
      Transcript.appendRight T₁
        (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))) :
    HEq (Prover.continueFromTo (P₁.append P₂) stmt wit
          (⟨m, by omega⟩ : Fin (m + n)).castSucc
          (⟨m, by omega⟩ : Fin (m + n)).succ rSeam)
      ((liftM (P₁.output (cast (append_PrvState_seam_castSucc hn) rSeam.2)) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Stmt₂ × Wit₂)) >>= fun ctxIn₂ =>
        (liftM
          (P₂.processRound (⟨0, hn⟩ : Fin n)
            (pure
              ((default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))),
                P₂.input ctxIn₂))) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            (pSpec₂.Transcript (⟨0, hn⟩ : Fin n).succ ×
              P₂.PrvState (⟨0, hn⟩ : Fin n).succ)) >>= fun p =>
        (pure
          (Transcript.appendRight T₁ p.1,
            cast (append_PrvState_seam_succ (P₁ := P₁) (P₂ := P₂) hn).symm p.2) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            ((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).succ
              × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ))) := by
  refine HEq.trans (append_continueFromTo_seam_step_message_appendRight
    (P₁ := P₁) (P₂ := P₂) (stmt := stmt) (wit := wit) hn hDir hDir₂ T₁ rSeam hT) ?_
  apply heq_of_eq
  rw [liftM_bind, bind_assoc]
  congr 1
  funext ctxIn₂
  simpa [OracleComp.liftComp_eq_liftM] using
    (liftComp_processRound_zero_message_appendRight
      (P₁ := P₁) (P₂ := P₂) hn hDir₂ T₁ ctxIn₂).symm

/-- Challenge-branch seam start with the boundary computation split out explicitly.

Unlike the message branch, the appended prover's seam challenge round samples the verifier
challenge before replaying `P₁.output`, while `P₂.processRound 0` would require the `P₂.input`
state before its challenge query.  This theorem preserves that challenge-first order and normalizes
the two replayed `oSpec` computations to direct appended-spec lifts. -/
theorem append_continueFromTo_seam_start_challenge_split (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (T₁ : FullTranscript pSpec₁)
    (rSeam : (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).castSucc
      × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc)
    (hT : rSeam.1 =
      Transcript.appendRight T₁
        (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))) :
    HEq (Prover.continueFromTo (P₁.append P₂) stmt wit
          (⟨m, by omega⟩ : Fin (m + n)).castSucc
          (⟨m, by omega⟩ : Fin (m + n)).succ rSeam)
      ((liftM (pSpec₂.getChallenge ⟨⟨0, hn⟩, hDir₂⟩) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            (pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩)) >>= fun challenge =>
        OracleComp.liftComp
          (P₁.output (cast (append_PrvState_seam_castSucc (P₁ := P₁) (P₂ := P₂) hn) rSeam.2))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) >>= fun ctxIn₂ =>
        OracleComp.liftComp
          (P₂.receiveChallenge ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctxIn₂))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) >>= fun f =>
        (pure
          (Transcript.appendRight T₁
              (Transcript.concat challenge
                (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))),
            cast (append_PrvState_seam_succ (P₁ := P₁) (P₂ := P₂) hn).symm
              (f challenge)) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            ((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).succ
              × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ))) := by
  refine HEq.trans (append_continueFromTo_seam_step_challenge_appendRight
    (P₁ := P₁) (P₂ := P₂) (stmt := stmt) (wit := wit) hn hDir hDir₂ T₁ rSeam hT) ?_
  apply heq_of_eq
  congr 1
  funext challenge
  rw [liftM_bind, bind_assoc]
  simp only [OracleComp.liftComp_eq_liftM]

/-- Seam transcript type equality: the appended transcript at the seam round `⟨m⟩.castSucc`
(covering only `pSpec₁`'s rounds) is `pSpec₁`'s full transcript. -/
theorem append_Transcript_seam_castSucc (hn : 0 < n) :
    (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).castSucc
      = FullTranscript pSpec₁ := by
  have := append_Transcript_castLE (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) (Fin.last m)
  rw [show ((Fin.last m).castLE (show m + 1 ≤ m + n + 1 by omega) : Fin (m + n + 1))
        = (⟨m, by omega⟩ : Fin (m + n)).castSucc from by ext; simp] at this
  exact this

/-- **Free `hT`**: any appended seam transcript is the `appendRight` of its `pSpec₁`-projection and the
empty `pSpec₂` prefix.  Discharges the `hT` hypothesis of `append_continueFromTo_right_msg` for free
(no run-embedding induction), via `appendRight_empty`. -/
theorem seam_transcript_appendRight (hn : 0 < n)
    (rSeamT : (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).castSucc) :
    rSeamT = Transcript.appendRight (cast (append_Transcript_seam_castSucc hn) rSeamT)
      (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))) := by
  apply eq_of_heq
  refine HEq.trans (cast_heq (append_Transcript_seam_castSucc hn) rSeamT).symm ?_
  exact (Transcript.appendRight_empty (cast (append_Transcript_seam_castSucc hn) rSeamT)).symm

/-- **Right-block run characterization (message seam).**  The appended prover's continuation over the
entire right block — from the seam round `⟨m⟩` to the last round — is, heterogeneously, `P₁`'s output
threaded into `P₂`'s full run-to-round, transported into the appended transcript via `appendRight`.
Assembles the seam (`append_continueFromTo_seam_start_message_processRound`), the interior fold
(`append_continueFromTo_right_interior`), the range-split (`continueFromTo_trans`), and the P₂-side
fold (`processRound_zero_continueFromTo_eq_runToRound_last`); the `1 + (n-1) = n` index gaps are
bridged by `continueFromTo_heq_target` / `liftComp_continueFromTo_heq_target`.  Discharges the appended
side of `appendRunRightResidual`. -/
theorem append_continueFromTo_right_msg (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (T₁ : FullTranscript pSpec₁)
    (rSeam : (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).castSucc
      × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc)
    (hT : rSeam.1 = Transcript.appendRight T₁
      (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))) :
    HEq (Prover.continueFromTo (P₁.append P₂) stmt wit (⟨m, by omega⟩ : Fin (m + n)).castSucc
          (Fin.last (m + n)) rSeam)
      ((liftM (P₁.output (cast (append_PrvState_seam_castSucc hn) rSeam.2)) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Stmt₂ × Wit₂)) >>= fun ctx =>
        ((fun p => (Transcript.appendRight T₁ p.1,
            cast (append_PrvState_last (P₁ := P₁) (P₂ := P₂) hn).symm p.2)) <$>
          liftComp (P₂.runToRound (Fin.last n) ctx.1 ctx.2)
            (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            ((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.last (m + n))
              × (P₁.append P₂).PrvState (Fin.last (m + n))))) := by
  rw [continueFromTo_trans (P₁.append P₂) stmt wit (⟨m, by omega⟩ : Fin (m + n)).castSucc
    (⟨m, by omega⟩ : Fin (m + n)).succ (Fin.last (m + n))
    (by rw [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega)
    (by rw [Fin.le_def, Fin.val_succ, Fin.val_last]; omega) rSeam]
  rw [eq_of_heq (append_continueFromTo_seam_start_message_processRound
    (P₁ := P₁) (P₂ := P₂) (stmt := stmt) (wit := wit) hn hDir hDir₂ T₁ rSeam hT)]
  simp only [bind_assoc, pure_bind]
  refine bind_heq_congr rfl rfl HEq.rfl (fun ctx ctx' hc => ?_)
  obtain rfl := eq_of_heq hc
  obtain ⟨c1, c2⟩ := ctx
  rw [← processRound_zero_continueFromTo_eq_runToRound_last hn P₂ c1 c2,
    OracleComp.liftComp_bind, map_bind, ← OracleComp.liftComp_eq_liftM]
  refine bind_heq_congr rfl rfl HEq.rfl (fun p p' hp => ?_)
  obtain rfl := eq_of_heq hp
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · -- n = 1: both sides pure(bridge p) via continueFromTo_self
    have hn1 : n = 1 := by omega
    subst hn1
    have hL : (Fin.last (m + 1) : Fin (m + 1 + 1)) = (⟨m, by omega⟩ : Fin (m + 1)).succ := by
      apply Fin.ext; simp [Fin.val_last, Fin.val_succ]
    refine HEq.trans (continueFromTo_heq_target hL (P₁.append P₂) stmt wit _) ?_
    rw [continueFromTo_self]
    have hRHS : (P₂.continueFromTo c1 c2 (⟨0, hn⟩ : Fin 1).succ (Fin.last 1) p
        : OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _) = pure p :=
      continueFromTo_self _ _ _ _ _
    rw [hRHS]
    first
      | rfl
      | (apply heq_of_eq; rfl)
      | (apply heq_of_eq; congr 1)
      | (apply heq_of_eq; simp only [OracleComp.liftComp_pure, map_pure]; congr 1)
  · -- n ≥ 2: interior induction at k₀ = ⟨1, hge⟩
    have hint := append_continueFromTo_right_interior (P₁ := P₁) (P₂ := P₂)
      (stmt := stmt) (wit := wit) (stmt₂ := c1) (wit₂ := c2)
      T₁ (⟨1, hge⟩ : Fin n) (by simp only [Fin.val_mk]; omega) (n - 1)
      (by simp only [Fin.val_mk]; omega) p
    rw [bind_pure_comp] at hint
    have eL : (Fin.last (m + n) : Fin (m + n + 1))
        = ⟨m + ((⟨1, hge⟩ : Fin n).val + (n - 1)), by simp only [Fin.val_mk]; omega⟩ := by
      apply Fin.ext; simp only [Fin.val_last, Fin.val_mk]; omega
    refine HEq.trans (continueFromTo_heq_target eL (P₁.append P₂) stmt wit
      (Transcript.appendRight T₁ p.1, cast (append_PrvState_seam_succ hn).symm p.2)) ?_
    refine HEq.trans hint ?_
    have eR : (⟨(⟨1, hge⟩ : Fin n).val + (n - 1), by simp only [Fin.val_mk]; omega⟩ : Fin (n + 1))
        = Fin.last n := by apply Fin.ext; simp only [Fin.val_last, Fin.val_mk]; omega
    have eRapp : (⟨m + ((⟨1, hge⟩ : Fin n).val + (n - 1)), by simp only [Fin.val_mk]; omega⟩
        : Fin (m + n + 1)) = Fin.last (m + n) := by
      apply Fin.ext; simp only [Fin.val_last, Fin.val_mk]; omega
    congr 1
    · rw [eR]
    · rw [eRapp]
    · have happ : ∀ {j₁ j₂ : Fin (n + 1)} (hj : j₁ = j₂) {u : pSpec₂.Transcript j₁}
          {u' : pSpec₂.Transcript j₂}, HEq u u' →
          HEq (Transcript.appendRight T₁ u) (Transcript.appendRight T₁ u') := by
        intro j₁ j₂ hj u u' hu; subst hj; rw [eq_of_heq hu]
      refine Function.hfunext (by rw [eR]) fun a a' ha => ?_
      obtain ⟨t, s⟩ := a
      obtain ⟨t', s'⟩ := a'
      obtain ⟨ht, hs⟩ := prod_heq_split (by rw [eR]) (by rw [eR]) ha
      exact prodMk_heq (by rw [eRapp]) (by rw [eRapp]) (happ eR ht)
        ((cast_heq _ _).trans (hs.trans (cast_heq _ _).symm))
    · exact liftComp_continueFromTo_heq_target eR P₂ c1 c2 p



/-- **`Fin.snoc`/`Fin.hconcat` bridge (partial `(T)` family).**  A partial-transcript
`Transcript.concat msg T` is `Fin.snoc T msg` over the transcript motive `δ`; the prefix/snoc
commutation keystone `Fin.happend_hconcat_eq` is, by contrast, stated for `Fin.hconcat`.  This lemma
identifies the two heterogeneously over an arbitrary snoc-motive `δ`, so that the right-block run
induction can move a `Transcript.concat` (a `snoc`) onto `Fin.hconcat` and then pull it out through
the `transcript₁` prefix via `happend_hconcat_eq`.  Proof: `Fin.hconcat_eq_snoc` rewrites `hconcat`
to a `snoc` over the `vconcat` motive, which agrees index-wise (`vconcat_castSucc`/`vconcat_last`)
with `δ`, closed by `Fin_snoc_heq`. -/
theorem snoc_heq_hconcat {N : ℕ} {δ : Fin (N + 1) → Type u}
    (T : (i : Fin N) → δ i.castSucc) (a : δ (Fin.last N)) :
    HEq (Fin.snoc T a) (Fin.hconcat T a) := by
  rw [Fin.hconcat_eq_snoc T a]
  refine Fin_snoc_heq rfl ?_ ?_ ?_
  · apply heq_of_eq; funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact (Fin.vconcat_castSucc (fun j => δ j.castSucc) (δ (Fin.last N)) j).symm
    · exact (Fin.vconcat_last (fun j => δ j.castSucc) (δ (Fin.last N))).symm
  · apply Function.hfunext rfl
    intro i j hij
    obtain rfl : i = j := by ext; exact (Fin.heq_ext_iff rfl).mp hij
    exact (cast_heq _ _).symm
  · exact (cast_heq _ _).symm

/-- **Right-block residual of `append_run`** (the appended-run equality after the proven seam-split).
After decomposing the appended run at the seam round `m` — via `run_eq_runToRound_last` (exposing
`run = runToRound (last (m+n)) ≫ output`) and `runToRound_eq_bind_continueFromTo` (factoring at
`k = ⟨m,_⟩`) — the full appended run-equality reduces to exactly this statement.  The left block and
the seam-split are therefore *proven* in `append_run` below; the only remaining content is the
right-block continuation `continueFromTo ⟨m,_⟩ (last (m+n))` together with the `output` assembly, to
be closed by the seam-peel (`append_continueFromTo_seam_peel`) followed by an interior
`Fin.induction` over `k : Fin n` (`append_{send,receive}Message_natAdd` / `append_getChallenge_natAdd`
/ `concat_append_right`) and `Prover.append`'s output branch.  Naming it pins the residual surface to
its sharpest form. -/
def appendRunRightResidual (stmt : Stmt₁) (wit : Wit₁) : Prop :=
  (((do
      let ⟨transcript, state⟩ ←
        (Prover.runToRound (⟨m, by omega⟩ : Fin (m + n + 1)) stmt wit (P₁.append P₂)
          >>= (P₁.append P₂).continueFromTo stmt wit ⟨m, by omega⟩ (Fin.last (m + n)))
      let output ← @liftM (OracleComp oSpec)
        (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
        (instMonadLiftTOfMonadLift (OracleComp oSpec) (OracleComp oSpec)
          (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)))
        (Stmt₃ × Wit₃) ((P₁.append P₂).output state)
      pure (transcript, output)) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
          (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃)))
    = (do
        let ⟨transcript₁, stmt₂, wit₂⟩ ← liftAppendLeft pSpec₂ (P₁.run stmt wit)
        let ⟨transcript₂, stmt₃, wit₃⟩ ← liftAppendRight pSpec₁ (P₂.run stmt₂ wit₂)
        return ⟨transcript₁ ++ₜ transcript₂, stmt₃, wit₃⟩)


/-- **Reverse exactness of the right-block residual.**  If the full appended-prover run equality is
already available, then the named residual `appendRunRightResidual` follows by the same proven
seam-split normalization used in `append_run`.  Together with `append_run`, this shows the residual
is exactly the remaining right-block obligation rather than a stronger assumption. -/
theorem appendRunRightResidual_of_append_run (stmt : Stmt₁) (wit : Wit₁)
    (hRun :
      (P₁.append P₂).run stmt wit = (do
        let ⟨transcript₁, stmt₂, wit₂⟩ ← liftAppendLeft pSpec₂ (P₁.run stmt wit)
        let ⟨transcript₂, stmt₃, wit₃⟩ ← liftAppendRight pSpec₁ (P₂.run stmt₂ wit₂)
        return ⟨transcript₁ ++ₜ transcript₂, stmt₃, wit₃⟩)) :
    appendRunRightResidual (P₁ := P₁) (P₂ := P₂) stmt wit := by
  rw [run_eq_runToRound_last,
      runToRound_eq_bind_continueFromTo (P₁.append P₂) stmt wit
        (⟨m, by omega⟩ : Fin (m + n + 1)) (Fin.last (m + n)) (by
          simp only [Fin.le_def, Fin.val_last]; omega)] at hRun
  simpa [appendRunRightResidual] using hRun


/-- The retained right-block residual implies the full native run factorization. The component
challenge inclusions are pinned by the canonical left and right lift functions. -/
theorem append_run_of_right_residual (stmt : Stmt₁) (wit : Wit₁)
    (hResidual : appendRunRightResidual (P₁ := P₁) (P₂ := P₂) stmt wit) :
    (P₁.append P₂).run stmt wit = (do
      let ⟨transcript₁, stmt₂, wit₂⟩ ← liftAppendLeft pSpec₂ (P₁.run stmt wit)
      let ⟨transcript₂, stmt₃, wit₃⟩ ← liftAppendRight pSpec₁ (P₂.run stmt₂ wit₂)
      return ⟨transcript₁ ++ₜ transcript₂, stmt₃, wit₃⟩) := by
  rw [run_eq_runToRound_last,
      runToRound_eq_bind_continueFromTo (P₁.append P₂) stmt wit
        (⟨m, by omega⟩ : Fin (m + n + 1)) (Fin.last (m + n)) (by
          simp only [Fin.le_def, Fin.val_last]; omega)]
  simpa [appendRunRightResidual] using hResidual

/-- **Discharge of `appendRunRightResidual` for a message seam.**  When the seam round (`pSpec₂`'s
round 0) is a prover message (`pSpec₂.dir 0 = .P_to_V`), the right-block residual equality holds
unconditionally.  Assembles the right-block run characterization (`append_continueFromTo_right_msg`,
with `hT` free via `seam_transcript_appendRight`), the seam (`append_runToRound_seam`),
`append_output_last`, and the transcript reconciliation `appendRight_full`, threading the seam `HEq`
and collapsing the residual lift representations via `liftComp_liftComp`.  This makes `append_run`
unconditional for message-first `P₂` (the common sequential-composition case). -/
theorem appendRunRightResidual_holds_msg (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V) :
    appendRunRightResidual (P₁ := P₁) (P₂ := P₂) stmt wit := by
  exact appendRunRightResidual_of_append_run stmt wit
    (Prover.append_run_of_seam (P₁ := P₁) (P₂ := P₂)
      (fun _ => Or.inr hDir₂) stmt wit)

/-- **Sequential-composition completeness for a message-first `P₂` (UNCONDITIONAL).**  When the seam
round (`pSpec₂`'s round 0) is a prover message, running the appended prover `P₁.append P₂` is exactly
running `P₁` then `P₂` and concatenating transcripts — no residual hypothesis required.  Combines the
conditional `append_run` with the kernel-clean discharge `appendRunRightResidual_holds_msg`.  This is
the completeness half of the LogUp-style sequential composition (#13) for the message-seam case. -/
theorem append_run_msg (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V) :
      (P₁.append P₂).run stmt wit = (do
        let ⟨transcript₁, stmt₂, wit₂⟩ ← liftAppendLeft pSpec₂ (P₁.run stmt wit)
        let ⟨transcript₂, stmt₃, wit₃⟩ ← liftAppendRight pSpec₁ (P₂.run stmt₂ wit₂)
        return ⟨transcript₁ ++ₜ transcript₂, stmt₃, wit₃⟩) :=
  Prover.append_run_of_seam (P₁ := P₁) (P₂ := P₂) (fun _ => Or.inr hDir₂) stmt wit

/-- The named right-block residual is equivalent to the full appended-prover run equality.  The
forward direction is `append_run`; the reverse direction is `appendRunRightResidual_of_append_run`.
This pins the remaining #13 append-run work to precisely the residual's statement. -/
theorem appendRunRightResidual_iff_append_run (stmt : Stmt₁) (wit : Wit₁) :
    appendRunRightResidual (P₁ := P₁) (P₂ := P₂) stmt wit ↔
      (P₁.append P₂).run stmt wit = (do
        let ⟨transcript₁, stmt₂, wit₂⟩ ← liftAppendLeft pSpec₂ (P₁.run stmt wit)
        let ⟨transcript₂, stmt₃, wit₃⟩ ← liftAppendRight pSpec₁ (P₂.run stmt₂ wit₂)
        return ⟨transcript₁ ++ₜ transcript₂, stmt₃, wit₃⟩) :=
  ⟨append_run_of_right_residual stmt wit, appendRunRightResidual_of_append_run stmt wit⟩

#print axioms Prover.appendRunRightResidual
#print axioms Prover.append_run
#print axioms Prover.appendRunRightResidual_of_append_run
#print axioms Prover.appendRunRightResidual_iff_append_run

-- Future work: define a function that extracts a second prover from the combined prover.

end Prover

namespace Verifier

variable {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}
  {stmt : Stmt₁}

end Verifier

namespace Reduction

variable {R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}
    {stmt : Stmt₁} {wit : Wit₁}

/- Unfortunately this is not true due to sequencing: `(R₁.append R₂).run` runs the two provers
first, then the two verifiers, whereas `R₁.run` and then `R₂.run` runs the first prover and
verifier, then the second prover and verifier.

We need justification to be able to swap the first verifier with the second prover, which would be
true if we interpret / maps this oracle computation (a priori a term of the free monad) into a
commutative monad (such as `Id`, i.e. all oracle queries are answered deterministically, `PMF`, i.e.
all oracle queries are answered probabilistically, `Option`, `ReaderT ρ`, `Set`, `WriterT` into a
commutative monoid, etc.). -/



end Reduction

end Execution
