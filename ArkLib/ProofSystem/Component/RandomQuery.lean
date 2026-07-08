/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.OracleReduction.LiftContext.OracleReduction
import ArkLib.OracleReduction.Security.OracleZeroKnowledge
import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
# Simple Oracle Reduction: Random Query

This describes a one-round oracle reduction to randomly test whether two oracles (of the same type,
with same oracle interface) are equal.

In more details: there is no witness nor public statement. There are two `OStatement`s, `a` and `b`,
of the same type. The relation is `a = b`.
   - The verifier samples random `q : OracleInterface.Query` for that type and sends it to the
     prover.
   - The verifier does not do any checks.
   - The output relation is that `a` and `b` are equal at that query.
   - We also support a variant where it's `a.query q = r` where `r` is the response, discarding `b`.
-/

open OracleSpec OracleComp OracleQuery OracleInterface ProtocolSpec
open scoped NNReal

variable {ι : Type} (oSpec : OracleSpec ι) (OStatement : Type) [O : OracleInterface OStatement]
  [inst : SampleableType (Query OStatement)]

namespace RandomQuery

@[reducible, simp] def StmtIn := Unit
@[reducible, simp] def StmtOut := Query OStatement

@[reducible, simp] def OStmtIn := fun _ : Fin 2 => OStatement
@[reducible, simp] def OStmtOut := fun _ : Fin 2 => OStatement

@[reducible, simp] def WitIn := Unit
@[reducible, simp] def WitOut := Unit

/-- The input relation is that the two oracles are equal. -/
@[reducible, simp]
def relIn : Set ((StmtIn × ∀ i, OStmtIn OStatement i) × WitIn) :=
  { ⟨⟨(), oracles⟩, ()⟩ | oracles 0 = oracles 1 }

/--
The output relation states that if the verifier's single query was `q`, then
`a` and `b` agree on that `q`, i.e. `answer a q = answer b q`.
-/
@[reducible, simp]
def relOut : Set ((StmtOut OStatement × ∀ i, OStmtOut OStatement i) × WitOut) :=
  { ⟨⟨q, oStmt⟩, ()⟩ | answer (oStmt 0) q = answer (oStmt 1) q }

@[reducible]
def pSpec : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[Query OStatement]⟩

instance : ∀ i, SampleableType ((pSpec OStatement).Challenge i)
  | ⟨0, _⟩ => inst

/--
The prover is trivial: it has no messages to send.  It only receives the verifier's challenge `q`,
and outputs the same `q`.

We keep track of `(a, b)` in the prover's state, along with the single random query `q`.
-/
@[inline, specialize]
def oracleProver : OracleProver oSpec
    Unit (fun _ : Fin 2 => OStatement) Unit
    (Query OStatement) (fun _ : Fin 2 => OStatement) Unit (pSpec OStatement) where

  PrvState
  | 0 => ∀ _ : Fin 2, OStatement
  | 1 => (∀ _ : Fin 2, OStatement) × (Query OStatement)

  input := fun x => x.1.2

  sendMessage | ⟨0, h⟩ => nomatch h

  receiveChallenge | ⟨0, _⟩ => fun oracles => pure fun q => (oracles, q)

  output := fun (oracles, q) => pure ((q, oracles), ())

/--
The oracle verifier simply returns the challenge, and performs no checks.
-/
@[inline, specialize]
def oracleVerifier : OracleVerifier oSpec
    Unit (fun _ : Fin 2 => OStatement)
    (Query OStatement) (fun _ : Fin 2 => OStatement) (pSpec OStatement) where

  verify := fun _ chal => do
    let q : Query OStatement := chal ⟨0, rfl⟩
    pure q

  embed := Function.Embedding.inl

  hEq := by intro i; exact rfl

/--
Combine the trivial prover and this verifier to form the `RandomQuery` oracle reduction:
the input oracles are `(a, b)`, and the output oracles are the same `(a, b)`
its output statement also contains the challenge `q`.
-/
@[inline, specialize]
def oracleReduction :
    OracleReduction oSpec Unit (fun _ : Fin 2 => OStatement) Unit
    (Query OStatement) (fun _ : Fin 2 => OStatement) Unit (pSpec OStatement) where
  prover := oracleProver oSpec OStatement
  verifier := oracleVerifier oSpec OStatement

instance instOracleVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent (oracleVerifier oSpec OStatement) where
  hCohInl i k h := by
    simp only [oracleVerifier, Function.Embedding.inl_apply] at h
    obtain rfl := Sum.inl.inj h
    rfl
  hCohInr i k h := by
    simp only [oracleVerifier, Function.Embedding.inl_apply] at h
    cases h

instance : VerifierOnly (pSpec OStatement) where
  verifier_first' := by simp

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

set_option linter.unusedSimpArgs false in
/-- The `RandomQuery` oracle reduction is perfectly complete. -/
@[simp]
theorem oracleReduction_completeness :
    (oracleReduction oSpec OStatement).perfectCompleteness
      init impl (relIn OStatement) (relOut OStatement) := by
  simp only [OracleReduction.perfectCompleteness, oracleReduction, relIn, relOut]
  simp only [Reduction.perfectCompleteness_eq_prob_one]
  intro ⟨stmt, oStmt⟩ wit hOStmt
  have hEq : oStmt 0 = oStmt 1 := hOStmt
  simp only [OracleReduction.toReduction, Reduction.run,
    Prover.run_of_verifier_first, oracleProver, oracleVerifier,
    OracleVerifier.toVerifier, Verifier.run]
  simp_rw [show (pure : _ → OptionT (OracleComp _) _) = fun x => (pure (some x) :
    OracleComp _ _) from rfl]
  simp only [← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_pure,
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
    FullTranscript.challenges, FullTranscript.messages, ChallengeIdx, Challenge,
    hEq]
  erw [simulateQ_query]
  simp only [StmtOut, OStmtOut, WitOut, Fin.isValue, Fin.vcons_of_one, ChallengeIdx,
    Challenge, ofPFunctor_toPFunctor, QueryImpl.liftTarget_self, MessageIdx, OStmtIn,
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
    StateT.run'_eq, probFailure_eq_zero, hEq,
    support_pure, Set.mem_singleton_iff, Prod.eq_iff_fst_eq_snd_eq]
  all_goals try erw [simulateQ_pure]
  all_goals try simp_all only [simulateQ_pure, pure_bind, map_pure,
    OptionT.run_mk, OptionT.run_pure, OptionT.run_bind, OptionT.run,
    StateT.run'_eq, StateT.run_pure, probFailure_eq_zero,
    support_pure, support_map, Set.mem_singleton_iff, Set.mem_image,
    OptionT.probFailure_eq, probOutput_pure, hEq]
  · rw [show OptionT.mk = id from rfl]
    simp only [ChallengeIdx, Fin.vcons_of_one, Challenge, Fin.isValue, input_query,
      cont_query, input_apply, id_eq, zero_add, probOutput_eq_zero_iff, support_map,
      Set.mem_image, Prod.exists, exists_and_right, exists_eq_right, not_exists]
    intro
    erw [simulateQ_pure]
    simp [support_pure, pure_bind]
  · intro a b x hx x_1 hx1 x_2 x_3
    erw [simulateQ_bind]
    simp only [liftComp_eq_liftM, pure_bind, simulateQ_pure, OptionT.lift,
      OptionT.run_mk, map_pure]
    erw [simulateQ_pure]
    simp only [pure_bind, simulateQ_pure, support_pure, StateT.run, StateT.run',
      Set.mem_singleton_iff, Prod.mk.injEq]
    rintro ⟨⟨rfl, rfl⟩, rfl⟩
    refine ⟨?_, rfl, ?_⟩ <;> congr 1

/-- The simulator for `RandomQuery`: the protocol is witness-free, so the simulator can rerun
the honest transcript distribution using the public oracle input and the unique `Unit` witness. -/
def transcriptSimulator :
    @OracleReduction.TranscriptSimulator ι oSpec Unit (Fin 2) (OStmtIn OStatement) 1
      (pSpec OStatement) :=
  fun stmtIn =>
    Reduction.honestTranscriptDist init impl
      (oracleReduction.{0} oSpec OStatement).toReduction stmtIn ()

/-- The honest transcript distribution for `RandomQuery` is definitionally the simulator
distribution. -/
theorem honestTranscriptDist_oracleReduction_evalDist
    (stmtIn : StmtIn × (∀ i, OStmtIn OStatement i)) :
    evalDist (Reduction.honestTranscriptDist init impl
        (oracleReduction.{0} oSpec OStatement).toReduction stmtIn ()) =
      evalDist (transcriptSimulator (oSpec := oSpec) (OStatement := OStatement)
        (init := init) (impl := impl) stmtIn) := rfl

/-- `RandomQuery` is perfectly HVZK as an oracle reduction: it has no private witness, and the
single verifier challenge is sampled by the same honest challenge implementation in the simulator. -/
theorem oracleReduction_perfectHVZK :
    OracleReduction.perfectHVZK init impl (relIn OStatement)
      (oracleReduction.{0} oSpec OStatement)
      (transcriptSimulator (oSpec := oSpec) (OStatement := OStatement)
        (init := init) (impl := impl)) := by
  intro stmtIn () _
  exact (honestTranscriptDist_oracleReduction_evalDist (oSpec := oSpec)
    (OStatement := OStatement) (init := init) (impl := impl) stmtIn).symm

/-- Perfect HVZK implies statistical HVZK for `RandomQuery` at every error budget. -/
theorem oracleReduction_statisticalHVZK (ε : NNReal) :
    OracleReduction.statisticalHVZK init impl (relIn OStatement)
      (oracleReduction.{0} oSpec OStatement)
      (transcriptSimulator (oSpec := oSpec) (OStatement := OStatement)
        (init := init) (impl := impl)) ε :=
  (oracleReduction_perfectHVZK (oSpec := oSpec) (OStatement := OStatement)
    (init := init) (impl := impl)).statisticalHVZK ε

/-- `RandomQuery` has an explicit perfect-HVZK simulator as an oracle reduction. -/
theorem oracleReduction_isHVZK :
    OracleReduction.isHVZK init impl (relIn OStatement) (oracleReduction.{0} oSpec OStatement) :=
  ⟨transcriptSimulator (oSpec := oSpec) (OStatement := OStatement)
      (init := init) (impl := impl),
    oracleReduction_perfectHVZK (oSpec := oSpec) (OStatement := OStatement)
      (init := init) (impl := impl)⟩

/-- `RandomQuery` has statistical HVZK at every error budget as an oracle reduction. -/
theorem oracleReduction_isStatHVZK (ε : NNReal) :
    OracleReduction.isStatHVZK init impl (relIn OStatement)
      (oracleReduction.{0} oSpec OStatement) ε :=
  (oracleReduction_isHVZK (oSpec := oSpec) (OStatement := OStatement)
    (init := init) (impl := impl)).isStatHVZK ε

#print axioms RandomQuery.transcriptSimulator
#print axioms RandomQuery.honestTranscriptDist_oracleReduction_evalDist
#print axioms RandomQuery.oracleReduction_perfectHVZK
#print axioms RandomQuery.oracleReduction_statisticalHVZK
#print axioms RandomQuery.oracleReduction_isHVZK
#print axioms RandomQuery.oracleReduction_isStatHVZK

-- def langIn : Set (Unit × (∀ _ : Fin 2, OStatement)) := setOf fun ⟨(), oracles⟩ =>
--   oracles 0 = oracles 1

-- def langOut : Set ((Query OStatement) × (∀ _ : Fin 2, OStatement)) := setOf fun ⟨q, oracles⟩ =>
--   answer (oracles 0) q = answer (oracles 1) q

def stateFunction [Inhabited OStatement] : (oracleVerifier oSpec OStatement).StateFunction init impl
    (relIn OStatement).language (relOut OStatement).language where
  toFun
  | 0 => fun ⟨_, oracles⟩ _ => oracles 0 = oracles 1
  | 1 => fun ⟨_, oracles⟩ chal =>
    let q : Query OStatement := by simpa [pSpec] using chal ⟨0, by aesop⟩
    answer (oracles 0) q = answer (oracles 1) q
  toFun_empty := fun stmt => by simp
  toFun_next | 0 => fun hDir ⟨stmt, oStmt⟩ tr h => by simp_all
  toFun_full := fun ⟨stmt, oStmt⟩ tr h => by
    -- The verifier deterministically returns `(tr.challenges ⟨0, rfl⟩, oStmt)`. If the answers at
    -- that query differ (hypothesis `h`), the output is never in `relOut.language`, so prob is 0.
    rw [probEvent_eq_zero_iff]
    intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    simp only [OracleVerifier.toVerifier, oracleVerifier, Verifier.run, StateT.run'_eq,
      support_map, Set.mem_image, Prod.exists] at hx
    obtain ⟨val, s', hmem, heq⟩ := hx
    erw [simulateQ_pure] at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    obtain ⟨rfl, -⟩ := hmem
    -- `x = (tr.challenges ⟨0, rfl⟩, oStmt)`; not in `relOut.language` since answers differ.
    injection heq with hx
    subst x
    simp only [Set.language, relOut, Set.mem_image, Set.mem_setOf_eq, Prod.exists, exists_const,
      exists_eq_right]
    intro hrel
    exact h (by simpa [FullTranscript.challenges, pSpec] using hrel)

/-- The round-by-round extractor is trivial since the output witness is `Unit`. -/
def rbrExtractor : Extractor.RoundByRound oSpec
    (StmtIn × (∀ _ : Fin 2, OStatement)) WitIn WitOut (pSpec OStatement) (fun _ => Unit) where
  eqIn := rfl
  extractMid := fun _ _ _ _ => ()
  extractOut := fun _ _ _ => ()

/-- The knowledge state function for the `RandomQuery` oracle reduction. -/
def knowledgeStateFunction :
    (oracleVerifier oSpec OStatement).KnowledgeStateFunction init impl
    (relIn OStatement) (relOut OStatement) (rbrExtractor oSpec OStatement) where
  toFun
  | 0 => fun ⟨_, oracles⟩ _ _ => oracles 0 = oracles 1
  | 1 => fun ⟨_, oracles⟩ chal _ =>
    let q : Query OStatement := by simpa [pSpec] using chal ⟨0, by aesop⟩
    answer (oracles 0) q = answer (oracles 1) q
  toFun_empty := fun stmt => by simp
  toFun_next | 0 => fun hDir ⟨stmt, oStmt⟩ tr h => by simp_all
  toFun_full := fun ⟨stmt, oStmt⟩ tr witOut => by
    -- Bind via `intro` to avoid an expensive `isDefEq` against the heavy `verifier.run` field type.
    intro h
    rw [gt_iff_lt, probEvent_pos_iff] at h
    obtain ⟨x, hx, hrel⟩ := h
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    -- The verifier deterministically returns `(tr.challenges ⟨0, rfl⟩, oStmt)`.
    simp only [OracleVerifier.toVerifier, oracleVerifier, Verifier.run, StateT.run'_eq,
      support_map, Set.mem_image, Prod.exists] at hx
    obtain ⟨val, s', hmem, heq⟩ := hx
    erw [simulateQ_pure] at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    obtain ⟨rfl, -⟩ := hmem
    injection heq with hxout
    subst x
    -- `hrel` is the output relation membership; the goal is the `toFun` body for the last round.
    simp only [relOut, Set.mem_setOf_eq] at hrel
    simpa [FullTranscript.challenges, pSpec] using hrel

variable [Fintype (Query OStatement)] [∀ q, DecidableEq (O.toOC.spec q)]

instance : Fintype ((pSpec OStatement).Challenge ⟨0, by simp⟩) := by
  dsimp [pSpec, ProtocolSpec.Challenge]; infer_instance

open NNReal

/-- The `RandomQuery` oracle reduction is round-by-round knowledge sound.

  The key fact governing the soundness of this reduction is a property of the form
  `∀ a b : OStatement, a ≠ b → #{q | oracle a q = oracle b q} ≤ d`.
  In other words, the oracle instance has distance at most `d`.
-/
@[simp]
theorem oracleVerifier_rbrKnowledgeSoundness [Nonempty (Query OStatement)]
    {d : ℕ} (hDist : distanceLE O d) :
    (oracleVerifier oSpec OStatement).rbrKnowledgeSoundness init impl
      (relIn OStatement)
      (relOut OStatement)
      (fun _ => (d : ℝ≥0) / (Fintype.card (Query OStatement) : ℝ≥0)) := by
  unfold OracleVerifier.rbrKnowledgeSoundness Verifier.rbrKnowledgeSoundness
  refine ⟨fun _ => Unit, rbrExtractor oSpec OStatement,
    knowledgeStateFunction oSpec OStatement, ?_⟩
  intro ⟨_, oracles⟩ _ rbrP i
  have : i = ⟨0, by simp⟩ := by aesop
  subst i
  dsimp at oracles
  simp [Prover.runWithLogToRound, Prover.runToRound, rbrExtractor, knowledgeStateFunction]
  erw [simulateQ_bind]
  simp only [MonadLift.monadLift, liftM, monadLift, MonadLiftT.monadLift]
  simp only [pure_bind, bind_assoc, map_pure, StateT.run'_eq, StateT.run_bind, map_bind]
  erw [simulateQ_pure]
  simp only [loggingOracle, simulateQ_pure, WriterT.run_pure, pure_bind, map_pure,
    StateT.run_pure, StateT.run_bind, QueryImpl.simulateQ_add_liftComp_right]
  erw [simulateQ_bind, QueryImpl.simulateQ_add_liftComp_right]
  erw [simulateQ_spec_query]
  simp only [QueryImpl.liftTarget_apply, challengeQueryImpl, StateT.run_bind, map_bind, pure_bind]
  classical
  rw [probEvent_bind_eq_tsum]
  refine le_trans (ENNReal.tsum_le_tsum
    (g := fun s => Pr[= s | init] * ((d : ENNReal) / (Fintype.card (Query OStatement) : ENNReal)))
    fun s => mul_le_mul' le_rfl ?_) ?_
  · rw [probEvent_bind_eq_tsum]
    have hc2 : ∀ (x : Query OStatement × σ),
        ((fun y => y.1) <$> (simulateQ
            (impl + QueryImpl.liftTarget (StateT σ ProbComp)
              (challengeQueryImpl (pSpec := pSpec OStatement)))
            (pure (default, x.1, ∅))).run x.2)
        = (pure (default, x.1, ∅) :
            ProbComp (Transcript 0 (pSpec OStatement) × Query OStatement ×
              (oSpec + [(pSpec OStatement).Challenge]ₒ'challengeOracleInterface).QueryLog)) := by
      intro x
      erw [simulateQ_pure]
      rw [StateT.run_pure, map_pure]
    apply le_trans (le_of_eq (tsum_congr fun x =>
      congrArg (fun mz => _ * probEvent mz _) (hc2 x)))
    rw [← probEvent_bind_eq_tsum]
    erw [StateT.run_lift]
    simp only [bind_assoc, pure_bind]
    show (probEvent ((fun x => (default, x, ∅)) <$> ($ᵗ _)) _) ≤ _
    rw [probEvent_map]
    simp only [Function.comp_def, ProtocolSpec.Transcript.concat, Fin.snoc]
    rw [probEvent_uniformSample]
    rcases Classical.em (oracles 0 = oracles 1) with h01 | h01
    · simp [h01]
    · refine ENNReal.div_le_div_right ?_ _
      refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_))
        (Nat.cast_le.mpr (hDist (oracles 0) (oracles 1) h01))
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      simpa using hq.2
  · rw [ENNReal.tsum_mul_right]
    exact le_trans (mul_le_mul' tsum_probOutput_le_one le_rfl) (by rw [one_mul])

end RandomQuery

-- namespace RandomQueryAndReduceClaim

-- /-!
--   Random query where we throw away the second oracle, and replace with the response:
--   - The input relation is `{ ⟨⟨_, 𝒪⟩, _⟩ | 𝒪 0 = 𝒪 1 }`.
--   - The output relation is `{ ⟨⟨q, r⟩, 𝒪⟩, _⟩ | oracle (𝒪 0) q = r }`.
--   - The (oracle) verifier sends a single random query `q` to the prover, queries the oracle
--     `𝒪 1` at
--     `q` to get response `r`, returns `(q, r)` as the output statement, and drop `𝒪 1` from the
--     output oracle statement.

--   This is just the concatenation of `RandomQuery` and `ReduceClaim`.
-- -/

-- @[reducible, simp] def StmtIn := Unit
-- @[reducible, simp] def StmtOut := Query OStatement × Response OStatement

-- @[reducible, simp] def OStmtIn := fun _ : Fin 2 => OStatement
-- @[reducible, simp] def OStmtOut := fun _ : Fin 1 => OStatement

-- @[reducible, simp] def WitIn := Unit
-- @[reducible, simp] def WitOut := Unit

-- @[reducible, simp]
-- def relIn : (StmtIn × ∀ i, OStmtIn OStatement i) → WitIn → Prop := fun ⟨(), oracles⟩ () =>
--   oracles 0 = oracles 1

-- /--
-- The final relation states that the first oracle `oStmt ()` agrees with the response `r` at the
-- query `q`.
-- -/
-- @[reducible, simp]
-- def relOut : (StmtOut OStatement × ∀ i, OStmtOut OStatement i) → WitOut → Prop :=
--   fun ⟨⟨q, r⟩, oStmt⟩ () => answer (oStmt 0) q = r

-- -- @[reducible]
-- -- def pSpec : ProtocolSpec 1 := ![(.V_to_P, Query OStatement)]

-- -- instance : ∀ i, OracleInterface ((pSpec OStatement).Message i) | ⟨0, h⟩ => nomatch h
-- -- @[reducible, simp] instance : ∀ i, SampleableType ((pSpec OStatement).Challenge i)
-- --   | ⟨0, _⟩ => by dsimp [pSpec, ProtocolSpec.Challenge]; exact inst

-- -- instance : OracleContext.Lens
-- --     RandomQuery.StmtIn (RandomQuery.StmtOut OStatement)
-- --     StmtIn (StmtOut OStatement)
-- --     (RandomQuery.OStmtIn OStatement) (RandomQuery.OStmtOut OStatement)
-- --     (OStmtIn OStatement) (OStmtOut OStatement)
-- --     RandomQuery.WitIn RandomQuery.WitOut
-- --     WitIn WitOut where
-- --   projStmt := fun () => ()
-- --   liftStmt := fun () => ()
-- --   projOStmt := fun i => fun () => ()
-- --   simOStmt := fun i => fun () => ()
-- --   liftOStmt := fun i => fun () => ()
-- --   projWit := fun () => ()
-- --   liftWit := fun () => ()

-- end RandomQueryAndReduceClaim
