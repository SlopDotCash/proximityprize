/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.OracleZeroKnowledge
import ArkLib.OracleReduction.Security.ZeroKnowledge
import ArkLib.OracleReduction.Composition.Sequential.Append
import Mathlib.Data.FinEnum

/-!
# Simple Oracle Reduction - SendWitness

This file contains the (oracle) reduction for the trivial one-message protocol where the prover
sends the (entire) witness to the verifier. There are two variants:

1. For oracle reduction: the witness is an indexed family of types, and sent in a single oracle
  message to the verifier (using the derived indexed product instance for oracle interface).

  We also define a simpler variant where one sends a single witness (converted to be indexed by
  `Fin 1`).

2. For reduction: the witness is a type, and sent as a statement to the verifier.
-/

open OracleSpec OracleComp OracleQuery ProtocolSpec Function Equiv

variable {ι : Type} (oSpec : OracleSpec ι) (Statement : Type)

/-- Reducing the query-implementation run of an `OptionT`-pure verifier output: a deterministic
`pure a` computation has `run'`-support exactly `{some a}`. Used to discharge the `toFun_full`
obligations of the `SendWitness` round-by-round knowledge-soundness proofs, whose verifiers are
deterministic. -/
theorem simulateQ_optionT_pure_run' {α σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (s : σ) (a : α) :
    (simulateQ impl (pure a : OptionT (OracleComp oSpec) α)).run' s = pure (some a) := by
  change (simulateQ impl (pure (some a) : OracleComp oSpec (Option α))).run' s = _
  rw [simulateQ_pure]
  change Prod.fst <$> (pure (some a) : StateT σ ProbComp _).run s = _
  rw [StateT.run_pure]; simp [map_pure]

namespace SendWitness

/-!
  First, the reduction version (no oracle statements)
-/

section Reduction

variable (Witness : Type)

@[reducible, simp]
def pSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[Witness]⟩

instance : ∀ i, VCVCompatible ((pSpec Witness).Challenge i) | ⟨0, h⟩ => nomatch h

instance : ∀ i, SampleableType ((pSpec Witness).Challenge i) | ⟨0, h⟩ => nomatch h

instance : ProverOnly (pSpec Witness) where
  prover_first' := by simp

@[inline, specialize]
def prover : Prover oSpec Statement Witness (Statement × Witness) Unit (pSpec Witness) where
  PrvState
  | 0 => Statement × Witness
  | 1 => Statement × Witness
  input := id
  sendMessage | ⟨0, _⟩ => fun ⟨stmt, wit⟩ => pure (wit, ⟨stmt, wit⟩)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨stmt, wit⟩ => pure (⟨stmt, wit⟩, ())

@[inline, specialize]
def verifier : Verifier oSpec Statement (Statement × Witness) (pSpec Witness) where
  verify := fun stmt transcript => pure ⟨stmt, transcript 0⟩

@[inline, specialize]
def reduction : Reduction oSpec Statement Witness (Statement × Witness) Unit (pSpec Witness) where
  prover := prover oSpec Statement Witness
  verifier := verifier oSpec Statement Witness

variable {Statement} {Witness}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (relIn : Set (Statement × Witness))

@[reducible, simp]
def toRelOut : Set ((Statement × Witness) × Unit) :=
  Prod.fst ⁻¹' relIn

/-- Running the `SendWitness` reduction deterministically sends the witness and returns the
  unchanged statement-witness pair. -/
theorem reduction_run (stmtIn : Statement) (witIn : Witness) :
    (reduction oSpec Statement Witness).run stmtIn witIn =
      (pure ((fun i => match i with | ⟨0, _⟩ => witIn, (stmtIn, witIn), ()),
        (stmtIn, witIn)) : OptionT (OracleComp _) _) := by
  rw [Reduction.run_of_prover_first]
  simp only [reduction, prover, verifier, id_eq]
  rfl

/-- The simulator for the `SendWitness` reduction when the relation's witness is determined by
the input statement. It emits the single prover message that the honest prover would send for
`witOf stmt`. -/
def transcriptSimulator (witOf : Statement → Witness) :
    Reduction.TranscriptSimulator oSpec Statement (pSpec Witness) :=
  fun stmt => pure (fun i => match i with | ⟨0, _⟩ => witOf stmt)

/-- The honest transcript distribution for `SendWitness` is the deterministic one-message
transcript containing the actual witness. -/
theorem honestTranscriptDist_reduction_evalDist
    (stmtIn : Statement) (witIn : Witness) :
    evalDist (Reduction.honestTranscriptDist init impl
        (reduction oSpec Statement Witness) stmtIn witIn) =
      evalDist (pure (fun i => match i with | ⟨0, _⟩ => witIn) :
        OptionT ProbComp (FullTranscript (pSpec Witness))) := by
  apply evalDist_ext
  intro transcript
  classical
  unfold Reduction.honestTranscriptDist
  rw [reduction_run]
  simp only [map_pure, OptionT.run_pure, simulateQ_pure, StateT.run'_eq,
    StateT.run_pure, bind_pure_comp]
  rw [OptionT.probOutput_eq, OptionT.probOutput_eq]
  simp [probOutput_map_const, HasEvalPMF.probFailure_eq_zero]

/-- `SendWitness` is perfectly HVZK for relations whose witness is determined by the statement.
The hypothesis is necessary: the protocol transcript reveals the witness. -/
theorem reduction_perfectHVZK_of_witness_eq
    (witOf : Statement → Witness)
    (hRel : ∀ stmt wit, (stmt, wit) ∈ relIn → wit = witOf stmt) :
    Reduction.perfectHVZK init impl relIn
      (reduction oSpec Statement Witness)
      (transcriptSimulator (oSpec := oSpec) (Statement := Statement) (Witness := Witness)
        witOf) := by
  intro stmt wit hrel
  unfold transcriptSimulator
  rw [← hRel stmt wit hrel]
  exact (honestTranscriptDist_reduction_evalDist (oSpec := oSpec) (init := init)
    (impl := impl) stmt wit).symm

/-- Perfect HVZK implies statistical HVZK for the statement-determined-witness
`SendWitness` relation at every error budget. -/
theorem reduction_statisticalHVZK_of_witness_eq
    (witOf : Statement → Witness)
    (hRel : ∀ stmt wit, (stmt, wit) ∈ relIn → wit = witOf stmt) (ε : NNReal) :
    Reduction.statisticalHVZK init impl relIn
      (reduction oSpec Statement Witness)
      (transcriptSimulator (oSpec := oSpec) (Statement := Statement) (Witness := Witness)
        witOf) ε :=
  (reduction_perfectHVZK_of_witness_eq (oSpec := oSpec) (Statement := Statement)
    (Witness := Witness) (init := init) (impl := impl) (relIn := relIn) witOf hRel).statisticalHVZK ε

/-- `SendWitness` has an explicit perfect-HVZK simulator when the relation's witness is
statement-determined. -/
theorem reduction_isHVZK_of_witness_eq
    (witOf : Statement → Witness)
    (hRel : ∀ stmt wit, (stmt, wit) ∈ relIn → wit = witOf stmt) :
    Reduction.isHVZK init impl relIn (reduction oSpec Statement Witness) :=
  ⟨transcriptSimulator (oSpec := oSpec) (Statement := Statement) (Witness := Witness) witOf,
    reduction_perfectHVZK_of_witness_eq (oSpec := oSpec) (Statement := Statement)
      (Witness := Witness) (init := init) (impl := impl) (relIn := relIn) witOf hRel⟩

/-- `SendWitness` has statistical HVZK at every error budget when the relation's witness is
statement-determined. -/
theorem reduction_isStatHVZK_of_witness_eq
    (witOf : Statement → Witness)
    (hRel : ∀ stmt wit, (stmt, wit) ∈ relIn → wit = witOf stmt) (ε : NNReal) :
    Reduction.isStatHVZK init impl relIn (reduction oSpec Statement Witness) ε :=
  (reduction_isHVZK_of_witness_eq (oSpec := oSpec) (Statement := Statement)
    (Witness := Witness) (init := init) (impl := impl) (relIn := relIn) witOf hRel).isStatHVZK ε

open Classical in
/-- The `SendWitness` reduction satisfies perfect completeness. -/
@[simp]
theorem reduction_completeness :
    (reduction oSpec Statement Witness).perfectCompleteness init impl relIn (toRelOut relIn) := by
  simp only [Reduction.perfectCompleteness, Reduction.completeness, Reduction.completenessFromRun, ENNReal.coe_zero, tsub_zero]
  intro stmtIn witIn hIn
  rw [reduction_run]
  simp only [OptionT.run_pure, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp
  · intro x hx
    rw [OptionT.mem_support_iff, OptionT.run_mk] at hx
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
    obtain ⟨s, _, hx⟩ := hx
    cases hx
    refine ⟨?_, rfl⟩
    simpa [toRelOut] using hIn

/-- The `SendWitness` reduction satisfies perfect RBR knowledge soundness.

  The protocol `pSpec Witness` is `ProverOnly` (single P_to_V round), so `ChallengeIdx` is empty
  and the RBR knowledge-soundness condition is vacuously true. The extractor reads the witness
  directly from the transcript (round 0), and the knowledge state function tracks membership in
  `relIn`. -/
theorem reduction_rbr_knowledge_soundness :
    (reduction oSpec Statement Witness).verifier.rbrKnowledgeSoundness
      init impl relIn (toRelOut relIn) 0 := by
  -- Construct the round-by-round extractor: WitMid = fun _ => Witness
  refine ⟨fun _ => Witness, {
    eqIn := rfl
    -- extractMid at round 0: pass through the intermediate witness (identity)
    extractMid := fun ⟨0, _⟩ _stmt _tr witMid => witMid
    -- extractOut: read witness from the full transcript
    extractOut := fun _stmt tr _ => tr ⟨0, by omega⟩
  }, {
    -- Knowledge state function: tracks (stmt, wit) ∈ relIn
    toFun := fun _ stmt _tr wit => (stmt, wit) ∈ relIn
    toFun_empty := fun _ _ => by simp
    -- toFun_next: for m with pSpec.dir m = .P_to_V, the KSF is preserved
    toFun_next := fun ⟨0, _⟩ _ _stmt _tr _msg _witMid h => h
    -- toFun_full: if verifier output is in toRelOut, then the extracted witness is in relIn
    toFun_full := fun stmt tr witOut hpr => by
      -- The verifier returns ⟨stmt, tr 0⟩, and toRelOut = Prod.fst ⁻¹' relIn,
      -- so (⟨stmt, tr 0⟩, witOut) ∈ toRelOut relIn means (stmt, tr 0) ∈ relIn.
      rw [gt_iff_lt, probEvent_pos_iff] at hpr
      obtain ⟨x, hx, hrel⟩ := hpr
      rw [OptionT.mem_support_iff] at hx
      simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
      obtain ⟨s, _, hx⟩ := hx
      simp only [reduction, verifier, Verifier.run] at hx
      rw [simulateQ_optionT_pure_run'] at hx
      simp only [support_pure, Set.mem_singleton_iff] at hx
      cases (Option.some.inj hx)
      exact hrel
  }, ?_⟩
  -- The final quantifier: ∀ i : ChallengeIdx (pSpec Witness), ... is vacuously true
  -- because pSpec Witness has only P_to_V rounds, so ChallengeIdx is empty.
  intro _stmtIn _witIn _prover ⟨⟨0, _⟩, hdir⟩
  -- hdir : (pSpec Witness).dir ⟨0, _⟩ = .V_to_P, but the direction is .P_to_V
  exact absurd hdir (by simp [pSpec])

#print axioms SendWitness.transcriptSimulator
#print axioms SendWitness.honestTranscriptDist_reduction_evalDist
#print axioms SendWitness.reduction_perfectHVZK_of_witness_eq
#print axioms SendWitness.reduction_statisticalHVZK_of_witness_eq
#print axioms SendWitness.reduction_isHVZK_of_witness_eq
#print axioms SendWitness.reduction_isStatHVZK_of_witness_eq

end Reduction

/-!
  Now, the oracle reduction version
-/

section OracleReduction

variable {ιₛ : Type} (OStatement : ιₛ → Type) [∀ i, OracleInterface (OStatement i)]
  {ιw : Type} [FinEnum ιw] (Witness : ιw → Type) [∀ i, OracleInterface (Witness i)]

@[reducible, simp]
def oraclePSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[∀ i, Witness i]⟩

-- instance : IsEmpty (oraclePSpec Witness).ChallengeIdx where
--   false := by aesop
-- instance : ∀ i, OracleInterface ((oraclePSpec Witness).Message i)
--   | ⟨0, _⟩ => OracleInterface.instForall _
-- instance : ∀ i, VCVCompatible ((oraclePSpec Witness).Challenge i)
--   | ⟨0, _⟩ => by aesop

/-- The oracle prover for the `SendWitness` oracle reduction.

For each round `i : Fin (FinEnum.card ιw)`, the prover sends the witness
`wit (FinEnum.equiv.symm i)` to the verifier.
-/
@[inline, specialize]
def oracleProver : OracleProver oSpec
    Statement OStatement (∀ i, Witness i)
    Statement (OStatement ⊕ᵥ Witness) Unit
    (oraclePSpec Witness) where
  PrvState := fun _ => (Statement × (∀ i, OStatement i)) × (∀ i, Witness i)
  input := id
  sendMessage | ⟨0, _⟩ => fun ⟨stmt, wit⟩ => pure (wit, ⟨stmt, wit⟩)
  -- No challenge is sent to the prover
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨⟨stmt, oStmt⟩, wit⟩ => pure (⟨stmt, Sum.rec oStmt wit⟩, ())

-- /-- The oracle verifier for the `SendWitness` oracle reduction.

-- It receives the input statement `stmt` and returns it, and also specifying the combination of
-- `OStatement` and `Witness` as the output oracle statements.
-- -/
-- @[inline, specialize]
-- def oracleVerifier : OracleVerifier (oraclePSpec Witness) oSpec
--     Statement Statement OStatement (OStatement ⊕ᵥ Witness) where
--   verify := fun stmt _ => pure stmt
--   -- ιₛ ⊕ ιw ↪ ιₛ ⊕ (oraclePSpec Witness).MessageIdx
--   embed := Embedding.sumMap (.refl _)
--     -- ιw ↪ (oraclePSpec Witness).MessageIdx
--     (Equiv.toEmbedding
--       -- ιw ≃ (oraclePSpec Witness).MessageIdx
--       -- after unfolding : ιw ≃ { i : Fin (FinEnum.card ιw) // True }
--       (.trans FinEnum.equiv -- ιw ≃ Fin (FinEnum.card ιw)
--         <| .symm -- { i : Fin (FinEnum.card ιw) // True } ≃ Fin (FinEnum.card ιw)
--         <| .subtypeUnivEquiv (by simp)))
--   hEq := by intro i; rcases i <;> simp

-- @[inline, specialize]
-- def oracleReduction : OracleReduction (oraclePSpec Witness) oSpec
--     Statement (∀ i, Witness i) Statement Unit
--     OStatement (OStatement ⊕ᵥ Witness) where
--   prover := oracleProver oSpec Statement OStatement Witness
--   verifier := oracleVerifier oSpec Statement OStatement Witness

-- variable {Statement} {OStatement} {Witness} [oSpec.Fintype]
--   (oRelIn : Statement × (∀ i, OStatement i) → (∀ i, Witness i) → Prop)

-- @[reducible, simp]
-- def toORelOut : Statement × (∀ i, (OStatement ⊕ᵥ Witness) i) → Unit → Prop :=
--   fun ⟨stmt, oStmtAndWit⟩ _ =>
--     oRelIn ⟨stmt, fun i => oStmtAndWit (Sum.inl i)⟩ (fun i => oStmtAndWit (Sum.inr i))

end OracleReduction

end SendWitness

namespace SendSingleWitness

/-!
  A special case of `SendWitness` oracle reduction where there is only one witness. We implicitly
  convert to `fun _ : Fin 1 => Witness`.
-/

variable {ιₛ : Type} (OStatement : ιₛ → Type) [∀ i, OracleInterface (OStatement i)]
  (Witness : Type) [OracleInterface Witness]

@[reducible, simp]
def oraclePSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[Witness]⟩

/-- The oracle prover for the `SendSingleWitness` oracle reduction.

The prover sends the witness `wit` to the verifier as the only oracle message.
-/
@[inline, specialize]
def oracleProver : OracleProver oSpec
    Statement OStatement Witness
    Statement (OStatement ⊕ᵥ (fun _ : Fin 1 => Witness)) Unit
    (oraclePSpec Witness) where
  PrvState := fun _ => (Statement × (∀ i, OStatement i)) × Witness
  input := id
  sendMessage | ⟨0, _⟩ => fun ⟨stmt, wit⟩ => pure (wit, ⟨stmt, wit⟩)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨⟨stmt, oStmt⟩, wit⟩ => pure (⟨stmt, Sum.rec oStmt (fun _ => wit)⟩, ())

/-- The oracle verifier for the `SendSingleWitness` oracle reduction.

The verifier receives the input statement `stmt` and returns it, and also specifying the oracle
message as the output oracle statement.
-/
@[inline, specialize]
def oracleVerifier : OracleVerifier oSpec
    Statement OStatement Statement (OStatement ⊕ᵥ (fun _ : Fin 1 => Witness))
    (oraclePSpec Witness) where
  verify := fun stmt _ => pure stmt
  embed := .sumMap (.refl _)
    <| Equiv.toEmbedding
    <|.symm (subtypeUnivEquiv (by aesop))
  hEq := by
    intro i; rcases i with j | j
    · rfl
    · fin_cases j; rfl

@[inline, specialize]
def oracleReduction : OracleReduction oSpec
    Statement OStatement Witness
    Statement (OStatement ⊕ᵥ (fun _ : Fin 1 => Witness)) Unit
    (oraclePSpec Witness) where
  prover := oracleProver oSpec Statement OStatement Witness
  verifier := oracleVerifier oSpec Statement OStatement Witness
instance instOracleVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent (oracleVerifier oSpec Statement OStatement Witness) where
  hCohInl i k h := by
    rcases i with i | i
    · simp only [oracleVerifier, Embedding.sumMap, Function.Embedding.coeFn_mk, Sum.map_inl,
        Embedding.refl_apply] at h
      obtain rfl := Sum.inl.inj h
      rfl
    · simp only [oracleVerifier, Embedding.sumMap, Function.Embedding.coeFn_mk, Sum.map_inr] at h
      cases h
  hCohInr i k h := by
    rcases i with i | i
    · simp only [oracleVerifier, Embedding.sumMap, Function.Embedding.coeFn_mk, Sum.map_inl,
        Embedding.refl_apply] at h
      cases h
    · simp only [oracleVerifier, Embedding.sumMap, Function.Embedding.coeFn_mk, Sum.map_inr] at h
      obtain rfl := Sum.inr.inj h
      fin_cases i
      rfl


variable {Statement} {OStatement} {Witness}

omit [(i : ιₛ) → OracleInterface (OStatement i)] [OracleInterface Witness] in
theorem oracleProver_run {stmt : Statement} {oStmt : ∀ i, OStatement i} {wit : Witness} :
    (oracleProver oSpec Statement OStatement Witness).run ⟨stmt, oStmt⟩ wit =
      pure (fun i => by aesop, ⟨stmt, Sum.rec oStmt (fun _ => wit)⟩, ()) := by
  simp only [oraclePSpec, Fin.vcons_fin_zero, Nat.reduceAdd, ChallengeIdx, Challenge,
    Fin.isValue, id_eq]
  change (pure _ : OracleComp _ _) = pure _
  congr 1; dsimp; congr 1; funext i; fin_cases i; rfl

theorem oracleVerifier_toVerifier_run {stmt : Statement} {oStmt : ∀ i, OStatement i}
    {tr : (oraclePSpec Witness).FullTranscript} :
    (oracleVerifier oSpec Statement OStatement Witness).toVerifier.run ⟨stmt, oStmt⟩ tr =
      pure ⟨stmt, Sum.rec oStmt (fun i => match i with | 0 => tr 0)⟩ := by
  simp only [Verifier.run, OracleVerifier.toVerifier, oracleVerifier]
  erw [simulateQ_pure, pure_bind]
  congr 1
  refine Prod.ext rfl ?_
  funext i
  rcases i with j | j
  · simp only [Embedding.sumMap, Function.Embedding.coeFn_mk, Sum.map_inl,
      Embedding.refl_apply]
  · fin_cases j
    simp only [Embedding.sumMap, Function.Embedding.coeFn_mk, Sum.map_inr]
    rfl

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (oRelIn : Set ((Statement × (∀ i, OStatement i)) × Witness))

@[reducible, simp]
def toORelOut :
    Set ((Statement × (∀ i, (Sum.elim OStatement fun _ : Fin 1 => Witness) i)) × Unit) :=
  setOf (fun ⟨⟨stmt, oStmtAndWit⟩, _⟩ =>
    oRelIn ⟨⟨stmt, fun i => oStmtAndWit (Sum.inl i)⟩, (oStmtAndWit (Sum.inr 0))⟩)

/-- The simulator for `SendSingleWitness` when the sent witness is determined by the public
statement and oracle statement. The transcript has one prover message, so the simulator emits that
publicly determined witness. -/
def oracleTranscriptSimulator (witOf : Statement × (∀ i, OStatement i) → Witness) :
    OracleReduction.TranscriptSimulator oSpec Statement OStatement (oraclePSpec Witness) :=
  fun stmtIn => pure (fun i => match i with | ⟨0, _⟩ => witOf stmtIn)

/-- The honest transcript distribution for `SendSingleWitness` is the deterministic one-message
transcript containing the sent witness. -/
theorem honestTranscriptDist_oracleReduction_evalDist
    (stmt : Statement) (oStmt : ∀ i, OStatement i) (wit : Witness) :
    evalDist (Reduction.honestTranscriptDist init impl
        (oracleReduction oSpec Statement OStatement Witness).toReduction (stmt, oStmt) wit) =
      evalDist (pure (fun i => match i with | ⟨0, _⟩ => wit) :
        OptionT ProbComp (FullTranscript (oraclePSpec Witness))) := by
  apply evalDist_ext
  intro transcript
  classical
  unfold Reduction.honestTranscriptDist
  have _inst : ProverOnly (oraclePSpec Witness) := { prover_first' := by simp }
  simp only [OracleReduction.toReduction, oracleReduction]
  rw [Reduction.run_of_prover_first]
  simp only [oracleProver, id_eq, liftM_pure, pure_bind, bind_pure_comp,
    OracleVerifier.toVerifier, oracleVerifier]
  erw [simulateQ_pure]
  simp only [StateT.run'_eq, StateT.run_pure, map_pure, bind_pure_comp]
  rw [OptionT.probOutput_eq, OptionT.probOutput_eq]
  simp [probOutput_map_const, HasEvalPMF.probFailure_eq_zero]
  rfl

/-- `SendSingleWitness` is perfectly HVZK when the relation's witness is determined by the public
statement and oracle statement. The hypothesis is necessary: the protocol transcript reveals the
sent witness. -/
theorem oracleReduction_perfectHVZK_of_witness_eq
    (witOf : Statement × (∀ i, OStatement i) → Witness)
    (hRel : ∀ stmtIn wit, (stmtIn, wit) ∈ oRelIn → wit = witOf stmtIn) :
    OracleReduction.perfectHVZK init impl oRelIn
      (oracleReduction oSpec Statement OStatement Witness)
      (oracleTranscriptSimulator (oSpec := oSpec) (Statement := Statement)
        (OStatement := OStatement) (Witness := Witness) witOf) := by
  intro stmtIn wit hrel
  unfold oracleTranscriptSimulator
  rw [← hRel stmtIn wit hrel]
  exact (honestTranscriptDist_oracleReduction_evalDist (oSpec := oSpec)
    (Statement := Statement) (OStatement := OStatement) (Witness := Witness)
    (init := init) (impl := impl) stmtIn.1 stmtIn.2 wit).symm

/-- Perfect HVZK implies statistical HVZK for `SendSingleWitness` at every error budget. -/
theorem oracleReduction_statisticalHVZK_of_witness_eq
    (witOf : Statement × (∀ i, OStatement i) → Witness)
    (hRel : ∀ stmtIn wit, (stmtIn, wit) ∈ oRelIn → wit = witOf stmtIn) (ε : NNReal) :
    OracleReduction.statisticalHVZK init impl oRelIn
      (oracleReduction oSpec Statement OStatement Witness)
      (oracleTranscriptSimulator (oSpec := oSpec) (Statement := Statement)
        (OStatement := OStatement) (Witness := Witness) witOf) ε :=
  (oracleReduction_perfectHVZK_of_witness_eq (oSpec := oSpec) (Statement := Statement)
    (OStatement := OStatement) (Witness := Witness) (init := init) (impl := impl)
    (oRelIn := oRelIn) witOf hRel).statisticalHVZK ε

/-- `SendSingleWitness` has an explicit perfect-HVZK simulator when the witness is determined by
the public statement and oracle statement. -/
theorem oracleReduction_isHVZK_of_witness_eq
    (witOf : Statement × (∀ i, OStatement i) → Witness)
    (hRel : ∀ stmtIn wit, (stmtIn, wit) ∈ oRelIn → wit = witOf stmtIn) :
    OracleReduction.isHVZK init impl oRelIn
      (oracleReduction oSpec Statement OStatement Witness) :=
  ⟨oracleTranscriptSimulator (oSpec := oSpec) (Statement := Statement)
      (OStatement := OStatement) (Witness := Witness) witOf,
    oracleReduction_perfectHVZK_of_witness_eq (oSpec := oSpec) (Statement := Statement)
      (OStatement := OStatement) (Witness := Witness) (init := init) (impl := impl)
      (oRelIn := oRelIn) witOf hRel⟩

/-- `SendSingleWitness` has statistical HVZK at every error budget when the witness is determined
by the public statement and oracle statement. -/
theorem oracleReduction_isStatHVZK_of_witness_eq
    (witOf : Statement × (∀ i, OStatement i) → Witness)
    (hRel : ∀ stmtIn wit, (stmtIn, wit) ∈ oRelIn → wit = witOf stmtIn) (ε : NNReal) :
    OracleReduction.isStatHVZK init impl oRelIn
      (oracleReduction oSpec Statement OStatement Witness) ε :=
  (oracleReduction_isHVZK_of_witness_eq (oSpec := oSpec) (Statement := Statement)
    (OStatement := OStatement) (Witness := Witness) (init := init) (impl := impl)
    (oRelIn := oRelIn) witOf hRel).isStatHVZK ε

/-- The `SendSingleWitness` oracle reduction satisfies perfect completeness. -/
@[simp]
theorem oracleReduction_completeness (h : NeverFail init) :
    (oracleReduction oSpec Statement OStatement Witness).perfectCompleteness init impl oRelIn
    (toORelOut oRelIn) := by
  simp only [OracleReduction.perfectCompleteness, Reduction.perfectCompleteness,
    Reduction.completeness, Reduction.completenessFromRun, ENNReal.coe_zero, tsub_zero]
  intro ⟨stmt, oStmt⟩ wit hIn
  have _inst : ProverOnly (oraclePSpec Witness) := { prover_first' := by simp }
  simp only [OracleReduction.toReduction, oracleReduction]
  rw [Reduction.run_of_prover_first]
  simp only [oracleProver, id_eq, liftM_pure, pure_bind, bind_pure_comp,
    OracleVerifier.toVerifier, oracleVerifier]
  erw [simulateQ_pure]
  simp only [StateT.run'_eq, StateT.run_pure, map_pure]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp
  · intro x hx
    rw [OptionT.mem_support_iff, OptionT.run_mk] at hx
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
    obtain ⟨s, _, hx⟩ := hx
    cases hx
    refine ⟨?_, ?_⟩
    · simp only [toORelOut, Set.mem_setOf_eq]
      convert hIn using 2
    · refine Prod.ext rfl ?_
      funext i
      rcases i with j | j
      · simp only [Embedding.sumMap, Function.Embedding.coeFn_mk, Sum.map_inl,
          Embedding.refl_apply]
      · fin_cases j
        simp only [Embedding.sumMap, Function.Embedding.coeFn_mk, Sum.map_inr]
        rfl

/-- The `SendSingleWitness` oracle reduction satisfies perfect RBR knowledge soundness.

  The protocol `oraclePSpec Witness` is `ProverOnly` (single P_to_V round), so `ChallengeIdx` is
  empty and the RBR knowledge-soundness condition is vacuously true. -/
theorem oracleReduction_rbr_knowledge_soundness :
    (oracleReduction oSpec Statement OStatement Witness).verifier.rbrKnowledgeSoundness
      init impl oRelIn (toORelOut oRelIn) 0 := by
  -- The oracle verifier's rbrKnowledgeSoundness reduces to the underlying Verifier's
  simp only [OracleReduction.verifier, OracleVerifier.rbrKnowledgeSoundness]
  -- Construct the round-by-round extractor: WitMid = fun _ => Witness
  refine ⟨fun _ => Witness, {
    eqIn := rfl
    extractMid := fun ⟨0, _⟩ _stmt _tr witMid => witMid
    extractOut := fun _stmt tr _ => tr ⟨0, by omega⟩
  }, {
    -- The RBR-KSF input statement is the verifier's input statement `Statement × (∀ i, OStatement i)`
    -- (the witness oracle is sent during the protocol, not part of the input), so the KSF just
    -- tracks membership of `(stmt, wit)` in `oRelIn`.
    toFun := fun _ stmt _tr wit => (stmt, wit) ∈ oRelIn
    toFun_empty := fun _ _ => by simp
    toFun_next := fun ⟨0, _⟩ _ _stmt _tr _msg _witMid h => h
    toFun_full := fun stmt tr witOut hpr => by
      -- The oracle verifier deterministically returns `⟨stmt.1, Sum.rec stmt.2 (fun _ => tr 0)⟩`;
      -- a positive-probability output lying in `toORelOut` therefore witnesses
      -- `oRelIn ⟨⟨stmt.1, stmt.2⟩, tr 0⟩`, which is the goal.
      obtain ⟨stmt, oStmt⟩ := stmt
      rw [gt_iff_lt, probEvent_pos_iff] at hpr
      obtain ⟨x, hx, hrel⟩ := hpr
      rw [OptionT.mem_support_iff] at hx
      simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
      obtain ⟨s, _, hx⟩ := hx
      simp only [oracleReduction] at hx
      erw [oracleVerifier_toVerifier_run, simulateQ_optionT_pure_run'] at hx
      simp only [support_pure, Set.mem_singleton_iff] at hx
      cases (Option.some.inj hx)
      -- `hrel : (⟨stmt, Sum.rec oStmt (fun _ => tr 0)⟩, witOut) ∈ toORelOut oRelIn`, whose
      -- `Sum.inl`/`Sum.inr` projections reduce definitionally to the goal `oRelIn ⟨⟨stmt, oStmt⟩, tr 0⟩`.
      simp only [toORelOut, Set.mem_setOf_eq] at hrel
      exact hrel
  }, ?_⟩
  -- ChallengeIdx is empty for oraclePSpec Witness (single P_to_V round)
  intro _stmtIn _witIn _prover ⟨⟨0, _⟩, hdir⟩
  exact absurd hdir (by simp [oraclePSpec])

#print axioms SendSingleWitness.oracleTranscriptSimulator
#print axioms SendSingleWitness.honestTranscriptDist_oracleReduction_evalDist
#print axioms SendSingleWitness.oracleReduction_perfectHVZK_of_witness_eq
#print axioms SendSingleWitness.oracleReduction_statisticalHVZK_of_witness_eq
#print axioms SendSingleWitness.oracleReduction_isHVZK_of_witness_eq
#print axioms SendSingleWitness.oracleReduction_isStatHVZK_of_witness_eq

end SendSingleWitness
