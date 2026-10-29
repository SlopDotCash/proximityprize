/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Component.SendWitness

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ProximityPrize.Extensions.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.OracleZeroKnowledge
import ArkLib.OracleReduction.Security.ZeroKnowledge
import ProximityPrize.Extensions.OracleReduction.Composition.Sequential.Append
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

local instance : MeasurableSpace (FullTranscript (pSpec Witness)) := ⊤

instance : ∀ i, SampleableType ((pSpec Witness).Challenge i) | ⟨0, h⟩ => nomatch h

instance : ProverOnly (pSpec Witness) where
  prover_first' := by simp

variable {Statement} {Witness}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (relIn : Set (Statement × Witness))

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
  unfold Reduction.honestTranscriptDist
  rw [reduction_run]
  simp only [map_pure, OptionT.run_pure, simulateQ_pure, StateT.run'_eq,
    StateT.run_pure, bind_pure_comp]
  rw [OptionT.evalDist_eq_comap_some, OptionT.evalDist_eq_comap_some]
  simp only [OptionT.run_mk, OptionT.run_pure, OracleComp.evalDist_map_const, evalDist_pure]

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
    extractIn := fun _ wit => wit
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
      rw [gt_iff_lt, OracleComp.OptionT.prEvent_mk_pos_iff] at hpr
      obtain ⟨x, hx, hrel⟩ := hpr
      simp only [support_bind, Set.mem_iUnion, exists_prop] at hx
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

#print axioms SendWitness.reduction_rbr_knowledge_soundness
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

end OracleReduction

end SendWitness

namespace SendSingleWitness

/-!
  A special case of `SendWitness` oracle reduction where there is only one witness. We implicitly
  convert to `fun _ : Fin 1 => Witness`.
-/

variable {ιₛ : Type} (OStatement : ιₛ → Type) [∀ i, OracleInterface (OStatement i)]
  (Witness : Type) [OracleInterface Witness]

variable {Statement} {OStatement} {Witness}

local instance : MeasurableSpace (FullTranscript (oraclePSpec Witness)) := ⊤


variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (oRelIn : Set ((Statement × (∀ i, OStatement i)) × Witness))

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
  unfold Reduction.honestTranscriptDist
  have _inst : ProverOnly (oraclePSpec Witness) := { prover_first' := by simp }
  simp only [OracleReduction.toReduction, oracleReduction]
  rw [Reduction.run_of_prover_first]
  simp only [oracleProver, id_eq, liftM_pure, pure_bind, bind_pure_comp,
    OracleVerifier.toVerifier, oracleVerifier]
  erw [simulateQ_pure]
  simp only [StateT.run'_eq, StateT.run_pure, map_pure, bind_pure_comp]
  rw [OptionT.evalDist_eq_comap_some, OptionT.evalDist_eq_comap_some]
  simp only [OptionT.run_mk, OptionT.run_pure, OracleComp.evalDist_map_const, evalDist_pure]
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
    extractIn := fun _ wit => wit
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
      rw [gt_iff_lt, OracleComp.OptionT.prEvent_mk_pos_iff] at hpr
      obtain ⟨x, hx, hrel⟩ := hpr
      simp only [support_bind, Set.mem_iUnion, exists_prop] at hx
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

#print axioms SendSingleWitness.oracleReduction_rbr_knowledge_soundness
#print axioms SendSingleWitness.oracleTranscriptSimulator
#print axioms SendSingleWitness.honestTranscriptDist_oracleReduction_evalDist
#print axioms SendSingleWitness.oracleReduction_perfectHVZK_of_witness_eq
#print axioms SendSingleWitness.oracleReduction_statisticalHVZK_of_witness_eq
#print axioms SendSingleWitness.oracleReduction_isHVZK_of_witness_eq
#print axioms SendSingleWitness.oracleReduction_isStatHVZK_of_witness_eq

end SendSingleWitness
