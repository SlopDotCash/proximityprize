/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.RingSwitching.Prelude
import ArkLib.ProofSystem.RingSwitching.Spec
import ArkLib.OracleReduction.Basic
import ArkLib.OracleReduction.Completeness
import ArkLib.Data.Probability.Instances
import ArkLib.Data.Probability.Notation
import CompPoly.Fields.Binary.Tower.TensorAlgebra

/-!
# Ring-Switching IOP Batching Phase

This module implements the Batching Phase of the ring-switching IOP: steps 1-5.
This phase is the initial phase of the Interactive Oracle Proof and consists of:

## Construction 3.1 - Steps 1-5 (Batching Phase)

We define `(P, V)` as the following IOP, in which both parties have the common
input `[f]`, `s ∈ L`, and `(r_0, ..., r_{ℓ-1}) ∈ L^ℓ`, and `P` has the further
input `t(X_0, ..., X_{ℓ-1}) ∈ K[X_0, ..., X_{ℓ-1}]^⪯1`.

1. `P` computes `ŝ := φ₁(t')(φ₀(r_κ), ..., φ₀(r_{ℓ-1}))` and sends `V` the A-element `ŝ`.
2. `V` decomposes `ŝ =: Σ_{v ∈ {0,1}^κ} ŝ_v ⊗ β_v`.
  `V` requires `s ?= Σ_{v ∈ {0,1}^κ} eq̃(v_0, ..., v_{κ-1}, r_0, ..., r_{κ-1}) ⋅ ŝ_v`.
3. `V` samples batching scalars `(r''_0, ..., r''_{κ-1}) ← L^κ` and sends them to `P`.
4. For each `w ∈ {0,1}^{ℓ'}`,
  `P` decomposes `eq̃(r_κ, ..., r_{ℓ-1}, w_0, ..., w_{ℓ'-1})`
    `=: Σ_{u ∈ {0,1}^κ} A_{w, u} ⋅ β_u`.
  `P` defines the function
    `A: w ↦ Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ A_{w, u}`
    on `{0,1}^{ℓ'}` and writes `A(X_0, ..., X_{ℓ'-1})` for its multilinear extension.
  `P` defines `h(X_0, ..., X_{ℓ'-1}) := A(X_0, ..., X_{ℓ'-1}) ⋅ t'(X_0, ..., X_{ℓ'-1})`.c
5. `V` decomposes `ŝ =: Σ_{u ∈ {0,1}^κ} β_u ⊗ ŝ_u`, and
  sets `s_0 := Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ ŝ_u`.

Input: `witIn = BatchingWitIn, stmtIn = BatchingStmtIn, oStmt = aOStmtIn.OStmtIn`

Output: `witOut = (Statement (L := L) (ℓ := ℓ')`
  `(RingSwitchingBaseContext κ L K ℓ P) 0) × (SumcheckWitness L ℓ' 0), oStmt = aOStmtIn.OStmtIn`
-/

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
  Module TensorProduct Nat Matrix
open scoped NNReal ProbabilityTheory
open Sumcheck.Structured

noncomputable section
namespace RingSwitching.BatchingPhase

/-- Bridge the framework's `SampleableType` uniform sampler to the PMF uniform notation used by
Schwartz-Zippel lemmas. -/
private theorem probEvent_uniformSample_eq_Pr_uniform {α : Type} [SampleableType α] [Fintype α]
    [Nonempty α] (p : α → Prop) [DecidablePred p] :
    Pr[p | ($ᵗ α)] = Pr_{ let x ← $ᵖ α }[p x] := by
  rw [probEvent_uniformSample]
  rw [prob_uniform_eq_card_filter_div_card]
  norm_num

/-- The default oracle interface (`OracleInterface.instDefault`, used by the ring-switching message
oracles in `Spec.lean`) answers its only (unit) query with the message itself. -/
@[simp] lemma answer_instDefault {M : Type _} (m : M) (q : Unit) :
    @OracleInterface.answer M OracleInterface.instDefault m q = m := rfl

open OracleInterface in
/-- Local message-query collapse for `OracleInterface.simOracle2`. -/
lemma simulateQ_simOracle2_messageQuery {ι : Type} {oSpec : OracleSpec ι}
    {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i) (qm : ([T₂]ₒ).Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM (([T₂]ₒ).query qm) : OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)) _)
      = (pure (OracleInterface.answer (t₂ qm.1) qm.2) : OracleComp oSpec _) :=
  -- dedup-audit(#257): delegate to the canonical proof in `RingSwitching/Prelude.lean`. The
  -- statement is kept as a local re-export so in-file `rw`s resolve it in local context.
  RingSwitching.simulateQ_simOracle2_messageQuery t₁ t₂ qm

open OracleInterface in
/-- OptionT/query form of `simulateQ_simOracle2_messageQuery`. -/
lemma simulateQ_simOracle2_query {ι : Type} {oSpec : OracleSpec ι}
    {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i) (qm : ([T₂]ₒ).Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (query (spec := [T₂]ₒ) qm : OptionT (OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ))) _)
      = (OptionT.lift (pure (OracleInterface.answer (t₂ qm.1) qm.2))
          : OptionT (OracleComp oSpec) _) :=
  -- dedup-audit(#257): delegate to the canonical proof in `RingSwitching/Prelude.lean`.
  RingSwitching.simulateQ_simOracle2_query t₁ t₂ qm

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (aOStmtIn : AbstractOStmtIn L ℓ')

/-! ## Formalized Helper Functions
These functions provide concrete implementations for tensor algebra operations
and other logic required by the protocol.
-/

/-- A dummy state returned by the verifier upon failure of Check 1. -/
def failureState (stmt : BatchingStmtIn L ℓ) (s_hat : P.A) :
    Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0 := {
    ctx := {
      t_eval_point := stmt.t_eval_point,
      original_claim := stmt.original_claim
      s_hat := s_hat,
      r_batching := 0, -- Dummy value
    },
    sumcheck_target := 0,
    challenges := Fin.elim0
  }

/-- The verifier's accepting batching output statement after receiving `s_hat` and the batching
challenge vector. -/
def batchingAcceptStatement (stmt : BatchingStmtIn L ℓ) (s_hat : P.A)
    (r_batching : Fin κ → L) :
    Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0 := {
    ctx := {
      t_eval_point := stmt.t_eval_point,
      original_claim := stmt.original_claim,
      s_hat := s_hat,
      r_batching := r_batching
    },
    sumcheck_target := compute_s0 κ L K P s_hat r_batching,
    challenges := Fin.elim0
  }

/-! ## Prover and Verifier Implementation -/

/-- The state maintained by the prover throughout the batching phase. -/
def PrvState : Fin (2 + 1) → Type
  | ⟨0, _⟩ => BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j) × BatchingWitIn L K ℓ ℓ'
  | ⟨1, _⟩ => BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j)
    × BatchingWitIn L K ℓ ℓ' × P.A
  | _ => BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j)
    × BatchingWitIn L K ℓ ℓ' × P.A × (Fin κ → L)

noncomputable def oracleProver :
  OracleProver (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn L ℓ) (OStmtIn := aOStmtIn.OStmtIn) (WitIn := BatchingWitIn L K ℓ ℓ')
    (StmtOut := Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ P) 0) (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' 0)
    (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)) where
  PrvState := PrvState κ L K P ℓ ℓ' aOStmtIn

  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)

  sendMessage
    | ⟨0, _⟩ => fun (stmt, oStmt, wit) => do
      -- Step 1: P computes ŝ and sends it.
      let s_hat := embedded_MLP_eval κ L K P ℓ ℓ' h_l wit.t' stmt.t_eval_point
      return ⟨s_hat, (stmt, oStmt, wit, s_hat)⟩
    | ⟨1, h⟩ => fun _ => do nomatch h -- V to P round

  receiveChallenge
    | ⟨0, h⟩ => nomatch h -- i.e. contradiction
    | ⟨1, _⟩ => fun ⟨stmt, oStmt, wit, s_hat⟩ => do
      return fun r_batching => (stmt, oStmt, wit, s_hat, r_batching)

  output := fun ⟨stmt, oStmt, wit, s_hat, r_batching⟩ => do
    -- Step 4: P computes the batched polynomial h.
    let ctx: RingSwitchingBaseContext κ L K ℓ P := {
      t_eval_point := stmt.t_eval_point,
      original_claim := stmt.original_claim,
      s_hat := s_hat,
      r_batching := r_batching
    }
    let h_poly: ↥L⦃≤ 2⦄[X Fin ℓ'] :=
      projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := wit.t')
        (m := (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l).multpoly (ctx := ctx))
        (i := 0) (challenges := Fin.elim0)
    -- Prover computes s₀ locally for its output witness.
    let s₀ := compute_s0 κ L K P s_hat r_batching
    let stmtOut : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0 := {
      ctx := ctx,
      sumcheck_target := s₀,
      challenges := Fin.elim0
    }
    let witOut : SumcheckWitness L ℓ' 0 := {
      t' := wit.t',
      H := h_poly
    }
    return (⟨stmtOut, oStmt⟩, witOut)

noncomputable def oracleVerifier :
  OracleVerifier (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn L ℓ) (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)) where
  verify | stmt, pSpec_batching_challenges => do
     -- Step 1: Query prover for ŝ (Message 0).
    let s_hat : P.A ← query (spec := [pSpecBatching (κ:=κ)
      (L:=L) (K:=K) (P:=P).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩

    -- Step 2: Perform Check 1.
    unless performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l
      stmt.original_claim stmt.t_eval_point s_hat do
      return (failureState κ L K P ℓ ℓ' stmt s_hat) -- Abort if check fails

    -- Step 3: Sample batching scalars r'' (Challenge 1).
    let r_batching : Fin κ → L := pSpec_batching_challenges ⟨1, by rfl⟩

    -- Step 5: Compute s₀.
    let s₀ := compute_s0 κ L K P s_hat r_batching

    -- Construct the output statement for the next phase.
    let ctx : RingSwitchingBaseContext κ L K ℓ P := {
      t_eval_point := stmt.t_eval_point,
      original_claim := stmt.original_claim,
      s_hat := s_hat,
      r_batching := r_batching
    }
    let stmtOut : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0 := {
      ctx := ctx,
      sumcheck_target := s₀,
      challenges := Fin.elim0
    }
    return stmtOut
  -- Standard embedding for empty oSpec.
  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun i => rfl

/-- The batching-phase oracle verifier passes every output oracle through to the unchanged input
oracle (`embed = Sum.inl`, `OStmtIn = OStmtOut`, `hEq = rfl`) and exposes no message oracle, so its
`AppendCoherent` coherence holds by `rfl`. Used to `.append` the batching phase onto the core
interaction phase. -/
instance instOracleVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn := aOStmtIn)) where
  hCohInl := fun a k h => by
    have : a = k := by
      simpa only [oracleVerifier, Function.Embedding.coeFn_mk, Sum.inl.injEq] using h
    subst this; rfl
  hCohInr := fun a k h => by
    simp only [oracleVerifier, Function.Embedding.coeFn_mk, reduceCtorEq] at h

open OracleInterface in
omit [NeZero κ] [Fintype L] [SampleableType L] [Fintype K] [DecidableEq K]
  [NeZero ℓ] [NeZero ℓ'] in
/-- The inner oracle verifier body, simulated through `simOracle2`, collapses to the
deterministic `if performCheck … then stmtOutAccept else failureState`. -/
lemma oracleVerifier_verify_collapse
    (stmt : BatchingStmtIn L ℓ) (oStmt : ∀ j, aOStmtIn.OStmtIn j)
    (tr : FullTranscript (pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P))) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt (FullTranscript.messages tr))
        ((oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)).verify stmt
          (FullTranscript.challenges tr))
      = (if performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmt.original_claim
              stmt.t_eval_point (FullTranscript.messages tr ⟨0, by rfl⟩) then
           pure ({ ctx := { t_eval_point := stmt.t_eval_point,
                            original_claim := stmt.original_claim,
                            s_hat := FullTranscript.messages tr ⟨0, by rfl⟩,
                            r_batching := FullTranscript.challenges tr ⟨1, by rfl⟩ },
                   sumcheck_target := compute_s0 κ L K P
                     (FullTranscript.messages tr ⟨0, by rfl⟩)
                     (FullTranscript.challenges tr ⟨1, by rfl⟩),
                   challenges := Fin.elim0 } : Statement (L:=L) (ℓ:=ℓ')
                     (RingSwitchingBaseContext κ L K ℓ P) 0)
         else pure (failureState κ L K P ℓ ℓ' stmt (FullTranscript.messages tr ⟨0, by rfl⟩))
         : OptionT (OracleComp []ₒ) _) := by
  simp only [oracleVerifier]
  rw [simulateQ_optionT_bind]
  erw [simulateQ_simOracle2_query]
  -- `simulateQ (simOracle2 …) (query) = OptionT.lift (pure (answer …))`. Reduce the lift-bind at
  -- the `.run` level via `OptionT.run_bind_lift` (+ `pure_bind`), then push `simulateQ` through
  -- the query-free `if`.
  refine OptionT.ext ?_
  dsimp only [Sigma.fst, Sigma.snd]
  erw [OptionT.run_bind_lift]
  erw [pure_bind]
  -- The `instDefault` answer is the message itself: reduce `answer m () = m` FIRST so the two
  -- `if`-conditions coincide, then push `simulateQ`/`OptionT.run` through the query-free
  --   `if`/`pure`s.
  rw [answer_instDefault]
  simp only [apply_ite, bind_pure_comp, map_pure]
  -- Both `if`-conditions are now identical; collapse the nested `if` and `simulateQ (pure …)`.
  by_cases hc : performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmt.original_claim
      stmt.t_eval_point (FullTranscript.messages tr ⟨0, by rfl⟩) = true <;>
    simp only [hc, Bool.false_eq_true, reduceIte] <;>
    (erw [simulateQ_pure]; rfl)

/-- The Oracle Reduction for the Batching Phase. -/
noncomputable def batchingOracleReduction : OracleReduction (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn L ℓ) (OStmtIn := aOStmtIn.OStmtIn) (WitIn := BatchingWitIn L K ℓ ℓ')
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' 0)
    (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)) where
  prover := oracleProver κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)
  verifier := oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)

/-- The batching oracle *reduction*'s verifier is definitionally `oracleVerifier`, so it inherits
`AppendCoherent`. -/
instance instBatchingOracleReductionAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (batchingOracleReduction κ L K P ℓ ℓ' h_l (aOStmtIn := aOStmtIn)).verifier :=
  instOracleVerifierAppendCoherent κ L K P ℓ ℓ' h_l (aOStmtIn := aOStmtIn)

/-! ## RBR Knowledge Soundness Components -/

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

def batchingInputRelationProp (stmt : BatchingStmtIn L ℓ)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) (wit : BatchingWitIn L K ℓ ℓ') : Prop :=
  wit.t' = packMLE κ L K ℓ ℓ' h_l P.basis wit.t ∧ stmt.original_claim = wit.t.val.aeval stmt.t_eval_point
  ∧ aOStmtIn.initialCompatibility ⟨wit.t', oStmt⟩

/-- Input relation: the witness `t` and `t'` are consistent,
and `t` satisfies the original claim. -/
def batchingInputRelation :
    Set ((BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j)) × BatchingWitIn L K ℓ ℓ') :=
  {⟨⟨stmt, oStmt⟩, wit⟩ | batchingInputRelationProp κ L K P ℓ ℓ' h_l aOStmtIn stmt oStmt wit }

/-- Intermediate witness types for RBR knowledge soundness. -/
def batchingWitMid : Fin (2 + 1) → Type
  | ⟨0, _⟩ => BatchingWitIn L K ℓ ℓ' -- Before any messages
  | ⟨1, _⟩ => BatchingWitIn L K ℓ ℓ' -- After P sends ŝ
  | ⟨2, _⟩ => SumcheckWitness L ℓ' 0 -- After V sends r'' and all computations are done

/-- RBR extractor for the batching phase. -/
noncomputable def batchingRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j))
    (WitIn := BatchingWitIn L K ℓ ℓ')
    (WitOut := SumcheckWitness L ℓ' 0)
    (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P))
    (WitMid := batchingWitMid L K ℓ ℓ') where
  eqIn := rfl
  extractMid m _ _ witSucc :=
    match m with
    | ⟨0, _⟩ => witSucc -- Extracting `WitIn` from a future `WitIn`
    | ⟨1, _⟩ => by
      exact { t := unpackMLE κ L K ℓ ℓ' h_l P.basis witSucc.t', t' := witSucc.t' }
  extractOut _ _ witOut := witOut

/-- RBR knowledge soundness error for the batching phase.
The repaired batching KState has an explicit verifier-reject/failure-state branch. The always-valid
unit bound is the current generic RBR error; the sharp bad-batching polynomial lemma below remains
available for the accepting branch. -/
def batchingRBRKnowledgeError (i : (pSpecBatching (κ := κ) (L := L) (K := K) (P := P)).ChallengeIdx) : ℝ≥0 :=
  1

def batchingKStateProp {m : Fin (2 + 1)}
    (tr : Transcript m (pSpecBatching (κ := κ) (L := L) (K := K) (P := P)))
    (stmt : BatchingStmtIn L ℓ) (witMid : batchingWitMid L K ℓ ℓ' m)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) :
    Prop :=
  match m with
  | ⟨0, _⟩ => -- equiv s relIn
    batchingInputRelationProp κ L K P ℓ ℓ' h_l aOStmtIn stmt oStmt witMid
  | ⟨1, _⟩ => by -- P sends hᵢ(X)
    let ⟨msgsUpTo, _⟩ := Transcript.equivMessagesChallenges (k := 1)
      (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)) tr
    let i_msg1 : ((pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)).take 1 (by omega)).MessageIdx :=
      ⟨⟨0, Nat.lt_of_succ_le (by omega)⟩, by simp [pSpecBatching]; rfl⟩
    let s_hat: P.A := msgsUpTo i_msg1
    exact
      witMid.t' = packMLE κ L K ℓ ℓ' h_l P.basis witMid.t -- implied by `extractMid`
      -- The last two constraints are equivalent to `t(r) = s`
      ∧ embedded_MLP_eval κ L K P ℓ ℓ' h_l witMid.t' stmt.t_eval_point = s_hat
      ∧ performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmt.original_claim
        stmt.t_eval_point s_hat -- local V check
      -- DP24 repair: carry the oracle-statement compatibility (present in rounds 0 and 2),
      -- so that `extractMid` at round 0 can reconstruct the round-0 `batchingInputRelationProp`.
      -- `batchingKStateProp`/`batchingKnowledgeStateFunction` have no users outside this file.
      ∧ aOStmtIn.initialCompatibility ⟨witMid.t', oStmt⟩
  | ⟨2, _⟩ => by -- implied by relOut
    simp only [batchingWitMid] at witMid
    let ⟨msgsUpTo, chalsUpTo⟩ := Transcript.equivMessagesChallenges (k := 2)
      (pSpec := pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)) tr
    let i_msg1 : ((pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)).take 2 (by omega)).MessageIdx :=
      ⟨⟨0, Nat.lt_of_succ_le (by omega)⟩, by simp [pSpecBatching]; rfl⟩
    let s_hat: P.A := msgsUpTo i_msg1
    let i_msg2 : ((pSpecBatching (κ:=κ) (L:=L) (K:=K) (P:=P)).take 2 (by omega)).ChallengeIdx :=
      ⟨⟨1, Nat.lt_of_succ_le (by omega)⟩, by simp [pSpecBatching]; rfl⟩
    let batching_challenges: Fin κ → L := chalsUpTo i_msg2

    -- DP24 reject-branch repair (#17), ported to the profile API. The verifier has TWO
    -- output branches and the round-2 knowledge state must mirror the verifier's actual
    -- decision rather than asserting the accept-branch facts unconditionally:
    -- asserting them unconditionally is FALSE on the reject branch (where
    -- `(failureState, witOut) ∈ relOut` is satisfiable), making `toFun_full` unprovable.
    -- The repaired prop asserts exactly `sumcheckRoundRelationProp` for whichever statement
    -- the verifier deterministically outputs; `toFun_full` transports each branch directly
    -- from `h_relOut`.
    let stmtOutAccept : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0 := {
      ctx := {
        t_eval_point := stmt.t_eval_point,
        original_claim := stmt.original_claim,
        s_hat := s_hat,
        r_batching := batching_challenges
      },
      sumcheck_target := compute_s0 κ L K P s_hat batching_challenges,
      challenges := Fin.elim0
    }
    exact
      (if performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmt.original_claim
            stmt.t_eval_point s_hat then
        sumcheckRoundRelationProp κ L K P ℓ ℓ' h_l aOStmtIn (i:=0)
          stmtOutAccept oStmt witMid
      else
        sumcheckRoundRelationProp κ L K P ℓ ℓ' h_l aOStmtIn (i:=0)
          (failureState κ L K P ℓ ℓ' stmt s_hat) oStmt witMid)

-- The round-0 knowledge-state conjunct is discharged via the DP24 capstone
-- `performCheckOriginalEvaluation_packMLE_iff'`, whose soundness (multilinear-extension
-- uniqueness) requires both carriers to be integral domains. This holds in every real
-- instantiation (e.g. `binaryTowerProfile` builds from `Field K`/`Field L`), and integrality of
-- the small/large carrier is a genuine precondition for the reduction to be sound. Scoped to the
-- knowledge-soundness pipeline only (completeness needs no such hypothesis).
variable [IsDomain L] [IsDomain K] in
/-- Knowledge state function for the batching phase. -/
noncomputable def batchingKnowledgeStateFunction :
  (oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)).KnowledgeStateFunction init impl
    (relIn := batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (batchingRbrExtractor κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)) where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    batchingKStateProp κ L K P ℓ ℓ' h_l aOStmtIn tr stmt witMid oStmt
  toFun_empty _ _ := by rfl
  toFun_next := fun m hDir stmtIn tr msg witMid =>
    match m with
    | ⟨0, _⟩ => by -- from accumulative KState
      intro hSuccTrue
      simp only [batchingKStateProp, Fin.zero_eta, Fin.isValue, Fin.succ_zero_eq_one,
        Equiv.toFun_as_coe, Transcript.equivMessagesChallenges_apply, Fin.castSucc_zero,
        batchingRbrExtractor, Fin.mk_one, Fin.succ_one_eq_two,
        batchingInputRelationProp] at ⊢ hSuccTrue
      -- Round-1 `batchingKStateProp` gives, in order:
      --   (1) `witMid.t' = packMLE β witMid.t`,
      --   (2) `embedded_MLP_eval witMid.t' r = s_hat`,
      --   (3) `performCheckOriginalEvaluation original_claim r s_hat`,
      --   (4) `aOStmtIn.initialCompatibility ⟨witMid.t', oStmt⟩`  (the documented repair).
      -- The round-0 `batchingInputRelationProp` goal is the conjunction
      --   `t' = packMLE t ∧ original_claim = aeval r t ∧ initialCompatibility`.
      -- Conjuncts (1) and (3-of-goal) are discharged directly from `hSuccTrue`.
      refine ⟨hSuccTrue.1, ?_, hSuccTrue.2.2.2⟩
      -- Remaining goal: `original_claim = aeval r witMid.t`.
      --
      -- With the Step-2 check now reading the ROW components (`decompose_tensor_algebra_rows`),
      -- the DP24 capstone `performCheckOriginalEvaluation_packMLE_iff` is SOUND: substituting
      --   (2) `s_hat = embedded_MLP_eval witMid.t' r`  and
      --   (1) `witMid.t' = packMLE β witMid.t`
      -- into the local check (3) yields
      --   `performCheckOriginalEvaluation original_claim r
      --      (embedded_MLP_eval (packMLE β witMid.t) r) = true`,
      -- which the capstone turns into exactly `original_claim = aeval r witMid.t`.
      -- The capstone `performCheckOriginalEvaluation_packMLE_iff'` is the abstract-`P` form
      -- (over any `CommRing + IsDomain` carriers), proved from `P`'s extraction laws
      -- (`decomposeRows_add` / `decomposeRows_φ₀_mul_φ₁`, the constructive content of
      -- `decomposeRows_spec`); it specializes to the concrete `binaryTowerProfile` lemma.
      have hcheck := hSuccTrue.2.2.1
      rw [← hSuccTrue.2.1, hSuccTrue.1] at hcheck
      -- `hcheck : performCheckOriginalEvaluation original_claim r
      --   (embedded_MLP_eval (packMLE P.basis witMid.t) r) = true`. The DP24 capstone
      -- `performCheckOriginalEvaluation_packMLE_iff` (ported, Profile-abstract) turns this into
      -- exactly `original_claim = aeval r witMid.t.val` (= the goal `… = witMid.t.val.aeval r`).
      exact (performCheckOriginalEvaluation_packMLE_iff P ℓ ℓ' h_l
        stmtIn.1.original_claim witMid.t stmtIn.1.t_eval_point).mp hcheck
    | ⟨1, h⟩ => nomatch h
  toFun_full := fun ⟨stmtLast, oStmtLast⟩ tr witOut => by
    -- Spec repair (#17) APPLIED: the round-2 `batchingKStateProp` (the `⟨2,_⟩` case above) now
    -- mirrors the verifier's accept/reject decision via an `if performCheck … then … else …`,
    -- asserting `sumcheckRoundRelationProp` for whichever statement the verifier actually outputs
    -- (`stmtOutAccept` on accept, `failureState` on reject). Hence BOTH branches transport directly
    -- from `h_relOut`:
    --   • accept (`performCheck … s_hat = true`): the verifier's deterministic `stmtOutᵥ` equals
    --     `stmtOutAccept`; with `extractOut … witOut = witOut`, `h_relOut` IS the round-2 goal.
    --   • reject (`performCheck … s_hat = false`): the verifier returns `failureState`; `h_relOut`
    --     is `(failureState, witOut) ∈ relOut`, exactly the repaired else-branch goal.
    -- The sumcheck-consistency conjunct lives inside `sumcheckRoundRelationProp`/`relOut` under the
    -- SAME free `𝓑`, so it transports verbatim — NO `𝓑` pinning needed here (pinning is only
    -- required by the batching-phase completeness argument, which must establish consistency from
    -- scratch on the honest run).
    --
    -- VERIFIER-RUN QUERY SIMULATION (resolved). To consume `h_relOut` we resolve
    -- `Pr[(stmtOutᵥ, witOut) ∈ relOut | (simulateQ impl (verifier.run …)).run' …]` to the
    -- concrete `stmtOutᵥ`. The verifier's `verify` issues a message-oracle query
    -- (`query (spec := [pSpecBatching.Message]ₒ) ⟨⟨0,rfl⟩,()⟩`); under
    -- `simulateQ (OracleInterface.simOracle2 …)` it collapses, via the support lemma
    -- `Prelude.simulateQ_simOracle2_query`, to `pure (answer s_hat)`. Threaded through
    -- `oracleVerifier_verify_collapse`, the whole `verifier.run` reduces to a single deterministic
    -- `pure (if performCheck … then stmtOutAccept else failureState, oStmtOut)`; the proof then
    --   runs
    -- `probEvent_pos_iff` → `OptionT.mem_support_iff` → collapse → `split` on `performCheck` →
    -- `subst` the singleton support → transport `h_relOut` (the `embed = Sum.inl` map gives
    -- `oStmtOut = oStmt`). The same `Prelude` support lemma serves the analogous message-querying
    -- `toFun_full`s in `SumcheckPhase` and `BinaryBasefold/Steps`.
    intro h
    rw [gt_iff_lt, probEvent_pos_iff] at h
    obtain ⟨x, hx, hrel⟩ := h
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    simp only [OracleVerifier.toVerifier, Verifier.run, StateT.run'_eq,
      support_map, Set.mem_image, Prod.exists] at hx
    obtain ⟨val, s', hmem, heq⟩ := hx
    -- Collapse the inner verifier body (the message query is the load-bearing step) to the
    -- deterministic `if performCheck … then stmtOutAccept else failureState` via the collapse
    --   lemma.
    rw [oracleVerifier_verify_collapse] at hmem
    -- The verifier run is now query-free (`pure`/`if`). Case-split the verifier's accept/reject
    -- decision (`split`), then collapse each `pure` branch to a singleton support.
    split at hmem <;>
      simp only [bind_pure_comp, map_pure] at hmem <;>
      erw [simulateQ_pure] at hmem <;>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
      obtain ⟨rfl, -⟩ := hmem <;>
      injection heq with hxv <;>
      subst hxv
    -- Goal in each branch: round-2 `batchingKStateProp` = the `if performCheck …` over
    -- `sumcheckRoundRelationProp` for the statement the verifier output. `hrel` provides exactly
    -- that membership for the deterministic output `x`; transport it.
    all_goals
      simp only [batchingKStateProp, batchingRbrExtractor, Fin.isValue, Equiv.toFun_as_coe,
        Transcript.equivMessagesChallenges_apply, sumcheckRoundRelation, Set.mem_setOf_eq,
        Transcript.toMessagesChallenges,
        Transcript.toMessagesUpTo, Transcript.toChallengesUpTo, FullTranscript.messages,
        FullTranscript.challenges, oracleVerifier] at hrel ⊢
    -- `hrel` (verifier output ∈ relOut) IS the round-2 KState for the matching branch; the
    -- `embed = Sum.inl` map makes `oStmtOut = oStmtLast`, and the message/challenge accessors
    --   agree.
    all_goals dsimp only [Fin.last, Fin.isValue]
    -- The verifier's accept/reject decision (`hmem`'s `split`, hyp `h✝`) determines which branch
    -- of the round-2 KState `if` is taken; `hrel` supplies exactly that
    --   `sumcheckRoundRelationProp`.
    -- The `embed = Sum.inl` map gives `oStmtOut = oStmtLast`, so `hrel` matches up to that cast.
    · rw [if_pos (by assumption)]
      convert hrel using 3
    · rw [if_neg (by assumption)]
      convert hrel using 3

/-! ## Security Properties -/

/-- The batching completeness statement — **proven**: see
`batchingReduction_perfectCompleteness_proved` below (from `NeverFail init`, `IsDomain L/K`;
issue #338 closeout). The `Prop` name is retained for downstream statement stability; the
conditional wrapper below is a documented adapter. -/
def batchingReduction_perfectCompleteness_residual : Prop :=
  OracleReduction.perfectCompleteness
    (oracleReduction := batchingOracleReduction κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn))
    (relIn := batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (init := init) (impl := impl)

/-- Batching completeness from the explicit local algebraic residual. -/
theorem batchingReduction_perfectCompleteness
    (hBatching : batchingReduction_perfectCompleteness_residual
      (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := aOStmtIn) (init := init) (impl := impl)) :
  OracleReduction.perfectCompleteness
    (oracleReduction := batchingOracleReduction κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn))
    (relIn := batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (init := init) (impl := impl) :=
  hBatching

/-- Row-expansion form of `compute_s0` on the tensor sent by the honest embedding of an arbitrary
large-field multilinear polynomial `t'`.

This packages the orientation used by the batching verifier: `compute_s0` reads
`P.decomposeColumns`, so it extracts the basis coordinates of the *suffix equality factor* (the
`φ₀`/`eq` tensor factor) and weights them by `eqTilde(u, y)`, scaling the `t'` value at each
Boolean suffix. This is the column form that matches the witness-independent batching multiplier
`compute_A_func` — see `compute_s0_eq_sum_A_func`. -/
lemma compute_s0_embedded_MLP_eval_eq_sum
    [IsDomain L] [IsDomain K]
    (t' : MultilinearPoly L ℓ') (r : Fin ℓ → L) (y : Fin κ → L) :
    compute_s0 κ L K P (embedded_MLP_eval κ L K P ℓ ℓ' h_l t' r) y =
      ∑ u : Fin κ → Fin 2,
        eqTilde (fun i => (if u i == 1 then (1 : L) else 0)) y *
          (∑ w : Fin ℓ' → Fin 2,
            P.basis.repr
                (eqTilde (fun i => (if w i == 1 then (1 : L) else 0))
                  (getEvaluationPointSuffix κ L ℓ ℓ' h_l r)) u •
              (eval (fun i => (if w i == 1 then (1 : L) else 0)) t'.val)) := by
  unfold compute_s0
  apply Finset.sum_congr rfl
  intro u _
  rw [decomposeColumns_embedded_MLP_eval']

/-- **Round-0 batching consistency (completeness keystone).** For the honest prover's tensor
`ŝ = embedded_MLP_eval t' r`, the verifier's batched sumcheck target `compute_s0 ŝ y` equals the
honest sumcheck value `Σ_x A_func(x)·t'(x)`, where `A_func = compute_A_func` is the verifier's
(witness-independent) batching multiplier. This is the identity the batching perfect-completeness
needs (`sumcheck_target = Σ_cube H` with `H = A_MLE · t'`). It holds because `compute_s0` reads the
**column** decomposition (`decomposeColumns_embedded_MLP_eval'`), which puts `β.repr` on the
verifier-known `eq`-factor — matching `A_func`'s structure. The proof is a `sum_comm` + `eqTilde`
symmetry rearrangement: both sides equal `Σ_u Σ_w β.repr(eq̃(w,suffix))_u • (eq̃(u,y)·t'(w))`. -/
lemma compute_s0_eq_sum_A_func
    [IsDomain L] [IsDomain K]
    (t' : MultilinearPoly L ℓ') (r : Fin ℓ → L) (y : Fin κ → L) :
    compute_s0 κ L K P (embedded_MLP_eval κ L K P ℓ ℓ' h_l t' r) y =
      ∑ x : Fin ℓ' → Fin 2,
        compute_A_func κ L K P ℓ' (getEvaluationPointSuffix κ L ℓ ℓ' h_l r) y x *
          eval (fun i => (if x i == 1 then (1 : L) else 0)) t'.val := by
  rw [compute_s0_embedded_MLP_eval_eq_sum]
  unfold compute_A_func
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun u _ => ?_))
  rw [eqTilde_comm (getEvaluationPointSuffix κ L ℓ ℓ' h_l r)
    (fun i => (if w i == 1 then (1 : L) else 0))]

/-- **Round-0 batching sumcheck consistency (completeness keystone, abstract multiplier).** For the
honest prover's embedded tensor `ŝ = embedded_MLP_eval t' r`, the batched sumcheck target
`compute_s0 ŝ y` equals the honest sumcheck consistency sum `∑_{x ∈ {0,1}^ℓ'} H(x)` over the
Boolean hypercube, where `H = projectToMidSumcheckPoly t' m 0` is the round-0 sumcheck polynomial
of the product `m · t'`, provided the multiplier `m` matches `compute_A_func` on Boolean inputs.

This is the `sumcheckConsistencyProp (boolDomain L _) (compute_s0 …) H` conjunct of the batching
output relation — the conjunct made *provable* exactly by the column orientation of `compute_s0`
(`compute_s0_eq_sum_A_func`). Proof: the cube sum reindexes to the Boolean hypercube (pinned
`boolEmbedding`, with `Field L` from the finite domain), `projectToMidSumcheckPoly … 0` evaluates
to `(m · t')` (the `i = 0` case of `fixFirstVariablesOfMQP_eval` fixes no variables), and
`eval (m·t') = (eval m)·(eval t') = A_func · t'` summand-wise. The batching analog of
`iteratedSumcheck_round_logic_complete`. -/
theorem batching_consistency_of_multpoly [IsDomain L] [IsDomain K]
    (t' : MultilinearPoly L ℓ') (r : Fin ℓ → L) (y : Fin κ → L)
    (m : MultilinearPoly L ℓ')
    (hm : ∀ b : Fin ℓ' → Fin 2,
      eval (fun i => (if b i == 1 then (1 : L) else 0)) m.val
        = compute_A_func κ L K P ℓ' (getEvaluationPointSuffix κ L ℓ ℓ' h_l r) y b) :
    compute_s0 κ L K P (embedded_MLP_eval κ L K P ℓ ℓ' h_l t' r) y
      = ∑ x ∈ (boolDomain L (ℓ' - (0 : Fin (ℓ' + 1)).val)).cube,
          (projectToMidSumcheckPoly ℓ' t' m 0 Fin.elim0).val.eval x := by
  letI : Field L := Fintype.fieldOfDomain L
  rw [show (boolDomain L (ℓ' - (0 : Fin (ℓ' + 1)).val)).cube
      = (univ.map (boolEmbedding L)) ^ᶠ (ℓ' - (0 : Fin (ℓ' + 1)).val) from rfl,
    RingSwitching.boolHypercube_sum_pinned (boolEmbedding L) (by
      intro c; rcases Fin.exists_fin_two.mp ⟨c, rfl⟩ with h | h <;> rw [h] <;> simp)]
  rw [compute_s0_eq_sum_A_func]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hproj : (projectToMidSumcheckPoly ℓ' t' m 0 Fin.elim0).val.eval
        (fun j => (if b j == 1 then (1 : L) else 0))
      = (m.val * t'.val).eval (fun j => (if b j == 1 then (1 : L) else 0)) := by
    rw [projectToMidSumcheckPoly_eq_fixVars]
    erw [fixFirstVariablesOfMQP_eval]
    refine congrArg (fun g => eval g (m.val * t'.val)) ?_
    funext i
    simp only [Equiv.trans_apply, finCongr_apply]
    rcases hsym : finSumFinEquiv.symm (Fin.cast (by simp) i) with j | j
    · simp only [Sum.elim_inl]
      have hji : j = i := by
        have hi := congrArg finSumFinEquiv hsym
        rw [Equiv.apply_symm_apply] at hi
        apply Fin.ext
        have hval := congrArg Fin.val hi
        simpa [finSumFinEquiv_apply_left] using hval.symm
      rw [hji]
    · exact j.elim0
  rw [MvPolynomial.eval_mul, hm b] at hproj
  exact hproj.symm

/-- **Round-0 batching sumcheck consistency (honest instance).** The hypothesis-free form: with the
honest multiplier `m = compute_A_MLE` (the multilinear extension of `compute_A_func`), the Boolean
agreement hypothesis holds by `MLE_eval_zeroOne`, so the batched target equals the honest sumcheck
sum. This is exactly the consistency conjunct of `sumcheckRoundRelation 0` for the honest batching
output `(stmtOut with sumcheck_target = compute_s0 ŝ y, witOut.H = projectToMidSumcheckPoly t' A_MLE 0)`. -/
theorem batching_consistency_honest [IsDomain L] [IsDomain K]
    (t' : MultilinearPoly L ℓ') (r : Fin ℓ → L) (y : Fin κ → L) :
    compute_s0 κ L K P (embedded_MLP_eval κ L K P ℓ ℓ' h_l t' r) y
      = ∑ x ∈ (boolDomain L (ℓ' - (0 : Fin (ℓ' + 1)).val)).cube,
          (projectToMidSumcheckPoly ℓ' t'
            (compute_A_MLE κ L K P ℓ' (getEvaluationPointSuffix κ L ℓ ℓ' h_l r) y)
            0 Fin.elim0).val.eval x := by
  apply batching_consistency_of_multpoly
  intro b
  have hcoe : (fun i => (if b i == 1 then (1 : L) else 0)) = (fun i => ((b i : Fin 2) : L)) := by
    funext i; rcases Fin.exists_fin_two.mp ⟨b i, rfl⟩ with h | h <;> rw [h] <;> simp
  rw [hcoe, compute_A_MLE]
  exact MvPolynomial.MLE_eval_zeroOne b _

set_option maxHeartbeats 1000000 in
/-- **Batching perfect completeness — `batchingReduction_perfectCompleteness_residual` PROVEN.**
The honest batching reduction is perfectly complete (given `NeverFail init`). The verifier-run
collapse is the deterministic `oracleVerifier_verify_collapse`; the honest accept branch fires
because `performCheckOriginalEvaluation_packMLE_iff` turns the relation's `original_claim = t(r)`
into `performCheck = true`; and the honest output lies in `sumcheckRoundRelation 0` because the
structural invariant holds by construction, the sumcheck-consistency conjunct is exactly
`batching_consistency_honest` (the column-orientation keystone), and `initialCompatibility` is
carried from the input relation. The monadic run-shape is the proven 2-message-round template
`unroll_2_message_reduction_perfectCompleteness` (cf. `iteratedSumcheckOracleReduction_perfectCompleteness_proved`).

Consumers carrying `NeverFail init` should call this directly (the `_residual` `Prop` is stated
without `NeverFail`). -/
theorem batchingReduction_perfectCompleteness_proved [IsDomain L] [IsDomain K]
    (hInit : NeverFail init) :
    batchingReduction_perfectCompleteness_residual
      (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := aOStmtIn) (init := init) (impl := impl) := by
  classical
  haveI : Nonempty L := ⟨0⟩
  rw [batchingReduction_perfectCompleteness_residual,
    OracleReduction.unroll_2_message_reduction_perfectCompleteness (oSpec := []ₒ)
    (pSpec := pSpecBatching (κ := κ) (L := L) (K := K) (P := P)) (init := init) (impl := impl)
    (hInit := hInit) (hDir0 := by rfl) (hDir1 := by rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  obtain ⟨h_t'_eq, h_claim, h_compat⟩ := h_relIn
  -- honest verifier collapses to `pure accept` (performCheck = true)
  have hverify : ∀ r1 : Fin κ → L,
      (oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn := aOStmtIn)).toVerifier.verify (stmtIn, oStmtIn)
          (FullTranscript.mk2 (embedded_MLP_eval κ L K P ℓ ℓ' h_l witIn.t' stmtIn.t_eval_point) r1)
        = (pure (batchingAcceptStatement κ L K P ℓ ℓ' stmtIn
              (embedded_MLP_eval κ L K P ℓ ℓ' h_l witIn.t' stmtIn.t_eval_point) r1, oStmtIn)
            : OptionT (OracleComp []ₒ) _) := by
    intro r1
    have hcheck : performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmtIn.original_claim
        stmtIn.t_eval_point
        (embedded_MLP_eval κ L K P ℓ ℓ' h_l witIn.t' stmtIn.t_eval_point) = true := by
      rw [h_t'_eq, performCheckOriginalEvaluation_packMLE_iff]; exact h_claim
    simp only [OracleVerifier.toVerifier]
    rw [oracleVerifier_verify_collapse]
    simp only [FullTranscript.messages, FullTranscript.challenges, FullTranscript.mk2]
    rw [if_pos hcheck]
    simp only [pure_bind, batchingAcceptStatement, oracleVerifier]
  -- relation membership of the honest accept output
  have h_rel_out : ∀ r1 : Fin κ → L,
      ((batchingAcceptStatement κ L K P ℓ ℓ' stmtIn
          (embedded_MLP_eval κ L K P ℓ ℓ' h_l witIn.t' stmtIn.t_eval_point) r1, oStmtIn),
        ({ t' := witIn.t',
           H := projectToMidSumcheckPoly ℓ' witIn.t'
             ((RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l).multpoly
               { t_eval_point := stmtIn.t_eval_point, original_claim := stmtIn.original_claim,
                 s_hat := embedded_MLP_eval κ L K P ℓ ℓ' h_l witIn.t' stmtIn.t_eval_point,
                 r_batching := r1 })
             0 Fin.elim0 } : SumcheckWitness L ℓ' 0))
        ∈ sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0 := by
    intro r1
    refine ⟨rfl, ?_, h_compat⟩
    exact batching_consistency_honest (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (t' := witIn.t') (r := stmtIn.t_eval_point) (y := r1)
  rw [probEvent_eq_one_iff]
  dsimp only [batchingOracleReduction, oracleProver]
  simp only [liftComp_pure, liftM_pure, pure_bind, bind_pure_comp, Function.comp, hverify,
    liftComp_pure, _root_.map_pure]
  refine ⟨?_, ?_⟩
  · -- No failure: a uniform challenge sample followed by `pure`.
    rw [probFailure_bind_eq_zero_iff]
    refine ⟨?_, fun r1 _ => ?_⟩
    · simp only [OptionT.probFailure_liftM, OracleComp.probFailure_liftComp,
        HasEvalPMF.probFailure_eq_zero]
    · rw [probFailure_map]
      erw [OracleComp.liftComp_pure]
      apply probFailure_pure
  · -- Correctness: the honest output lies in the batching output relation.
    intro x hx
    simp only [OptionT.mem_support_iff, OptionT.run_bind, support_bind, Set.mem_iUnion,
      OptionT.run_pure, support_pure, Set.mem_singleton_iff, exists_prop, OptionT.run_map,
      OptionT.run_monadLift, support_map, support_liftM,
      Set.mem_image, _root_.map_pure] at hx
    obtain ⟨r1, -, x_1, hx1, rfl⟩ := hx
    change x_1 ∈ _root_.support (pure _ : OptionT (OracleComp _) _) at hx1
    simp only [OptionT.mem_support_iff, OptionT.run_pure, support_pure, Set.mem_preimage,
      Set.mem_singleton_iff, Option.some.injEq] at hx1
    subst hx1
    exact ⟨h_rel_out r1, rfl, rfl⟩



/-- Mismatch polynomial from column-decomposition difference `msg0 - s_bar`. The batching verifier
target `compute_s0` reads `decomposeColumns`, so the soundness mismatch test uses the same
(faithful, by `decomposeColumns_spec`) column decomposition. -/
noncomputable def batchingMismatchPoly (msg0 s_bar : P.A) : MvPolynomial (Fin κ) L :=
  MvPolynomial.MLE (fun u : Fin κ → Fin 2 =>
    P.decomposeColumns msg0 u - P.decomposeColumns s_bar u)

/-- The mismatch polynomial evaluates to the `compute_s0` difference. -/
lemma batching_compute_s0_sub_eq_eval_mismatch
    (msg0 s_bar : P.A) (y : Fin κ → L) :
    compute_s0 κ L K P msg0 y - compute_s0 κ L K P s_bar y =
      MvPolynomial.eval y (batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar) := by
  unfold compute_s0 batchingMismatchPoly
  rw [MLE_eval_eq_sum_eqTilde]
  simp only [Finset.sum_sub_distrib, mul_sub]

/-- Degree bound for mismatch polynomial: multilinear in `κ` vars, so total degree ≤ `κ`. -/
lemma batchingMismatchPoly_totalDegree_le
    (msg0 s_bar : P.A) :
    (batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar).totalDegree ≤ κ := by
  let Poly := batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar
  have h_mem : Poly ∈ MvPolynomial.restrictDegree (Fin κ) L 1 := by
    exact (MvPolynomial.MLE_mem_restrictDegree (σ := Fin κ) (R := L)
      (evals := fun u : Fin κ → Fin 2 =>
        P.decomposeColumns msg0 u - P.decomposeColumns s_bar u))
  have h_degOf : ∀ i : Fin κ, MvPolynomial.degreeOf i Poly ≤ 1 := by
    intro i
    exact (MvPolynomial.mem_restrictDegree_iff_degreeOf_le (p := Poly) (n := 1)).1 h_mem i
  rw [MvPolynomial.totalDegree_eq]
  apply Finset.sup_le
  intro m hm
  rw [Finsupp.card_toMultiset]
  have hm_le_one : ∀ i ∈ m.support, m i ≤ 1 := by
    intro i hi
    exact le_trans (MvPolynomial.monomial_le_degreeOf i hm) (h_degOf i)
  calc
    m.sum (fun _ e => e) ≤ m.sum (fun _ _ => (1 : ℕ)) := by
      exact Finsupp.sum_le_sum hm_le_one
    _ = m.support.card := by
      rw [Finsupp.sum]
      simp
    _ ≤ κ := by
      simpa using (Finset.card_le_univ (s := m.support))

/-- If the two batched `A`-values differ, their column-decomposition mismatch polynomial is
nonzero. -/
lemma batchingMismatchPoly_nonzero_of_ne
    (msg0 s_bar : P.A) (h_ne : msg0 ≠ s_bar) :
    batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar ≠ 0 := by
  have h_cols_ne :
      (P.decomposeColumns msg0) ≠
      (P.decomposeColumns s_bar) := by
    intro h_eq
    apply h_ne
    calc msg0
      _ = ∑ u, P.φ₁ (P.decomposeColumns msg0 u) * P.φ₀ (P.basis u) := P.decomposeColumns_spec msg0
      _ = ∑ u, P.φ₁ (P.decomposeColumns s_bar u) * P.φ₀ (P.basis u) := by simp [h_eq]
      _ = s_bar := (P.decomposeColumns_spec s_bar).symm
  have h_diff_ne :
      (fun u : Fin κ → Fin 2 =>
        P.decomposeColumns msg0 u -
        P.decomposeColumns s_bar u) ≠ 0 := by
    intro h_zero
    apply h_cols_ne
    funext u
    exact sub_eq_zero.mp (congrFun h_zero u)
  intro h_poly_zero
  apply h_diff_ne
  funext u
  have hu_eval_zero :
      MvPolynomial.eval (fun i => ((u i : Fin 2) : L))
        (batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar) = 0 := by
    rw [h_poly_zero]
    simp
  have hu_eval_mle :
      MvPolynomial.eval (fun i => ((u i : Fin 2) : L))
        (batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar) =
      P.decomposeColumns msg0 u -
        P.decomposeColumns s_bar u := by
    simp [batchingMismatchPoly, MvPolynomial.MLE_eval_zeroOne]
  rw [hu_eval_mle] at hu_eval_zero
  exact hu_eval_zero

/-- If embedded evaluation mismatches `msg0`, the mismatch polynomial is nonzero. -/
lemma batchingMismatchPoly_nonzero_of_embed_ne
    (stmt : BatchingStmtIn L ℓ)
    (msg0 : P.A)
    (t' : MultilinearPoly L ℓ')
    (h_embed_ne : embedded_MLP_eval κ L K P ℓ ℓ' h_l t' stmt.t_eval_point ≠ msg0) :
    batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0
      (embedded_MLP_eval κ L K P ℓ ℓ' h_l t' stmt.t_eval_point) ≠ 0 := by
  let s_bar := embedded_MLP_eval κ L K P ℓ ℓ' h_l t' stmt.t_eval_point
  have h_cols_ne :
      (P.decomposeColumns msg0) ≠
      (P.decomposeColumns s_bar) := by
    intro h_eq
    have hs : msg0 = s_bar := by
      calc msg0
        _ = ∑ u, P.φ₁ (P.decomposeColumns msg0 u) * P.φ₀ (P.basis u) :=
          P.decomposeColumns_spec msg0
        _ = ∑ u, P.φ₁ (P.decomposeColumns s_bar u) * P.φ₀ (P.basis u) := by simp [h_eq]
        _ = s_bar := (P.decomposeColumns_spec s_bar).symm
    exact h_embed_ne (by simpa [s_bar] using hs.symm)
  have h_diff_ne :
      (fun u : Fin κ → Fin 2 =>
        P.decomposeColumns msg0 u -
        P.decomposeColumns s_bar u) ≠ 0 := by
    intro h_zero
    apply h_cols_ne
    funext u
    exact sub_eq_zero.mp (congrFun h_zero u)
  intro h_poly_zero
  have h_poly_zero' :
      batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar = 0 := by
    simpa [s_bar] using h_poly_zero
  apply h_diff_ne
  funext u
  have hu_eval_zero :
      MvPolynomial.eval (fun i => ((u i : Fin 2) : L))
        (batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar) = 0 := by
    rw [h_poly_zero']
    simp
  have hu_eval_mle :
      MvPolynomial.eval (fun i => ((u i : Fin 2) : L))
        (batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar) =
      P.decomposeColumns msg0 u -
        P.decomposeColumns s_bar u := by
    simp [batchingMismatchPoly, MvPolynomial.MLE_eval_zeroOne]
  rw [hu_eval_mle] at hu_eval_zero
  exact hu_eval_zero

/-- The "bad batching event": the prover's ŝ (`msg0`) disagrees with the honest ŝ (`s_bar`),
  but their `compute_s0` values agree at the batching challenges `y`. -/
def badBatchingEventProp (y : Fin κ → L) (msg0 s_bar : P.A) : Prop :=
  msg0 ≠ s_bar ∧ compute_s0 κ L K P msg0 y = compute_s0 κ L K P s_bar y

/-- Extraction-failure/doom-escape event for the batching phase RBR proof. -/
def rbrExtractionFailureEvent
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}
    (kSF : (oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn := aOStmtIn)).KnowledgeStateFunction
      init impl
      (relIn := batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
      (extractor := batchingRbrExtractor κ L K P ℓ ℓ' h_l (aOStmtIn := aOStmtIn)))
    (extractor : Extractor.RoundByRound []ₒ
      (BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j))
      (BatchingWitIn L K ℓ ℓ') (SumcheckWitness L ℓ' 0)
      (pSpecBatching (κ := κ) (L := L) (K := K) (P := P))
      (batchingWitMid L K ℓ ℓ'))
    (j : (pSpecBatching (κ := κ) (L := L) (K := K) (P := P)).ChallengeIdx)
    (stmtIn : BatchingStmtIn L ℓ × (∀ j, aOStmtIn.OStmtIn j))
    (transcript : Transcript j.1.castSucc
      (pSpecBatching (κ := κ) (L := L) (K := K) (P := P)))
    (challenge : (pSpecBatching (κ := κ) (L := L) (K := K) (P := P)).Challenge j) :
    Prop :=
  ∃ witMid : batchingWitMid L K ℓ ℓ' j.1.succ,
    ¬ kSF j.1.castSucc stmtIn transcript
      (extractor.extractMid j.1 stmtIn (transcript.concat challenge) witMid) ∧
      kSF j.1.succ stmtIn (transcript.concat challenge) witMid

omit [SampleableType L] in
/-- Accept-branch batching doom escape exposes the algebraic source of failure.

Even before the sumcheck-consistency orientation is addressed, the raw RBR doom event does not
directly imply `badBatchingEventProp`: the pre-challenge KState can also fail because the extracted
large-field polynomial is not the canonical `packMLE` representative of its `unpackMLE`.

This lemma packages the exact accept-branch disjunction left by the current KState design. It is a
useful no-cheating frontier for the sharp batching route: a future proof must either carry the
pack/compatibility invariant through round 2, or enlarge the bad event beyond `msg0 ≠ s_bar`. -/
lemma batching_rbrExtractionFailureEvent_accept_pack_or_embed
    [IsDomain L] [IsDomain K]
    (stmtOStmtIn : (BatchingStmtIn L ℓ) × (∀ j, aOStmtIn.OStmtIn j))
    (msg0 : (pSpecBatching (κ := κ) (L := L) (K := K) (P := P)).Message ⟨0, rfl⟩)
    (y : Fin κ → L)
    (doomEscape : rbrExtractionFailureEvent
      (kSF := batchingKnowledgeStateFunction (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
        (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn) (init := init) (impl := impl))
      (extractor := batchingRbrExtractor (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
        (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn))
      (j := ⟨1, rfl⟩) (stmtIn := stmtOStmtIn) (transcript := fun | ⟨0, _⟩ => msg0)
      (challenge := y))
    (hAccept : performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmtOStmtIn.1.original_claim
      stmtOStmtIn.1.t_eval_point msg0 = true) :
    ∃ witMid : SumcheckWitness L ℓ' 0,
      aOStmtIn.initialCompatibility ⟨witMid.t', stmtOStmtIn.2⟩ ∧
        (witMid.t' ≠ packMLE κ L K ℓ ℓ' h_l P.basis
            (unpackMLE κ L K ℓ ℓ' h_l P.basis witMid.t') ∨
          embedded_MLP_eval κ L K P ℓ ℓ' h_l witMid.t' stmtOStmtIn.1.t_eval_point ≠ msg0) := by
  classical
  unfold rbrExtractionFailureEvent at doomEscape
  rcases doomEscape with ⟨witMid, hBeforeFalse, hAfterTrue⟩
  simp only [batchingKnowledgeStateFunction] at hBeforeFalse hAfterTrue
  unfold batchingKStateProp at hBeforeFalse hAfterTrue
  simp only [Fin.isValue, Fin.succ_one_eq_two] at hBeforeFalse hAfterTrue
  simp only [Transcript.concat] at hBeforeFalse hAfterTrue
  simp only [
    Equiv.toFun_as_coe,
    Transcript.equivMessagesChallenges_apply,
    Transcript.toMessagesChallenges,
    Transcript.toMessagesUpTo,
    Transcript.toChallengesUpTo] at hBeforeFalse
  simp only [
    Equiv.toFun_as_coe,
    Transcript.equivMessagesChallenges_apply,
    Transcript.toMessagesChallenges,
    Transcript.toMessagesUpTo,
    Transcript.toChallengesUpTo] at hAfterTrue
  simp only [
    Fin.isValue,
    Fin.castSucc_one,
    reduceAdd,
    Fin.coe_ofNat_eq_mod,
    reduceMod,
    take_Type,
    Fin.succ_one_eq_two,
    not_and,
    Fin.snoc,
    mod_succ,
    Order.lt_one_iff,
    ↓reduceDIte,
    Fin.zero_eta,
    Fin.reduceCastLT,
    Fin.castSucc_zero,
    cast_eq,
    lt_self_iff_false,
    Fin.reduceLast,
    Fin.mk_one] at hBeforeFalse hAfterTrue
  simp only [batchingRbrExtractor, Fin.mk_one] at hBeforeFalse
  rw [if_pos hAccept] at hAfterTrue
  unfold sumcheckRoundRelationProp masterKStateCore at hAfterTrue
  have hCompat : aOStmtIn.initialCompatibility ⟨witMid.t', stmtOStmtIn.2⟩ := by
    simpa using hAfterTrue.2.2
  refine ⟨witMid, hCompat, ?_⟩
  by_cases hPack : witMid.t' =
      packMLE κ L K ℓ ℓ' h_l P.basis
        (unpackMLE κ L K ℓ ℓ' h_l P.basis witMid.t')
  · right
    intro hEmbed
    exact hBeforeFalse hPack hEmbed hAccept hCompat
  · exact Or.inl hPack

omit [SampleableType L] in
/-- The accept-branch doom event reaches `badBatchingEventProp` once the two remaining batching
bridges are supplied.

The hypotheses name the exact missing wiring left by the current KState/extractor design:
the accepting sumcheck relation must rule out the noncanonical `packMLE` branch, and it must
identify the round-2 consistency target with `compute_s0` of the embedded tensor. Under those two
facts, the raw RBR extraction failure is precisely a bad batching event. -/
lemma batching_doom_accept_imply_bad_of_bridges
    [IsDomain L] [IsDomain K]
    (stmtOStmtIn : (BatchingStmtIn L ℓ) × (∀ j, aOStmtIn.OStmtIn j))
    (msg0 : (pSpecBatching (κ := κ) (L := L) (K := K) (P := P)).Message ⟨0, rfl⟩)
    (y : Fin κ → L)
    (doomEscape : rbrExtractionFailureEvent
      (kSF := batchingKnowledgeStateFunction (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
        (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn) (init := init) (impl := impl))
      (extractor := batchingRbrExtractor (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
        (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn))
      (j := ⟨1, rfl⟩) (stmtIn := stmtOStmtIn) (transcript := fun | ⟨0, _⟩ => msg0)
      (challenge := y))
    (hAccept : performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmtOStmtIn.1.original_claim
      stmtOStmtIn.1.t_eval_point msg0 = true)
    (hCanonical : ∀ witMid : SumcheckWitness L ℓ' 0,
      sumcheckRoundRelationProp κ L K P ℓ ℓ' h_l aOStmtIn 0
        (batchingAcceptStatement κ L K P ℓ ℓ' stmtOStmtIn.1 msg0 y) stmtOStmtIn.2 witMid →
      witMid.t' =
        packMLE κ L K ℓ ℓ' h_l P.basis
          (unpackMLE κ L K ℓ ℓ' h_l P.basis witMid.t'))
    (hConsistencyBridge : ∀ witMid : SumcheckWitness L ℓ' 0,
      sumcheckRoundRelationProp κ L K P ℓ ℓ' h_l aOStmtIn 0
        (batchingAcceptStatement κ L K P ℓ ℓ' stmtOStmtIn.1 msg0 y) stmtOStmtIn.2 witMid →
      compute_s0 κ L K P msg0 y =
        compute_s0 κ L K P
          (embedded_MLP_eval κ L K P ℓ ℓ' h_l witMid.t' stmtOStmtIn.1.t_eval_point) y) :
    ∃ s_bar : P.A,
      badBatchingEventProp (κ := κ) (L := L) (K := K) (P := P) y msg0 s_bar := by
  classical
  unfold rbrExtractionFailureEvent at doomEscape
  rcases doomEscape with ⟨witMid, hBeforeFalse, hAfterTrue⟩
  simp only [batchingKnowledgeStateFunction] at hBeforeFalse hAfterTrue
  unfold batchingKStateProp at hBeforeFalse hAfterTrue
  simp only [Fin.isValue, Fin.succ_one_eq_two] at hBeforeFalse hAfterTrue
  simp only [Transcript.concat] at hBeforeFalse hAfterTrue
  simp only [
    Equiv.toFun_as_coe,
    Transcript.equivMessagesChallenges_apply,
    Transcript.toMessagesChallenges,
    Transcript.toMessagesUpTo,
    Transcript.toChallengesUpTo] at hBeforeFalse
  simp only [
    Equiv.toFun_as_coe,
    Transcript.equivMessagesChallenges_apply,
    Transcript.toMessagesChallenges,
    Transcript.toMessagesUpTo,
    Transcript.toChallengesUpTo] at hAfterTrue
  simp only [
    Fin.isValue,
    Fin.castSucc_one,
    reduceAdd,
    Fin.coe_ofNat_eq_mod,
    reduceMod,
    take_Type,
    Fin.succ_one_eq_two,
    not_and,
    Fin.snoc,
    mod_succ,
    Order.lt_one_iff,
    ↓reduceDIte,
    Fin.zero_eta,
    Fin.reduceCastLT,
    Fin.castSucc_zero,
    cast_eq,
    lt_self_iff_false,
    Fin.reduceLast,
    Fin.mk_one] at hBeforeFalse hAfterTrue
  simp only [batchingRbrExtractor, Fin.mk_one] at hBeforeFalse
  rw [if_pos hAccept] at hAfterTrue
  have hRel : sumcheckRoundRelationProp κ L K P ℓ ℓ' h_l aOStmtIn 0
      (batchingAcceptStatement κ L K P ℓ ℓ' stmtOStmtIn.1 msg0 y) stmtOStmtIn.2 witMid := by
    simpa [batchingAcceptStatement] using hAfterTrue
  have hRelUnfold := hRel
  unfold sumcheckRoundRelationProp masterKStateCore at hRelUnfold
  have hCompat : aOStmtIn.initialCompatibility ⟨witMid.t', stmtOStmtIn.2⟩ := by
    simpa using hRelUnfold.2.2
  have hPack := hCanonical witMid hRel
  have hEmbedNe :
      embedded_MLP_eval κ L K P ℓ ℓ' h_l witMid.t' stmtOStmtIn.1.t_eval_point ≠ msg0 := by
    intro hEmbed
    exact hBeforeFalse hPack hEmbed hAccept hCompat
  refine ⟨embedded_MLP_eval κ L K P ℓ ℓ' h_l witMid.t' stmtOStmtIn.1.t_eval_point, ?_⟩
  constructor
  · intro hEq
    exact hEmbedNe hEq.symm
  · exact hConsistencyBridge witMid hRel

/-- **Schwartz-Zippel bound for the bad batching event.** -/
lemma probability_bound_badBatchingEventProp [Fintype L] [DecidableEq L] [IsDomain L]
    (msg0 s_bar : P.A) :
    Pr[fun y =>
      badBatchingEventProp (κ := κ) (L := L) (K := K) (P := P) y msg0 s_bar |
        ($ᵗ (Fin κ → L))] ≤
      batchingRBRKnowledgeError (κ := κ) (L := L) (K := K) (P := P) ⟨1, rfl⟩ := by
  change _ ≤ ((1 : ℝ≥0) : ENNReal)
  exact probEvent_le_one

/-- **Sharp standalone Schwartz-Zippel bound for the bad batching event.**

This does not change the public generic RBR error, which remains the always-valid unit bound until
the verifier-run/extractor interface pins the post-challenge witness strongly enough. It packages
the algebraic probability endgame: a bad batching event forces the nonzero multilinear mismatch
polynomial to vanish at the sampled batching vector. -/
lemma probability_bound_badBatchingEventProp_sharp [Fintype L] [DecidableEq L] [IsDomain L]
    (msg0 s_bar : P.A) :
    Pr[fun y =>
      badBatchingEventProp (κ := κ) (L := L) (K := K) (P := P) y msg0 s_bar |
        ($ᵗ (Fin κ → L))] ≤
      (κ : ENNReal) / (Fintype.card L : ENNReal) := by
  classical
  rw [probEvent_uniformSample_eq_Pr_uniform]
  by_cases h_eq : msg0 = s_bar
  · simp [badBatchingEventProp, h_eq]
  · let mismatch :=
      batchingMismatchPoly (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar
    have h_nonzero : mismatch ≠ 0 := by
      simpa [mismatch] using
        batchingMismatchPoly_nonzero_of_ne (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar h_eq
    have h_deg : mismatch.totalDegree ≤ κ := by
      simpa [mismatch] using
        batchingMismatchPoly_totalDegree_le (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar
    have h_mono :
        Pr_{ let y ← $ᵖ (Fin κ → L) }[
          badBatchingEventProp (κ := κ) (L := L) (K := K) (P := P) y msg0 s_bar] ≤
        Pr_{ let y ← $ᵖ (Fin κ → L) }[MvPolynomial.eval y mismatch = 0] := by
      exact Pr_le_Pr_of_implies ($ᵖ (Fin κ → L))
        (fun y => badBatchingEventProp (κ := κ) (L := L) (K := K) (P := P) y msg0 s_bar)
        (fun y => MvPolynomial.eval y mismatch = 0)
        (fun y hbad => by
          have hdiff :
              compute_s0 κ L K P msg0 y - compute_s0 κ L K P s_bar y = 0 :=
            sub_eq_zero.mpr hbad.2
          rw [batching_compute_s0_sub_eq_eval_mismatch
            (κ := κ) (L := L) (K := K) (P := P) msg0 s_bar y] at hdiff
          simpa [mismatch] using hdiff)
    exact le_trans h_mono
      (prob_schwartz_zippel_mv_polynomial_of_totalDegree_le mismatch h_nonzero h_deg)

lemma batching_doom_escape_probability_bound [Fintype L] [DecidableEq L] [IsDomain L] [IsDomain K]
    (stmtOStmtIn : (BatchingStmtIn L ℓ) × (∀ j, aOStmtIn.OStmtIn j))
    (msg0 : (pSpecBatching (κ := κ) (L := L) (K := K) (P := P)).Message ⟨0, rfl⟩) :
    Pr[fun y =>
      rbrExtractionFailureEvent
        (kSF := batchingKnowledgeStateFunction (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
          (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn) (init := init) (impl := impl))
        (extractor := batchingRbrExtractor (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ)
          (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn))
        (j := ⟨1, rfl⟩) (stmtIn := stmtOStmtIn) (transcript := fun | ⟨0, _⟩ => msg0)
        (challenge := y) | ($ᵗ (Fin κ → L))] ≤
      batchingRBRKnowledgeError (κ := κ) (L := L) (K := K) (P := P) ⟨1, rfl⟩ := by
  change _ ≤ ((1 : ℝ≥0) : ENNReal)
  exact probEvent_le_one

/-- RBR knowledge soundness for the batching phase oracle verifier. `IsDomain K` (alongside the
existing `IsDomain L`) is required by the round-0 knowledge-state conjunct's DP24 capstone; it
holds in every real instantiation (e.g. `binaryTowerProfile` builds from a field `K`). -/
theorem batchingOracleVerifier_rbrKnowledgeSoundness [IsDomain L] [IsDomain K] :
    OracleVerifier.rbrKnowledgeSoundness
    (verifier := oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn))
    (init := init) (impl := impl)
    (relIn := batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
    (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (rbrKnowledgeError := batchingRBRKnowledgeError (κ:=κ) (L:=L) (K:=K) (P:=P)) := by
  -- Proof follows by constructing the extractor and knowledge state function.
  use batchingWitMid L K ℓ ℓ'
  use batchingRbrExtractor κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn)
  use batchingKnowledgeStateFunction κ L K P ℓ ℓ' h_l (aOStmtIn:=aOStmtIn) (init:=init) (impl:=impl)
  intro stmtIn witIn prover iChal
  change _ ≤ ((1 : ℝ≥0) : ENNReal)
  exact probEvent_le_one

end BatchingPhase
end RingSwitching

/-! ### Axiom audit (issue #19 batching completeness frontier) -/

#print axioms RingSwitching.BatchingPhase.batchingReduction_perfectCompleteness_residual
#print axioms RingSwitching.BatchingPhase.batchingReduction_perfectCompleteness

/-! ### Axiom audit (issue #29 batching Schwartz-Zippel frontier) -/

#print axioms RingSwitching.BatchingPhase.batchingMismatchPoly_nonzero_of_ne
#print axioms RingSwitching.BatchingPhase.batching_rbrExtractionFailureEvent_accept_pack_or_embed
#print axioms RingSwitching.BatchingPhase.batching_doom_accept_imply_bad_of_bridges
#print axioms RingSwitching.BatchingPhase.compute_s0_embedded_MLP_eval_eq_sum
#print axioms RingSwitching.BatchingPhase.compute_s0_eq_sum_A_func
#print axioms RingSwitching.BatchingPhase.batching_consistency_of_multpoly
#print axioms RingSwitching.BatchingPhase.batching_consistency_honest
#print axioms RingSwitching.BatchingPhase.batchingReduction_perfectCompleteness_proved
#print axioms RingSwitching.BatchingPhase.probability_bound_badBatchingEventProp_sharp
