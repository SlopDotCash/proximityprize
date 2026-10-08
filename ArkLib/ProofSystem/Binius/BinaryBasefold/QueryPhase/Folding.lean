/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness
import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
import ArkLib.OracleReduction.Completeness
import ArkLib.OracleReduction.Basic
import ArkLib.Data.Misc.Basic

/-!
## Query Phase (Final Query Round)
The final verification phase (proximity testing) as an oracle reduction.
(Note that here `B_k` means the boolean hypercube of dimension `k`)

- `V` executes the following querying procedure:
  for `γ` repetitions do
    `V` samples a challenge `v ← B_{ℓ+R}` randomly and sends it to P.
    for `i in {0, ϑ, ..., ℓ-ϑ}` (i.e., taking `ϑ`-sized steps) do
      for each `u` in `B_v`, => gather data for `c_{i+ϑ}`
        `V` sends (query, [f^(i)], (u_0, ..., u_{ϑ-1}, v_{i+ϑ}, ..., v_{ℓ+R-1})) to the oracle.
      if `i > 0` then `V` requires `c_i ?= f^(i)(v_i, ..., v_{ℓ+R-1})`.
      `V` defines `c_{i+ϑ} := fold(f^(i), r'_i, ..., r'_{i+ϑ-1})(v_{i+ϑ}, ..., v_{ℓ+R-1})`.
    `V` requires `c_ℓ ?= c`.
-/

namespace Binius.BinaryBasefold.QueryPhase

noncomputable section
open OracleSpec OracleComp
open AdditiveNTT Polynomial MvPolynomial ProtocolSpec
open Binius.BinaryBasefold.CoreInteraction

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal ProbabilityTheory

section FinalQueryRoundIOR

/-!
### Oracle-Aware Reduction Logic for Query Phase

The query phase uses `OracleAwareReductionLogicStep` because its verifier check involves
oracle queries (querying committed codewords at fiber points).
-/

/-- The oracle-aware reduction logic step for the query phase.

This encapsulates the pure logic of the query phase:
- `verifierCheck`: Runs `verifyQueryPhase` which queries oracles for fiber evaluations
- `verifierOut`: Returns `true` (acceptance) or `false` (rejection)
- `honestProverTranscript`: The honest transcript just receives the challenges
- `proverOut`: The honest prover always outputs `(true, ())` -/
instance instQueryChallengeFintype : ∀ j, Fintype ((pSpecQuery 𝔽q β γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge j)
  | ⟨0, _⟩ => by
    haveI : Fintype (sDomain 𝔽q β h_ℓ_add_R_rate 0) :=
      fintype_sDomain 𝔽q β h_ℓ_add_R_rate 0
    exact inferInstanceAs
      (Fintype (Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0))

instance instQuerySpecFintype :
    ∀ t, Fintype ([(pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge]ₒ.Range t)
  | ⟨⟨⟨0, _⟩, _⟩, _⟩ => by
    haveI : Fintype (sDomain 𝔽q β h_ℓ_add_R_rate 0) := fintype_sDomain 𝔽q β h_ℓ_add_R_rate 0
    exact inferInstanceAs (Fintype (Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0))

instance instQuerySpecInhabited :
    ∀ t, Inhabited ([(pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge]ₒ.Range t)
  | ⟨⟨⟨0, _⟩, _⟩, _⟩ => ⟨fun _ => 0⟩

instance instQueryChallengeInhabited : ∀ j, Inhabited ((pSpecQuery 𝔽q β γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge j)
  | ⟨0, _⟩ => ⟨fun _ => 0⟩

omit [CharP L 2] [SampleableType L] in
/-- Congruence of `single_point_localized_fold_matrix_form` under a (propositionally equal)
change of destination index. Reconstructed (the original was deleted); models
`extractSuffixFromChallenge_congr_destIdx`. -/
lemma single_point_localized_fold_matrix_form_congr_dest_index
    {i : Fin r} {steps : ℕ} {destIdx destIdx' : Fin r}
    {h_destIdx : destIdx.val = i.val + steps} {h_destIdx_le : destIdx ≤ ℓ}
    {r_challenges : Fin steps → L} {y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx}
    {fiber_eval_mapping : Fin (2 ^ steps) → L}
    (h_destIdx_eq_destIdx' : destIdx = destIdx') :
    single_point_localized_fold_matrix_form 𝔽q β i steps h_destIdx h_destIdx_le r_challenges y
        fiber_eval_mapping
      = single_point_localized_fold_matrix_form 𝔽q β i steps
          (h_destIdx_eq_destIdx' ▸ h_destIdx) (h_destIdx_eq_destIdx' ▸ h_destIdx_le) r_challenges
          (h_destIdx_eq_destIdx' ▸ y) fiber_eval_mapping := by
  subst h_destIdx_eq_destIdx'
  rfl

omit [CharP L 2] [SampleableType L] in
/-- Congruence of `single_point_localized_fold_matrix_form` under a (propositionally equal)
change of the `steps` index. Mirror of `single_point_localized_fold_matrix_form_congr_dest_index`
over the `steps` index. -/
lemma single_point_localized_fold_matrix_form_congr_steps_index
    {i : Fin r} {steps steps' : ℕ} {destIdx : Fin r}
    {h_destIdx : destIdx.val = i.val + steps} {h_destIdx_le : destIdx ≤ ℓ}
    {r_challenges : Fin steps → L} {y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx}
    {fiber_eval_mapping : Fin (2 ^ steps) → L}
    (h_steps_eq_steps' : steps = steps') :
    single_point_localized_fold_matrix_form 𝔽q β i steps h_destIdx h_destIdx_le r_challenges y
        fiber_eval_mapping
      = single_point_localized_fold_matrix_form 𝔽q β i steps'
          (h_steps_eq_steps' ▸ h_destIdx) h_destIdx_le
          (h_steps_eq_steps' ▸ r_challenges) y
          (h_steps_eq_steps' ▸ fiber_eval_mapping) := by
  subst h_steps_eq_steps'
  rfl

/-- For a block index `k < ℓ / ϑ` (with `ϑ ∣ ℓ`), the block end `(k + 1) * ϑ`
is `≤ ℓ`. Product-form companion of `k_succ_mul_ϑ_le_ℓ_₂`. -/
lemma k_succ_mul_ϑ_le_ℓ (k : Fin (ℓ / ϑ)) : (k.val + 1) * ϑ ≤ ℓ := by
  have h := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  rw [Nat.add_mul, Nat.one_mul]
  omega

noncomputable def queryPhaseLogicStep :
    OracleAwareReductionLogicStep
      -- oSpec is the base/shared oracle (empty for query phase - no random oracles)
      -- The structure internally uses oSpec + ([OracleIn]ₒ + [pSpec.Message]ₒ)
      (oSpec := []ₒ)
      (StmtIn := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
      (WitIn := Unit)
      (OracleIn := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (OracleOut := fun _ : Empty => Unit)
      (StmtOut := Bool)
      (WitOut := Unit)
      (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  -- Relations
  completeness_relIn := strictFinalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  completeness_relOut := acceptRejectOracleRel
  -- Verifier (Oracle-Aware): verifierCheck queries oracles and returns StmtOut
  -- Iterates through all γ_repetitions and checks each one
  verifierCheck := fun stmtIn transcript => do
    let challenges := transcript.challenges
    let fold_challenges : Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0 :=
      challenges ⟨0, by rfl⟩
    for rep in (List.finRange γ_repetitions) do
      let v := fold_challenges rep
      let _ ← checkSingleRepetition 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        v stmtIn stmtIn.final_constant
    return true  -- StmtOut = Bool for QueryPhase
  -- Pure output computation (deterministic)
  verifierOut := fun _stmtIn _transcript => true
  -- Oracle embedding (no output oracles for query phase)
  embed := ⟨Empty.elim, fun a _ => Empty.elim a⟩
  hEq := fun i => Empty.elim i
  -- Honest prover transcript: just receives the challenges
  honestProverTranscript := fun stmtIn _witIn _oStmtIn challenges =>
    FullTranscript.mk1 (challenges ⟨0, by rfl⟩)
  -- Prover output: always outputs (true, ())
  proverOut := fun _stmtIn _witIn _oStmtIn _transcript =>
    ((true, fun i => Empty.elim i), ())

def queryPhaseProverState : Fin (1 + 1) → Type := fun
  | 0 => FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ) ×
    (∀ i, OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) i) × Unit
  | 1 => FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ) ×
    (∀ i, OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) i) × Unit ×
    (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge ⟨0, by rfl⟩

/-- The oracle prover for the final query phase.

Uses components from `queryPhaseLogicStep` for consistency with the logic specification. -/
noncomputable def queryOracleProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStmtIn := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (WitIn := Unit)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (WitOut := Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  -- Prover state: tracks (stmtIn, oStmtIn, witIn) and optionally the challenges
  PrvState := queryPhaseProverState 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  input := fun ⟨⟨stmtIn, oStmtIn⟩, witIn⟩ => (stmtIn, oStmtIn, witIn)
  sendMessage
  | ⟨0, h⟩ => nomatch h
  receiveChallenge
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩  => do
    -- V sends all γ challenges v₁, ..., v_γ
    pure (fun challenges => (stmtIn, oStmtIn, witIn, challenges))
  output := fun ⟨stmtIn, oStmtIn, witIn, challenges⟩ => do
    -- Build the transcript using the logic step's honestProverTranscript
    let transcript := FullTranscript.mk1 (pSpec :=
      pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (challenges)
    -- Delegate to proverOut from the logic step
    pure ((queryPhaseLogicStep 𝔽q β γ_repetitions).proverOut stmtIn witIn oStmtIn transcript)

/-- The oracle verifier for the final query phase.

Uses components from `queryPhaseLogicStep` for consistency with the logic specification:
- `verifierCheck`: monadic check via `verifyQueryPhase`
- `verifierOut`: pure output computation
- `embed` and `hEq`: oracle embedding from the logic step -/
noncomputable def queryOracleVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStmtIn := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  verify := fun stmtIn challenges => do
    let transcript := FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (challenges ⟨0, by rfl⟩)
    let logic : OracleAwareReductionLogicStep []ₒ (FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ)) Unit
        (OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
        (fun _ : Empty => Unit) Bool Unit
        (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
      queryPhaseLogicStep 𝔽q β γ_repetitions
    let _ ← logic.verifierCheck stmtIn transcript
    pure (logic.verifierOut stmtIn transcript)
  -- Use embed and hEq from the logic step
  embed := (queryPhaseLogicStep 𝔽q β γ_repetitions).embed
  hEq := (queryPhaseLogicStep 𝔽q β γ_repetitions).hEq

/-- The oracle reduction for the final query phase. -/
noncomputable def queryOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStmtIn := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (WitIn := Unit)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (WitOut := Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  prover := queryOracleProver 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  verifier := queryOracleVerifier 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

/-- The final query round as an `OracleProof` (since it outputs Bool and no oracle statements). -/
noncomputable def queryOracleProof : OracleProof
    (oSpec := []ₒ)
    (Statement := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStatement := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (Witness := Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  queryOracleReduction 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

lemma OracleComp.liftM_query_eq_liftM_liftM.{u, v, z}
    {ι : Type u} {spec : OracleSpec ι} {m : Type v → Type z}
    [MonadLift (OracleComp spec) m] {α : Type v}
    (q : OracleQuery spec α) :
    (liftM q : m α) = liftM (liftM q : OracleComp spec α) := rfl

omit [CharP L 2] [SampleableType L] in
lemma mem_support_queryFiberPoints
    -- The number of oracles in query phase is toCodewordsCount(ℓ) = ℓ/ϑ
    {oraclePositionIdx : Fin (ℓ / ϑ)} (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (f_i_on_fiber : Vector L (2 ^ ϑ))
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn :
      ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (challenges : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges)
    -- Hypothesis: The fiber evaluations come from the simulated oracle query
    (h_fiber_mem :
      let step := queryPhaseLogicStep 𝔽q β γ_repetitions
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmtIn transcript.messages
      some (f_i_on_fiber) ∈
      support (simulateQ.{0, 0, 0} so
        ((queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oraclePositionIdx v)))) :
    let k_th_oracleIdx: Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
      ⟨oraclePositionIdx, by simp only [toOutCodewordsCount, Fin.val_last,
        lt_self_iff_false, ↓reduceIte, add_zero, Fin.is_lt];⟩
    ∀ (fiberIndex : Fin (2 ^ ϑ)),
      f_i_on_fiber.get fiberIndex =
      (oStmtIn k_th_oracleIdx (getFiberPoint 𝔽q β oraclePositionIdx v fiberIndex)) := by
  simp only [MessageIdx] at h_fiber_mem
  set step : OracleAwareReductionLogicStep []ₒ (FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ)) Unit
      (OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (fun _ : Empty => Unit) Bool Unit
      (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
    queryPhaseLogicStep 𝔽q β γ_repetitions with h_step
  set transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges with h_transcript
  set so := OracleInterface.simOracle2 []ₒ oStmtIn transcript.messages with h_so
  -- rw [simulateQ_liftComp] at h_fiber_mem
  unfold queryFiberPoints at h_fiber_mem
  simp only [bind_pure] at h_fiber_mem
  unfold queryCodeword at h_fiber_mem
  -- Simplify the simulation through liftComp/liftM
  -- simp_rw [← simulateQ_liftComp] at h_fiber_mem
  -- simp only [liftComp_eq_liftM] at h_fiber_mem
  -- Step 1: Unpack Vector.mapM membership
  erw [OptionT.simulateQ_vector_mapM] at h_fiber_mem
  erw [OptionT.mem_support_vector_mapM] at h_fiber_mem
  -- simp only [liftM, monadLift, MonadLift.monadLift] at h_fiber_mem
  conv_rhs at h_fiber_mem =>
    erw [simulateQ_liftComp]
    simp only [MessageIdx, Message, Fin.getElem_fin, Vector.getElem_mk, OptionT.run_monadLift,
      simulateQ_map, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      OptionT.mem_support_iff, toPFunctor_emptySpec, OptionT.support_run_eq, support_map,
      Set.mem_image, Option.some.injEq, exists_eq_right]
    erw [simulateQ_map]
    erw [simulateQ_query]
    erw [simulateQ_simOracle2_lift_liftComp_query_T1]
  simp only [monadLift_self, LawfulApplicative.map_pure, support_pure,
    Set.mem_singleton_iff] at h_fiber_mem ⊢
  intro fiberIndex
  have h_res := h_fiber_mem fiberIndex
  have h_ans : ∀ (q : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨(⟨oraclePositionIdx.val, by
        simp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false, ↓reduceIte,
          add_zero, Fin.is_lt]⟩ : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ))).val * ϑ, by
        have := toCodewordsCount_mul_ϑ_lt_ℓ ℓ ϑ (Fin.last ℓ)
          ⟨oraclePositionIdx.val, by
            simp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false, ↓reduceIte,
              add_zero, Fin.is_lt]⟩
        omega⟩),
      OracleInterface.answer (oStmtIn ⟨oraclePositionIdx.val, by
        simp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false, ↓reduceIte,
          add_zero, Fin.is_lt]⟩) q
        = oStmtIn ⟨oraclePositionIdx.val, by
        simp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false, ↓reduceIte,
          add_zero, Fin.is_lt]⟩ q := fun _ => rfl
  simp only [OracleQuery.cont_query, id_eq, h_ans, Array.getElem_finRange, Fin.cast_mk,
    Fin.eta] at h_res
  simpa only [Vector.get_eq_getElem, id_eq] using (Option.some.inj h_res)

/-! Simulated `queryFiberPoints` has zero failure probability. -/
omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ in
lemma probFailure_simulateQ_queryFiberPoints_eq_zero
    (so : QueryImpl
      ([]ₒ + ([OracleStatement 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ +
        [(pSpecQuery 𝔽q β γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ))
      (OracleComp []ₒ))
    (k : Fin (List.finRange (ℓ / ϑ)).length)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    Pr[⊥ |
      OptionT.mk
        (simulateQ.{0, 0, 0} so
          (queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ((List.finRange (ℓ / ϑ)).get k) v))] = 0 := by
  dsimp only [queryFiberPoints, queryCodeword, OptionT.mk]
  erw [simulateQ_bind]
  erw [OptionT.probFailure_mk_do_bind_eq_zero_iff.{0, 0}]
  constructor
  · erw [OptionT.simulateQ_vector_mapM]
    simp only [MessageIdx, Message, List.get_eq_getElem, HasEvalPMF.probFailure_eq_zero]
  · intro x hx_mem_support
    erw [OptionT.simulateQ_vector_mapM.{0}] at hx_mem_support
    cases x with
    | none =>
      exact absurd hx_mem_support
        (OptionT.not_mem_support_run_none_of_probFailure_eq_zero _ (by
          apply OptionT.probFailure_vector_mapM_eq_zero
          intro x _
          erw [OptionT.probFailure_eq (m := OracleComp []ₒ)]
          simp only [HasEvalPMF.probFailure_eq_zero, zero_add]
          rw [probOutput_eq_zero_iff]
          erw [simulateQ_map]
          simp))
    | some a =>
      simp only [OptionT.mk]
      erw [simulateQ_pure, probFailure_pure]

lemma getBit_eq_testBit (n k : ℕ) : Nat.getBit k n = 1 ↔ Nat.testBit n k = true := by
  unfold Nat.getBit Nat.testBit
  have h : n >>> k &&& 1 = 1 &&& n >>> k := Nat.land_comm _ _
  rw [h]
  cases h_eq : 1 &&& n >>> k
  · simp
  · case succ m =>
    have h_le : m + 1 ≤ 1 := by
      calc m + 1 = 1 &&& n >>> k := h_eq.symm
        _ ≤ 1 := Nat.and_le_left
    have h_m_0 : m = 0 := by omega
    subst h_m_0
    simp


/-- Lemma 1 (Safety):
Proves that if `c_k` is the result of `iterated_fold` up to step `k`,
it must match the oracle evaluation at that step (provided by `h_relIn`).
-/
lemma query_phase_consistency_guard_safe
    {k : Fin (ℓ / ϑ)}
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (c_k : L)
    (f_i_on_fiber : Vector L (2 ^ ϑ))
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((stmtIn, oStmtIn), witIn))
    -- Hypothesis: c_k is the correct iterated fold value up to this point
    (h_c_k_correct :
      let := k_mul_ϑ_lt_ℓ (k := k)
      let := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
      c_k = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := k.val * ϑ)
        (destIdx := ⟨k.val * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)
        (f := getFirstOracle 𝔽q β oStmtIn)
        (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ)
          stmtIn.challenges 0 (by simp only [zero_add, Fin.val_last]; omega))
        (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add])
        (extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
          (destIdx := ⟨k.val * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)))
    -- Hypothesis: We are at a step > 0 where a check actually happens
    (h_k_pos : k.val * ϑ > 0)
    (challenges : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges)
    -- Hypothesis: The fiber evaluations come from the simulated oracle query
    (h_fiber_mem :
      let step := queryPhaseLogicStep 𝔽q β γ_repetitions
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmtIn transcript.messages
      some (f_i_on_fiber) ∈
      support (simulateQ.{0, 0, 0} so
        ((queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k v)))) :
  let := k_mul_ϑ_lt_ℓ (k := k)
  c_k = f_i_on_fiber.get (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (v := v) (i := ⟨k.val * ϑ, by omega⟩) (steps := ϑ)) := by
  have _ := h_k_pos
  have h_fiber_val := mem_support_queryFiberPoints 𝔽q β γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oraclePositionIdx := k) v f_i_on_fiber stmtIn
    oStmtIn witIn challenges (h_fiber_mem := h_fiber_mem)
  simp only at h_fiber_val
  rw [h_c_k_correct]
  simp only
  have h₁ : k.val * ϑ < ℓ := k_mul_ϑ_lt_ℓ (k := k)
  set destIdx : Fin r := ⟨k.val * ϑ, by omega⟩ with h_destIdx_eq
  conv_rhs => rw [h_fiber_val]
  dsimp only [strictFinalSumcheckRelOut, strictFinalSumcheckRelOutProp,
    strictfinalSumcheckStepFoldingStateProp] at h_relIn
  simp only [Fin.val_last, exists_and_right, Subtype.exists] at h_relIn
  rcases h_relIn with ⟨exists_t_MLP, _⟩
  rcases exists_t_MLP with ⟨t, h_t_mem_support, h_strictOracleFoldingConsistency⟩
  dsimp only [strictOracleFoldingConsistencyProp] at h_strictOracleFoldingConsistency
  -- Now extract the oStmtIn equality at position k
  have h_oStmtIn_k_eq := h_strictOracleFoldingConsistency ⟨k.val,
    by simp only [toOutCodewordsCount_last, Fin.is_lt]⟩
  simp only [id_eq] at h_oStmtIn_k_eq
  conv_rhs => rw [h_oStmtIn_k_eq]
  -- The correctly-typed equivalent lives in `QueryPhaseSuffix.lean` (the deleted local lemma was
  -- ill-typed: it fed a `Fin r`-indexed source into an `Fin ℓ`-typed obligation, so elaborating its
  -- statement ground `isDefEq` to the heartbeat cap). `previousSuffix_eq_getFiberPoint…` is exactly
  -- `extractSuffixFromChallenge (block source j·ϑ) = getFiberPoint j (extractMiddleFinMask …)`.
  have h_point_eq : extractSuffixFromChallenge 𝔽q β v ⟨↑k * ϑ, by omega⟩ (by simp only; omega) =
      getFiberPoint 𝔽q β k v (extractMiddleFinMask 𝔽q β v ⟨↑k * ϑ, by omega⟩ ϑ) :=
    previousSuffix_eq_getFiberPoint_extractMiddleFinMask 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k v
  -- `set destIdx` above folded the literal `⟨k*ϑ, _⟩`; expose it again so `h_point_eq` matches.
  rw [h_point_eq]
  rw [← polyToOracleFunc_eq_getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (t := ⟨t, h_t_mem_support⟩) (i := Fin.last ℓ)
    (challenges := stmtIn.challenges) (oStmt := oStmtIn)
    (h_consistency := h_strictOracleFoldingConsistency)]
  rfl

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
private lemma query_step_value_of_support_pos
    {k : Fin (ℓ / ϑ)}
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (c_k : L) (s' : L) -- The next state (c_next)
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((stmtIn, oStmtIn), ()))
    (h_c_k_correct_of_k_pos :
      let := k_mul_ϑ_lt_ℓ (k := k)
      let := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
      if _ : k.val > 0 then
        c_k = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := k.val * ϑ)
          (destIdx := ⟨k.val * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)
          (f := getFirstOracle 𝔽q β oStmtIn)
          (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges
            0 (by simp only [zero_add, Fin.val_last]; omega))
          (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add])
          (extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
            (destIdx := ⟨k.val * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega))
      else True)
    -- Hypothesis: s' is a valid output of the simulated step function
    (challenges : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges)
    (h_s'_mem :
      let step := queryPhaseLogicStep 𝔽q β γ_repetitions
      let witIn : Unit := ()
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmtIn transcript.messages
      s' ∈
      support (OptionT.mk
        (simulateQ.{0, 0, 0} so
          ((checkSingleFoldingStep 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k c_k v stmtIn)))))
    (h_k_pos : k.val > 0) :
    s' = logical_computeFoldedValue 𝔽q β k v stmtIn
      (logical_queryFiberPoints 𝔽q β oStmtIn k v) := by
  let witIn : Unit := ()
  -- This is basically due to definition of s'
  -- First, convert h_s'_mem to equality form
  dsimp only [checkSingleFoldingStep] at h_s'_mem
  -- 2. Handle the conditional guard (k > 0 vs k = 0)
  --    In both cases, the core computation (query + fold) is the same.
  have h₁ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  have h₂ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  have h_ϑ_pos : ϑ > 0 := Nat.pos_of_neZero ϑ
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (by exact hdiv.out)
  let destIdx : Fin r := ⟨(k.val + 1) * ϑ, by
    have := k_succ_mul_ϑ_le_ℓ (k := k); omega⟩
  let midIdx : Fin r := ⟨k.val * ϑ, by
    have := k_succ_mul_ϑ_le_ℓ (k := k); omega⟩
  -- Case k > 0: The guard is present.
  -- **Simplify the monadic structure**
  -- fiber_vec is the vector of fiber evaluations at domain Sˆ{k * ϑ} of (y ∈ Sˆ{(k+1) * ϑ})
  -- Goal s'= fold (f^0)(r_0, ..., r_{(k+1)*ϑ-1})(y)
  have h_mul_ϑ_gt_0 : k.val * ϑ > 0 := by
    simp only [gt_iff_lt, CanonicallyOrderedAdd.mul_pos]; omega
  simp only [MessageIdx, Message, gt_iff_lt, h_mul_ϑ_gt_0, ↓reduceDIte, _root_.OracleComp.guard_eq, Fin.val_last,
    bind_pure_comp, ReduceClaim.support_mk, Set.mem_setOf_eq] at h_s'_mem
  erw [simulateQ_bind, support_bind] at h_s'_mem
  simp only [Set.mem_iUnion, exists_prop] at h_s'_mem
  rcases h_s'_mem with ⟨fiber_vec_Opt, h_fiber_vec_Opt_mem_support, h_s'_mem_support_guard⟩
  cases fiber_vec_Opt with
  | none =>
    simp [OptionT.bind, OptionT.mk, simulateQ_pure, support_pure] at h_s'_mem_support_guard
  | some fiber_vec =>
    -- h_s'_eq : s' = the evaluation at y of the folded function from fiber_vec
    -- simp only [OptionT.simulateQ_map] at h_s'_mem_support_guard
    have h_fiber_val := mem_support_queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oraclePositionIdx := k) v fiber_vec stmtIn
      oStmtIn () challenges (by exact h_fiber_vec_Opt_mem_support)
    erw [simulateQ_bind, support_bind] at h_s'_mem_support_guard
    simp only [Function.comp_apply, Set.mem_iUnion, exists_prop] at h_s'_mem_support_guard
    have h₁ : k.val * ϑ < ℓ := k_mul_ϑ_lt_ℓ (k := k)
    -- 1. Simplify failure probability to just the guard condition
    -- simp only [h_i_pos, ↓reduceIte, OptionT.simulateQ_map]
    have h_guard_pass : c_k = fiber_vec.get (extractMiddleFinMask 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v) (i := ⟨k.val * ϑ, by omega⟩) (steps := ϑ)) := by
      have h_mul_gt_0 : k.val * ϑ > 0 := by
        simp only [gt_iff_lt, CanonicallyOrderedAdd.mul_pos]
        omega
      -- 4. Apply the lemma
      have res := query_phase_consistency_guard_safe 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (k := k) (v := v) (c_k := c_k) (f_i_on_fiber := fiber_vec) (stmtIn := stmtIn)
        (oStmtIn := oStmtIn) (witIn := witIn) (h_relIn := h_relIn) (h_c_k_correct := by
        simp only at h_c_k_correct_of_k_pos
        simp only [gt_iff_lt, h_k_pos] at h_c_k_correct_of_k_pos
        exact h_c_k_correct_of_k_pos
      ) (h_k_pos := h_mul_gt_0) (γ_repetitions := γ_repetitions) (challenges := challenges)
        (h_fiber_mem := by simp only [witIn]; exact h_fiber_vec_Opt_mem_support)
      exact res
    simp only [h_guard_pass, ↓reduceIte] at h_s'_mem_support_guard
    erw [simulateQ_pure] at h_s'_mem_support_guard
    simp only [support_pure, Set.mem_singleton_iff, exists_eq_left, OptionT.simulateQ_pure,
      OptionT.support_OptionT_pure_run, Option.some.injEq] at h_s'_mem_support_guard
    -- Step 1: Use symmetry of h_s'_eq
    have h_vec : fiber_vec.get = logical_queryFiberPoints 𝔽q β oStmtIn k v := by
      funext u
      exact h_fiber_val u
    simpa only [logical_computeFoldedValue, h_vec] using h_s'_mem_support_guard

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
private lemma query_step_value_of_support_zero
    {k : Fin (ℓ / ϑ)}
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (c_k : L) (s' : L) -- The next state (c_next)
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((stmtIn, oStmtIn), ()))
    (h_c_k_correct_of_k_pos :
      let := k_mul_ϑ_lt_ℓ (k := k)
      let := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
      if _ : k.val > 0 then
        c_k = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := k.val * ϑ)
          (destIdx := ⟨k.val * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)
          (f := getFirstOracle 𝔽q β oStmtIn)
          (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges
            0 (by simp only [zero_add, Fin.val_last]; omega))
          (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add])
          (extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
            (destIdx := ⟨k.val * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega))
      else True)
    -- Hypothesis: s' is a valid output of the simulated step function
    (challenges : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges)
    (h_s'_mem :
      let step := queryPhaseLogicStep 𝔽q β γ_repetitions
      let witIn : Unit := ()
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmtIn transcript.messages
      s' ∈
      support (OptionT.mk
        (simulateQ.{0, 0, 0} so
          ((checkSingleFoldingStep 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k c_k v stmtIn)))))
    (h_k_pos : ¬ k.val > 0) :
    s' = logical_computeFoldedValue 𝔽q β k v stmtIn
      (logical_queryFiberPoints 𝔽q β oStmtIn k v) := by
  -- This is basically due to definition of s'
  -- First, convert h_s'_mem to equality form
  dsimp only [checkSingleFoldingStep] at h_s'_mem
  -- 2. Handle the conditional guard (k > 0 vs k = 0)
  --    In both cases, the core computation (query + fold) is the same.
  have h₁ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  have h₂ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  have h_ϑ_pos : ϑ > 0 := Nat.pos_of_neZero ϑ
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (by exact hdiv.out)
  let destIdx : Fin r := ⟨(k.val + 1) * ϑ, by
    have := k_succ_mul_ϑ_le_ℓ (k := k); omega⟩
  let midIdx : Fin r := ⟨k.val * ϑ, by
    have := k_succ_mul_ϑ_le_ℓ (k := k); omega⟩
  -- Case k = 0: No guard.
  ---------------------------------------------------------------------
  -- First establish that k = 0
  simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at h_k_pos
  have h_mul_eq_0 : ↑k * ϑ = 0 := by
    rw [h_k_pos]; simp only [zero_mul]
  have h_k_eq_0 : k.val = 0 := by
    by_contra h_ne
    have : k.val > 0 := Nat.pos_of_ne_zero h_ne
    have : k.val * ϑ > 0 := Nat.mul_pos this (Nat.pos_of_neZero ϑ)
    omega
  have h_index_nonempty : 0 < ℓ / ϑ := by omega
  let k_zero : Fin (ℓ / ϑ) := ⟨0, h_index_nonempty⟩
  have h_k_eq_zero : k = k_zero := Fin.eq_of_val_eq h_k_eq_0
  subst k
  dsimp only [k_zero, Fin.val_mk] at h_s'_mem ⊢
  simp only [zero_mul, zero_add] at h_s'_mem ⊢
  simp only [MessageIdx, Message, gt_iff_lt, lt_self_iff_false, ↓reduceDIte, Fin.mk_zero',
    Fin.val_last, bind_pure_comp, ReduceClaim.support_mk,
    Set.mem_setOf_eq] at h_s'_mem
  erw [simulateQ_bind, support_bind] at h_s'_mem
  simp only [Set.mem_iUnion, exists_prop] at h_s'_mem
  rcases h_s'_mem with ⟨fiber_vec_Opt, h_fiber_vec_Opt_mem_support, h_s'_mem_support_guard⟩
  cases fiber_vec_Opt with
  | none =>
    simp [OptionT.bind, OptionT.mk, simulateQ_pure, support_pure] at h_s'_mem_support_guard
  | some fiber_vec =>
    -- **Simplify the monadic structure**
    simp only [LawfulApplicative.map_pure] at h_s'_mem_support_guard
    erw [simulateQ_pure] at h_s'_mem_support_guard
    simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at h_s'_mem_support_guard
    -- h_s'_mem_support_guard : s' = single_point_localized_fold_matrix_form
    have h_fiber_val := mem_support_queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oraclePositionIdx := k_zero) v fiber_vec stmtIn
      oStmtIn () challenges (by exact h_fiber_vec_Opt_mem_support)
    -- Step 1: Use symmetry of h_s'_eq
    have h_vec : fiber_vec.get = logical_queryFiberPoints 𝔽q β oStmtIn k_zero v := by
      funext u
      exact h_fiber_val u
    simpa only [logical_computeFoldedValue, h_vec, k_zero, Fin.val_mk,
      zero_mul, zero_add, Fin.mk_zero'] using h_s'_mem_support_guard

set_option maxHeartbeats 200000 in
private lemma logical_fold_preserves_direct
    {k : Fin (ℓ / ϑ)}
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((stmtIn, oStmtIn), ()))
 :
    let := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
    logical_computeFoldedValue 𝔽q β k v stmtIn
      (logical_queryFiberPoints 𝔽q β oStmtIn k v) = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := (k.val * ϑ + ϑ))
        (destIdx := ⟨(k.val * ϑ + ϑ), by
          have hm : (k.val * ϑ + ϑ) = k.val * ϑ + ϑ := by ring
          omega⟩)
        (h_destIdx_le := by
          have hm : (k.val * ϑ + ϑ) = k.val * ϑ + ϑ := by ring
          simp only
          omega)
        (f := getFirstOracle 𝔽q β oStmtIn)
        (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0
          (by
            have hm : (k.val * ϑ + ϑ) = k.val * ϑ + ϑ := by ring
            simp only [zero_add, Fin.val_last]
            omega))
        (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add])
        (extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
          (destIdx := ⟨(k.val * ϑ + ϑ), by
            have hm : (k.val * ϑ + ϑ) = k.val * ϑ + ϑ := by ring
            omega⟩)
          (h_destIdx_le := by
            have hm : (k.val * ϑ + ϑ) = k.val * ϑ + ϑ := by ring
            simp only
            omega)) := by
  have h₁ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  have h₂ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
  have h_ϑ_pos : ϑ > 0 := Nat.pos_of_neZero ϑ
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (by exact hdiv.out)
  let destIdx : Fin r := ⟨(k.val * ϑ + ϑ), by
    have := k_succ_mul_ϑ_le_ℓ (k := k); omega⟩
  let midIdx : Fin r := ⟨k.val * ϑ, by
    have := k_succ_mul_ϑ_le_ℓ (k := k); omega⟩
  let fiber_vec : Vector L (2 ^ ϑ) := Vector.ofFn (logical_queryFiberPoints 𝔽q β oStmtIn k v)
  have h_vec : fiber_vec.get = logical_queryFiberPoints 𝔽q β oStmtIn k v := by
    funext u
    simp [fiber_vec]
  have h_fiber_val : let j : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
      ⟨k.val, by simpa only [toOutCodewordsCount_last] using k.isLt⟩
      ∀ u, fiber_vec.get u = oStmtIn j (getFiberPoint 𝔽q β k v u) := by
    intro j u
    rw [h_vec]
    rfl
  dsimp only [logical_computeFoldedValue]
  rw [←h_vec]
  dsimp only [getChallengeSuffix] -- extractSuffixFromChallenge  arise here
  have h_destIdx_eq : destIdx.val = k.val * ϑ + ϑ := by
    rfl
  --  iterated_fold 𝔽q β 0 ((↑k * ϑ + ϑ)) ⋯ ⋯ (getFirstOracle 𝔽q β oStmtIn)
  --   (getFoldingChallenges (Fin.last ℓ) stmtIn.challenges 0 ⋯) (extractSuffixFromChallenge
  -- 𝔽q β v ⟨(↑k * ϑ + ϑ), ⋯⟩ ⋯)
  set challenges_full := getFoldingChallenges (𝓡 := 𝓡) (r := r) (ϑ := (k.val * ϑ + ϑ))
    (i := Fin.last ℓ) stmtIn.challenges (k := 0)
    (h := by simpa only [zero_add, Fin.val_last] using h₁) with h_challenges_full_defs
  set challenges_mid := getFoldingChallenges (𝓡 := 𝓡) (r := r) (ϑ := k.val * ϑ)
    (i := Fin.last ℓ) stmtIn.challenges (k := 0)
    (h := by simp only [zero_add, Fin.val_last]; omega) with h_challenges_mid_defs
  set challenges_last : Fin ϑ → L := fun j =>
    foldOrderChallenges (ℓ := ℓ) (i := Fin.last ℓ) stmtIn.challenges
      ⟨k.val * ϑ + j.val, by simp only [Fin.val_last]; omega⟩ with h_challenges_last_defs
  set y_left := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
    (destIdx := ⟨k.val * ϑ + ϑ, by omega⟩) (h_destIdx_le := by omega) with hy_left_defs
  set y_right := extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
    (destIdx := ⟨(k.val * ϑ + ϑ), by have := k_succ_mul_ϑ_le_ℓ (k := k); omega⟩)
    (h_destIdx_le := by omega) with hy_right_defs
  -- -- Step 2: Transform the RHS
  -- Define f_mid directly from oStmtIn k, which is simpler and aligns with fiber_vec.get
  let k_oracle_idx : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
    ⟨k, by simp only [toOutCodewordsCount_last, Fin.is_lt]⟩
  let f_mid : ↥(sDomain 𝔽q β h_ℓ_add_R_rate midIdx) → L := oStmtIn k_oracle_idx
  set fiber_vec_actual_def := fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := midIdx) (steps := ϑ) (destIdx := ⟨k * ϑ + ϑ, by omega⟩) (h_destIdx := by
      simp only [Nat.add_right_cancel_iff]; rfl)
    (h_destIdx_le := by omega) (f := f_mid)
    (y := y_left) with h_fiber_vec_actual_def
  have h_fiber_vec_get : fiber_vec.get = fiber_vec_actual_def := by
    rw [h_vec]
    funext x
    dsimp only [fiber_vec_actual_def]
    rw [fiberEvaluations_apply_eq_qMap_total_fiber 𝔽q β (h_i_add_steps_le := h₁)]
    exact congrArg (oStmtIn k_oracle_idx)
      (getFiberPoint_eq_qMap_total_fiber 𝔽q β k v x)
  rw [h_fiber_vec_get]; dsimp only [fiber_vec_actual_def]
  have h_eq := single_point_localized_fold_matrix_form_eq_iterated_fold 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx) (steps := ϑ)
    (destIdx := ⟨k * ϑ + ϑ, by omega⟩) (h_destIdx := by simp only [Nat.add_right_cancel_iff]; rfl)
    (h_destIdx_le := by omega) (h_i_lt := by dsimp only [midIdx]; exact k_mul_ϑ_lt_ℓ (k := k))
    (f := f_mid) (y := y_left) (r_challenges :=
      fun j => foldOrderChallenges (ℓ := ℓ) (i := Fin.last ℓ) stmtIn.challenges
        ⟨k.val * ϑ + j.val, by simp only [Fin.val_last]; omega⟩)
  erw [h_eq]
  dsimp only [f_mid]
  -- Now rw the oStmtIn k_oracle_idx into the iterated_fold of f⁽⁰⁾ form
  -- Extract t and strictOracleFoldingConsistencyProp from h_relIn
  dsimp only [strictFinalSumcheckRelOut, strictFinalSumcheckRelOutProp,
    strictfinalSumcheckStepFoldingStateProp] at h_relIn
  simp only [Fin.val_last, exists_and_right, Subtype.exists] at h_relIn
  rcases h_relIn with ⟨exists_t_MLP, _⟩
  rcases exists_t_MLP with ⟨t, h_t_mem_support, h_strictOracleFoldingConsistency⟩
  dsimp only [strictOracleFoldingConsistencyProp] at h_strictOracleFoldingConsistency
  -- Get the equality for k_oracle_idx: oStmtIn k_oracle_idx = iterated_fold from 0 to k.val * ϑ
  have h_f_mid_eq_iterated_fold := h_strictOracleFoldingConsistency k_oracle_idx
  simp only [id_eq] at h_f_mid_eq_iterated_fold
  rw [h_f_mid_eq_iterated_fold]
  let P₀: L[X]_(2 ^ ℓ) := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
    (fun ω => t.eval (statementOrderBitsOfIndex ω))
  let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
  have h_transitivity := iterated_fold_transitivity 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := (0 : Fin r))
    (midIdx := ⟨k.val * ϑ, by omega⟩)
    (destIdx := ⟨k.val * ϑ + ϑ, by omega⟩)
    (steps₁ := k.val * ϑ) (steps₂ := ϑ)
    (h_midIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add])
    (h_midIdx_le := by change k.val * ϑ ≤ ℓ; omega)
    (h_destIdx := by simp only [Nat.add_right_cancel_iff])
    (h_destIdx_le := by change k.val * ϑ + ϑ ≤ ℓ; exact h₁)
    (f := f₀)
    (r_challenges₁ := getFoldingChallenges (𝓡 := 𝓡) (r := r)
      (Fin.last ℓ) stmtIn.challenges 0 (by simp only [zero_add, Fin.val_last]; omega))
    (r_challenges₂ := fun j =>
      foldOrderChallenges (ℓ := ℓ) (i := Fin.last ℓ) stmtIn.challenges
        ⟨k.val * ϑ + j.val, by simp only [Fin.val_last]; omega⟩)
  have h_transitivity_at := congrFun h_transitivity y_left
  refine h_transitivity_at.trans ?_
  rw [← h_challenges_mid_defs, ← h_challenges_last_defs]
  have h_f₀_eq_getFirstOracle : f₀ = getFirstOracle 𝔽q β oStmtIn := by
    exact polyToOracleFunc_eq_getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (t := ⟨t, h_t_mem_support⟩) (i := Fin.last ℓ)
      (challenges := stmtIn.challenges) (oStmt := oStmtIn)
      (h_consistency := h_strictOracleFoldingConsistency)
  rw [h_f₀_eq_getFirstOracle]
  have h_challenges_eq : Fin.append challenges_mid challenges_last = challenges_full := by
    funext j
    dsimp only [Fin.append, Fin.addCases, challenges_full, challenges_mid, challenges_last]
    by_cases h : j.val < k.val * ϑ
    · simp only [h, ↓reduceDIte, Fin.castLT_mk]
      rfl
    · dsimp only [getFoldingChallenges]
      simp only [h, ↓reduceDIte, Fin.cast_mk, Fin.subNat_mk, Fin.natAdd_mk,
        Fin.val_last, eq_rec_constant]
      apply congrArg (foldOrderChallenges (ℓ := ℓ) (i := Fin.last ℓ) stmtIn.challenges)
      apply Fin.ext
      simp only [Fin.val_mk, Fin.val_subNat, Fin.val_cast]
      omega
  rw [h_challenges_eq]

/-- Every successful query step computes the next prefix fold of the first oracle. -/
lemma query_phase_step_preserves_fold
    {k : Fin (ℓ / ϑ)}
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (c_k : L) (s' : L) -- The next state (c_next)
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((stmtIn, oStmtIn), ()))
    (h_c_k_correct_of_k_pos :
      let := k_mul_ϑ_lt_ℓ (k := k)
      let := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
      if _ : k.val > 0 then
        c_k = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := k.val * ϑ)
          (destIdx := ⟨k.val * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)
          (f := getFirstOracle 𝔽q β oStmtIn)
          (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges
            0 (by simp only [zero_add, Fin.val_last]; omega))
          (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add])
          (extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
            (destIdx := ⟨k.val * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega))
      else True)
    -- Hypothesis: s' is a valid output of the simulated step function
    (challenges : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges)
    (h_s'_mem :
      let step := queryPhaseLogicStep 𝔽q β γ_repetitions
      let witIn : Unit := ()
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmtIn transcript.messages
      s' ∈
      support (OptionT.mk
        (simulateQ.{0, 0, 0} so
          ((checkSingleFoldingStep 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k c_k v stmtIn))))) :
    let := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
    s' = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := (k.val + 1) * ϑ)
        (destIdx := ⟨(k.val + 1) * ϑ, by
          have hm : (k.val + 1) * ϑ = k.val * ϑ + ϑ := by ring
          omega⟩)
        (h_destIdx_le := by
          have hm : (k.val + 1) * ϑ = k.val * ϑ + ϑ := by ring
          simp only
          omega)
        (f := getFirstOracle 𝔽q β oStmtIn)
        (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0
          (by
            have hm : (k.val + 1) * ϑ = k.val * ϑ + ϑ := by ring
            simp only [zero_add, Fin.val_last]
            omega))
        (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add])
        (extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
          (destIdx := ⟨(k.val + 1) * ϑ, by
            have hm : (k.val + 1) * ϑ = k.val * ϑ + ϑ := by ring
            omega⟩)
          (h_destIdx_le := by
            have hm : (k.val + 1) * ϑ = k.val * ϑ + ϑ := by ring
            simp only
            omega)) := by
  have hv : s' = logical_computeFoldedValue 𝔽q β k v stmtIn
      (logical_queryFiberPoints 𝔽q β oStmtIn k v) := by
    by_cases hk : k.val > 0
    · exact query_step_value_of_support_pos 𝔽q β (γ_repetitions := γ_repetitions)
        v c_k s' stmtIn oStmtIn h_relIn h_c_k_correct_of_k_pos challenges h_s'_mem hk
    · exact query_step_value_of_support_zero 𝔽q β (γ_repetitions := γ_repetitions)
        v c_k s' stmtIn oStmtIn h_relIn h_c_k_correct_of_k_pos challenges h_s'_mem hk
  have hf := logical_fold_preserves_direct 𝔽q β (k := k) v stmtIn oStmtIn h_relIn
  let folded : {n : ℕ // n ≤ ℓ} → L := fun n =>
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := n.val)
      (destIdx := ⟨n.val, lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) n.property⟩)
      (h_destIdx := by simp only [Fin.val_zero, zero_add])
      (h_destIdx_le := n.property) (f := getFirstOracle 𝔽q β oStmtIn)
      (r_challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡) (Fin.last ℓ)
        stmtIn.challenges 0 (by simpa only [zero_add, Fin.val_last] using n.property))
      (extractSuffixFromChallenge 𝔽q β v
        ⟨n.val, lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) n.property⟩ n.property)
  have hn : (⟨k.val * ϑ + ϑ, k_succ_mul_ϑ_le_ℓ_₂ (k := k)⟩ : {n : ℕ // n ≤ ℓ}) =
      ⟨(k.val + 1) * ϑ, k_succ_mul_ϑ_le_ℓ k⟩ := by
    apply Subtype.ext
    simp only [Nat.add_mul, Nat.one_mul]
  exact (hv.trans hf).trans (congrArg folded hn)

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
omit [SampleableType L] in
/-- Folding the first oracle through all challenges evaluates its multilinear witness. -/
lemma firstOracle_fullFold_eq_eval
    (t : MultilinearPoly L ℓ) (challenges : Fin (Fin.last ℓ) → L)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_oracle : strictOracleFoldingConsistencyProp 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t (Fin.last ℓ) challenges oStmt)
    (m : ℕ) (hm : m = ℓ) (destIdx : Fin r) (hd : destIdx.val = m)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := m) (destIdx := destIdx)
      (h_destIdx := by simpa only [Fin.val_zero, zero_add] using hd)
      (h_destIdx_le := by change destIdx.val ≤ ℓ; omega)
      (f := getFirstOracle 𝔽q β oStmt)
      (r_challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡)
        (i := Fin.last ℓ) challenges 0 (by simp [hm])) y = t.val.eval challenges := by
  subst m
  have hdest : destIdx = ⟨ℓ, lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Nat.le_refl ℓ)⟩ := Fin.ext hd
  subst destIdx
  let coeffs₀ : Fin (2 ^ ℓ) → L := fun ω => t.val.eval (statementOrderBitsOfIndex ω)
  have h_first := polyToOracleFunc_eq_getFirstOracle 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := t) (i := Fin.last ℓ)
    (challenges := challenges) (oStmt := oStmt) (h_consistency := h_oracle)
  rw [←h_first]
  have h_base := intermediate_poly_P_base 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (h_ℓ := by omega) (coeffs := coeffs₀)
  have h_f₀ :
      polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0
        (polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega) coeffs₀) =
      (fun (x : sDomain 𝔽q β h_ℓ_add_R_rate 0) =>
        (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
          ⟨(0 : Fin r).val, by have h0 : (0 : Fin r).val = 0 := rfl; omega⟩ coeffs₀).eval x.val) := by
    funext x
    exact (congrArg (fun p => Polynomial.eval x.val p) h_base).symm
  rw [h_f₀]
  have h_ch : getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ℓ)
      (i := Fin.last ℓ) challenges 0 (by simp) =
      foldOrderChallenges (ℓ := ℓ) (i := Fin.last ℓ) challenges := by
    funext c
    simp [getFoldingChallenges]
  rw [h_ch]
  rw [iterated_fold_advances_evaluation_poly_nat 𝔽q β]
  exact (intermediateEvaluationPoly_last_iteratedRefineCoeffs_eval 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (coeffs := coeffs₀)
    (r_challenges := foldOrderChallenges (ℓ := ℓ) (i := Fin.last ℓ) challenges)
    (y := y)).trans
      (multilinear_eval_eq_sum_statementOrderBitsOfIndex (t := t) (r := challenges)).symm

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
omit [SampleableType L] [DecidableEq 𝔽q] in
/-- The full prefix fold equals the final constant in a strictly consistent statement. -/
lemma query_phase_final_fold_eq_constant
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (c : L)
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((stmtIn, oStmtIn), witIn))
    -- Hypothesis: x is the result of folding all the way to ℓ
    (h_c_correct :
      have h_mul_eq : (ℓ / ϑ) * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
      c = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := (ℓ / ϑ) * ϑ)
        (destIdx := ⟨(ℓ / ϑ) * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega)
        (f := getFirstOracle 𝔽q β oStmtIn)
        (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0
          (by simp only [zero_add, Fin.val_last]; omega))
        (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add])
        (extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v)
          (destIdx := ⟨(ℓ / ϑ) * ϑ, by omega⟩) (h_destIdx_le := by simp only; omega))
    ) :
    c = stmtIn.final_constant := by
  classical
  letI : SampleableType L := SampleableType.ofFintype L
  rcases h_relIn with ⟨t, hOracle, hFinal⟩
  have hm : ℓ / ϑ * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
  have hϑ : ϑ ≤ ℓ := Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out
  let j := getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
  have hj : j.val * ϑ = ℓ - ϑ := by
    dsimp [j]
    rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul, hm]
  have h_end := getLastOracle_finalFold_eq_eval' 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := t)
    (challenges := stmtIn.challenges) (oStmt := oStmtIn) hOracle
    (curIdx := ⟨j.val * ϑ, by omega⟩)
    (destIdx := ⟨j.val * ϑ + ϑ, by omega⟩)
    (hcur := hj) (hdest := rfl) (hdest_le := by simp only [Fin.val_mk]; omega)
    (h_destIdx_oracle := rfl) (hpos := by omega)
    (rchal := getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
      (i := Fin.last ℓ) stmtIn.challenges (j.val * ϑ) (by simp only [Fin.val_last]; omega))
    (hrchal := rfl) (y := 0)
  have hcst : stmtIn.final_constant = t.val.eval stmtIn.challenges :=
    (congrFun hFinal 0).symm.trans h_end
  exact h_c_correct.trans ((firstOracle_fullFold_eq_eval 𝔽q β
    t stmtIn.challenges oStmtIn hOracle (ℓ / ϑ * ϑ) hm _ rfl _).trans hcst.symm)

end FinalQueryRoundIOR
end
end Binius.BinaryBasefold.QueryPhase
