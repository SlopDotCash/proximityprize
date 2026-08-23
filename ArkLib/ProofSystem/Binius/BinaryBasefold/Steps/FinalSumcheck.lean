/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
import ArkLib.ProofSystem.Binius.BinaryBasefold.ExtractMLPCorrectness
import ArkLib.ToVCVio.Oracle
import ArkLib.ToVCVio.Simulation
import ArkLib.OracleReduction.Completeness

/-!
# Binary Basefold Final Sumcheck Step

The final sum-check round of the Binary Basefold core interaction as an oracle reduction. Defines
the prover (`finalSumcheckProver`), verifier (`finalSumcheckVerifier`), and reduction
(`finalSumcheckOracleReduction`), proves its perfect completeness, and provides the round-by-round
knowledge extractor (`finalSumcheckRbrExtractor`) together with supporting evaluation lemmas.
-/

set_option linter.style.longFile 2100

namespace Binius.BinaryBasefold.CoreInteraction
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
-- open scoped Binius.BinaryBasefold
open scoped NNReal ProbabilityTheory

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

section SingleIteratedSteps
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context} -- Sumcheck context

section FinalSumcheckStep
/-!
## Final Sumcheck Step

This section implements the final sumcheck step that sends the constant `c := f^(ℓ)(0, ..., 0)`
from the prover to the verifier. This step completes the sumcheck verification by ensuring
the final constant is consistent with the folding chain.

The step consists of :
- P → V : constant `c := f^(ℓ)(0, ..., 0)`
- V verifies : `s_ℓ = eqTilde(r, r') * c`
=> `c` should be equal to `t(r'_0, ..., r'_{ℓ-1})` and `f^(ℓ)(0, ..., 0)`

**Key Mathematical Insight** : At round ℓ, we have :
- `P^(ℓ)(X) = Σ_{w ∈ B_0} H_ℓ(w) · X_w^(ℓ)(X) = H_ℓ(0) · X_0^(ℓ)(X) = H_ℓ(0)`
- Since `H_ℓ(X)` is constant (zero-variate): `H_ℓ(X) = t(r'_0, ..., r'_{ℓ-1})`
- Therefore : `P^(ℓ)(X) = t(r'_0, ..., r'_{ℓ-1})` (constant polynomial)
- And `s_ℓ = ∑_{w ∈ B_0} t(r'_0, ..., r'_{ℓ-1}) = t(r'_0, ..., r'_{ℓ-1})`
-/

open Classical in
/-! The prover for the final sumcheck step -/
noncomputable def finalSumcheckProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitOut := Unit)
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  PrvState := fun
    | 0 => Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ) × (∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
        × Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)
    | _ => Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ) × (∀ j, OracleStatement 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
        × Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) × L
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)
  sendMessage
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩ => do
    -- Compute the message using the honest transcript from logic
    let c : L := witIn.f ⟨0, by simp only [zero_mem]⟩ -- f^(ℓ)(0, ..., 0)
    pure ⟨c, (stmtIn, oStmtIn, witIn, c)⟩
  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- No challenges in this step
  output := fun ⟨stmtIn, oStmtIn, witIn, c⟩ => do
    -- Construct the transcript from the message and challenges (no challenges in this step)
    let t := FullTranscript.mk1 (pSpec := pSpecFinalSumcheckStep (L := L)) c
    -- Delegate to the logic instance for prover output
    pure ((finalSumcheckStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).proverOut stmtIn witIn oStmtIn t)

/-! The verifier for the final sumcheck step -/
open Classical in
noncomputable def finalSumcheckVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  verify := fun stmtIn _ => do
    -- Get the final constant `c` from the prover's message
    let c : L ← query (spec := [(pSpecFinalSumcheckStep (L := L)).Message]ₒ)
      ⟨⟨0, by rfl⟩, (by exact ())⟩
    -- Construct the transcript
    let t := FullTranscript.mk1 (pSpec := pSpecFinalSumcheckStep (L := L)) c
    -- Get the logic instance
    let logic := (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
    -- Use guard for verifier check (fails if check doesn't pass)
    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)
  embed := (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).embed
  hEq := (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).hEq

/-! The oracle reduction for the final sumcheck step -/
noncomputable def finalSumcheckOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitOut := Unit)
    (pSpec := pSpecFinalSumcheckStep (L := L)) where
  prover := finalSumcheckProver 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
  verifier := finalSumcheckVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)

/-! Perfect completeness for the final sumcheck step -/
theorem finalSumcheckOracleReduction_perfectCompleteness {σ : Type}
    (init : ProbComp σ) (hInit : NeverFail init)
  (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  OracleReduction.perfectCompleteness
    (pSpec := pSpecFinalSumcheckStep (L := L))
    (relIn := strictRoundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (mp := BBF_SumcheckMultiplierParam) (Fin.last ℓ))
    (relOut := strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (oracleReduction := finalSumcheckOracleReduction 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)) (init := init) (impl := impl) := by
  -- Step 1: Unroll the 2-message reduction to convert from probability to logic
  rw [OracleReduction.unroll_1_message_reduction_perfectCompleteness_P_to_V (oSpec := []ₒ)
    (hInit := hInit) (pSpec := pSpecFinalSumcheckStep (L := L))
    (hDir0 := by rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  -- Step 2: Convert probability 1 to universal quantification over support
  rw [probEvent_eq_one_iff]
  -- Step 3: Unfold protocol definitions
  dsimp only [finalSumcheckOracleReduction, finalSumcheckProver, finalSumcheckVerifier,
    OracleVerifier.toVerifier, FullTranscript.mk1]
  let step := (finalSumcheckStepLogic 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
  let strongly_complete : step.IsStronglyComplete := finalSumcheckStep_is_logic_complete (L := L)
    𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
  -- Step 4: Split into safety and correctness goals
  refine ⟨?_, ?_⟩
  · rw [← HasEvalSPMF.neverFail_iff]
    obtain ⟨h_V_check, -, -⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (challenges := fun ⟨j, hj⟩ => by
        dsimp only [pSpecFinalSumcheckStep, Fin.isValue, Matrix.cons_val_zero] at hj
        exact absurd hj (by simp))
    simp only [liftComp_eq_liftM, liftM_pure, pure_bind]
    simp only [guard_eq, OptionT.simulateQ_bind, simulateQ_bind,
      simulateQ_simOracle2_liftM_query_T2, simulateQ_ite, OptionT.simulateQ_pure,
      simulateQ_pure, OptionT.simulateQ_failure, apply_ite, pure_bind]
    erw [OptionT.simulateQ_bind]
    erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
    simp only [OptionT.bind, OptionT.mk, pure_bind]
    erw [pure_bind]
    have hVc := h_V_check
    dsimp only [finalSumcheckStepLogic] at hVc
    dsimp only
    erw [if_pos h_V_check]
    erw [pure_bind]
    infer_instance
  · obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (challenges := fun ⟨j, hj⟩ => by
        dsimp only [pSpecFinalSumcheckStep, Fin.isValue, Matrix.cons_val_zero] at hj
        exact absurd hj (by simp))
    intro x hx
    simp only [liftComp_eq_liftM, liftM_pure, pure_bind] at hx
    simp only [guard_eq, simulateQ_ite, OptionT.simulateQ_pure, simulateQ_pure,
      OptionT.simulateQ_failure, apply_ite, pure_bind] at hx
    erw [OptionT.simulateQ_bind] at hx
    erw [OptionT.simulateQ_simOracle2_liftM_query_T2] at hx
    simp only [OptionT.bind, OptionT.mk, pure_bind] at hx
    erw [pure_bind] at hx
    dsimp only at hx
    erw [if_pos h_V_check] at hx
    erw [pure_bind] at hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨h_rel, h_agree.1, h_agree.2⟩

/-! RBR knowledge error for the final sumcheck step -/
def finalSumcheckKnowledgeError (m : pSpecFinalSumcheckStep (L := L).ChallengeIdx) :
  ℝ≥0 :=
  match m with
  | ⟨0, h0⟩ => nomatch h0

omit [SampleableType L] in
/-- Bridge: `getFirstOracle 𝔽q β oStmt` is the level-0 oracle `oStmt ⟨0,h⟩` (its domain reindex is
the identity), up to heterogeneous equality. Discharges the `getFirstOracle ↔ oStmt ⟨0,·⟩` HEq
sites cleanly via `oracle_heq_congr`. -/
private theorem getFirstOracle_heq {i : Fin (ℓ + 1)}
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)
    (h : 0 < toOutCodewordsCount ℓ ϑ i) :
    HEq (getFirstOracle 𝔽q β oStmt) (oStmt ⟨0, h⟩) := by
  have hidx : (0 : Fin r) = ⟨(⟨0, h⟩ : Fin (toOutCodewordsCount ℓ ϑ i)).val * ϑ, by
      have := toCodewordsCount_mul_ϑ_lt_ℓ ℓ ϑ i ⟨0, h⟩; omega⟩ :=
    Fin.eq_of_val_eq (by simp)
  unfold getFirstOracle
  apply Function.hfunext
  · rw [hidx]
  · intro a b hab
    apply heq_of_eq
    apply OracleStatement.oracle_eval_congr 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmtIn := oStmt)
      (j := ⟨0, h⟩) (j' := ⟨0, (instNeZeroNatToOutCodewordsCount ℓ ϑ i).pos⟩)
      (h_j := Fin.eq_of_val_eq rfl)
    rw [eq_cast_iff_heq]
    refine HEq.trans (b := a) ?_ hab
    exact (Subtype.heq_iff_coe_eq (fun x => by rw [hidx])).mpr rfl

set_option maxHeartbeats 8000000 in
omit [SampleableType L] in
lemma firstOracle_UDRClose_of_finalSumcheckStepOracleConsistency
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (h_oracle_consistency : finalSumcheckStepOracleConsistencyProp 𝔽q β
      (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
      (stmtOut := stmtOut) (oStmtOut := oStmt)) :
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (h_i := Nat.zero_le ℓ) (f := getFirstOracle 𝔽q β oStmt) := by
  have h_le : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
  dsimp only [finalSumcheckStepOracleConsistencyProp] at h_oracle_consistency
  rcases h_oracle_consistency with ⟨h_oracle_cons, h_final_cons⟩
  let j0 : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) := ⟨0, by
    exact Nat.pos_of_neZero (toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
  ⟩
  have h_ϑ_pos : 0 < ϑ := Nat.pos_of_dvd_of_pos hdiv.out (Nat.pos_of_neZero ℓ)
  by_cases h_ℓ_eq_ϑ : ℓ = ϑ
  · have h_div : ℓ / ϑ = 1 := by
      rw [h_ℓ_eq_ϑ]
      rw [Nat.div_self (n := ϑ) (H := h_ϑ_pos)]
    have h_getLastOraclePositionIndex_last : getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ) = 0 := by
      dsimp only [getLastOraclePositionIndex]
      simp only [toOutCodewordsCount_last, Fin.mk_eq_zero, h_div]
    let jLast : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
      getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
    have h_jLast_eq_zero : jLast = 0 := by
      dsimp only [jLast]
      exact h_getLastOraclePositionIndex_last
    have h_jLast_val : jLast.val = 0 := by
      exact congrArg Fin.val h_jLast_eq_zero
    let zeroIdxLast : Fin r := ⟨↑jLast * ϑ, by
      have h_r_pos : 0 < r := Nat.pos_of_neZero r
      rw [h_jLast_val, zero_mul]
      exact h_r_pos⟩
    let destIdxLast : Fin r := ⟨↑jLast * ϑ + ϑ, by
      have h_ℓ_lt_r : ℓ < r := by omega
      have h_ϑ_lt_r : ϑ < r := by
        rw [← h_ℓ_eq_ϑ]
        exact h_ℓ_lt_r
      rw [h_jLast_val, zero_mul, zero_add]
      exact h_ϑ_lt_r⟩
    let challengesLast : Fin ϑ → L :=
      getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
        (challenges := stmtOut.challenges) (k := ↑jLast * ϑ) (h := by
          rw [h_jLast_val]; simpa using h_le)
    have h_zeroIdxLast : zeroIdxLast.val = 0 := by
      simp [zeroIdxLast, h_jLast_eq_zero]
    have h_zeroIdxLast_eq : zeroIdxLast = 0 := Fin.eq_of_val_eq h_zeroIdxLast
    have h_destIdxLast : destIdxLast = 0 + ϑ := by
      simp [destIdxLast, h_jLast_eq_zero]
    have h_destIdxLast_le : destIdxLast ≤ ℓ := by
      simp only [h_jLast_eq_zero, Fin.coe_ofNat_eq_mod, toOutCodewordsCount_last, h_ℓ_eq_ϑ,
        Nat.zero_mod, zero_mul, zero_add, le_refl, destIdxLast]
    have h_compl0 :
        isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := zeroIdxLast)
          (steps := ϑ)
          (destIdx := destIdxLast)
          (h_destIdx := by
            rw [h_zeroIdxLast_eq]
            exact h_destIdxLast)
          (h_destIdx_le := h_destIdxLast_le)
          (f_i := oStmt jLast)
          (f_i_plus_steps := fun _ => stmtOut.final_constant)
          (challenges := challengesLast) := by
      have h_final_cons' := h_final_cons
      simp only [jLast, zeroIdxLast, destIdxLast, challengesLast, id_eq] at h_final_cons' ⊢
      exact h_final_cons'
    rcases h_compl0 with ⟨h_fw_dist_lt, _, _⟩
    have h_close :=
      UDRClose_of_fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := zeroIdxLast) (steps := ϑ) (h_destIdx := by
          rw [h_zeroIdxLast_eq]
          exact h_destIdxLast)
        (h_destIdx_le := h_destIdxLast_le) (f := oStmt jLast)
        (h_fw_dist_lt := h_fw_dist_lt)
    convert h_close using 1
    · exact h_zeroIdxLast_eq.symm
    · exact (getFirstOracle_heq 𝔽q β oStmt _).trans (OracleStatement.oracle_heq_congr 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmtIn := oStmt)
        (j := ⟨0, by
          letI := instNeZeroNatToOutCodewordsCount ℓ ϑ (Fin.last ℓ)
          exact Nat.pos_of_neZero _⟩)
        (j' := jLast)
        (h_j := Fin.eq_of_val_eq
          (by simpa using (congrArg Fin.val h_jLast_eq_zero).symm)))
  · dsimp only [oracleFoldingConsistencyProp] at h_oracle_cons
    have h_lt : ϑ < ℓ := by omega
    have h_div_gt_1 : ℓ / ϑ > 1 := by
      have h_res := (Nat.div_lt_div_right (a := ϑ) (b := ϑ) (c := ℓ) (ha := h_ϑ_pos.ne')
        (by simp only [dvd_refl]) (by exact hdiv.out)).mpr h_lt
      rw [Nat.div_self (n := ϑ) (H := h_ϑ_pos)] at h_res
      exact h_res
    have h_j0_next_lt : ↑j0 + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ) := by
      dsimp only [j0]
      rw [toOutCodewordsCount_last]
      exact h_div_gt_1
    let zeroIdx0 : Fin r := ⟨↑j0 * ϑ, by
      have h_r_pos : 0 < r := Nat.pos_of_neZero r
      dsimp only [j0]
      rw [zero_mul]
      exact h_r_pos⟩
    let destIdx0 : Fin r := ⟨↑j0 * ϑ + ϑ, by
      have h_ℓ_lt_r : ℓ < r := by omega
      have h_ϑ_lt_r : ϑ < r := lt_of_le_of_lt h_le h_ℓ_lt_r
      dsimp only [j0]
      rw [zero_mul, zero_add]
      exact h_ϑ_lt_r⟩
    have h_zeroIdx0 : zeroIdx0.val = 0 := by
      simp [zeroIdx0, j0]
    have h_destIdx0 : destIdx0 = 0 + ϑ := by
      simp [destIdx0, j0]
    have h_destIdx0_le : destIdx0 ≤ ℓ := by
      dsimp only [destIdx0, j0]
      rw [zero_mul, zero_add]
      exact h_le
    have h_k_next_le_last : ↑j0 * ϑ + ϑ ≤ Fin.last ℓ := by
      exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
        (i := Fin.last ℓ) (j := j0) (hj := h_j0_next_lt)
    let fNext0 : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx0 :=
      getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := Fin.last ℓ)
        oStmt j0 h_j0_next_lt
        (destDomainIdx := destIdx0)
        (h_destDomainIdx := by simp only [destIdx0])
    let challenges0 : Fin ϑ → L :=
      getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
        (challenges := stmtOut.challenges) (k := ↑j0 * ϑ) (h := h_k_next_le_last)
    have h_isCompliant_f₀ :
        isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := zeroIdx0) (steps := ϑ)
          (destIdx := destIdx0)
          (h_destIdx := by
            rw [h_zeroIdx0]
            exact h_destIdx0)
          (h_destIdx_le := h_destIdx0_le)
          (f_i := oStmt ⟨↑j0, by exact j0.isLt⟩)
          (f_i_plus_steps := fNext0)
          (challenges := challenges0) := by
      have h_oracle_cons' := h_oracle_cons j0 h_j0_next_lt
      simp only [zeroIdx0, destIdx0, fNext0, challenges0] at h_oracle_cons' ⊢
      exact h_oracle_cons'
    rcases h_isCompliant_f₀ with ⟨h_fw_dist_lt, _, _⟩
    have h_close :=
      UDRClose_of_fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := zeroIdx0) (steps := ϑ) (h_destIdx := by
          rw [h_zeroIdx0]
          exact h_destIdx0)
        (h_destIdx_le := h_destIdx0_le) (f := oStmt ⟨↑j0, by exact j0.isLt⟩)
        (h_fw_dist_lt := h_fw_dist_lt)
    have h_zeroIdx0_eq : zeroIdx0 = (0 : Fin r) := Fin.eq_of_val_eq (by simp [zeroIdx0, j0])
    convert h_close using 1
    · exact h_zeroIdx0_eq.symm
    · exact (getFirstOracle_heq 𝔽q β oStmt _).trans (OracleStatement.oracle_heq_congr 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmtIn := oStmt)
        (j := ⟨0, by
          letI := instNeZeroNatToOutCodewordsCount ℓ ϑ (Fin.last ℓ)
          exact Nat.pos_of_neZero _⟩)
        (j' := ⟨↑j0, j0.isLt⟩)
        (h_j := Fin.eq_of_val_eq (by dsimp only [j0])))

omit [SampleableType L] in
/-- If a block starting at domain index `0` is compliant (`isCompliant`), the Berlekamp–Welch
extractor at level `0` succeeds on the source oracle: compliance contains fiberwise-closeness,
which gives UDR-closeness, and the decoder succeeds inside the UDR
(`extractMLP_zero_isSome_of_UDRClose`). -/
lemma extractMLP_some_of_isCompliant_at_zero
    {destIdx : Fin r} {steps : ℕ} [NeZero steps]
    (zero_Idx : Fin r) (h_zero_Idx : zero_Idx.val = 0)
    (h_destIdx : destIdx = 0 + steps)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) zero_Idx)
    (f_next : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
    (challenges : Fin steps → L)
    (h_compl :
      isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := zero_Idx) (steps := steps)
        (destIdx := destIdx) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
        (f_i := f_i) (f_i_plus_steps := f_next) (challenges := challenges)) :
    ∃ tpoly : MultilinearPoly L ℓ,
      extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0
        (fun x => f_i (cast (congrArg (fun i => ↥(sDomain 𝔽q β h_ℓ_add_R_rate i))
          (Fin.eq_of_val_eq (by simpa using h_zero_Idx.symm) : (0 : Fin r) = zero_Idx)) x))
        = some tpoly := by
  classical
  have h0 : zero_Idx = (0 : Fin r) := Fin.eq_of_val_eq (by simpa using h_zero_Idx)
  subst h0
  obtain ⟨h_fw, -, -⟩ := h_compl
  have h_udr := UDRClose_of_fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := (0 : Fin r)) (steps := steps) (h_destIdx := by
      simpa using h_destIdx)
    (h_destIdx_le := h_destIdx_le) (f := f_i) h_fw
  have hUDR : 2 * Code.distFromCode (u := f_i)
      (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r)) <
      (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) : ℕ∞) := by
    simpa [UDRClose] using h_udr
  obtain ⟨tpoly, htpoly⟩ := extractMLP_zero_isSome_of_UDRClose 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) f_i hUDR
  refine ⟨tpoly, ?_⟩
  have hfeq : (fun x => f_i (cast (congrArg (fun i => ↥(sDomain 𝔽q β h_ℓ_add_R_rate i))
      (Fin.eq_of_val_eq (by simp) : (0 : Fin r) = (0 : Fin r))) x)) = f_i := by
    funext x
    simp
  simpa [hfeq] using htpoly

omit [SampleableType L] in
/-! When final-sumcheck oracle consistency holds, extractMLP must succeed.

This connects the proximity-based `finalSumcheckStepOracleConsistencyProp` to the decoder:
- That prop implies oracle folding consistency and final compliance (last oracle → constant)
- Folding consistency implies the first oracle is within unique decoding radius
- Berlekamp-Welch decoder succeeds when within UDR, returning `some` -/
omit [SampleableType L] in
lemma extractMLP_some_of_oracleFoldingConsistency
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (h_oracle_consistency : finalSumcheckStepOracleConsistencyProp 𝔽q β
      (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
      (stmtOut := stmtOut) (oStmtOut := oStmt)) :
    -- extractMLP is used in `finalSumcheckRbrExtractor`
    ∃ tpoly, extractMLP 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (f := getFirstOracle 𝔽q β oStmt) = some tpoly := by
  have h_udr := firstOracle_UDRClose_of_finalSumcheckStepOracleConsistency 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtOut := stmtOut) (oStmt := oStmt)
    h_oracle_consistency
  exact extractMLP_zero_isSome_of_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (getFirstOracle 𝔽q β oStmt) (by simpa [UDRClose] using h_udr)

omit [SampleableType L] in
private theorem UDRCodeword_heq_of_fin_eq
    {i j : Fin r} (hij : i = j)
    (h_i : i ≤ ℓ) (h_j : j ≤ ℓ)
    {f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i}
    {g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j}
    (hfg : HEq f g)
    (h₁ : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (h_i := h_i) (f := f))
    (h₂ : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := j) (h_i := h_j) (f := g)) :
    HEq
      (UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (h_i := h_i) (f := f) (h_within_radius := h₁))
      (UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := j) (h_i := h_j) (f := g) (h_within_radius := h₂)) := by
  cases hij
  cases hfg
  apply heq_of_eq
  exact UDRCodeword_eq_of_close (𝔽q := 𝔽q) (β := β)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    (h_i := h_i) (f := f) h₁ h₂

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
private theorem iterated_fold_heq_of_fin_eq
    (i : Fin r) (steps : ℕ)
    {destIdx₁ destIdx₂ : Fin r} (hij : destIdx₁ = destIdx₂)
    (h_destIdx₁ : ↑destIdx₁ = ↑i + steps)
    (h_destIdx₂ : ↑destIdx₂ = ↑i + steps)
    (h_destIdx_le₁ : ↑destIdx₁ ≤ ℓ) (h_destIdx_le₂ : ↑destIdx₂ ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (r_challenges : Fin steps → L) :
    HEq
      (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (steps := steps) (destIdx := destIdx₁)
        h_destIdx₁ h_destIdx_le₁ f r_challenges)
      (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (steps := steps) (destIdx := destIdx₂)
        h_destIdx₂ h_destIdx_le₂ f r_challenges) := by
  cases hij
  apply heq_of_eq
  funext y
  cases proof_irrel_heq h_destIdx₁ h_destIdx₂
  cases proof_irrel_heq h_destIdx_le₁ h_destIdx_le₂
  rfl

private def finalOracleBlockIdx
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) : Fin r :=
  ⟨t * ϑ, by
    apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ)
    exact oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨t, ht⟩)⟩

private def finalPrefixChallenges
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    Fin (t * ϑ) → L := fun cId =>
  foldOrderChallenges (ℓ := ℓ) (i := Fin.last ℓ) stmtOut.challenges ⟨cId, by
    exact lt_of_lt_of_le cId.isLt
      (oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨t, ht⟩))⟩

private def finalBlockChallenges
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (t : ℕ) (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    Fin ϑ → L := fun cId =>
  foldOrderChallenges (ℓ := ℓ) (i := Fin.last ℓ) stmtOut.challenges ⟨t * ϑ + cId, by
    have h_lt : t * ϑ + cId.val < t * ϑ + ϑ := by
      omega
    exact lt_of_lt_of_le h_lt
      (oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩))⟩

private def finalDecodedPrefixFold
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (finalOracleBlockIdx (ℓ := ℓ)
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) :=
  iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := 0) (steps := t * ϑ)
    (destIdx := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)
    (h_destIdx := by
      dsimp [finalOracleBlockIdx]
      simp only [zero_add])
    (h_destIdx_le := by
      dsimp [finalOracleBlockIdx]
      exact oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨t, ht⟩))
    (f := f₀)
    (r_challenges := finalPrefixChallenges stmtOut t ht)

private def finalOracleRaw
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) := by
  change OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (ϑ := ϑ) (i := Fin.last ℓ) ⟨t, ht⟩
  exact oStmtOut ⟨t, ht⟩

private def finalOracleDecoded
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
    (h_close : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)
      (h_i := oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨t, ht⟩))
      (f := finalOracleRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht)) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) :=
  UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)
    (h_i := oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨t, ht⟩))
    (f := finalOracleRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht)
    (h_within_radius := h_close)

omit [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] in
private theorem finalOracleBlockIdx_zero
    (ht : 0 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ht = 0 := by
  apply Fin.eq_of_val_eq
  dsimp [finalOracleBlockIdx]
  simp only [zero_mul]

private def finalOracleClose
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) : Prop :=
  UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)
    (h_i := oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨t, ht⟩))
    (f := oStmtOut ⟨t, ht⟩)

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
private theorem finalOracleDecoded_eq_of_close
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
    (h_close₁ h_close₂ : finalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht) :
    finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht h_close₁ =
    finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht h_close₂ := by
  cases Subsingleton.elim h_close₁ h_close₂
  rfl

set_option maxHeartbeats 1000000 in
-- This transitivity lemma unfolds two nested iterated folds before the final congruence step.
private theorem finalDecodedPrefixFold_step
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (t : ℕ) (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        t (Nat.lt_of_succ_lt ht))
      (steps := ϑ)
      (destIdx := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (t + 1) ht)
      (h_destIdx := by
        dsimp [finalOracleBlockIdx]
        rw [Nat.add_mul, Nat.one_mul])
      (h_destIdx_le := by
        dsimp [finalOracleBlockIdx]
        rw [Nat.add_mul, Nat.one_mul]
        exact oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩))
      (f := finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t (Nat.lt_of_succ_lt ht))
      (r_challenges := finalBlockChallenges
        (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) stmtOut t ht) =
    finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ (t + 1) ht := by
  dsimp [finalDecodedPrefixFold]
  have h_transitivity := iterated_fold_transitivity 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := (0 : Fin r))
    (midIdx := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      t (Nat.lt_of_succ_lt ht))
    (destIdx := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (t + 1) ht)
    (steps₁ := t * ϑ) (steps₂ := ϑ)
    (h_midIdx_le := by
      dsimp [finalOracleBlockIdx]
      simpa using oracle_index_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩))
    (h_midIdx := by
      dsimp [finalOracleBlockIdx]
      try simp only [zero_add])
    (h_destIdx := by
      dsimp [finalOracleBlockIdx]
      try simp only [zero_add]
      rw [Nat.add_mul, Nat.one_mul])
    (h_destIdx_le := by
      dsimp [finalOracleBlockIdx]
      rw [Nat.add_mul, Nat.one_mul]
      exact oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩))
    (f := f₀)
    (r_challenges₁ := finalPrefixChallenges
      (L := L) (ℓ := ℓ) (ϑ := ϑ) stmtOut t (Nat.lt_of_succ_lt ht))
    (r_challenges₂ := finalBlockChallenges
      (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) stmtOut t ht)
  rw [h_transitivity]
  funext y
  have h_steps_eq : t * ϑ + ϑ = (t + 1) * ϑ := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := (0 : Fin r)) (steps := t * ϑ + ϑ) (steps' := (t + 1) * ϑ)
    (destIdx := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (t + 1) ht)
    (h_destIdx := by
      dsimp [finalOracleBlockIdx]
      try simp only [zero_add]
      rw [Nat.add_mul, Nat.one_mul])
    (h_destIdx_le := by
      dsimp [finalOracleBlockIdx]
      rw [Nat.add_mul, Nat.one_mul]
      exact oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩))
    (h_steps_eq_steps' := h_steps_eq)
    (f := f₀)
    (r_challenges := Fin.append
      (finalPrefixChallenges
        (L := L) (ℓ := ℓ) (ϑ := ϑ) stmtOut t (Nat.lt_of_succ_lt ht))
      (finalBlockChallenges
        (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) stmtOut t ht))
    (y := y)]
  have h_challenges_eq :
      (fun cId : Fin ((t + 1) * ϑ) =>
        Fin.append
          (finalPrefixChallenges
            (L := L) (ℓ := ℓ) (ϑ := ϑ) stmtOut t (Nat.lt_of_succ_lt ht))
          (finalBlockChallenges
            (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) stmtOut t ht)
          ⟨cId, by
            have h_cast_lt : cId.val < t * ϑ + ϑ := by
              have h_lt' : cId.val < (t + 1) * ϑ := cId.isLt
              omega
            exact h_cast_lt⟩) =
      finalPrefixChallenges (L := L) (ℓ := ℓ) (ϑ := ϑ) stmtOut (t + 1) ht := by
    funext cId
    dsimp only [finalPrefixChallenges, finalBlockChallenges, Fin.append, Fin.addCases]
    by_cases h : cId.val < t * ϑ
    · simp only [h, ↓reduceDIte, Fin.castLT_mk]
    · simp only [h, ↓reduceDIte, Fin.cast_mk, Fin.subNat_mk, Fin.natAdd_mk, eq_rec_constant]
      congr 1
      simp only [Fin.mk.injEq]
      omega
  rw [h_challenges_eq]

set_option maxHeartbeats 800000 in
-- This base-oracle decoded equality uses subsingleton transport on close proofs.
omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
private theorem firstOracleDecoded_eq_f₀
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (h_close_first : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (h_i := Nat.zero_le ℓ) (f := getFirstOracle 𝔽q β oStmtOut))
    (h_dec0_eq_f0 :
      UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (h_i := Nat.zero_le ℓ) (f := getFirstOracle 𝔽q β oStmtOut)
        (h_within_radius := h_close_first) = f₀)
    (h_close0 : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (h_i := Nat.zero_le ℓ) (f := getFirstOracle 𝔽q β oStmtOut)) :
    UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (h_i := Nat.zero_le ℓ) (f := getFirstOracle 𝔽q β oStmtOut)
      (h_within_radius := h_close0) = f₀ := by
  cases Subsingleton.elim h_close0 h_close_first
  exact h_dec0_eq_f0

set_option maxHeartbeats 8000000 in
-- This zero-step oracle identification needs extra heartbeats for the dependent cast cleanup.
omit [SampleableType L] in
private theorem finalOracleRaw_zero_heq_getFirstOracle
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (ht : 0 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    HEq
      (finalOracleRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht)
      (getFirstOracle 𝔽q β oStmtOut) := by
  have h_idx0 := finalOracleBlockIdx_zero
    (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ht
  have h_dom :
      ↥(sDomain 𝔽q β h_ℓ_add_R_rate
        (finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ht)) =
      ↥(sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r)) := by
    exact congrArg (fun i => ↥(sDomain 𝔽q β h_ℓ_add_R_rate i)) h_idx0
  have h_j0 :
      (⟨0, ht⟩ : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ))) =
      ⟨0, by
        letI := instNeZeroNatToOutCodewordsCount ℓ ϑ (Fin.last ℓ)
        exact Nat.pos_of_neZero (toOutCodewordsCount ℓ ϑ (Fin.last ℓ))⟩ := by
    apply Fin.eq_of_val_eq
    rfl
  dsimp only [finalOracleRaw]
  exact (OracleStatement.oracle_heq_congr 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (oStmtIn := oStmtOut)
    (j := ⟨0, ht⟩)
    (j' := ⟨0, by
      letI := instNeZeroNatToOutCodewordsCount ℓ ϑ (Fin.last ℓ)
      exact Nat.pos_of_neZero _⟩)
    (h_j := (Fin.eq_of_val_eq rfl :
      (⟨0, ht⟩ : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ))) = ⟨0, by
        letI := instNeZeroNatToOutCodewordsCount ℓ ϑ (Fin.last ℓ)
        exact Nat.pos_of_neZero _⟩))).trans (getFirstOracle_heq 𝔽q β oStmtOut _).symm

omit [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero ϑ] in
/-- Transport `UDRClose` across an index equality and a heterogeneous function equality. -/
private theorem UDRClose_of_fin_eq
    {i j : Fin r} (h_ij : i = j)
    {h_i : i ≤ ℓ} {h_j : j ≤ ℓ}
    {f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i}
    {g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j}
    (h_fg : HEq f g)
    (h_close : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f) :
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j h_j g := by
  subst h_ij
  cases h_fg
  exact h_close

set_option maxHeartbeats 800000 in
-- This zero-step close transport crosses from the final-oracle view back to the first oracle.
private theorem finalOracleClose_zero_eq_first
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (ht : 0 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
    (h_close0 : finalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht) :
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (h_i := Nat.zero_le ℓ) (f := getFirstOracle 𝔽q β oStmtOut) := by
  have h_idx0 := finalOracleBlockIdx_zero
    (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ht
  change UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ht)
      (h_i := oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨0, ht⟩))
      (f := finalOracleRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht) at h_close0
  exact UDRClose_of_fin_eq (𝔽q := 𝔽q) (β := β)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_idx0
    (finalOracleRaw_zero_heq_getFirstOracle (𝔽q := 𝔽q) (β := β)
      (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut ht)
    h_close0

-- This zero-case decoded equality combines UDRCodeword transport with a zero-step fold rewrite.
set_option maxHeartbeats 4000000 in
private theorem finalOracleDecoded_zero_eq_prefixFold
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (h_close_first : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (h_i := Nat.zero_le ℓ) (f := getFirstOracle 𝔽q β oStmtOut))
    (h_dec0_eq_f0 :
      UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (h_i := Nat.zero_le ℓ) (f := getFirstOracle 𝔽q β oStmtOut)
        (h_within_radius := h_close_first) = f₀)
    (ht : 0 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
    (h_close0 : finalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht) :
    finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht h_close0 =
    finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ 0 ht := by
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := by
    apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
  have h_idx0 := finalOracleBlockIdx_zero
    (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ht
  have h_raw0_heq :
      HEq
        (finalOracleRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht)
        (getFirstOracle 𝔽q β oStmtOut) :=
    finalOracleRaw_zero_heq_getFirstOracle (𝔽q := 𝔽q) (β := β)
      (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut ht
  have h_close0_first :
      UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (h_i := Nat.zero_le ℓ) (f := getFirstOracle 𝔽q β oStmtOut) := by
    exact finalOracleClose_zero_eq_first (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut ht h_close0
  have h_decoded0_heq_f₀ :
      HEq
        (finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht h_close0)
        f₀ := by
    have h_decoded0_heq_first :
        HEq
          (finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut 0 ht h_close0)
          (UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := (0 : Fin r)) (h_i := Nat.zero_le ℓ) (f := getFirstOracle 𝔽q β oStmtOut)
            (h_within_radius := h_close0_first)) := by
      exact UDRCodeword_heq_of_fin_eq (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_idx0
        (oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨0, ht⟩))
        (by simp) h_raw0_heq h_close0 h_close0_first
    exact h_decoded0_heq_first.trans
      (heq_of_eq (firstOracleDecoded_eq_f₀ (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut f₀ h_close_first h_dec0_eq_f0 h_close0_first))
  have h_prefix_zero_heq :
      HEq
        (finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ 0 ht)
        f₀ := by
    have h_dom0 :
        ↥(sDomain 𝔽q β h_ℓ_add_R_rate
          (finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ht)) =
        ↥(sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r)) := by
      exact congrArg (fun i => ↥(sDomain 𝔽q β h_ℓ_add_R_rate i)) h_idx0
    exact funext_heq h_dom0 (fun _ => rfl) (by
      intro y
      apply heq_of_eq
      dsimp [finalDecodedPrefixFold]
      rw [iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (steps := 0 * ϑ) (steps' := 0)
        (destIdx := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ht)
        (h_destIdx := by
          dsimp [finalOracleBlockIdx]
          simp only [zero_mul, add_zero])
        (h_destIdx_le := by
          exact oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨0, ht⟩))
        (h_steps_eq_steps' := by simp only [zero_mul]) (f := f₀)
        (r_challenges := finalPrefixChallenges
          (L := L) (ℓ := ℓ) (ϑ := ϑ) stmtOut 0 ht) (y := y)]
      rw [iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r))
        (destIdx := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ht)
        (h_destIdx := by
          dsimp [finalOracleBlockIdx]
          simp only [zero_mul])
        (h_destIdx_le := by
          exact oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := ⟨0, ht⟩))
        (f := f₀)
        (r_challenges := fun cId => finalPrefixChallenges
          (L := L) (ℓ := ℓ) (ϑ := ϑ) stmtOut 0 ht ⟨cId, by omega⟩)]
      rfl)
  exact eq_of_heq (h_decoded0_heq_f₀.trans h_prefix_zero_heq.symm)

set_option maxHeartbeats 800000 in
-- This current-close extractor unfolds one oracle-consistency witness and reindexes the block.
omit [CharP L 2] [SampleableType L] in
private theorem finalOracleClose_curr
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (h_oracle_cons : oracleFoldingConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := Fin.last ℓ) (challenges := stmtOut.challenges) (oStmt := oStmtOut))
    (t : ℕ)
    (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    finalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t (Nat.lt_of_succ_lt ht) := by
  let jCurr : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) := ⟨t, Nat.lt_of_succ_lt ht⟩
  have h_complCurr := h_oracle_cons jCurr ht
  rcases h_complCurr with ⟨h_fw_curr, _, _⟩
  exact UDRClose_of_fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t (Nat.lt_of_succ_lt ht))
    (steps := ϑ)
    (h_destIdx := by
      dsimp [finalOracleBlockIdx, jCurr, oraclePositionToDomainIndex])
    (h_destIdx_le := by
      have h_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := jCurr)
      dsimp [finalOracleBlockIdx, jCurr, oraclePositionToDomainIndex] at h_le ⊢
      omega)
    (f := oStmtOut jCurr)
    h_fw_curr

private def finalOracleDecodedAt
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
    (h_close : finalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) :=
  finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht h_close

private def finalDecodedPrefixAt
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (t : ℕ) (ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) :=
  finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t ht

private def finalOracleNextIdxOrig
    (t : ℕ) (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) : Fin r :=
  ⟨t * ϑ + ϑ, by
    apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ + ϑ)
    exact oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩)⟩

private def finalOracleNextRaw
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) :=
  getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (Fin.last ℓ) oStmtOut ⟨t, Nat.lt_of_succ_lt ht⟩ ht
    (destDomainIdx := finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)
    (h_destDomainIdx := by rfl)

private def finalOracleNextClose
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) : Prop :=
  UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)
    (h_i := by
      exact oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩))
    (f := finalOracleNextRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht)

private def finalOracleNextCodeword
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ) (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
    (h_close : finalOracleNextClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) :=
  UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)
    (h_i := by
      have h_le := oracle_block_k_next_le_i ℓ ϑ (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩) (hj := ht)
      show (finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) ≤ ℓ
      dsimp [finalOracleNextIdxOrig]
      have h_eq : (t + 1) * ϑ = t * ϑ + ϑ := by
        rw [Nat.add_mul, one_mul]
      exact h_eq ▸ h_le)
    (f := finalOracleNextRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht)
    (h_within_radius := h_close)

set_option maxHeartbeats 800000 in
private theorem finalOracleDecoded_next_heq
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (t : ℕ)
    (ht : t + 1 < toOutCodewordsCount ℓ ϑ (Fin.last ℓ))
    (h_close_next : finalOracleNextClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht)
    (h_close_next_final : finalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut (t + 1) ht) :
    HEq
      (finalOracleNextCodeword (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht h_close_next)
      (finalOracleDecodedAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut (t + 1) ht h_close_next_final) := by
  dsimp only [finalOracleNextCodeword, finalOracleDecodedAt, finalOracleDecoded]
  have h_idx :
      finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht =
      finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t + 1) ht := by
    apply Fin.ext
    dsimp [finalOracleNextIdxOrig, finalOracleBlockIdx]
    rw [Nat.add_mul, Nat.one_mul]
  have h_dom :
      ↥(sDomain 𝔽q β h_ℓ_add_R_rate
        (finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht)) =
      ↥(sDomain 𝔽q β h_ℓ_add_R_rate
        (finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t + 1) ht)) := by
    exact congrArg (fun i => ↥(sDomain 𝔽q β h_ℓ_add_R_rate i)) h_idx
  have h_raw_heq :
      HEq
        (finalOracleNextRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht)
        (finalOracleRaw (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut (t + 1) ht) := by
    exact funext_heq h_dom (fun _ => rfl) (by
      intro y
      apply heq_of_eq
      dsimp [finalOracleNextRaw, getNextOracle, finalOracleRaw,
        finalOracleNextIdxOrig, finalOracleBlockIdx])
  exact UDRCodeword_heq_of_fin_eq (𝔽q := 𝔽q) (β := β)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_idx
    (by
      have h_le := oracle_block_k_next_le_i ℓ ϑ
        (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩) (hj := ht)
      show
        (finalOracleNextIdxOrig (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ht) ≤ ℓ
      dsimp [finalOracleNextIdxOrig]
      have h_eq : (t + 1) * ϑ = t * ϑ + ϑ := by
        rw [Nat.add_mul, Nat.one_mul]
      exact h_eq ▸ h_le)
    (by
      exact oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
        (i := Fin.last ℓ) (j := ⟨t + 1, ht⟩))
    h_raw_heq h_close_next h_close_next_final

set_option maxHeartbeats 800000 in
-- This induction over all final oracles repeatedly invokes the transport-heavy successor theorem.
private theorem finalOracleDecoded_nat_eq_prefixFold
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (h_oracle_cons : oracleFoldingConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := Fin.last ℓ) (challenges := stmtOut.challenges) (oStmt := oStmtOut))
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (h_close_first : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (h_i := Nat.zero_le ℓ) (f := getFirstOracle 𝔽q β oStmtOut))
    (h_dec0_eq_f0 :
      UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (h_i := Nat.zero_le ℓ) (f := getFirstOracle 𝔽q β oStmtOut)
        (h_within_radius := h_close_first) = f₀) :
    ∀ t, ∀ ht : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ),
      ∀ h_close : finalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht,
        finalOracleDecodedAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht h_close =
        finalDecodedPrefixAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t ht := by
  intro t
  induction t with
  | zero =>
      intro ht
      intro h_close
      exact finalOracleDecoded_zero_eq_prefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut oStmtOut f₀
        h_close_first h_dec0_eq_f0 ht h_close
  | succ t ih =>
      intro ht
      intro h_close
      let ht_prev : t < toOutCodewordsCount ℓ ϑ (Fin.last ℓ) := Nat.lt_of_succ_lt ht
      have h_close_curr :
          finalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht_prev :=
        finalOracleClose_curr (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut oStmtOut h_oracle_cons t ht
      have h_curr_eq :
          finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht_prev h_close_curr =
          finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t ht_prev :=
        ih ht_prev h_close_curr
      let jCurr : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) := ⟨t, ht_prev⟩
      have h_complCurr := h_oracle_cons jCurr ht
      rcases h_complCurr with ⟨h_fw_curr, h_close_next, h_fold_curr⟩
      have h_close_curr_fw :
          finalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht_prev :=
        finalOracleClose_curr (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut oStmtOut h_oracle_cons t ht
      have h_curr_decoded_eq :
          finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht_prev h_close_curr_fw =
          finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht_prev h_close_curr := by
        exact finalOracleDecoded_eq_of_close (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht_prev h_close_curr_fw h_close_curr
      change
        iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨t * ϑ, by
            apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ)
            exact oracle_block_k_le_i (ℓ := ℓ) (ϑ := ϑ)
              (i := Fin.last ℓ) (j := jCurr)⟩)
          (steps := ϑ)
          (destIdx := ⟨t * ϑ + ϑ, by
            apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ + ϑ)
            exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
              (i := Fin.last ℓ) (j := jCurr) (hj := ht)⟩)
          (h_destIdx := by rfl)
          (h_destIdx_le := by
            exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
              (i := Fin.last ℓ) (j := jCurr) (hj := ht))
          (f := finalOracleDecoded (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht_prev h_close_curr_fw)
          (r_challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
            (i := Fin.last ℓ) (challenges := stmtOut.challenges) (t * ϑ)
            (h := by
              exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
                (i := Fin.last ℓ) (j := jCurr) (hj := ht))) =
        finalOracleNextCodeword (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht h_close_next at h_fold_curr
      rw [h_curr_decoded_eq, h_curr_eq] at h_fold_curr
      change
        iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨t * ϑ, by
            apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ)
            exact oracle_block_k_le_i (ℓ := ℓ) (ϑ := ϑ)
              (i := Fin.last ℓ) (j := jCurr)⟩)
          (steps := ϑ)
          (destIdx := ⟨t * ϑ + ϑ, by
            apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ + ϑ)
            exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
              (i := Fin.last ℓ) (j := jCurr) (hj := ht)⟩)
          (h_destIdx := by rfl)
          (h_destIdx_le := by
            exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
              (i := Fin.last ℓ) (j := jCurr) (hj := ht))
          (f := finalDecodedPrefixAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t ht_prev)
          (r_challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
            (i := Fin.last ℓ) (challenges := stmtOut.challenges) (t * ϑ)
            (h := by
              exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
                (i := Fin.last ℓ) (j := jCurr) (hj := ht))) =
        finalOracleNextCodeword (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht h_close_next at h_fold_curr
      have h_rhs_heq :
          HEq
            (finalOracleNextCodeword (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht h_close_next)
            (finalOracleDecodedAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut (t + 1) ht h_close) := by
        exact finalOracleDecoded_next_heq (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut t ht h_close_next h_close
      have h_fold_curr_heq := (heq_of_eq h_fold_curr).trans h_rhs_heq
      have h_blockChallenges_eq :
          getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) (i := Fin.last ℓ)
            (challenges := stmtOut.challenges) (t * ϑ)
            (h := by
              exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
                (i := Fin.last ℓ) (j := jCurr) (hj := ht)) =
          finalBlockChallenges
            (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) stmtOut t ht := by
        funext cId
        dsimp [getFoldingChallenges, finalBlockChallenges, jCurr, oraclePositionToDomainIndex]
      rw [h_blockChallenges_eq] at h_fold_curr_heq
      have h_step_heq :
          HEq
            (finalDecodedPrefixAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ (t + 1) ht)
            (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := ⟨t * ϑ, by
                apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ)
                exact oracle_block_k_le_i (ℓ := ℓ) (ϑ := ϑ)
                  (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩)⟩)
              (steps := ϑ)
              (destIdx := ⟨t * ϑ + ϑ, by
                apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ + ϑ)
                exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
                  (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩) (hj := ht)⟩)
              (h_destIdx := by rfl)
              (h_destIdx_le := by
                exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
                  (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩) (hj := ht))
              (f := finalDecodedPrefixAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t (Nat.lt_of_succ_lt ht))
              (r_challenges := finalBlockChallenges
                (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) stmtOut t ht)) := by
        have h_step' := finalDecodedPrefixFold_step (𝔽q := 𝔽q) (β := β)
          (ℓ := ℓ) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t ht
        have h_dest_eq :
            finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t + 1) ht =
            ⟨t * ϑ + ϑ, by
              apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ + ϑ)
              exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
                (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩) (hj := ht)⟩ := by
          apply Fin.eq_of_val_eq
          change (t + 1) * ϑ = t * ϑ + ϑ
          rw [Nat.add_mul, Nat.one_mul]
        have h_rhs_transport :
            HEq
              (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (i := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t (Nat.lt_of_succ_lt ht))
                (steps := ϑ)
                (destIdx := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t + 1) ht)
                (h_destIdx := by
                  dsimp [finalOracleBlockIdx]
                  rw [Nat.add_mul, Nat.one_mul])
                (h_destIdx_le := by
                  dsimp [finalOracleBlockIdx]
                  rw [Nat.add_mul, Nat.one_mul]
                  exact oracle_index_add_steps_le_ℓ ℓ ϑ
                    (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩))
                (f := finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t (Nat.lt_of_succ_lt ht))
                (r_challenges := finalBlockChallenges
                  (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) stmtOut t ht))
              (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (i := ⟨t * ϑ, by
                  apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ)
                  exact oracle_block_k_le_i (ℓ := ℓ) (ϑ := ϑ)
                    (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩)⟩)
                (steps := ϑ)
                (destIdx := ⟨t * ϑ + ϑ, by
                  apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ + ϑ)
                  exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
                    (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩) (hj := ht)⟩)
                (h_destIdx := by rfl)
                (h_destIdx_le := by
                  exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
                    (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩) (hj := ht))
                (f := finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t (Nat.lt_of_succ_lt ht))
                (r_challenges := finalBlockChallenges
                  (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) stmtOut t ht)) := by
          exact iterated_fold_heq_of_fin_eq (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (𝓡 := 𝓡)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t (Nat.lt_of_succ_lt ht))
            (steps := ϑ)
            (destIdx₁ := finalOracleBlockIdx (ℓ := ℓ) (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t + 1) ht)
            (destIdx₂ := ⟨t * ϑ + ϑ, by
              apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (x := t * ϑ + ϑ)
              exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
                (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩) (hj := ht)⟩)
            h_dest_eq
            (h_destIdx₁ := by
              dsimp [finalOracleBlockIdx]
              rw [Nat.add_mul, Nat.one_mul])
            (h_destIdx₂ := by
              dsimp [finalOracleBlockIdx])
            (h_destIdx_le₁ := by
              dsimp [finalOracleBlockIdx]
              rw [Nat.add_mul, Nat.one_mul]
              exact oracle_index_add_steps_le_ℓ ℓ ϑ
                (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩))
            (h_destIdx_le₂ := by
              exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ)
                (i := Fin.last ℓ) (j := ⟨t, Nat.lt_of_succ_lt ht⟩) (hj := ht))
            (f := finalDecodedPrefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ t (Nat.lt_of_succ_lt ht))
            (r_challenges := finalBlockChallenges
              (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) stmtOut t ht)
        exact (heq_of_eq h_step').symm.trans h_rhs_transport
      have h_res :
          HEq
            (finalDecodedPrefixAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ (t + 1) ht)
            (finalOracleDecodedAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut (t + 1) ht h_close) := by
        exact h_step_heq.trans h_fold_curr_heq
      exact eq_of_heq h_res.symm

set_option maxHeartbeats 800000 in
-- This positive-index wrapper is a thin specialization of the nat-index theorem.
private theorem finalOracleDecoded_pos_eq_prefixFold
    (stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtOut : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (Fin.last ℓ) j)
    (h_oracle_cons : oracleFoldingConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := Fin.last ℓ) (challenges := stmtOut.challenges) (oStmt := oStmtOut))
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (h_close_first : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (h_i := Nat.zero_le ℓ) (f := getFirstOracle 𝔽q β oStmtOut))
    (h_dec0_eq_f0 :
      UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r)) (h_i := Nat.zero_le ℓ) (f := getFirstOracle 𝔽q β oStmtOut)
        (h_within_radius := h_close_first) = f₀)
    (j : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)))
    (_h_j_pos : 0 < j.val)
    (h_close_j : finalOracleClose (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut j.val j.isLt) :
    finalOracleDecodedAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtOut j.val j.isLt h_close_j =
    finalDecodedPrefixAt (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut f₀ j.val j.isLt := by
  exact finalOracleDecoded_nat_eq_prefixFold (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut oStmtOut h_oracle_cons f₀
    h_close_first h_dec0_eq_f0 j.val j.isLt h_close_j

set_option maxHeartbeats 20000 in
-- This extraction-to-final-constant proof expands the final verifier and its consistency witness.

/-!
The round-by-round knowledge-extractor tail of this file
(`extracted_t_poly_eval_eq_final_constant` through `finalSumcheckKnowledgeStateFunction`)
is an unverified draft quarantined to `FinalSumcheckExtractorDraft.wip` (same directory)
until its phantom-lemma and KState-design blockers are resolved — see the header of that
file and issue #317 (2026-06-11). Nothing in the BinaryBasefold cone consumes it; the only
external consumer is FRIBinius/CoreInteractionPhase (`extracted_t_poly_eval_eq_final_constant`),
which stays red until the draft is repaired.
-/

end FinalSumcheckStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold.CoreInteraction
