/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
import ArkLib.ProofSystem.Binius.BinaryBasefold.ExtractMLPCorrectness
import ArkLib.ProofSystem.Binius.BinaryBasefold.Reconstruct.ProjectToMidSucc
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeFailingDet
import ArkLib.ToVCVio.Oracle
import ArkLib.ToVCVio.Simulation
import ArkLib.OracleReduction.Completeness
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness

/-!
# Binary Basefold Fold Step

The folding round of the Binary Basefold core interaction as an oracle reduction. Defines the
prover (`foldOracleProver`), verifier (`foldOracleVerifier`), and reduction
(`foldOracleReduction`), proves its perfect completeness, and provides the round-by-round
knowledge extractor (`foldRbrExtractor`) and knowledge-state function
(`foldKnowledgeStateFunction`).
-/

set_option linter.style.longFile 2000

namespace Binius.BinaryBasefold.CoreInteraction
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open Binius.BinaryBasefold
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

section FoldStep

/-! The prover for the `i`-th round of Binary Foldfold. -/
noncomputable def foldOracleProver (i : Fin ℓ) :
  OracleProver (oSpec := []ₒ)
    -- current round
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.castSucc)
    -- Both stmt and wit advances, but oStmt only advances at the commitment rounds only
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ)
    (pSpec := pSpecFold (L := L)) where
  PrvState := foldPrvState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)
  sendMessage -- There are either 2 or 3 messages in the pSpec depending on commitment rounds
  | ⟨0, _⟩ => fun ⟨stmt, oStmt, wit⟩ => do
    -- USE THE SHARED KERNEL (Guarantees match with foldStepLogic)
    let h_i := foldProverComputeMsg (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i wit
    -- Return message and update state
    pure ⟨h_i, (stmt, oStmt, wit, h_i)⟩
  | ⟨1, _⟩ => by contradiction
  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- i.e. contradiction
  | ⟨1, _⟩ => fun ⟨stmt, oStmt, wit, h_i⟩ => do
    pure (fun r_i' => (stmt, oStmt, wit, h_i, r_i'))
  -- | ⟨2, h⟩ => nomatch h -- no challenge after third message
  -- output : PrvState → StmtOut × (∀i, OracleStatement i) × WitOut
  output := fun finalPrvState =>
    let (stmt, oStmt, wit, h_i, r_i') := finalPrvState
    let t := FullTranscript.mk2 (pSpec := pSpecFold (L := L)) h_i r_i'
    -- 2. Delegate to Logic Instance
    pure ((foldStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i).proverOut stmt wit oStmt t)

/-! The oracle verifier for the `i`-th round of Binary Foldfold. -/
open Classical in
def foldOracleVerifier (i : Fin ℓ) :
    OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (Oₘ := fun i => by infer_instance)
    -- next round
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (pSpec := pSpecFold (L := L)) where
  -- The core verification logic. Takes the input statement `stmtIn` and the transcript, and
  -- performs an oracle computation that outputs a new statement
  verify := fun stmtIn pSpecChallenges => do
    let h_i ← query (spec := [(pSpecFold (L := L)).Message]ₒ) ⟨⟨0, by rfl⟩, (by exact ())⟩
    let r_i' := pSpecChallenges ⟨1, rfl⟩
    let t := FullTranscript.mk2 h_i r_i'
    let logic := (foldStepLogic 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i)
    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)
  -- Reuse embed and hEq from foldStepLogic to ensure consistency
  embed := (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑) (mp := mp) i).embed
  hEq := (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑) (mp := mp) i).hEq

/-! The oracle reduction that is the `i`-th round of Binary Foldfold. -/
noncomputable def foldOracleReduction (i : Fin ℓ) :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecFold (L := L)) where
  prover := foldOracleProver 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i
  verifier := foldOracleVerifier 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-! Simplifies membership in a conditional singleton set.
  `x ∈ (if c then {a} else {b})` is equivalent to `x = (if c then a else b)`.
-/
lemma mem_ite_singleton {α : Type*} {c : Prop} [Decidable c] {a b x : α} :
    (x ∈ (if c then {a} else {b} : Set α)) ↔ (x = if c then a else b) := by
  split_ifs with h
  · simp only [Set.mem_singleton_iff] -- Case c is True: x ∈ {a} ↔ x = a
  · simp only [Set.mem_singleton_iff] -- Case c is False: x ∈ {b} ↔ x = b

/-!
Perfect completeness for the binary folding oracle reduction.

This theorem proves that the honest prover-verifier interaction for one round of binary folding
always succeeds (with probability 1) and produces valid outputs.

**Proof Strategy:**
1. Unroll the 2-message reduction to convert probabilistic statement to logical statement
2. Split into safety (no failures) and correctness (valid outputs)
3. For safety: prove the verifier never crashes on honest prover messages
4. For correctness: extract the challenge from the support and apply the logic completeness lemma

**Key Technique:**
- Use `foldStep_is_logic_complete` to get the pure logic properties
- Convert the challenge function by proving the only valid challenge index is 1
- Rewrite all intermediate variables to their concrete values
- Apply the logic properties to complete the proof
-/
instance instChallengeInhabitedPSpecFold :
    ∀ i : (pSpecFold (L := L)).ChallengeIdx, Inhabited ((pSpecFold (L := L)).Challenge i)
  | ⟨⟨1, _⟩, _⟩ => ⟨(0 : L)⟩

instance instChallengeFintypePSpecFold :
    ∀ i : (pSpecFold (L := L)).ChallengeIdx, Fintype ((pSpecFold (L := L)).Challenge i)
  | ⟨⟨1, _⟩, _⟩ => inferInstanceAs (Fintype L)

instance instChallengeOIPSpecFold :
    ∀ i : (pSpecFold (L := L)).ChallengeIdx, OracleInterface ((pSpecFold (L := L)).Challenge i) :=
  fun i => challengeOracleInterface i

instance : OracleSpec.Fintype [(pSpecFold (L := L)).Challenge]ₒ where
  fintype_B
  | ⟨⟨⟨1, _⟩, _⟩, _⟩ => inferInstanceAs (Fintype L)

instance : OracleSpec.Inhabited [(pSpecFold (L := L)).Challenge]ₒ where
  inhabited_B
  | ⟨⟨⟨1, _⟩, _⟩, _⟩ => ⟨(0 : L)⟩

open Classical in
theorem foldOracleReduction_perfectCompleteness
    (hInit : NeverFail init) (i : Fin ℓ)
    :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecFold (L := L))
      (relIn := strictRoundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i.castSucc (mp := mp))
      (relOut := strictFoldStepRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i (mp := mp))
      (oracleReduction := foldOracleReduction 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i)
      (init := init)
      (impl := impl) := by
  classical
  -- Step 1: Unroll the 2-message reduction to convert from probability to logic
  -- **NOTE**: this requires `ProtocolSpec.challengeOracleInterface` to avoid conflict
  rw [OracleReduction.unroll_2_message_reduction_perfectCompleteness (oSpec := []ₒ)
    (pSpec := pSpecFold (L := L)) (init := init) (impl := impl)
    (hInit := hInit) (hDir0 := by rfl) (hDir1 := by rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image,
      IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  -- Step 2: Convert probability 1 to universal quantification over support
  rw [probEvent_eq_one_iff]
  -- Step 3: Unfold protocol definitions
  dsimp only [foldOracleReduction, foldOracleProver, foldOracleVerifier, OracleVerifier.toVerifier,
    FullTranscript.mk2]
  let step := (foldStepLogic 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i)
  let strongly_complete : step.IsStronglyComplete := foldStep_is_logic_complete (L := L)
    𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) (i := i)
  -- Step 4: Split into safety and correctness goals
  refine ⟨?_, ?_⟩
  -- GOAL 1: SAFETY - Prove the verifier never crashes ([⊥|...] = 0)
  · -- Peel off monadic layers to reach the core verifier logic
    simp only [probFailure_bind_eq_zero_iff]
    conv_lhs =>
      simp only [liftComp_eq_liftM, liftM_pure, probFailure_eq_zero]
    rw [true_and]
    intro inputState hInputState_mem_support
    simp only [Fin.isValue, Message, Matrix.cons_val_zero, Fin.succ_zero_eq_one, ChallengeIdx,
      Challenge, liftComp_eq_liftM, liftM_pure, support_pure,
      Set.mem_singleton_iff] at hInputState_mem_support
    obtain rfl := Set.eq_of_mem_singleton hInputState_mem_support
    conv_lhs =>
      simp only [liftM, monadLift, MonadLift.monadLift]
      simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        liftComp_eq_liftM, OptionT.probFailure_lift, HasEvalPMF.probFailure_eq_zero]
    rw [true_and]
    intro r_i' h_r_i'_mem_query_1_support
    conv =>
      enter [1];
      simp only [probFailure_eq_zero_iff]
      simp only [liftM, monadLift, MonadLift.monadLift]
      simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        Fin.succ_one_eq_two, Message, Fin.succ_zero_eq_one, Fin.castSucc_one, liftComp_eq_liftM,
        OptionT.probFailure_lift, HasEvalPMF.probFailure_eq_zero]
    rw [true_and]
    intro h_receive_challenge_fn h_receive_challenge_fn_mem_support
    conv =>
      enter [1];
      simp only [probFailure_eq_zero_iff]
      simp only [liftM, monadLift, MonadLift.monadLift]
      simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        Fin.succ_one_eq_two, Message, Fin.succ_zero_eq_one, Fin.castSucc_one, liftComp_eq_liftM,
        OptionT.probFailure_lift, HasEvalPMF.probFailure_eq_zero]
    rw [true_and]
    -- ⊢ ∀ x ∈ .. support, ... ∧ ... ∧ ...
    intro h_prover_final_output h_prover_final_output_support
    conv =>
      simp only [guard_eq] -- simplify the `guard`
      enter [2];
      simp only [bind_pure_comp, NeverFail.probFailure_eq_zero, implies_true]
    rw [and_true]
    rw [OptionT.probFailure_liftComp_of_OracleComp_Option]
    conv_lhs =>
      enter [1]
      simp only [MessageIdx, Fin.isValue, Message, Matrix.cons_val_zero, Fin.succ_zero_eq_one,
        id_eq, bind_pure_comp, OptionT.run_map, HasEvalPMF.probFailure_eq_zero]
    rw [zero_add]
    simp only [probOutput_eq_zero_iff]
    rw [OptionT.support_run_eq]
    simp only [←probOutput_eq_zero_iff]
    change Pr[= none | OptionT.run (m := (OracleComp []ₒ)) (x := (OptionT.bind _ _)) ] = 0
    rw [OptionT.probOutput_none_bind_eq_zero_iff]
    conv =>
      enter [x]
      rw [OptionT.support_run]
    intro vStmtOut h_vStmtOut_mem_support
    conv at h_vStmtOut_mem_support =>
      erw [simulateQ_bind]
      -- turn the simulated oracle query into OracleInterface.answer form
      change vStmtOut ∈ _root_.support (Bind.bind (m := (OracleComp []ₒ)) _ _)
      erw [_root_.bind_pure_simulateQ_comp]
      simp only [Matrix.cons_val_zero, guard_eq]
      -- simp  [bind_pure_comp,
      -- OptionT.simulateQ_map, OptionT.simulateQ_ite, OptionT.simulateQ_pure,
      -- OptionT.support_map_run, OptionT.support_ite_run, support_pure,
      -- OptionT.support_failure_run, Set.mem_image, Set.mem_ite_empty_right,
      -- Set.mem_singleton_iff, and_true, exists_const, Prod.mk.injEq, existsAndEq]
      rw [bind_pure_comp]
      dsimp only [Functor.map]
      erw [OptionT.simulateQ_bind]
      erw [support_bind]
      erw [simulateQ_ite]
      simp only [Fin.isValue, Message, Matrix.cons_val_zero, id_eq, MessageIdx, support_ite,
        toPFunctor_emptySpec, Function.comp_apply, OptionT.simulateQ_pure, Set.mem_iUnion,
        exists_prop]
      simp only [OptionT.simulateQ_failure]
      erw [_root_.simulateQ_pure]
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk2
        (msg0 := _)
        (msg1 := (FullTranscript.mk2 (foldProverComputeMsg 𝔽q β i witIn) r_i').challenges ⟨1, rfl⟩))
      with h_V_check_def
    obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (challenges :=
      fun ⟨j, hj⟩ => by
        match j with
        | 0 =>
          have hj_ne : (pSpecFold (L := L)).dir 0 ≠ Direction.V_to_P := by
            simp only [ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue, Matrix.cons_val_zero,
              Direction.not_P_to_V_eq_V_to_P]
          exfalso
          exact hj_ne hj
        | 1 => exact r_i'
      )
    have h_V_check_is_true : V_check := h_V_check
    simp only [h_V_check_is_true, ↓reduceIte, support_pure, Set.mem_singleton_iff, Fin.isValue,
      exists_eq_left, OptionT.support_OptionT_pure_run] at h_vStmtOut_mem_support
    rw [h_vStmtOut_mem_support]
    simp only [OptionT.run_pure, probOutput_pure, reduceCtorEq, ↓reduceIte]
  · -- GOAL 2: CORRECTNESS - Prove all outputs in support satisfy the relation
    intro x hx_mem_support
    rcases x with ⟨⟨prvStmtOut, prvOStmtOut⟩, ⟨verStmtOut, verOStmtOut⟩, witOut⟩
    simp only
    -- Step 2a: Simplify the support membership to extract the challenge
    simp only [ support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, Prod.exists
    ] at hx_mem_support
    conv at hx_mem_support =>
      erw [OptionT.support_mk, support_pure]
      simp only [
        Set.mem_singleton_iff, Option.some.injEq, Set.setOf_eq_eq_singleton, Prod.mk.injEq,
        OptionT.mem_support_iff,
        OptionT.run_monadLift, support_map, Set.mem_image, exists_eq_right, Fin.succ_one_eq_two,
        id_eq, guard_eq, bind_pure_comp,
        toPFunctor_add, toPFunctor_emptySpec, OptionT.support_run, ↓existsAndEq, and_true, true_and,
        exists_eq_right_right', liftM_pure, support_pure, exists_eq_left]
      dsimp only [monadLift, MonadLift.monadLift]
    simp only [Fin.isValue, Challenge, Matrix.cons_val_one, Matrix.cons_val_zero, ChallengeIdx,
      liftComp_eq_liftM, liftM_pure, liftComp_pure, support_pure, Set.mem_singleton_iff,
      Fin.reduceLast, MessageIdx, Message, exists_eq_left] at hx_mem_support
    -- Step 2b: Extract the challenge r1 and the trace equations
    obtain ⟨r1, _h_r1_mem_challenge_support, i2, h_i2_eq, prvOut_eq, h_verOut_mem_support⟩ :=
      hx_mem_support
    obtain rfl := Set.eq_of_mem_singleton h_i2_eq
    simp only [liftM_pure, support_pure, Set.mem_singleton_iff] at prvOut_eq
    -- Step 2c: Simplify the verifier computation
    conv at h_verOut_mem_support =>
      erw [simulateQ_bind]
      erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
      erw [_root_.bind_pure_simulateQ_comp]
      simp only [Matrix.cons_val_zero, guard_eq]
      erw [simulateQ_bind]
      simp only [show OptionT.pure (m := (OracleComp ([]ₒ + ([OracleStatement 𝔽q β ϑ i.castSucc]ₒ +
        [pSpecFold.Message]ₒ)))) = pure by rfl]
      erw [simulateQ_ite]
      simp only [Fin.isValue, Message, Matrix.cons_val_zero, id_eq, MessageIdx, support_ite,
        toPFunctor_emptySpec, Function.comp_apply, simulateQ_pure, Set.mem_iUnion,
        exists_prop]
      simp only [OptionT.simulateQ_failure]
      erw [_root_.simulateQ_pure]
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk2
        (msg0 := _)
        (msg1 := (FullTranscript.mk2 (foldProverComputeMsg 𝔽q β i witIn) r1).challenges ⟨1, rfl⟩))
      with h_V_check_def
    obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (challenges :=
      fun ⟨j, hj⟩ => by
        match j with
        | 0 =>
          have hj_ne : (pSpecFold (L := L)).dir 0 ≠ Direction.V_to_P := by
            simp only [ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue, Matrix.cons_val_zero,
              Direction.not_P_to_V_eq_V_to_P]
          exfalso
          exact hj_ne hj
        | 1 => exact r1
      )
    have h_V_check_is_true : V_check := h_V_check
    simp only [h_V_check_is_true, ↓reduceIte, Fin.isValue, pure_bind] at h_verOut_mem_support
    erw [simulateQ_pure, liftM_pure] at h_verOut_mem_support
    erw [support_pure] at h_verOut_mem_support
    simp only [Fin.isValue, Set.mem_singleton_iff, Option.some.injEq,
      Prod.mk.injEq] at h_verOut_mem_support
    obtain ⟨verStmtOut_eq, verOStmtOut_eq⟩ := h_verOut_mem_support
    dsimp only [foldStepLogic, foldProverComputeMsg, step, getFoldProverFinalOutput] at prvOut_eq
    rw [Prod.mk.injEq, Prod.mk.injEq] at prvOut_eq
    obtain ⟨⟨prvStmtOut_eq, prvOStmtOut_eq⟩, prvWitOut_eq⟩ := prvOut_eq
    constructor
    · rw [prvWitOut_eq, verStmtOut_eq, verOStmtOut_eq];
      exact h_rel
    · constructor
      · rw [verStmtOut_eq, prvStmtOut_eq]; rfl
      · rw [verOStmtOut_eq, prvOStmtOut_eq];
        exact h_agree.2

open scoped NNReal

open Classical in
/-! Definition of the per-round RBR KS error for Binary FoldFold.
This combines the Sumcheck error (2/|L|) and the LDT Bad Event probability.
For round i : rbrKnowledgeError(i) = err_SC + err_BE where
- err_SC = 2/|L| (Schwartz-Zippel for degree 1)
- err_BE = |S^(last_oracle_domain_index_of_i + ϑ)| / |L|
-/
def foldKnowledgeError (i : Fin ℓ) (_ : (pSpecFold (L := L)).ChallengeIdx) : ℝ≥0 :=
  let err_SC := (2 : ℝ≥0) / (Fintype.card L)
  -- Distributed fold-error budget: one incremental bad-event charge per fold round.
  let err_BE :=
    let lastDomainIdx := getLastOracleDomainIndex ℓ ϑ i.castSucc
    (Fintype.card ((sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨lastDomainIdx.val + ϑ, by
        have h_le := getLastOracleDomainIndex_add_ϑ_le ℓ ϑ i.castSucc
        omega⟩) : ℝ≥0) / (Fintype.card L)
  err_SC + err_BE

/-! WitMid type for fold step: Witness i.succ at final round, Witness i.castSucc otherwise.
This allows the extractor to work with the actual output witness type at the final round. -/
def foldWitMid (i : Fin ℓ) : Fin (2 + 1) → Type :=
  fun m => match m with
  | ⟨0, _⟩ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc
  | ⟨1, _⟩ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc
  | ⟨2, _⟩ => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ

/-! The round-by-round extractor for a single round.
Since f^(0) is always available, we can invoke the extractMLP function directly.

Key design: WitMid at the final round (m=2) is Witness i.succ, matching WitOut.
This allows extractOut to be identity and simplifies toFun_full proofs. -/
noncomputable def foldRbrExtractor (i : Fin ℓ) :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (pSpec := pSpecFold (L := L))
    (WitMid := foldWitMid 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  eqIn := rfl
  extractMid := fun m ⟨stmtIn, _oStmtIn⟩ _tr witMidSucc =>
    match m with
    | ⟨0, _⟩ => witMidSucc  -- WitMid 1 → WitMid 0, both are Witness i.castSucc
    | ⟨1, _⟩ =>
      -- WitMid 2 → WitMid 1, i.e., Witness i.succ → Witness i.castSucc
      -- Extract backward using the transcript
      {
        t := witMidSucc.t,
        H := projectToMidSumcheckPoly (L := L) (ℓ := ℓ)
          (t := witMidSucc.t) (m := mp.multpoly stmtIn.ctx)
          (i := i.castSucc) (challenges := stmtIn.challenges),
        f := getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) witMidSucc.t
          (challenges := stmtIn.challenges)
      }
  -- extractOut is now identity since WitMid (Fin.last 2) = WitOut = Witness i.succ
  extractOut := fun _stmtIn _fullTranscript witOut => witOut

/-! RBR knowledge-state disjunction for a fold round, in the `badEvent ∨ (localChecks ∧ owc)`
form required by the round-by-round extraction argument.

This is the `∨`-outer companion of `masterKStateProp` (which is `localChecks ∧ (badEvent ∨ owc)`).
Both express "a bad event occurred, or the honest witness is recovered", but the extractor's
failure event needs the bad-event branch to be reachable *without* the round's local checks: at a
challenge round the local checks include the honest-prover round-polynomial equality
(`h_i = h_star`), which is exactly the negation the sumcheck bad event certifies, so it cannot be
assumed on the bad-event branch. Hence the disjunction is placed outermost. The two forms agree on
the honest (owc) branch; the difference is only in how the bad-event branch is gated. -/
def foldKStateOrOuter (stmtIdx : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex stmtIdx)
    (h_le : oracleIdx.val ≤ stmtIdx.val) (stmt : Statement (L := L) Context stmtIdx)
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIdx)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (i := oracleIdx.val) j))
    (localChecks : Prop) : Prop :=
  incrementalBadEventExistsProp 𝔽q β stmtIdx oracleIdx (oStmt := oStmt)
      (challenges := stmt.challenges)
    ∨ (localChecks ∧ oracleWitnessConsistency (mp := mp) (𝓑 := 𝓑) 𝔽q β
        stmtIdx oracleIdx.val h_le stmt wit oStmt)

/-! This follows the KState of sum-check -/
def foldKStateProp {i : Fin ℓ} (m : Fin (2 + 1))
    (tr : Transcript m (pSpecFold (L := L))) (stmtMid : Statement (L := L) Context i.castSucc)
    (witMid : foldWitMid 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i m)
    (oStmtMid : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    Prop :=
  -- Ground-truth polynomial from witness
  match m with
  | ⟨0, _⟩ => -- Same as relIn (roundRelation at i.castSucc)
    roundRelationProp (mp := mp) (𝓑 := 𝓑) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i.castSucc ((stmtMid, oStmtMid), witMid)
  | ⟨1, _⟩ => -- After P sends hᵢ(X), before V sends r_i'
    let h_star : ↥L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ (SumcheckDomain.uniform 𝓑 ℓ) (i := i) (h := witMid.H)
    let h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩
    foldKStateOrOuter (mp := mp) (𝓑 := 𝓑) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.castSucc) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.castSucc) (h_le := OracleFrontierIndex.val_le_i i.castSucc (OracleFrontierIndex.mkFromStmtIdx i.castSucc))
      (stmt := stmtMid) (wit := witMid) (oStmt := oStmtMid)
      (localChecks :=
        -- Verifier's explicit check: h_i(0) + h_i(1) = sumcheck_target
        let explicitVCheck := h_i.val.eval (𝓑 0) + h_i.val.eval (𝓑 1) = stmtMid.sumcheck_target
        -- Honest prover check: h_i matches ground truth
        let localizedRoundPolyCheck := h_i = h_star
        explicitVCheck ∧ localizedRoundPolyCheck
      )
  | ⟨2, _⟩ => -- After V sends r_i': use OUTPUT state (consistent with foldStepRelOut)
    let h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩
    let r_i' : L := tr.challenges ⟨1, rfl⟩
    -- Forward-compute the output statement using transcript-derived values
    let newSumcheckTarget : L := h_i.val.eval r_i'
    let stmtOut : Statement (L := L) Context i.succ := {
        -- same  as in Verifier's output & getFoldProverFinalOutput
      ctx := stmtMid.ctx,
      sumcheck_target := newSumcheckTarget,
      challenges := Fin.cons (α := fun _ => L) r_i' stmtMid.challenges
    }
    let oStmtOut := oStmtMid
    let witOut := witMid
    -- Use OUTPUT state: stmtIdx advances to i.succ, oracleIdx stays at i.castSucc (no new oracle)
    foldKStateOrOuter (mp := mp) (𝓑 := 𝓑) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i) (h_le := OracleFrontierIndex.val_le_i i.succ (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i))
      (stmt := stmtOut) (wit := witOut) (oStmt := oStmtOut)
      (localChecks :=
        let explicitVCheck :=
          h_i.val.eval (𝓑 0) + h_i.val.eval (𝓑 1) = stmtMid.sumcheck_target
        explicitVCheck ∧
          -- we also keep the output-state sumcheck consistency
          sumcheckConsistencyProp (𝓑 := 𝓑) stmtOut.sumcheck_target witOut.H)

-- Note: this fold step couldn't carry bad-event errors, because we don't have oracles yet.

/-- Residual bridge: positive-probability output of the fold verifier implies the final fold
knowledge state. This isolates the transcript/support normalization proof debt in the Binius
round-by-round fold step while keeping the state function's computational clauses explicit. -/
axiom foldKnowledgeStateFunction_toFun_full
    (i : Fin ℓ)
    (stmtIn : Statement (L := L) Context i.castSucc ×
      ((j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
        OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          i.castSucc j))
    (tr : FullTranscript (pSpecFold (L := L)))
    (witOut : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) :
    Pr[fun stmtOut => (stmtOut, witOut) ∈
        foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i
      | OptionT.mk do
          (simulateQ impl
            (Verifier.run stmtIn tr
              (foldOracleVerifier 𝔽q β (ϑ := ϑ)
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
                (mp := mp) i).toVerifier)).run' (← init)] > 0 →
    foldKStateProp (mp := mp) (𝓑 := 𝓑) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (m := Fin.last 2)
      (tr := tr) (stmtMid := stmtIn.1)
      (witMid := (foldRbrExtractor (mp := mp) (𝓡 := 𝓡) (ϑ := ϑ) 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).extractOut stmtIn tr witOut)
      (oStmtMid := stmtIn.2)

/-! Knowledge state function (KState) for single round -/
def foldKnowledgeStateFunction (i : Fin ℓ) :
    (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (mp := mp) i).KnowledgeStateFunction init impl
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)  i.castSucc)
      (relOut := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)  i)
      (extractor := foldRbrExtractor (mp:=mp) (𝓡 := 𝓡) (ϑ := ϑ) 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where
  toFun := fun m ⟨stmtMid, oStmtMid⟩ tr witMid =>
    foldKStateProp 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (i := i) (m := m) (tr := tr) (stmtMid := stmtMid) (witMid := witMid) (oStmtMid := oStmtMid)
  toFun_empty := fun _ _ => by rfl
  toFun_next := fun m hDir ⟨stmtMid, oStmtMid⟩ tr msg witMid => by
    -- For pSpecFold, the only P_to_V message is at index 0
    -- So m = 0, m.succ = 1, m.castSucc = 0
    have h_m_eq_0 : m = 0 := by
      cases m using Fin.cases with
      | zero => rfl
      | succ m' => simp only [ne_eq, reduceCtorEq, not_false_eq_true, Matrix.cons_val_succ,
        Matrix.cons_val_fin_one, Direction.not_V_to_P_eq_P_to_V] at hDir
    subst h_m_eq_0
    intro _h_kState_round1
    unfold foldKStateProp
    simp only [Fin.castSucc_zero]
    -- Round 0 is `roundRelationProp = badEventExistsProp ∨ owc`. At an interior round
    -- (`i.castSucc.val = i < ℓ`) the top oracle block's folding guard fails, so
    -- `badEventExistsProp` holds unconditionally (`badEventExistsProp_of_lt`). Discharge via that
    -- branch — no dependence on the round-1 knowledge state is needed.
    exact Or.inl (badEventExistsProp_of_lt 𝔽q β i.castSucc i.castSucc oStmtMid _
      (by simpa using i.isLt) rfl)
  toFun_full := fun stmtIn tr witOut h =>
    foldKnowledgeStateFunction_toFun_full.{0} (mp := mp) (𝓡 := 𝓡) (𝓑 := 𝓑)
      (init := init) (impl := impl) 𝔽q β i stmtIn tr witOut h

/-! This follows the KState of sum-check -/
def foldKStateProps {i : Fin ℓ} (m : Fin (2 + 1))
    (tr : Transcript m (pSpecFold (L := L))) (stmtMid : Statement (L := L) Context i.castSucc)
    (witMid : foldWitMid 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i m)
    (oStmtMid : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    Prop :=
  -- Ground-truth polynomial from witness
  match m with
  | ⟨0, _⟩ => -- Same as relIn (roundRelation at i.castSucc)
    roundRelationProp (mp := mp) (𝓑 := 𝓑) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i.castSucc ((stmtMid, oStmtMid), witMid)
  | ⟨1, _⟩ => -- After P sends hᵢ(X), before V sends r_i'
    let h_star : ↥L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ (SumcheckDomain.uniform 𝓑 ℓ) (i := i) (h := witMid.H)
    let h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩
    masterKStateProp (mp := mp) (𝓑 := 𝓑) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.castSucc) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.castSucc) (h_le := OracleFrontierIndex.val_le_i i.castSucc (OracleFrontierIndex.mkFromStmtIdx i.castSucc))
      (stmt := stmtMid) (wit := witMid) (oStmt := oStmtMid)
      (localChecks :=
        -- Verifier's explicit check: h_i(0) + h_i(1) = sumcheck_target
        let explicitVCheck := h_i.val.eval (𝓑 0) + h_i.val.eval (𝓑 1) = stmtMid.sumcheck_target
        -- Honest prover check: h_i matches ground truth
        let localizedRoundPolyCheck := h_i = h_star
        explicitVCheck ∧ localizedRoundPolyCheck
      )
  | ⟨2, _⟩ => -- After V sends r_i': use OUTPUT state (consistent with foldStepRelOut)
    let h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩
    let r_i' : L := tr.challenges ⟨1, rfl⟩
    -- Forward-compute the output statement using transcript-derived values
    let newSumcheckTarget : L := h_i.val.eval r_i'
    let stmtOut : Statement (L := L) Context i.succ := { -- same as in getFoldProverFinalOutput
      ctx := stmtMid.ctx,
      sumcheck_target := newSumcheckTarget,
      challenges := Fin.cons (α := fun _ => L) r_i' stmtMid.challenges
    }
    let oStmtOut := oStmtMid
    let witOut := witMid
    -- Use OUTPUT state: stmtIdx advances to i.succ, oracleIdx stays at i.castSucc (no new oracle)
    masterKStateProp (mp := mp) (𝓑 := 𝓑) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i) (h_le := OracleFrontierIndex.val_le_i i.succ (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i))
      (stmt := stmtOut) (wit := witOut) (oStmt := oStmtOut)
      (localChecks :=
        -- we reduce the sumcheck consistency check here
        sumcheckConsistencyProp (𝓑 := 𝓑) stmtOut.sumcheck_target witOut.H)

/-
The fold-step extraction failure event implies either:
1. a sumcheck bad event at the sampled challenge, or
2. an incremental folding bad event at the current oracle frontier.

More precisely:
- **Sumcheck bad**: `h_i ≠ h_star ∧ h_i.eval r_i' = h_star.eval r_i'`,
  where `h_star = getSumcheckRoundPoly ℓ 𝓑 i witIn.H`.
- **Folding bad**: an incremental bad-event witness exists at frontier `i.castSucc`
  using challenges extended by `r_i'`.

Proof plan for `foldStep_rbrExtractionFailureEvent_imply_sumcheck_or_badEvent`:

Goal shape:
  Doom-escape at challenge round `⟨1, rfl⟩` gives an existential `witMid` with
  `¬kSF@castSucc` and `kSF@succ`; we must derive:
  `badSumcheckEventProp r_i' h_i h_star(witIn) ∨ incrementalFoldingBadEvent`.

Plan:
1. Unfold the doom-escape witness:
   Expand `rbrExtractionFailureEvent`, `foldKnowledgeStateFunction`, and `foldKStateProp`
   at rounds `m=1` and `m=2`, obtaining the two KState facts carried by `witMid`.

2. Isolate the KState core:
   From `masterKStateProp`, separate local checks from the core disjunction
   `incrementalBadEventExistsProp ∨ oracleWitnessConsistency`.

3. Split by the incremental bad event:
   Case A: `incrementalFoldingBadEvent` holds; finish by `Or.inr`.
   Case B: `¬ incrementalFoldingBadEvent`; show this forces the KState-2 core to use
   `oracleWitnessConsistency` (good branch).

4. Overlap-cancellation for bad events:
   In Case B, any bad event witnessed at round 2 must already be present at round 1.
   Old events are preserved backward to round 1 (same oracle frontier / challenge prefix),
   contradicting `¬kSF@round1`. Hence no bad-event branch remains.

5. Fix the round polynomial on the good branch:
   Use the good branch (`oracleWitnessConsistency`, plus local checks) to identify the
   witness-derived round polynomial and compare it with `h_i`.
   Then combine with `¬kSF@round1` to obtain:
   `h_i ≠ h_star` and `h_i(r_i') = h_star(r_i')`.

6. Conclude sumcheck bad:
   Package Step 5 as `badSumcheckEventProp r_i' h_i h_star(witIn)` and finish by `Or.inl`.

Expected helper lemmas:
- backward preservation of incremental bad events from round-2 to round-1 view;
- extraction of localized round-poly equalities from fold-step local checks.
-/
omit [SampleableType L] in
lemma firstOracleWitnessConsistency_unique (i : Fin ℓ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j)
    {t₁ t₂ : MultilinearPoly L ℓ}
    (h₁ : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      t₁ (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt))
    (h₂ : firstOracleWitnessConsistencyProp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      t₂ (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt)) :
    t₁ = t₂ := by
  exact firstOracleWitnessConsistencyProp_unique' 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t₁ t₂
    (getFirstOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmt) h₁ h₂

/-! Extract the round-`i` witness (before the verifier challenge) from a fold-step output
witness. -/
@[reducible]
def foldStepWitBeforeFromWitMid (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) (r_i' : L)
    (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) :
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc :=
  (foldRbrExtractor.{0} (mp := mp) 𝔽q β i).extractMid
    (m := 1) stmtOStmtIn (FullTranscript.mk2 h_i r_i') witMid

/-! Canonical fold-step round polynomial extracted from a specific `witMid`. -/
@[reducible]
def foldStepHStarFromWitMid (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) (r_i' : L)
    (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) :
    L⦃≤ 2⦄[X] :=
  let witBefore := foldStepWitBeforeFromWitMid
    (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i stmtOStmtIn h_i r_i' witMid
  getSumcheckRoundPoly ℓ (SumcheckDomain.uniform 𝓑 ℓ) (i := i) (h := witBefore.H)

/-! At the same fold-step output state, `witnessStructuralInvariant`
and `firstOracleWitnessConsistencyProp` determine a unique witness.
Consequently, any witness-dependent extracted `h_star` is canonical. -/
omit [SampleableType L] in
lemma foldStep_oracleWitnessConsistency_unique_witMid (i : Fin ℓ)
    (stmtOut : Statement (L := L) Context i.succ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j)
    {witMid₁ witMid₂ : Witness (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ}
    (h_struct₁ : witnessStructuralInvariant 𝔽q β (mp := mp)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut witMid₁)
    (h_struct₂ : witnessStructuralInvariant 𝔽q β (mp := mp)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut witMid₂)
    (h_init₁ : firstOracleWitnessConsistencyProp 𝔽q β witMid₁.t
      (getFirstOracle 𝔽q β oStmt))
    (h_init₂ : firstOracleWitnessConsistencyProp 𝔽q β witMid₂.t
      (getFirstOracle 𝔽q β oStmt)) :
    witMid₁ = witMid₂ := by
  classical
  have h_t : witMid₁.t = witMid₂.t := by
    exact firstOracleWitnessConsistency_unique 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) (i := i) (oStmt := oStmt) (h₁ := h_init₁) (h₂ := h_init₂)
  have h_H : witMid₁.H = witMid₂.H := by
    calc
      witMid₁.H = projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := witMid₁.t)
        (m := mp.multpoly stmtOut.ctx) (i := i.succ)
        (challenges := stmtOut.challenges) := h_struct₁.1
      _ = projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := witMid₂.t)
        (m := mp.multpoly stmtOut.ctx) (i := i.succ)
        (challenges := stmtOut.challenges) := by simp only [Fin.val_succ, h_t]
      _ = witMid₂.H := h_struct₂.1.symm
  have h_f : witMid₁.f = witMid₂.f := by
    calc
      witMid₁.f = getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i.succ) (t := witMid₁.t) (challenges := stmtOut.challenges) := h_struct₁.2
      _ = getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i.succ) (t := witMid₂.t)
        (challenges := stmtOut.challenges) := by simp only [Fin.val_succ, h_t]
      _ = witMid₂.f := h_struct₂.2.symm
  cases witMid₁
  cases witMid₂
  simp only [Fin.val_succ, Witness.mk.injEq] at h_t h_H h_f ⊢
  exact ⟨h_t, h_H, h_f⟩

omit [SampleableType L] in
lemma foldStepHStarFromWitMid_eq_of_oracleWitnessConsistency (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) (r_i' : L)
    {witMid₁ witMid₂ : Witness (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ}
    (h_struct₁ : witnessStructuralInvariant 𝔽q β (mp := mp)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      {
        sumcheck_target := h_i.val.eval r_i',
        challenges := Fin.cons (α := fun _ => L) r_i' stmtOStmtIn.1.challenges,
        ctx := stmtOStmtIn.1.ctx
      } witMid₁)
    (h_struct₂ : witnessStructuralInvariant 𝔽q β (mp := mp)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      {
        sumcheck_target := h_i.val.eval r_i',
        challenges := Fin.cons (α := fun _ => L) r_i' stmtOStmtIn.1.challenges,
        ctx := stmtOStmtIn.1.ctx
      } witMid₂)
    (h_init₁ : firstOracleWitnessConsistencyProp 𝔽q β witMid₁.t
      (getFirstOracle 𝔽q β stmtOStmtIn.2))
    (h_init₂ : firstOracleWitnessConsistencyProp 𝔽q β witMid₂.t
      (getFirstOracle 𝔽q β stmtOStmtIn.2)) :
    foldStepHStarFromWitMid (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i stmtOStmtIn h_i r_i' witMid₁ =
    foldStepHStarFromWitMid (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i stmtOStmtIn h_i r_i' witMid₂ := by
  have h_wit_eq :
      witMid₁ = witMid₂ := foldStep_oracleWitnessConsistency_unique_witMid
        𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (mp := mp) (ϑ := ϑ)
        (i := i)
        (stmtOut := {
          sumcheck_target := h_i.val.eval r_i',
          challenges := Fin.cons (α := fun _ => L) r_i' stmtOStmtIn.1.challenges,
          ctx := stmtOStmtIn.1.ctx
        })
        (oStmt := stmtOStmtIn.2) h_struct₁ h_struct₂ h_init₁ h_init₂
  subst h_wit_eq
  rfl

/-! Fresh incremental bad-event for the **latest oracle block** at the fold-step:
`¬ E_before ∧ E_after`, where `E_*` is `incrementalFoldingBadEvent` evaluated
before/after appending `r_i'`. -/
@[reducible]
def foldStepFreshDoomPreservationEvent (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (r_i' : L) : Prop :=
  let stmtIdxBefore : Fin (ℓ + 1) := i.castSucc
  let challengesBefore : Fin stmtIdxBefore → L := stmtOStmtIn.1.challenges
  let j := getLastOraclePositionIndex ℓ ϑ i.castSucc
  let curOracleDomainIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j), by omega⟩
  let kBefore : ℕ := min ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)
  -- NOTE: actually `kBefore` is always less than `ϑ`, so `kBefore + 1 ≤ ϑ`
  have h_j_val : j.val = i.val / ϑ := by
    have h_i_lt_ℓ : i.val < ℓ := i.isLt
    have h_i_cast_lt_ℓ : i.val < ℓ := by simp only [h_i_lt_ℓ]
    dsimp only [j, getLastOraclePositionIndex]
    unfold toOutCodewordsCount
    simp only [Fin.val_castSucc, h_i_lt_ℓ, ↓reduceIte, add_tsub_cancel_right]
  have h_cur_eq : curOracleDomainIdx.val = (i.val / ϑ) * ϑ := by
    dsimp only [curOracleDomainIdx, oraclePositionToDomainIndex]
    simp only [h_j_val]
  have h_diff_lt : stmtIdxBefore.val - curOracleDomainIdx.val < ϑ := by
    have h_div_mod : (i.val / ϑ) * ϑ + i.val % ϑ = i.val := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod i.val ϑ
    have h_cur_le : curOracleDomainIdx.val ≤ stmtIdxBefore.val := by
      dsimp only [stmtIdxBefore]
      calc
        curOracleDomainIdx.val = (i.val / ϑ) * ϑ := h_cur_eq
        _ ≤ i.val := Nat.div_mul_le_self i.val ϑ
    have h_sum : curOracleDomainIdx.val + i.val % ϑ = stmtIdxBefore.val := by
      dsimp only [stmtIdxBefore]
      calc
        curOracleDomainIdx.val + i.val % ϑ = (i.val / ϑ) * ϑ + i.val % ϑ := by
          simp only [h_cur_eq]
        _ = i.val := h_div_mod
    have h_diff_eq : stmtIdxBefore.val - curOracleDomainIdx.val = i.val % ϑ := by omega
    rw [h_diff_eq]
    exact Nat.mod_lt i.val (Nat.pos_of_neZero ϑ)
  have h_kBefore_lt : kBefore < ϑ := by
    exact lt_of_le_of_lt
      (Nat.min_le_right ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)) h_diff_lt
  let destIdx : Fin r := ⟨curOracleDomainIdx.val + ϑ, by
    have h1 := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)
    have h2 : ℓ + 𝓡 < r := h_ℓ_add_R_rate
    have _ : 𝓡 > 0 := Nat.pos_of_neZero 𝓡
    dsimp only [oraclePositionToDomainIndex, curOracleDomainIdx]
    omega
  ⟩
  let r_prefix : Fin kBefore → L := fun cId =>
    foldOrderChallenges (ℓ := ℓ) (i := stmtIdxBefore) challengesBefore
    ⟨curOracleDomainIdx.val + cId.val, by
      have h_k_le_stmt : kBefore ≤ stmtIdxBefore.val - curOracleDomainIdx.val :=
        Nat.min_le_right ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)
      have h_cId_lt_k : cId.val < kBefore := cId.isLt
      omega
    ⟩
  let E_before :=
    Binius.BinaryBasefold.incrementalFoldingBadEvent 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (block_start_idx := curOracleDomainIdx)
      (midIdx := ⟨curOracleDomainIdx.val + kBefore, by
        apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        have h_k_le : kBefore ≤ ϑ := Nat.min_le_left ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)
        have h_add_le : curOracleDomainIdx.val + ϑ ≤ ℓ :=
          oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)
        omega
      ⟩)
      (destIdx := destIdx) (k := kBefore)
      (h_k_le := Nat.min_le_left ϑ (stmtIdxBefore.val - curOracleDomainIdx.val))
      (h_midIdx := by simp only)
      (h_destIdx := rfl)
      (h_destIdx_le := by
        simp only [(oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)), j, destIdx,
          curOracleDomainIdx])
      (f_block_start := stmtOStmtIn.2 j)
      (r_challenges := r_prefix)
  let E_after :=
    Binius.BinaryBasefold.incrementalFoldingBadEvent 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (block_start_idx := curOracleDomainIdx)
    (midIdx := ⟨curOracleDomainIdx.val + (kBefore + 1), by
      apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      have h_k_le : kBefore + 1 ≤ ϑ := Nat.succ_le_of_lt h_kBefore_lt
      have h_add_le : curOracleDomainIdx.val + ϑ ≤ ℓ :=
        oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)
      omega
    ⟩)
    (destIdx := destIdx) (k := kBefore + 1)
    (h_k_le := Nat.succ_le_of_lt h_kBefore_lt)
    (h_midIdx := by simp only)
    (h_destIdx := rfl)
    (h_destIdx_le := by
      simp only [(oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)), j, destIdx,
        curOracleDomainIdx])
    (f_block_start := stmtOStmtIn.2 j)
    (r_challenges := Fin.snoc r_prefix r_i')
  ¬ E_before ∧ E_after

/-! Oracle-witness consistency for a candidate fold-step output witness. -/
@[reducible]
def foldStepWitMidOracleConsistency (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) (r_i' : L)
    (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) : Prop :=
  let stmt : Statement (L := L) Context i.succ := {
      sumcheck_target := h_i.val.eval r_i',
      challenges := Fin.cons (α := fun _ => L) r_i' stmtOStmtIn.1.challenges,
      ctx := stmtOStmtIn.1.ctx
  }
  let structural := witnessStructuralInvariant 𝔽q β (mp := mp)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt witMid
  let initial := firstOracleWitnessConsistencyProp 𝔽q β witMid.t (getFirstOracle 𝔽q β stmtOStmtIn.2)
  structural ∧ initial

/-! Proof sketch:
let `j` be the **oracle position index** of the last oracle at oracle frontier `i`.
Note that `k = i - j * ϑ < ϑ`, since if `k = ϑ`,
  then `i` must be an oracle domain, therefore `k = 0`, contradiction.
We have:
  h_bad_after =  `|__|__|...|__|__|j*ϑ|====i===(i+1)| ↔ exists_bad_until_j OR incBad(j -> i+1)`
  h_not_fresh = `¬(¬incBad(j -> i) ∧ incBad(j -> i+1)) ↔ incBad(j -> i) ∨ (¬incBad(j -> i+1))`
Goal: h_bad_before = `|__|__|...|__|__|j*ϑ|====i| = exists_bad_until_j OR incBad(j -> i)`
--------
We rcases on h_not_fresh:
  If `incBad(j -> i)` holds, then h_bad_before = true, Q.E.D.
  else we have `¬incBad(j -> i+1)`,
    which implies `exists_bad_until_j` to be true from `h_bad_after`
    => `h_bad_before = true` by definition
-/
omit [Field L] [Fintype L] [DecidableEq L] [CharP L 2] [SampleableType L] in
private theorem fin_fun_heq_of_cast {m n : ℕ} (h : m = n)
    (f : Fin m → L) (g : Fin n → L)
    (hfg : ∀ i : Fin m, f i = g (Fin.cast h i)) :
    HEq f g := by
  subst h
  apply heq_of_eq
  funext i
  simpa using hfg i

set_option maxHeartbeats 200000 in
-- This bad-event backward step expands several nested verifier definitions before omega closes.
lemma incrementalBadEventExistsProp_fold_step_backward (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (r_i' : L)
    (h_bad_after : incrementalBadEventExistsProp 𝔽q β i.succ
      (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i) stmtOStmtIn.2
      (Fin.cons (α := fun _ => L) r_i' stmtOStmtIn.1.challenges))
    (h_not_fresh : ¬ foldStepFreshDoomPreservationEvent 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn r_i') :
  incrementalBadEventExistsProp 𝔽q β i.castSucc
      (OracleFrontierIndex.mkFromStmtIdx i.castSucc) stmtOStmtIn.2
      stmtOStmtIn.1.challenges := by
  classical
  unfold incrementalBadEventExistsProp at h_bad_after ⊢
  rcases h_bad_after with ⟨j, hj⟩
  by_cases h_old : j.val + 1 < toOutCodewordsCount ℓ ϑ i.castSucc
  · refine ⟨j, ?_⟩
    have hj_copy := hj
    dsimp at hj_copy ⊢
    have h_k_full : j.val * ϑ + ϑ ≤ i.val := by
      exact oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ) (i := i.castSucc) (j := j) (hj := h_old)
    have hk_after : min ϑ (i.val + 1 - j.val * ϑ) = ϑ := by
      omega
    have hk_before : min ϑ (i.val - j.val * ϑ) = ϑ := by
      omega
    let afterSlice : Fin ϑ → L := fun cId =>
      foldOrderChallenges (ℓ := ℓ) (i := i.succ)
        (Fin.cons (α := fun _ => L) r_i' stmtOStmtIn.1.challenges)
        ⟨j.val * ϑ + cId.val, by
          have h_idx_lt : j.val * ϑ + cId.val < i.val := by
            exact lt_of_lt_of_le (Nat.add_lt_add_left cId.isLt (j.val * ϑ)) h_k_full
          exact lt_trans h_idx_lt (Nat.lt_succ_self i.val)⟩
    let beforeSlice : Fin ϑ → L := fun cId =>
      foldOrderChallenges (ℓ := ℓ) (i := i.castSucc) stmtOStmtIn.1.challenges
        ⟨j.val * ϑ + cId.val, by
          exact lt_of_lt_of_le (Nat.add_lt_add_left cId.isLt (j.val * ϑ)) h_k_full⟩
    have h_challenges : afterSlice = beforeSlice := by
      funext cId
      have hlt : j.val * ϑ + cId.val < i.val :=
        lt_of_lt_of_le (Nat.add_lt_add_left cId.isLt (j.val * ϑ)) h_k_full
      exact foldOrderChallenges_cons_of_lt (ℓ := ℓ) i stmtOStmtIn.1.challenges r_i'
        ⟨j.val * ϑ + cId.val, hlt⟩
    let blockStart : Fin r := ⟨j.val * ϑ, by
      exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (oraclePositionToDomainIndex (ℓ := ℓ) (ϑ := ϑ) j).isLt⟩
    let blockDest : Fin r := ⟨j.val * ϑ + ϑ, by
      exact lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j))⟩
    have hj_after_full :
        incrementalFoldingBadEvent 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (block_start_idx := blockStart)
          (k := ϑ)
          (h_k_le := le_rfl)
          (midIdx := blockDest)
          (destIdx := blockDest)
          (h_midIdx := rfl)
          (h_destIdx := rfl)
          (h_destIdx_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j))
          (f_block_start := stmtOStmtIn.2 j)
          (r_challenges := afterSlice) := by
      convert hj_copy using 1
      · apply Fin.eq_of_val_eq
        dsimp [blockDest]
        omega
      · exact hk_after.symm
      · have h_afterSlice_heq :
            HEq
              (fun cId : Fin (min ϑ (i.val + 1 - j.val * ϑ)) =>
                foldOrderChallenges (ℓ := ℓ) (i := i.succ)
                  (Fin.cons (α := fun _ => L) r_i' stmtOStmtIn.1.challenges)
                  ⟨j.val * ϑ + cId.val, by
                    have h_cId_lt :
                        cId.val < i.val + 1 - j.val * ϑ := by
                      exact lt_of_lt_of_le cId.isLt (Nat.min_le_right ϑ _)
                    have h_block_le : j.val * ϑ ≤ i.val + 1 := by
                      omega
                    calc
                      j.val * ϑ + cId.val < j.val * ϑ + (i.val + 1 - j.val * ϑ) :=
                        Nat.add_lt_add_left h_cId_lt (j.val * ϑ)
                      _ = i.val + 1 := Nat.add_sub_of_le h_block_le⟩)
              afterSlice := by
          apply fin_fun_heq_of_cast hk_after
          intro cId
          dsimp [afterSlice]
        exact HEq.symm h_afterSlice_heq
    have h_bad_after_full :
        foldingBadEvent 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := blockStart)
          (destIdx := blockDest)
          (steps := ϑ)
          (h_destIdx := rfl)
          (h_destIdx_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j))
          (f_i := stmtOStmtIn.2 j)
          (r_challenges := afterSlice) := by
      exact
        (incrementalFoldingBadEvent_eq_foldingBadEvent_of_k_eq_ϑ
          (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (ϑ := ϑ)
          (block_start_idx := blockStart)
          (midIdx := blockDest)
          (destIdx := blockDest)
          (h_midIdx := by rfl)
          (h_destIdx := rfl)
          (h_destIdx_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j))
          (f_block_start := stmtOStmtIn.2 j)
          (r_challenges := afterSlice)).1 hj_after_full
    have h_bad_before_full := h_bad_after_full
    rw [h_challenges] at h_bad_before_full
    have hj_before_full :
        incrementalFoldingBadEvent 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (block_start_idx := blockStart)
          (k := ϑ)
          (h_k_le := le_rfl)
          (midIdx := blockDest)
          (destIdx := blockDest)
          (h_midIdx := rfl)
          (h_destIdx := rfl)
          (h_destIdx_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j))
          (f_block_start := stmtOStmtIn.2 j)
          (r_challenges := beforeSlice) := by
      exact
        (incrementalFoldingBadEvent_eq_foldingBadEvent_of_k_eq_ϑ
          (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (ϑ := ϑ)
          (block_start_idx := blockStart)
          (midIdx := blockDest)
          (destIdx := blockDest)
          (h_midIdx := by rfl)
          (h_destIdx := rfl)
          (h_destIdx_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j))
          (f_block_start := stmtOStmtIn.2 j)
          (r_challenges := beforeSlice)).2 h_bad_before_full
    convert hj_before_full using 1
    · apply Fin.eq_of_val_eq
      dsimp [blockDest]
      omega
    · have h_beforeSlice_heq :
          HEq
            (fun cId : Fin (min ϑ (i.val - j.val * ϑ)) =>
              foldOrderChallenges (ℓ := ℓ) (i := i.castSucc) stmtOStmtIn.1.challenges
                ⟨j.val * ϑ + cId.val, by
                  have h_cId_lt :
                      cId.val < i.val - j.val * ϑ := by
                    exact lt_of_lt_of_le cId.isLt (Nat.min_le_right ϑ _)
                  have h_block_le : j.val * ϑ ≤ i.val := by
                    exact le_trans (by omega) h_k_full
                  calc
                    j.val * ϑ + cId.val < j.val * ϑ + (i.val - j.val * ϑ) :=
                      Nat.add_lt_add_left h_cId_lt (j.val * ϑ)
                    _ = i.val := Nat.add_sub_of_le h_block_le⟩)
            beforeSlice := by
        apply fin_fun_heq_of_cast hk_before
        intro cId
        dsimp [beforeSlice]
      exact h_beforeSlice_heq
  · refine ⟨j, ?_⟩
    have hj_copy := hj
    dsimp at hj_copy ⊢
    have h_j_last : j = getLastOraclePositionIndex ℓ ϑ i.castSucc := by
      apply Fin.eq_of_val_eq
      have hj_lt : j.val < toOutCodewordsCount ℓ ϑ i.castSucc := by
        have hj_lt' := j.isLt
        simp only [OracleFrontierIndex.val_mkFromStmtIdxCastSuccOfSucc] at hj_lt'
        exact hj_lt'
      have h_val : j.val = toOutCodewordsCount ℓ ϑ i.castSucc - 1 := by
        have h_ge : toOutCodewordsCount ℓ ϑ i.castSucc ≤ j.val + 1 := by
          omega
        omega
      dsimp [getLastOraclePositionIndex]
      exact h_val
    subst j
    dsimp [foldStepFreshDoomPreservationEvent] at h_not_fresh
    have h_j_val : (getLastOraclePositionIndex ℓ ϑ i.castSucc).val = i.val / ϑ := by
      dsimp only [getLastOraclePositionIndex]
      unfold toOutCodewordsCount
      simp only [Fin.val_castSucc, i.isLt, ↓reduceIte, add_tsub_cancel_right]
    have h_diff_lt :
        i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ < ϑ := by
      rw [h_j_val, Nat.mul_comm, ← Nat.mod_eq_sub_mul_div]
      exact Nat.mod_lt i.val (Nat.pos_of_neZero ϑ)
    have h_diff_eq :
        i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ = i.val % ϑ := by
      rw [h_j_val, Nat.mul_comm, ← Nat.mod_eq_sub_mul_div]
    have h_last_le :
        (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ ≤ i.val := by
      rw [h_j_val, Nat.mul_comm]
      have h_div := Nat.div_mul_le_self i.val ϑ
      rw [Nat.mul_comm] at h_div
      exact h_div
    have hk_after_last :
        min ϑ (i.val + 1 - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ) =
          min ϑ (i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ) + 1 := by
      rw [show i.val + 1 - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ =
          (i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ) + 1 by
            omega]
      rw [h_diff_eq]
      have h_mod_lt : i.val % ϑ < ϑ := by
        exact Nat.mod_lt i.val (Nat.pos_of_neZero ϑ)
      omega
    let kBefore : ℕ := min ϑ (i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ)
    let prefixSlice : Fin kBefore → L := fun cId =>
      foldOrderChallenges (ℓ := ℓ) (i := i.castSucc) stmtOStmtIn.1.challenges
        ⟨(getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + cId.val, by
          have h_min_le :
              kBefore ≤ i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ := by
            dsimp [kBefore]
            exact Nat.min_le_right ϑ _
          have h_cId_lt :
              cId.val < i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ := by
            exact lt_of_lt_of_le cId.isLt h_min_le
          have h_idx_lt :
              (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + cId.val < i.val := by
            omega
          exact h_idx_lt⟩
    let afterSlice : Fin (kBefore + 1) → L := fun cId =>
      foldOrderChallenges (ℓ := ℓ) (i := i.succ)
        (Fin.cons (α := fun _ => L) r_i' stmtOStmtIn.1.challenges)
        ⟨(getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + cId.val, by
          have h_cId_le : cId.val ≤ kBefore := by
            exact Nat.lt_succ_iff.mp cId.isLt
          have h_idx_le :
              (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + cId.val ≤ i.val := by
            dsimp [kBefore] at h_cId_le
            have h_min_le :
                min ϑ (i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ) ≤
                  i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ :=
              Nat.min_le_right ϑ _
            omega
          exact lt_of_le_of_lt h_idx_le (Nat.lt_succ_self i.val)⟩
    let freshSlice : Fin (kBefore + 1) → L := Fin.snoc (α := fun _ => L) prefixSlice r_i'
    have h_after_challenges : afterSlice = freshSlice := by
      funext cId
      induction cId using Fin.lastCases with
      | cast jc =>
        have h_lt : jc.val < kBefore := jc.isLt
        have h_min : kBefore ≤ i.val - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ :=
          Nat.min_le_right _ _
        have h_idx_lt :
            (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + jc.val < i.val := by omega
        simp only [afterSlice, freshSlice, prefixSlice, Fin.snoc_castSucc, Fin.coe_castSucc]
        exact foldOrderChallenges_cons_of_lt (ℓ := ℓ) i stmtOStmtIn.1.challenges r_i'
          ⟨(getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + jc.val, h_idx_lt⟩
      | last =>
        have h_idx_eq :
            (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + (Fin.last kBefore).val = i.val := by
          dsimp [kBefore]
          omega
        have h1 : afterSlice (Fin.last kBefore) = r_i' := by
          have hidx : afterSlice (Fin.last kBefore) =
              foldOrderChallenges (ℓ := ℓ) (i := i.succ)
                (Fin.cons (α := fun _ => L) r_i' stmtOStmtIn.1.challenges) (Fin.last i.val) := by
            simp only [afterSlice]
            congr 1
            exact Fin.eq_of_val_eq h_idx_eq
          rw [hidx]
          exact foldOrderChallenges_cons_last (ℓ := ℓ) i stmtOStmtIn.1.challenges r_i'
        have h2 : freshSlice (Fin.last kBefore) = r_i' :=
          Fin.snoc_last (α := fun _ => L) (x := r_i') (p := prefixSlice)
        rw [h1, h2]
    let blockStart : Fin r := ⟨(getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ, by
      exact lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (Nat.le_of_lt (lt_of_le_of_lt h_last_le i.isLt))⟩
    let blockMidAfter : Fin r :=
      ⟨(getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + (kBefore + 1), by
        apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        dsimp [kBefore]
        omega⟩
    let blockDest : Fin r := ⟨(getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + ϑ, by
      exact lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc)
          (j := getLastOraclePositionIndex ℓ ϑ i.castSucc))⟩
    have h_after_last_afterSlice :
        incrementalFoldingBadEvent 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (block_start_idx := blockStart)
          (k := kBefore + 1)
          (h_k_le := by
            dsimp [kBefore]
            omega)
          (midIdx := blockMidAfter)
          (destIdx := blockDest)
          (h_midIdx := rfl)
          (h_destIdx := rfl)
          (h_destIdx_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc)
            (j := getLastOraclePositionIndex ℓ ϑ i.castSucc))
          (f_block_start := stmtOStmtIn.2 (getLastOraclePositionIndex ℓ ϑ i.castSucc))
          (r_challenges := afterSlice) := by
      convert hj_copy using 1
      · apply Fin.eq_of_val_eq
        dsimp [blockStart, blockMidAfter, kBefore]
        omega
      · dsimp [kBefore]
        omega
      · have h_afterSlice_heq :
            HEq
              (fun cId : Fin
                  (min ϑ (i.val + 1 - (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ)) =>
                foldOrderChallenges (ℓ := ℓ) (i := i.succ)
                  (Fin.cons (α := fun _ => L) r_i' stmtOStmtIn.1.challenges)
                  ⟨(getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + cId.val, by
                    have h_cId_lt :
                        cId.val <
                          i.val + 1 -
                            (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ := by
                      exact lt_of_lt_of_le cId.isLt (Nat.min_le_right ϑ _)
                    have h_block_le :
                        (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ ≤ i.val + 1 := by
                      omega
                    calc
                      (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ + cId.val <
                          (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ +
                            (i.val + 1 -
                              (getLastOraclePositionIndex ℓ ϑ i.castSucc).val * ϑ) :=
                        Nat.add_lt_add_left h_cId_lt _
                      _ = i.val + 1 := Nat.add_sub_of_le h_block_le⟩)
              afterSlice := by
          apply fin_fun_heq_of_cast hk_after_last
          intro cId
          dsimp [afterSlice]
        exact HEq.symm h_afterSlice_heq
    have h_after_last' := h_after_last_afterSlice
    rw [h_after_challenges] at h_after_last'
    by_contra h_before_false
    exact h_not_fresh ⟨h_before_false, h_after_last'⟩
lemma foldStep_rbrExtractionFailureEvent_imply_sumcheck_or_badEvent (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) (r_i' : L)
    (doomEscape : rbrExtractionFailureEvent
      (kSF := foldKnowledgeStateFunction (mp := mp) (𝓑 := 𝓑) (init := init)
        (impl := impl) (σ := σ) 𝔽q β i)
      (extractor := foldRbrExtractor (mp := mp) 𝔽q β i) (i := ⟨1, rfl⟩) (stmtIn := stmtOStmtIn)
    (transcript := FullTranscript.mk1 h_i) (challenge := r_i')) :
    let incrementalFoldingBadEvent :=
      foldStepFreshDoomPreservationEvent 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn r_i'
    incrementalFoldingBadEvent ∨ (
      ¬incrementalFoldingBadEvent ∧
      (∃ witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ,
        (foldStepWitMidOracleConsistency (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
          (i := i) stmtOStmtIn h_i r_i' witMid)
        ∧ (badSumcheckEventProp r_i' h_i
            (foldStepHStarFromWitMid (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (𝓑 := 𝓑) i stmtOStmtIn h_i r_i' witMid))
      )
    ) := by
  classical
  let incrementalFoldingBadEvent : Prop :=
    foldStepFreshDoomPreservationEvent 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn r_i'
  unfold rbrExtractionFailureEvent at doomEscape
  rcases doomEscape with ⟨witMid, h_kState_before_false, h_kState_after_true⟩
  simp only [foldKnowledgeStateFunction] at h_kState_before_false h_kState_after_true
  unfold foldKStateProp at h_kState_before_false h_kState_after_true
  simp only [Fin.isValue, Fin.castSucc_one, Fin.succ_one_eq_two, Nat.reduceAdd,
    Transcript.concat] at h_kState_before_false h_kState_after_true
  by_cases h_bad : incrementalFoldingBadEvent
  · left
    exact h_bad
  · right
    refine ⟨h_bad, ?_⟩
    -- Under ¬ fresh bad-event, the m=2 KState cannot be on the bad branch.
    have h_after_good_exists : ∃ h_after_good, h_kState_after_true = Or.inr h_after_good := by
      cases h_kState_after_true with
      | inl h_bad_after =>
        exfalso
        have h_bad_before : incrementalBadEventExistsProp 𝔽q β i.castSucc
          (OracleFrontierIndex.mkFromStmtIdx i.castSucc) stmtOStmtIn.2
          stmtOStmtIn.1.challenges :=
          incrementalBadEventExistsProp_fold_step_backward 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
            i stmtOStmtIn r_i' h_bad_after h_bad
        exact h_kState_before_false (Or.inl h_bad_before)
      | inr h_after_good =>
        exact ⟨h_after_good, rfl⟩
    rcases h_after_good_exists with ⟨h_after_good, rfl⟩
    have h_explicit_after :
        h_i.val.eval (𝓑 0) + h_i.val.eval (𝓑 1) = stmtOStmtIn.1.sumcheck_target := by
      exact h_after_good.1.1
    have h_sumcheck_after :
        sumcheckConsistencyProp (𝓑 := 𝓑) (Polynomial.eval r_i' h_i.val) witMid.H := by
      exact h_after_good.1.2
    have h_consistency : foldStepWitMidOracleConsistency 𝔽q β i stmtOStmtIn h_i r_i' witMid :=
      ⟨h_after_good.2.1, h_after_good.2.2.2.1⟩
    have h_left_from_consistency :
        badSumcheckEventProp r_i' h_i
          (foldStepHStarFromWitMid (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (𝓑 := 𝓑) i stmtOStmtIn h_i r_i' witMid) := by
      have h_wit_struct_after :
          witMid.H = projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := witMid.t)
            (m := mp.multpoly stmtOStmtIn.1.ctx) (i := i.succ)
            (challenges := Fin.cons (α := fun _ => L) r_i' stmtOStmtIn.1.challenges) := by
        exact h_consistency.1.1
      let H_before : L⦃≤ 2⦄[X Fin (ℓ - i.castSucc)] :=
        projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := witMid.t)
          (m := mp.multpoly stmtOStmtIn.1.ctx) (i := i.castSucc)
          (challenges := stmtOStmtIn.1.challenges)
      let h_star_extracted : L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ (SumcheckDomain.uniform 𝓑 ℓ) (i := i) (h := H_before)
      have h_eval_eq_extracted :
          Polynomial.eval r_i' h_i.val = Polynomial.eval r_i' h_star_extracted.val := by
        unfold sumcheckConsistencyProp at h_sumcheck_after
        rw [h_wit_struct_after] at h_sumcheck_after
        erw [← Sumcheck.Structured.projectToNextSumcheckPoly_eq_projectToMidSumcheckPoly_succ
          ℓ witMid.t (mp.multpoly stmtOStmtIn.1.ctx) i stmtOStmtIn.1.challenges r_i']
          at h_sumcheck_after
        have h_sum_eq :=
          Sumcheck.Structured.projectToNextSumcheckPoly_sum_eq (L := L) (𝓑 := 𝓑) (ℓ := ℓ)
            (i := i) (Hᵢ := H_before) (rᵢ := r_i')
        have h_sum_eq' :
            Polynomial.eval r_i' h_star_extracted.val =
              ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - i.succ),
                (projectToNextSumcheckPoly (L := L) (ℓ := ℓ) (i := i)
                  (Hᵢ := H_before) (rᵢ := r_i')).val.eval x := by
          have h_sum_eq' := h_sum_eq
          dsimp only [h_star_extracted] at h_sum_eq' ⊢
          exact h_sum_eq'
        calc
          Polynomial.eval r_i' h_i.val
              = ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - i.succ),
                  (projectToNextSumcheckPoly (L := L) (ℓ := ℓ) (i := i)
                    (Hᵢ := H_before) (rᵢ := r_i')).val.eval x := h_sumcheck_after
          _ = Polynomial.eval r_i' h_star_extracted.val := by
            symm
            exact h_sum_eq'
      have h_hi_ne_extracted : h_i ≠ h_star_extracted := by
        intro h_eq
        apply h_kState_before_false
        right
        -- Or-outer `before` state: `localChecks_before ∧ oracleWitnessConsistency_before`, where
        -- `oracleWitnessConsistency = structural ∧ sumcheck ∧ firstOracle ∧ folding`.
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · constructor
          · exact h_explicit_after
          · have h_eq' := h_eq
            simp only [h_star_extracted, H_before, foldRbrExtractor, Fin.isValue] at h_eq' ⊢
            exact h_eq'
        · unfold witnessStructuralInvariant
          simp only [Fin.val_castSucc, foldRbrExtractor, Fin.zero_eta, Fin.isValue,
            Fin.succ_zero_eq_one, Fin.mk_one, Fin.succ_one_eq_two,
            Fin.coe_ofNat_eq_mod, Nat.reduceMod, and_self]
        · -- sumcheck consistency of the extracted before-witness: its round polynomial is `h_i`
          -- (via `h_eq`), and the verifier's explicit check gives its boolean-cube sum.
          show sumcheckConsistencyProp (𝓑 := 𝓑) _ _
          simp only [foldRbrExtractor, Fin.isValue]
          unfold sumcheckConsistencyProp
          rw [← h_explicit_after]
          have h_eq' := h_eq
          simp only [h_star_extracted, H_before, foldRbrExtractor, Fin.isValue] at h_eq'
          rw [h_eq']
          exact Sumcheck.Structured.getSumcheckRoundPoly_sum_eq (𝓑 := 𝓑) (i := i) (h := H_before)
        · exact h_consistency.2
        · have h_folding_after := h_after_good.2.2.2.2
          unfold oracleFoldingConsistencyProp at h_folding_after ⊢
          intro j hj
          have h_fold_j := h_folding_after j hj
          unfold isCompliant at h_fold_j ⊢
          rcases h_fold_j with ⟨h_fw_close, h_next_close, h_iter⟩
          refine ⟨h_fw_close, h_next_close, ?_⟩
          -- The after-state folding consistency uses `olderStmtChallenges` of the cons'd output
          -- statement; dropping the fresh head recovers `stmtOStmtIn.1.challenges`, which is exactly
          -- what the before-state (self-restricted) folding consistency uses. So the folded
          -- challenge slices — hence the iterated folds — coincide.
          simp only [OracleFrontierIndex.val_mkFromStmtIdxCastSuccOfSucc,
            OracleFrontierIndex.val_mkFromStmtIdx,
            olderStmtChallenges_cons_castSucc, olderStmtChallenges_self] at h_iter ⊢
          exact h_iter
      change badSumcheckEventProp r_i' h_i h_star_extracted
      exact ⟨h_hi_ne_extracted, h_eval_eq_extracted⟩
    exact ⟨witMid, h_consistency, h_left_from_consistency⟩

/-! Per-transcript bound: for the first prover message `msg0`, the probability (over the verifier
  challenge `y`) that extraction fails is at most `foldKnowledgeError`. Stated for
  `P (FullTranscript.mk1 msg0)` so it matches the goal after `tsum_uniform_Pr_eq_Pr` in the main
  soundness proof.
  **Proof strategy:**
  1. **Implication**: Show that extraction failure `P(tr, y)` implies either
    - a SINGLE sumcheck “bad” event
    - or an incremental folding bad event (bad oracle / consistency failure)
  2. **Monotonicity**: Conclude `Pr[P] ≤ Pr[SZ ∨ BE]` via `prob_mono`.
  3. **Union bound**: Apply `Pr_or_le` to get `Pr[SZ ∨ BE] ≤ Pr[SZ] + Pr[BE]`.
  4. **Schwartz–Zippel**: Bound `Pr[SZ]` by `1/|L|` using univariate degree-1
    agreement (lemmas from Instances.lean)
  5. **Bad event**: Bound `Pr[BE]` using the incremental folding bad-event probability
    (`prop_4_21_2_incremental_bad_event_probability`).
  6. **Combine**: Add the two bounds and match the RHS to `foldKnowledgeError`. -/
lemma foldStep_doom_escape_probability_bound (i : Fin ℓ)
    (stmtOStmtIn : (Statement (L := L) Context i.castSucc) × (∀ j,
      OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j))
    (h_i : (pSpecFold (L := L)).Message ⟨0, rfl⟩) :
    Pr_{ let y ← $ᵖ L }[
      rbrExtractionFailureEvent
        (kSF := foldKnowledgeStateFunction (mp := mp) (𝓑 := 𝓑)
          (init := init) (impl := impl) (σ := σ) 𝔽q β i)
        (extractor := foldRbrExtractor (mp := mp) 𝔽q β i) ⟨1, rfl⟩
          stmtOStmtIn (FullTranscript.mk1 h_i) y ] ≤
      foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i ⟨1, by rfl⟩ := by
  classical
  let doomEvent := fun y : L =>
    rbrExtractionFailureEvent
      (kSF := foldKnowledgeStateFunction (mp := mp) (𝓑 := 𝓑)
        (init := init) (impl := impl) (σ := σ) 𝔽q β i)
      (extractor := foldRbrExtractor (mp := mp) 𝔽q β i) ⟨1, rfl⟩
      stmtOStmtIn (FullTranscript.mk1 h_i) y
  let sumcheckBadEvent : L → Prop := fun y =>
    let incrementalFoldingBadEvent :=
      foldStepFreshDoomPreservationEvent 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn y
    (¬incrementalFoldingBadEvent ∧
        (∃ witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ,
        (foldStepWitMidOracleConsistency (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
          (i := i) stmtOStmtIn h_i y witMid)
        ∧ (badSumcheckEventProp y h_i
            (foldStepHStarFromWitMid (mp := mp) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (𝓑 := 𝓑) i stmtOStmtIn h_i y witMid))
      ))
  let incrementalBadFoldEvent := fun y : L =>
    foldStepFreshDoomPreservationEvent 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn y
  let incrementalBadFoldEvent_or_sumcheckBadEvent := fun y : L =>
    (incrementalBadFoldEvent y) ∨ (sumcheckBadEvent y)
  have h_prob_mono := PrUnion.Pr_mono ($ᵖ L)
    doomEvent incrementalBadFoldEvent_or_sumcheckBadEvent
    (by
      intro y h_doomEscape
      have h_imp := (foldStep_rbrExtractionFailureEvent_imply_sumcheck_or_badEvent
          (mp := mp) (𝓑 := 𝓑) (init := init) (impl := impl) 𝔽q β
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) (stmtOStmtIn := stmtOStmtIn) (h_i := h_i)
          (r_i' := y) (doomEscape := h_doomEscape))
      dsimp only [incrementalBadFoldEvent_or_sumcheckBadEvent, sumcheckBadEvent,
        incrementalBadFoldEvent]
      by_cases h_bad : foldStepFreshDoomPreservationEvent 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i stmtOStmtIn y
      · exact Or.inl h_bad
      · cases h_imp with
        | inl h_bad' => exact False.elim (h_bad h_bad')
        | inr h_sum => exact Or.inr h_sum
    )
  refine le_trans h_prob_mono ?_
  dsimp only [incrementalBadFoldEvent_or_sumcheckBadEvent, foldKnowledgeError]
  apply le_trans
      (PrUnion.Pr_or_le ($ᵖ L) incrementalBadFoldEvent sumcheckBadEvent)
  conv_rhs => simp only [ENNReal.coe_add]; rw [add_comm]
  apply add_le_add
  · dsimp only [incrementalBadFoldEvent, foldStepFreshDoomPreservationEvent]
    let stmtIdxBefore : Fin (ℓ + 1) := i.castSucc
    let challengesBefore : Fin stmtIdxBefore → L := stmtOStmtIn.1.challenges
    let j := getLastOraclePositionIndex ℓ ϑ i.castSucc
    let curOracleDomainIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j), by omega⟩
    let kBefore : ℕ := min ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)
    have h_j_val : j.val = i.val / ϑ := by
      have h_i_lt_ℓ : i.val < ℓ := i.isLt
      have h_i_cast_lt_ℓ : i.val < ℓ := by
        simp only [h_i_lt_ℓ]
      dsimp only [j, getLastOraclePositionIndex]
      unfold toOutCodewordsCount
      simp only [Fin.val_castSucc, h_i_lt_ℓ, ↓reduceIte, add_tsub_cancel_right]
    have h_cur_eq : curOracleDomainIdx.val = (i.val / ϑ) * ϑ := by
      dsimp only [curOracleDomainIdx, oraclePositionToDomainIndex]
      simp only [h_j_val]
    have h_diff_lt : stmtIdxBefore.val - curOracleDomainIdx.val < ϑ := by
      have h_div_mod : (i.val / ϑ) * ϑ + i.val % ϑ = i.val := by
        rw [Nat.mul_comm]
        exact Nat.div_add_mod i.val ϑ
      have h_cur_le : curOracleDomainIdx.val ≤ stmtIdxBefore.val := by
        dsimp only [stmtIdxBefore]
        calc
          curOracleDomainIdx.val = (i.val / ϑ) * ϑ := h_cur_eq
          _ ≤ i.val := Nat.div_mul_le_self i.val ϑ
      have h_sum : curOracleDomainIdx.val + i.val % ϑ = stmtIdxBefore.val := by
        dsimp only [stmtIdxBefore]
        calc
          curOracleDomainIdx.val + i.val % ϑ = (i.val / ϑ) * ϑ + i.val % ϑ := by
            simp only [h_cur_eq]
          _ = i.val := h_div_mod
      have h_diff_eq : stmtIdxBefore.val - curOracleDomainIdx.val = i.val % ϑ := by omega
      rw [h_diff_eq]
      exact Nat.mod_lt i.val (Nat.pos_of_neZero ϑ)
    have h_kBefore_lt : kBefore < ϑ := by
      exact lt_of_le_of_lt
        (Nat.min_le_right ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)) h_diff_lt
    let destIdx : Fin r := ⟨curOracleDomainIdx.val + ϑ, by
      have h1 := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)
      have h2 : ℓ + 𝓡 < r := h_ℓ_add_R_rate
      have _ : 𝓡 > 0 := Nat.pos_of_neZero 𝓡
      dsimp only [oraclePositionToDomainIndex, curOracleDomainIdx]
      omega
    ⟩
    let r_prefix : Fin kBefore → L := fun cId =>
      foldOrderChallenges (ℓ := ℓ) (i := stmtIdxBefore) challengesBefore
      ⟨curOracleDomainIdx.val + cId.val, by
        have h_k_le_stmt : kBefore ≤ stmtIdxBefore.val - curOracleDomainIdx.val :=
          Nat.min_le_right ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)
        have h_cId_lt_k : cId.val < kBefore := cId.isLt
        omega
      ⟩
    have h_res := prop_4_21_2_incremental_bad_event_probability 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (block_start_idx := curOracleDomainIdx)
      (midIdx_i := ⟨curOracleDomainIdx.val + kBefore, by
        apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        have h_k_le : kBefore ≤ ϑ := Nat.min_le_left ϑ (stmtIdxBefore.val - curOracleDomainIdx.val)
        have h_add_le : curOracleDomainIdx.val + ϑ ≤ ℓ :=
          oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)
        omega
      ⟩)
      (midIdx_i_succ := ⟨curOracleDomainIdx.val + kBefore + 1, by
        apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        have h_k_le : kBefore + 1 ≤ ϑ := Nat.succ_le_of_lt h_kBefore_lt
        have h_add_le : curOracleDomainIdx.val + ϑ ≤ ℓ :=
          oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j)
        omega
      ⟩)
      (destIdx := destIdx) (k := kBefore)
        (h_k_lt := h_kBefore_lt)
        (h_midIdx_i := by simp only)
        (h_midIdx_i_succ := by simp only)
        (h_destIdx := rfl)
      (h_destIdx_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i.castSucc) (j := j))
        (f_block_start := stmtOStmtIn.2 j)
      (r_prefix := r_prefix)
    dsimp only [destIdx, curOracleDomainIdx, j, kBefore, r_prefix, stmtIdxBefore, challengesBefore]
      at h_res
    have h_cur_le_stmt : curOracleDomainIdx.val ≤ stmtIdxBefore.val := by
      dsimp only [stmtIdxBefore]
      calc
        curOracleDomainIdx.val = (i.val / ϑ) * ϑ := h_cur_eq
        _ ≤ i.val := Nat.div_mul_le_self i.val ϑ
    have h_kBefore_eq : kBefore = stmtIdxBefore.val - curOracleDomainIdx.val := by
      dsimp only [kBefore]
      exact Nat.min_eq_right (Nat.le_of_lt h_diff_lt)
    have h_kAfter_eq : min ϑ (i.succ.val - curOracleDomainIdx.val) = kBefore + 1 := by
      have h_cur_le_i : curOracleDomainIdx.val ≤ i.val := by
        have h_cur_le_i' := h_cur_le_stmt
        simp only [stmtIdxBefore] at h_cur_le_i'
        exact h_cur_le_i'
      have h_sub_succ : i.val + 1 - curOracleDomainIdx.val
        = (i.val - curOracleDomainIdx.val) + 1 := by
        have h_sub_succ' := Nat.succ_sub h_cur_le_i
        rw [Nat.succ_eq_add_one] at h_sub_succ'
        exact h_sub_succ'
      have h_kBefore_eq' : kBefore = i.val - curOracleDomainIdx.val := by
        have h_kBefore_eq'' := h_kBefore_eq
        simp only [stmtIdxBefore] at h_kBefore_eq''
        exact h_kBefore_eq''
      simp only [Fin.val_succ]
      rw [h_sub_succ, ← h_kBefore_eq']
      exact Nat.min_eq_right (Nat.succ_le_of_lt h_kBefore_lt)
    conv_rhs => simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true,
      ENNReal.coe_div, ENNReal.coe_natCast]
    exact h_res
  · dsimp only [sumcheckBadEvent]
    -- Strategy: ignore the `foldStepFreshDoomPreservationEvent`, plus `oracleWitnessConsistency`
      -- guarantees uniqueness of witMid, then we can transform this to prove the bound via
        -- `probability_bound_badSumcheckEventProp`
    let compatPred : MultilinearPoly L ℓ → Prop := fun t =>
      firstOracleWitnessConsistencyProp 𝔽q β t (getFirstOracle 𝔽q β stmtOStmtIn.2)
    by_cases hCompat : ∃ t : MultilinearPoly L ℓ, compatPred t
    · rcases hCompat with ⟨t_fixed, h_t_fixed_compat⟩
      let H_fixed : L⦃≤ 2⦄[X Fin (ℓ - i.castSucc)] :=
        projectToMidSumcheckPoly (L := L) (ℓ := ℓ) (t := t_fixed)
          (m := mp.multpoly stmtOStmtIn.1.ctx)
          (i := i.castSucc) (challenges := stmtOStmtIn.1.challenges)
      let h_star_fixed : L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ (SumcheckDomain.uniform 𝓑 ℓ) (i := i) (h := H_fixed)
      have h_prob_mono_sum := PrUnion.Pr_mono ($ᵖ L)
        (fun y => sumcheckBadEvent y)
        (fun y => badSumcheckEventProp y h_i h_star_fixed)
        (by
          intro y h_sum
          rcases h_sum with ⟨_h_not_fresh, witMid, h_cons, h_bad⟩
          have h_t_eq : witMid.t = t_fixed :=
            firstOracleWitnessConsistency_unique 𝔽q β
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) (i := i)
              (oStmt := stmtOStmtIn.2) (h₁ := h_cons.2) (h₂ := h_t_fixed_compat)
          have h_bad' := h_bad
          simp only [h_star_fixed, H_fixed, foldStepHStarFromWitMid,
            foldStepWitBeforeFromWitMid, foldRbrExtractor, Fin.isValue, h_t_eq] at h_bad' ⊢
          exact h_bad'
        )
      refine le_trans h_prob_mono_sum ?_
      have h_sz := probability_bound_badSumcheckEventProp (h_i := h_i) (h_star := h_star_fixed)
      conv_rhs =>
        rw [ENNReal.coe_div (hr := by
          simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true])]
        simp only [ENNReal.coe_ofNat, ENNReal.coe_natCast]
      exact h_sz
    · have h_prob_mono_false := PrUnion.Pr_mono ($ᵖ L)
        (fun y => sumcheckBadEvent y)
        (fun _ => False)
        (by
          intro y h_sum
          rcases h_sum with ⟨_h_not_fresh, witMid, h_cons, _h_bad⟩
          exact (hCompat ⟨witMid.t, h_cons.2⟩).elim
        )
      refine le_trans h_prob_mono_false ?_
      simp only [PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind, PMF.bind_const, PMF.pure_apply,
        eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte, _root_.zero_le]

/-! RBR knowledge soundness for a single round oracle verifier. -/
axiom foldOracleVerifier_rbrKnowledgeSoundness (i : Fin ℓ) :
    (foldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (mp := mp) i).rbrKnowledgeSoundness init impl
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)  i.castSucc)
      (relOut := foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)  i)
      (foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)

end FoldStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold.CoreInteraction
