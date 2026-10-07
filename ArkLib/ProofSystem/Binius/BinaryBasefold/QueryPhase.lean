/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase.Folding
import ArkLib.ProofSystem.Binius.BinaryBasefold.FinalRelation

/-!
# Binary Basefold query completeness and knowledge soundness

The verifier and its folding lemmas are defined in `QueryPhase.Folding`.
This module proves completeness and the query-phase knowledge-soundness bound.
-/

set_option linter.style.longFile 2100

namespace Binius.BinaryBasefold.QueryPhase

noncomputable section
open OracleSpec OracleComp
open AdditiveNTT Polynomial MvPolynomial ProtocolSpec
open Binius.BinaryBasefold.CoreInteraction

open scoped ProbabilityTheory NNReal

/-- Uniform function sampling gives the product probability of the coordinate event. -/
private lemma uniform_forall_fin_probability {A : Type} [Fintype A] [Nonempty A]
    (n : ℕ) (P : A → Prop) :
    Pr_{ let f ← $ᵖ (Fin n → A) }[ ∀ i, P (f i) ] =
      (Pr_{ let x ← $ᵖ A }[ P x ]) ^ n := by
  classical
  have hcard : (Finset.univ.filter (fun f : Fin n → A => ∀ i, P (f i))).card =
      (Finset.univ.filter P).card ^ n := by
    calc
      _ = (Fintype.piFinset (fun _ : Fin n => Finset.univ.filter P)).card := by
        congr 1
        ext f
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
      _ = _ := by simp only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [prob_uniform_eq_card_filter_div_card, hcard, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow, ENNReal.coe_pow]
  simp only [div_eq_mul_inv, mul_pow, ENNReal.inv_pow]

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

/-- Relation used in the forIn loop of `checkSingleRepetition`: at index 0 the folded value is 0;
  at index `oraclePositionIdx > 0` it equals `iterated_fold` up to that position with challenges
    from `stmtIn` and suffix from `v`. -/
@[reducible]
def checkSingleRepetition_foldRel
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩) :
    Fin ((List.finRange (ℓ / ϑ)).length + 1) → L → Prop :=
  let f₀ := getFirstOracle 𝔽q β oStmtIn
  fun oraclePositionIdx val_folded_point =>
    if hk : oraclePositionIdx.val = 0 then
      val_folded_point = 0  -- Base case: initial value is 0
    else
      have h_toCodewordCount : toOutCodewordsCount ℓ ϑ (Fin.last ℓ) = ℓ / ϑ :=
        toOutCodewordsCount_last ℓ ϑ
      have h_le : oraclePositionIdx ≤ ℓ/ϑ := by
        have h := oraclePositionIdx.isLt
        simp only [List.length_finRange] at h
        exact Nat.le_of_lt_succ h
      have h_mul : (ℓ/ϑ) * ϑ = ℓ := by rw [Nat.div_mul_cancel (hdiv.out)]
      have h_mul_le : oraclePositionIdx * ϑ ≤ ℓ := by
        conv_rhs => rw [←h_mul]
        apply Nat.mul_le_mul_right; exact h_le
      let destIdx : Fin r := ⟨oraclePositionIdx * ϑ, by omega⟩
      let suffix_point_from_v : sDomain 𝔽q β h_ℓ_add_R_rate destIdx :=
        extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (v:=v) (destIdx:=destIdx) (h_destIdx_le:=by omega)
      val_folded_point = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := 0) (steps := oraclePositionIdx * ϑ) (destIdx := destIdx) (h_destIdx := by
          simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; rfl)
        (h_destIdx_le := by
          rw [←h_mul]
          dsimp only [destIdx];
          apply Nat.mul_le_mul_right; exact h_le
        ) (f := f₀)
        (r_challenges := getFoldingChallenges (𝓡 := 𝓡) (r := r) (Fin.last ℓ) stmtIn.challenges 0
          (by simp only [zero_add, Fin.val_last]; omega)) suffix_point_from_v

/-- Safety of the simulated inner `forIn` loop used by
`checkSingleRepetition_probFailure_eq_zero`. -/
lemma checkSingleRepetition_inner_forIn_probFailure_eq_zero
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ((stmtIn, oStmtIn), witIn))
    (rep : Fin γ_repetitions)
    (challenges : (pSpecQuery 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges) :
      let step := queryPhaseLogicStep 𝔽q β γ_repetitions
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmtIn transcript.messages
      let v := (FullTranscript.mk1 (challenges ⟨0, by rfl⟩)).challenges ⟨0, by rfl⟩ rep
      let f : Fin (ℓ / ϑ) → L → OracleComp []ₒ (Option (ForInStep L)) :=
        fun (a : Fin (ℓ / ϑ)) (b : L) ↦
          ((ForInStep.yield <$>
            (simulateQ.{0, 0, 0} so
                (checkSingleFoldingStep 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) a b v stmtIn
              ).run
            )) : OptionT (OracleComp []ₒ) (ForInStep L))
      let inner_forIn_block : OptionT (OracleComp []ₒ) L :=
        forIn (List.finRange (ℓ / ϑ)) (0 : L) f
      Pr[⊥ | inner_forIn_block] = 0 := by
  intro step transcript so v f inner_forIn_block
  dsimp only [inner_forIn_block]
  let Rel : Fin ((List.finRange (ℓ / ϑ)).length + 1) → L → Prop :=
    checkSingleRepetition_foldRel 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) (v := v)
  -- For this proof, we define a trivial relation since the real invariant
  -- is complex and involves the correctness of folding operations
  -- a. Push _root_.OracleComp.liftComp inside the forIn loop (twice, for the two layers)
  --    Goal: simulateQ so (_root_.OracleComp.liftComp (_root_.OracleComp.liftComp (forIn ...)))
  --    Becomes: simulateQ so (forIn ... (fun x s => _root_.OracleComp.liftComp ...))
  -- **Applying indutive relation inference**
  apply probFailure_forIn_of_relations_simplified (rel := Rel) (h_start := by rfl) (h_step := by
    -- Inductive step: any INNER repetition never fails
    intro (k : Fin (List.finRange (ℓ / ϑ)).length) (c_k : L) h_rel_k_c
    -- simp only [List.get_eq_getElem, List.getElem_finRange] at *
    -- Simplify k.succ ≠ 0 (always true)
    have h_succ_ne_zero : k.succ ≠ 0 := Fin.succ_ne_zero k
    constructor
    · -- Part 1: checkSingleFoldingStep is safe (never fails)
      -- where the forInStep.yield has spec
      -- `OracleComp [OracleStatement 𝔽q β ϑ (Fin.last ℓ)]ₒ (ForInStep L)`
      -- [⊥|simulateQ so
      --     ((ForInStep.yield <$> checkSingleFoldingStep 𝔽q β
      --       ((List.finRange (ℓ / ϑ)).get k) c_k v stmtIn).liftComp
      --       ([]ₒ ++ₒ
      --         ([OracleStatement 𝔽q β ϑ (Fin.last ℓ)]ₒ ++ₒ
      --           [fun i ↦ ![Fin γ_repetitions → ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0)] ↑i]ₒ)))] =
      -- 0
      dsimp only [f]
      -- rw [simulateQ_liftComp]
      rw [map_eq_bind_pure_comp]
      erw [probFailure_map] -- Pr[⊥ | f <$> mx] = Pr[⊥ | mx] **IMPORTANT**
      -- ⊢ Pr[⊥ | simulateQ so (checkSingleFoldingStep 𝔽q β γ_repetitions
      --   ((List.finRange (ℓ / ϑ)).get k) c_k v stmtIn).run] = 0
      dsimp only [checkSingleFoldingStep]
      erw [simulateQ_bind]
      erw [OptionT.probFailure_mk_do_bind_eq_zero_iff.{0, 0}]
      have h_probFailure_queryFiberPoints_eq_zero : Pr[⊥ |
        OptionT.mk
          (simulateQ so
            (queryFiberPoints 𝔽q β γ_repetitions ((List.finRange (ℓ / ϑ)).get k) v))] = 0 := by
        apply probFailure_simulateQ_queryFiberPoints_eq_zero
          (γ_repetitions := γ_repetitions) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (𝔽q := 𝔽q) (β := β)
          (so := so) (k := k) (v := v)
      have h_probOutput_none_queryFiberPoints_eq_zero :=
        OptionT.probOutput_none_run_eq_zero_of_probFailure_eq_zero
          (hfail := h_probFailure_queryFiberPoints_eq_zero)
      constructor
      · -- queryFiberPoints never fails (oracle queries)
        simp only [MessageIdx, List.get_eq_getElem, List.getElem_finRange, Fin.eta,
          HasEvalPMF.probFailure_eq_zero]
      · -- The guard and pure computation
        intro fiber_vec_opt h_fiber_vec_opt_mem_support
        have h_fiber_vec_eq_some :=
          exists_eq_some_of_mem_support_of_probOutput_none_eq_zero.{0, 0} (x := fiber_vec_opt)
            (hx := h_fiber_vec_opt_mem_support)
            (hnone := h_probOutput_none_queryFiberPoints_eq_zero)
        rcases h_fiber_vec_eq_some with ⟨fiber_vec, rfl⟩
        simp only [MessageIdx, List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.val_cast,
          gt_iff_lt, CanonicallyOrderedAdd.mul_pos, Message, _root_.OracleComp.guard_eq, Fin.val_last, bind_pure_comp,
          dite_eq_ite]
        have h_ϑ_pos : ϑ > 0 := by exact Nat.pos_of_neZero ϑ
        simp only [h_ϑ_pos, and_true]
        by_cases h_i_pos : k.val > 0
        · -- Case k > 0: guard (c_k = f_i_val)
          let k_idx : Fin (ℓ / ϑ) := ⟨k.val, by
            have h := k.isLt
            simp only [List.length_finRange] at h
            exact h⟩
          have h₁ : k.val * ϑ < ℓ := k_mul_ϑ_lt_ℓ (k := k_idx)
          have h_k_idx_eq : k_idx = (List.finRange (ℓ / ϑ)).get k := by
            simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta]
            apply Fin.eq_of_val_eq
            simp only [Fin.val_cast]; rfl
          -- 1. Simplify failure probability to just the guard condition
          simp only [h_i_pos, ↓reduceIte, OptionT.simulateQ_map]
          have h_guard_pass :
              c_k = fiber_vec.get
                (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  (v := v) (i := ⟨k.val * ϑ, by omega⟩) (steps := ϑ)) := by
            -- ⊢ c_k = f_i_on_fiber.get (extractMiddleFinMask ...)
            -- 1. Construct the correct index type for the lemma
            -- 3. Unfold Rel to get the equality
            unfold Rel checkSingleRepetition_foldRel at h_rel_k_c
            have h_k_castSucc_ne_0 : ¬(k.castSucc.val = 0) := by
              simp only [Fin.val_castSucc]; omega
            rw [dif_neg h_k_castSucc_ne_0] at h_rel_k_c
            simp only [Fin.val_castSucc] at h_rel_k_c
            -- simp only [Fin.isValue, List.get_eq_getElem, List.getElem_finRange, Fin.eta,
            --   Fin.val_cast]
            have h_mul_gt_0 : k.val * ϑ > 0 := by
              simp only [gt_iff_lt, CanonicallyOrderedAdd.mul_pos]
              omega
            -- 4. Apply the lemma
            have res := query_phase_consistency_guard_safe 𝔽q β
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k_idx) (v := v) (c_k := c_k)
              (f_i_on_fiber := fiber_vec) (stmtIn := stmtIn) (oStmtIn := oStmtIn)
              (witIn := witIn) (h_relIn := h_relIn) (h_c_k_correct := h_rel_k_c)
              (h_k_pos := h_mul_gt_0) (γ_repetitions := γ_repetitions)
              (challenges := challenges) (h_fiber_mem := by
              rw [h_k_idx_eq]
              exact h_fiber_vec_opt_mem_support
            )
            exact res
          simp only [h_guard_pass, ↓reduceIte, OptionT.run_pure, simulateQ_pure]
          erw [probFailure_pure]
        · -- Case k = 0: no guard
          simp only [h_i_pos, ↓reduceIte]
          erw [simulateQ_pure, probFailure_pure]
    · -- Part 2: Results in support satisfy the next relation
      intro s' h_s'_support
      simp only [checkSingleRepetition_foldRel, dite_eq_ite, Fin.val_succ, Rel]
      simp only [MessageIdx, List.get_eq_getElem, List.getElem_finRange, Fin.eta, support_map,
        Set.mem_image, OptionT.mem_support_iff, toPFunctor_emptySpec, OptionT.support_run,
        f] at h_s'_support
      -- Extract the actual value from ForInStep.yield
      rcases h_s'_support with ⟨x, h_x_support, h_s'_eq⟩
      rw [←h_s'_eq]
      dsimp only [ForInStep.state]
      -- Handle the index casting issue
      let k_idx : Fin (ℓ / ϑ) := ⟨k.val, by
        have h := k.isLt
        simp only [List.length_finRange] at h
        exact h
      ⟩
      -- Apply the preservation lemma
      let res := query_phase_step_preserves_fold 𝔽q β (γ_repetitions := γ_repetitions)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k_idx) (v := v) (c_k := c_k)
        (s' := x) (stmtIn := stmtIn) (oStmtIn := oStmtIn) (h_relIn := h_relIn)
        (challenges := challenges) (h_s'_mem := by
        dsimp only [so] at h_x_support
        dsimp only [pSpecQuery]
        exact h_x_support
      ) (h_c_k_correct_of_k_pos := by
        dsimp only [k_idx]
        dsimp only [Rel, checkSingleRepetition_foldRel] at h_rel_k_c
        simp only [Fin.val_castSucc, dite_eq_ite] at h_rel_k_c
        by_cases hk : k.val > 0
        · simp only [gt_iff_lt, hk, ↓reduceDIte]
          have h_ne_k_pos : ¬ (k.val = 0) := by omega
          simp only [h_ne_k_pos, ↓reduceIte] at h_rel_k_c
          exact h_rel_k_c
        · simp only [gt_iff_lt, hk, ↓reduceDIte]
      )
      exact res
  )

/--
Safety and Correctness of `checkSingleRepetition` under Honest Simulation.

This lemma proves that for any repetition `rep`, the check:
1. Never fails (safety).
2. Only returns if the accumulated value equals `final_constant`.
-/
lemma checkSingleRepetition_probFailure_eq_zero
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (witIn : Unit)
    (h_relIn : strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ((stmtIn, oStmtIn), witIn))
    (rep : Fin γ_repetitions)
    (challenges : (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges) :
      let step := queryPhaseLogicStep 𝔽q β γ_repetitions
      let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
      let so := OracleInterface.simOracle2.{0, 0, 0, 0, 0} []ₒ oStmtIn transcript.messages
      let v := (FullTranscript.mk1 (challenges ⟨0, by rfl⟩)).challenges ⟨0, by rfl⟩ rep
      Pr[⊥ | OptionT.mk.{0, 0} (simulateQ.{0, 0, 0} so
        (checkSingleRepetition 𝔽q β (γ_repetitions := γ_repetitions) (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v stmtIn stmtIn.final_constant).run)] = 0 := by
  intro step transcript so v
  let f₀ := getFirstOracle 𝔽q β oStmtIn
  let Rel : Fin ((List.finRange (ℓ / ϑ)).length + 1) → L → Prop :=
    checkSingleRepetition_foldRel 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) (v := v)
  -- 1. Expand definition to expose the `forIn` and `guard`
  dsimp only [checkSingleRepetition]
  -- 2. Distribute simulateQ and liftM over the Bind (>>=)
  --    This splits `simulateQ (Loop >>= Guard)` into `simulateQ Loop >>= simulateQ Guard`
  simp only [bind_pure_comp]
  simp only [Fin.eta]
  -- erw [liftComp_bind]
  erw [simulateQ_bind]
  dsimp only [Function.comp_def]
  -- dsimp only [_root_.OracleComp.liftComp]
  simp only [OptionT.simulateQ_forIn.{0}] -- **universe 0 is important** here
  dsimp only [OptionT.mk]
  erw [OptionT.probFailure_mk_do_bind_eq_zero_iff.{0, 0}]
  dsimp only [OptionT.mk]
  -- rw [OptionT.liftComp_forIn]
  conv =>
    enter [1];
    simp only [MessageIdx, List.forIn_yield_eq_foldlM, id_map', List.foldlM_range, bind_pure_comp,
      HasEvalPMF.probFailure_eq_zero, zero_add, probOutput_eq_zero_iff', finSupport_map,
      Finset.mem_image, reduceCtorEq, and_false, exists_const, not_false_eq_true]
  rw [true_and]
  intro c h_c_support_inner_loop
  -- **if the inner for loop is passed, then the guard must be passed (given relIn)**
  simp only [MessageIdx, Message, LawfulApplicative.map_pure, bind_pure_comp,
    OptionT.simulateQ_map] at h_c_support_inner_loop
  set f : Fin (ℓ / ϑ) → L → OracleComp []ₒ (Option (ForInStep L)) :=
    fun (a :  Fin (ℓ / ϑ)) (b : L) ↦
    ((ForInStep.yield <$>
      (simulateQ.{0, 0, 0} so
        (checkSingleFoldingStep 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) a b v stmtIn
        ).run
      )) : OptionT (OracleComp []ₒ) (ForInStep L)) with h_f_def
  set inner_forIn_block := ((forIn (List.finRange (ℓ / ϑ)) (0 : L) f) :
    OptionT (OracleComp []ₒ) L) with h_inner_forIn_block
  have h_probFailure_loop_eq_zero : Pr[⊥ | inner_forIn_block] = 0 := by
    exact checkSingleRepetition_inner_forIn_probFailure_eq_zero 𝔽q β
      (γ_repetitions := γ_repetitions) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn) (oStmtIn := oStmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (rep := rep) (challenges := challenges)
  have h_probOutput_inner_forIn_block_eq_none :=
        OptionT.probOutput_none_run_eq_zero_of_probFailure_eq_zero
          (hfail := h_probFailure_loop_eq_zero)
  have h_c_eq_some := exists_eq_some_of_mem_support_of_probOutput_none_eq_zero.{0, 0} (x := c)
      (hx := h_c_support_inner_loop) (hnone := h_probOutput_inner_forIn_block_eq_none)
  rcases h_c_eq_some with ⟨c_val, rfl⟩
  -- h_c_support_inner_loop : c ∈ forIn (List.finRange (ℓ / ϑ)) 0 f .support
  -- ⊢ x = stmtIn.final_constant
  -- We reuse the SAME relation `Rel` and the SAME logic we used for safety!
  have h_c_eq_final_constant : c_val = stmtIn.final_constant := by
    apply query_phase_final_fold_eq_constant 𝔽q β (v := v) (c := c_val)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn) (witIn := witIn)
      (h_relIn := h_relIn) (h_c_correct := by
        -- 1. Apply the helper lemma to transport the invariant to the end
      -- h_x_support : x ∈
      --   (forIn (List.finRange (ℓ / ϑ)) 0 fun a b ↦
      --       simulateQ (QueryImpl.lift so) (checkSingleFoldingStep 𝔽q β a b v stmtIn)
        -- >>= pure ∘ ForInStep.yield).support
      have h_rel_final : Rel ⟨ℓ/ϑ, by simp only [List.length_finRange,
        lt_add_iff_pos_right, zero_lt_one]⟩ c_val := by
        -- unfold OptionT at h_c_support_inner_loop
        -- Apply the yield-only helper
        let relation_correct_of_mem_support := support_forIn_subset_rel_yield_only.{0}
          (m := OptionT (OracleComp []ₒ)) (l := List.finRange (ℓ/ϑ)) (rel := Rel) (f := f)
          (init := 0) (h_start := by rfl) (h_step := by
          -- simp only [←simulateQ_liftComp]
          intro (k : Fin (List.finRange (ℓ / ϑ)).length) (c_k : L) h_rel_k_c iteration_output
            h_iteration_output_iteration
          -- 1. Unpack support (extract c_next)
          -- 1. Distribute simulateQ over >>= and pure
          --    This transforms: simulateQ (action >>= pure) -> (simulateQ action) >>= pure
          simp only [MessageIdx,  List.get_eq_getElem, List.getElem_finRange,
            Fin.eta, support_map, Set.mem_image, OptionT.mem_support_iff, toPFunctor_emptySpec,
            OptionT.support_run, f] at h_iteration_output_iteration
          -- 2. Now the hypothesis is exactly: ∃ c_next, c_next ∈ support ∧ output = yield c_next
          --    Extract it just like before!
          rcases h_iteration_output_iteration with ⟨c_next, h_c_next_mem, h_iteration_output_eq⟩
          rw [←h_iteration_output_eq]
          dsimp only [OptionT.run] at h_c_next_mem
          -- simp only [h_iteration_output_eq]
          constructor
          · rfl
          · -- Construct index (Same logic as Part 2)
            let k_idx : Fin (ℓ / ϑ) :=
              ⟨k.val, by
                have h_k_lt := k.isLt
                simp only [List.length_finRange] at h_k_lt
                exact h_k_lt⟩
            -- Apply preservation lemma (Exact same syntax as Part 2)
            let res := query_phase_step_preserves_fold 𝔽q β (γ_repetitions := γ_repetitions)
              (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (k := k_idx) (v := v) (c_k := c_k)
              (s' := c_next) (stmtIn := stmtIn) (oStmtIn := oStmtIn) (h_relIn := h_relIn)
              (challenges := challenges) (h_s'_mem := h_c_next_mem)
              (h_c_k_correct_of_k_pos := by
                dsimp only [k_idx]
                dsimp only [Rel, checkSingleRepetition_foldRel] at h_rel_k_c
                simp only [Fin.val_castSucc, dite_eq_ite] at h_rel_k_c
                by_cases hk : k.val > 0
                · simp only [gt_iff_lt, hk, ↓reduceDIte]
                  have h_ne_k_pos : ¬ (k.val = 0) := by omega
                  simp only [h_ne_k_pos, ↓reduceIte] at h_rel_k_c
                  exact h_rel_k_c
                · simp only [gt_iff_lt, hk, ↓reduceDIte]
              )
            exact res
        )
        let res := relation_correct_of_mem_support c_val h_c_support_inner_loop
        simp only [List.length_finRange] at res
        exact res
      -- 2. Unpack the relation at the final index (ℓ/ϑ)
      unfold Rel at h_rel_final
      -- Prove that the final index is not 0
      have h_nonzero : (⟨ℓ/ϑ, by simp only [List.length_finRange,
        lt_add_iff_pos_right, zero_lt_one]⟩ :
          Fin (List.length (List.finRange (ℓ / ϑ)) + 1)) ≠ 0 := by
        simp only [ne_eq, Fin.mk_eq_zero, Nat.div_eq_zero_iff, not_or, not_lt]
        constructor
        · have h := Nat.pos_of_neZero (ϑ); omega
        · exact Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out
      -- Resolve the "if" statement to the "else" branch
      -- unfold Rel at h_rel_final
      dsimp only [checkSingleRepetition_foldRel] at h_rel_final
      simp only [ne_eq, Fin.mk_eq_zero] at h_nonzero
      rw [dif_neg h_nonzero] at h_rel_final
      -- Matches the goal exactly
      exact h_rel_final
    )
  rw [h_c_eq_final_constant]
  simp only [MessageIdx, _root_.OracleComp.guard_eq, ↓reduceIte]
  erw [simulateQ_pure.{0, 0, 0}]
  erw [probFailure_pure.{0, 0}]

/-- Pair-support projection wrapper of `support_simulateQ_run'_eq`.
`Prod.fst` of the stateful run support matches the spec support. -/
lemma support_run_simulateQ_run_fst_eq {ι : Type}
    {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited] {σ α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp oSpec (Option α)) (s : σ)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    Prod.fst <$> support (m := ProbComp) (α := Option α × σ) ((simulateQ impl oa) s) =
      support (m := OracleComp oSpec) (α := Option α) oa := by
  have h_support := support_simulateQ_run'_eq (impl := impl) (oa := oa) (s := s)
    (hImplSupp := hImplSupp)
  rw [StateT.run'_eq, support_map] at h_support
  exact h_support
omit [CharP L 2] [SampleableType L] in
private lemma getChallengeSuffix_heq
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    {k k' : Fin (ℓ / ϑ)} (h : k = k') :
    HEq (getChallengeSuffix 𝔽q β k v) (getChallengeSuffix 𝔽q β k' v) := by
  subst k'
  rfl

/-! **Per-repetition support → logical** (extracted for reuse from completeness-style reasoning).
**Counterpart** of `checkSingleRepetition_probFailure_eq_zero` for the `OracleComp.support` case.
If `(ForInStep.yield PUnit.unit, state_post)` lies in the support of one iteration of the
  verifier's forIn body (for a given `rep`), then the logical proximity check holds for that
  repetition: `logical_checkSingleRepetition 𝔽q β oStmtIn (tr.challenges ⟨0, rfl⟩ rep) stmtIn
    stmtIn.final_constant`.
-/
set_option maxHeartbeats 1000000 in
-- The nested stateful query simulation expands several OptionT and forIn layers.
set_option backward.isDefEq.respectTransparency false in
omit [CharP L 2] [SampleableType L] in
lemma logical_checkSingleRepetition_of_mem_support_forIn_body {σ : Type}
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (tr : FullTranscript (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
    (stmtIn : FinalSumcheckStatementOut)
    (rep : Fin γ_repetitions)
    (state_pre : σ)
    (forIn_body : Fin γ_repetitions → PUnit → StateT σ ProbComp (Option (ForInStep PUnit)))
    (h_forIn_body_eq : forIn_body =
      fun (a : Fin γ_repetitions) (_ : PUnit.{1}) =>
      OptionT.mk (simulateQ impl ((((fun (_ : Unit) ↦ ForInStep.yield PUnit.unit) <$>
          ((simulateQ.{0, 0, 0} (impl := OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
            ((checkSingleRepetition 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              ((FullTranscript.mk1 (tr.challenges ⟨0, rfl⟩)).challenges ⟨0, rfl⟩ a)
              stmtIn stmtIn.final_constant) :
                OptionT (OracleComp
                  ([]ₒ + ([OracleStatement 𝔽q β ϑ (Fin.last ℓ)]ₒ +
                    [(pSpecQuery 𝔽q β γ_repetitions).Message]ₒ))) Unit).run) :
            OracleComp []ₒ (Option Unit))) :
          OptionT (OracleComp []ₒ) (ForInStep PUnit.{1})))))
    (h_mem : ∃ (res : ForInStep PUnit.{1} × σ), (some res.1, res.2) ∈
     support ((forIn_body rep PUnit.unit).run state_pre)) :
    logical_checkSingleRepetition 𝔽q β oStmtIn (tr.challenges ⟨0, rfl⟩ rep) stmtIn
      stmtIn.final_constant := by
  -- 1. Extract the witness res = (control_flow, state_post)
  rcases h_mem with ⟨⟨res_flow, state_post_single_outer_repetition⟩, h_support⟩
  -- 2. Unfold the body definition
  rw [h_forIn_body_eq] at h_support
  set v := tr.challenges ⟨0, rfl⟩ rep with h_v
  let Rel := checkSingleRepetition_foldRel 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (stmtIn := stmtIn) (oStmtIn := oStmtIn) (v := v)
  dsimp only [logical_checkSingleRepetition]
  conv at h_support =>
    -- 1. Expand definition to expose the `forIn` and `guard`
    dsimp only [checkSingleRepetition]
    -- 2. Distribute simulateQ and liftM over the Bind (>>=)
    --    This splits `simulateQ (Loop >>= Guard)` into `simulateQ Loop >>= simulateQ Guard`
    dsimp only [liftM, monadLift, MonadLift.monadLift]
    erw [simulateQ_bind, simulateQ_bind, simulateQ_bind]
    erw [support_bind]
    dsimp only [Function.comp_def]
    simp only [Fin.isValue, id_map',
      _root_.OracleComp.guard_eq, map_bind, simulateQ_bind, simulateQ_liftComp, StateT.run_bind, Function.comp_apply,
      simulateQ_map, simulateQ_ite, simulateQ_pure, OptionT.simulateQ_failure,
      StateT.run_map, support_bind,
      support_map, Set.mem_iUnion, Set.mem_image, Prod.mk.injEq, Prod.exists, exists_eq_right_right,
      exists_and_right, exists_and_left, exists_prop]
    erw [support_bind]
    simp only [Fin.isValue, id_map',
      _root_.OracleComp.guard_eq, map_bind, simulateQ_bind, simulateQ_liftComp, StateT.run_bind, Function.comp_apply,
      simulateQ_map, simulateQ_ite, simulateQ_pure, OptionT.simulateQ_failure,
      StateT.run_map, support_bind,
      support_map, Set.mem_iUnion, Set.mem_image, Prod.mk.injEq, Prod.exists, exists_eq_right_right,
      exists_and_right, exists_and_left, exists_prop]
  obtain ⟨output_final_guard, output_state_final_guard, exists_c_last,
    h_final_yield_support_mem⟩ := h_support
  -- c_last is the yielded folded value from the last inner iteration (i.e. γ_repetitions-1)
  rcases exists_c_last with ⟨c_last, output_state_inner_forIn, ⟨h_mem_forIn_support,
    h_mem_final_guard_support⟩⟩
  conv at h_mem_forIn_support =>
    simp only [Function.comp_def, simulateQ_pure, pure_bind]
    rw [OptionT.simulateQ_forIn]
    rw [OptionT.simulateQ_forIn_stateful_comp]
  -- Bridge to the `OptionT` path lemma: extract a successful `c_last` from support.
  obtain ⟨c_last_val, h_c_last_eq_some⟩ : ∃ c_last_val : L, c_last = some c_last_val := by
    cases h_c : c_last with
    | none =>
      exfalso
      simp only [MessageIdx, h_c, Message, simulateQ_pure] at h_mem_final_guard_support
      erw [support_pure] at h_mem_final_guard_support
      simp only [Set.mem_singleton_iff, Prod.mk.injEq] at h_mem_final_guard_support
      obtain ⟨h_guard_none, _⟩ := h_mem_final_guard_support
      have h_final_mem := h_final_yield_support_mem
      simp only [h_guard_none, simulateQ_pure] at h_final_mem
      erw [support_pure] at h_final_mem
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at h_final_mem
    | some a =>
      exact ⟨a, rfl⟩
  have h_mem_forIn_support_some := by
    have h_mem_forIn_support_some := h_mem_forIn_support
    simp only [h_c_last_eq_some] at h_mem_forIn_support_some ⊢
    exact h_mem_forIn_support_some
  have h_ϑ_pos : ϑ > 0 := by exact Nat.pos_of_neZero ϑ
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
  have h_ℓ_div_ϑ_ge_1 : ℓ/ϑ ≥ 1 := by exact (Nat.one_le_div_iff h_ϑ_pos).mpr h_ϑ_le_ℓ
  have h_0_lt : 0 < (ℓ / ϑ) := by omega
  have h_ℓ_div_mul_eq_ℓ : (ℓ / ϑ) * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
  have h_lastOraclePosIdx_mul_add :
    (getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)).val * ϑ + ϑ = ℓ := by
    conv_rhs => rw [←h_ℓ_div_mul_eq_ℓ]
    rw [getLastOraclePositionIndex_last]; simp only
    rw [Nat.sub_mul, Nat.one_mul]; rw [Nat.sub_add_cancel (by rw [h_ℓ_div_mul_eq_ℓ]; omega)]
  -- **Applying indutive relation inference** for the inner `forIn` only
  let Rel' := fun (i : Fin ((List.finRange (ℓ / ϑ)).length + 1)) (c_next : Option L) (_s : σ) =>
    -- state i => at the end of the inner repetition `i-1`
    -- which means at `i = 0`, value = True since nothing meaningful to check
    logical_stepCondition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmtIn)
      (k := ⟨i - 1, by
        have hi := i.isLt;
        simp only [List.length_finRange] at hi; omega
      ⟩) (v := v) (stmt := stmtIn) (final_constant := stmtIn.final_constant)
    ∧ (
      if hi : i > 0 then
        have hi_lt := i.isLt;
        have hi_lt₂ : i - 1 < ℓ / ϑ := by
          simp only [List.length_finRange] at hi_lt; omega
        let k : Fin (ℓ / ϑ) := ⟨i - 1, by omega⟩
        -- **NOTE**: At the end of repetition `k = i-1`, the value c_next which is
          -- the evaluation on `S^{(k+1)*ϑ}` of the folded oracle function must be computed
        -- let point := getChallengeSuffix 𝔽q β (List.finRange (ℓ / ϑ))[↑k] v; fiber_vec.get
        let point := getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (v := v) (k := k)
        let fiber_vec : Fin (2 ^ ϑ) → L := logical_queryFiberPoints 𝔽q β oStmtIn k v
        let output_of_iteration_k : L :=
          (single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨k.val * ϑ, by
            exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h := k_mul_ϑ_lt_ℓ (k := k))
          ⟩) (steps := ϑ) (destIdx := ⟨k.val * ϑ + ϑ, by
            apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            exact k_succ_mul_ϑ_le_ℓ_₂ (k := k)
          ⟩) (h_destIdx := by
            simp only)
          (h_destIdx_le := k_succ_mul_ϑ_le_ℓ_₂ (k := k))
          (r_challenges := fun j ↦ foldOrderChallenges stmtIn.challenges ⟨↑k * ϑ + ↑j, by
            simp only [Fin.val_last]
            have h_le : k.val * ϑ + ϑ ≤ ℓ := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
            omega
          ⟩)
          (y := point) (fiber_eval_mapping := fiber_vec))
        some output_of_iteration_k = c_next
      else True)
  have h_ϑ_pos : ϑ > 0 := Nat.pos_of_neZero ϑ
  -- inductive relation inference for the intermediate folding steps
  have h_inductive_relations := _root_.OptionT.exists_rel_path_of_mem_support_forIn_stateful.{0}
    (spec := []ₒ) (l := List.finRange (ℓ / ϑ)) (init := 0) (σ := σ)
    (s := state_pre) (res := (c_last_val, output_state_inner_forIn))
    (h_mem := h_mem_forIn_support_some) (rel := Rel') (h_start := by
      simp only [logical_stepCondition, logical_checkSingleFoldingStep, gt_iff_lt,
        CanonicallyOrderedAdd.mul_pos, tsub_pos_iff_lt, dite_else_true, Fin.val_last,
        Fin.coe_ofNat_eq_mod, List.length_finRange, Nat.zero_mod, zero_tsub, h_0_lt, ↓reduceDIte,
        not_lt_zero', false_and, zero_mul, Fin.mk_zero', IsEmpty.forall_iff, lt_self_iff_false,
        zero_add, and_self, Rel']
    )
    (h_step := by
      intro k (c_cur : L) (s_curr : σ) h_rel_k res_step h_res_step_mem
      -- c_cur is the yielded folded value from the previous inner iteration (i.e. k-1)
      have h_k := k.isLt
      simp only [List.length_finRange] at h_k
      have h_k_succ_sub_1_lt : k.succ.val - 1 < ℓ / ϑ := by
        simp only [Fin.val_succ, add_tsub_cancel_right]; omega
      have h_k_sub_1_lt : k.val - 1 < ℓ / ϑ := by
        omega
      have h_k_succ_gt_0 : k.succ > 0 := by simp only [gt_iff_lt, Fin.succ_pos]
      dsimp only [Rel', logical_stepCondition] at h_rel_k
      simp only [Fin.val_castSucc, h_k_sub_1_lt, ↓reduceDIte] at h_rel_k
      -- **Nested simulateQ structure** (do not simp the outer impl):
      -- • Outer: `simulateQ impl (...)` comes from RoundByRound's toFun_full: the reduction runs
      --   the verifier with a stateful oracle impl (black box). We do NOT unfold impl; we only
      --   use that its support equals the spec (support_simulateQ_run'_eq).
      -- • Inner: `simulateQ (simOracle2 []ₒ oStmtIn tr.messages) (...)` comes
      --   from OracleVerifier.toVerifier (Basic.lean): verifier checks are run with
      --   simOracle2 so oStmtIn and transcript answer the oracle queries. This inner layer
      --   can be simplified further (unfold checkSingleFoldingStep, use simOracle2 lemmas).
      set inner_base : OracleComp []ₒ (Option L) :=
        simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
          (checkSingleFoldingStep 𝔽q β γ_repetitions ((List.finRange (ℓ / ϑ)).get k)
            c_cur v stmtIn).run
      set inner_oa : OptionT (OracleComp []ₒ) (ForInStep L) :=
        ForInStep.yield <$> (OptionT.mk inner_base)
      have h_run'_supp_eq := OptionT.support_run_simulateQ_run'_eq (impl := impl)
        (oa := inner_oa)
        (s := s_curr)
        (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])
      -- res_step ∈ (run s).support → res_step.1 ∈ (run' s).support = inner_oa.support
      have h_fst_mem :
          some res_step.1 ∈ support ((simulateQ impl
            inner_oa).run' s_curr) := by
        have h_run_mem :
            (some res_step.1, res_step.2) ∈
              support ((simulateQ impl inner_oa).run s_curr) := by
          have h_run_mem := h_res_step_mem
          simp only [inner_oa, inner_base, h_v, bind_pure_comp,
            OptionT.simulateQ_map] at h_run_mem ⊢
          exact h_run_mem
        simp only [StateT.run', support_map, Set.mem_image]
        exact ⟨(some res_step.1, res_step.2), h_run_mem, rfl⟩
      rw [h_run'_supp_eq] at h_fst_mem
      have h_fst_mem_opt : res_step.1 ∈ support (inner_oa) := by
        exact (OptionT.mem_support_iff (mx := inner_oa) (x := res_step.1)).2 h_fst_mem
      have h_inner_step_mem :
          ∃ c_next,
            (some c_next) ∈ support inner_base ∧ ForInStep.yield c_next = res_step.1 := by
        rcases (OptionT.mem_support_OptionT_map_some
            (ma := OptionT.mk inner_base) (f := ForInStep.yield) (y := res_step.1)).1
              h_fst_mem_opt with
          ⟨c_next, h_c_next_mem_mk, h_yield_eq⟩
        exact ⟨c_next, (OptionT.mem_support_mk (mx := inner_base) (x := c_next)).1
          h_c_next_mem_mk, h_yield_eq⟩
      rcases h_inner_step_mem with ⟨c_next, h_fst_mem, h_res_step1_eq⟩
      dsimp only [Rel', logical_stepCondition]
      dsimp only [inner_base] at h_fst_mem
      unfold checkSingleFoldingStep at h_fst_mem
      erw [simulateQ_bind] at h_fst_mem
      erw [simulateQ_bind, support_bind] at h_fst_mem
      dsimp only [OptionT.run] at h_fst_mem
      simp only [Set.mem_iUnion, exists_prop] at h_fst_mem
      rcases h_fst_mem with ⟨fiber_vec_opt, h_fiber_vec_opt_mem_support, h_c_k_mem_output⟩
      have h_probFailure_queryFiberPoints_eq_zero := probFailure_simulateQ_queryFiberPoints_eq_zero
          (𝔽q := 𝔽q) (β := β) (γ_repetitions := γ_repetitions) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (so := OracleInterface.simOracle2 []ₒ oStmtIn tr.messages) (k := k) (v := v)
      have h_probOutput_none_queryFiberPoints_eq_zero :=
        OptionT.probOutput_none_run_eq_zero_of_probFailure_eq_zero
          (hfail := h_probFailure_queryFiberPoints_eq_zero)
      have h_fiber_vec_opt_mem_support_run :
          fiber_vec_opt ∈
            support (simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
              (queryFiberPoints 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ((List.finRange (ℓ / ϑ)).get k)
                v)) := by
        have h_fiber_vec_opt_mem_support' := h_fiber_vec_opt_mem_support
        simp only [queryFiberPoints, support_bind,
          Set.mem_iUnion, exists_prop] at h_fiber_vec_opt_mem_support' ⊢
        rcases h_fiber_vec_opt_mem_support' with ⟨i, h_i_mem, h_i_out⟩
        have h_eq : fiber_vec_opt = i := by
          cases i with
          | none =>
            change fiber_vec_opt = none at h_i_out ⊢
            exact h_i_out
          | some val =>
            change fiber_vec_opt = some val at h_i_out ⊢
            exact h_i_out
        subst h_eq
        rw [bind_pure_comp]
        convert h_i_mem using 1
        rw [id_map']
      have h_fiber_vec_opt_eq_some := exists_eq_some_of_mem_support_of_probOutput_none_eq_zero
        (x := fiber_vec_opt) (hx := h_fiber_vec_opt_mem_support_run)
        (hnone := h_probOutput_none_queryFiberPoints_eq_zero)
      rcases h_fiber_vec_opt_eq_some with ⟨fiber_vec, h_fiber_vec_opt_eq_some⟩
      rw [h_fiber_vec_opt_eq_some] at h_fiber_vec_opt_mem_support_run h_c_k_mem_output
      have h_fiber_val := mem_support_queryFiberPoints 𝔽q β γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oraclePositionIdx := ⟨k, h_k⟩) (v := v)
          (f_i_on_fiber := fiber_vec) (stmtIn := stmtIn) (oStmtIn := oStmtIn)
            (witIn := ()) (challenges := tr.challenges)
        (h_fiber_mem := by
          dsimp only [queryPhaseLogicStep]
          have h_transcript : (FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β γ_repetitions
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (tr.challenges ⟨0, rfl⟩)).messages
              = tr.messages := by
            -- funext j
            simp only [MessageIdx, Fin.isValue, FullTranscript.mk1_eq_snoc]
            unfold FullTranscript.messages Transcript.concat
            funext x
            obtain ⟨i, hi⟩ := x; fin_cases i; simp [pSpecQuery] at hi
          rw [h_transcript]
          have h_k_fin_eq : (List.finRange (ℓ / ϑ)).get k = ⟨k, h_k⟩ := by
            apply Fin.eq_of_val_eq
            simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.val_cast]
          have h_mem := h_fiber_vec_opt_mem_support_run
          simp only [MessageIdx, List.get_eq_getElem, List.getElem_finRange, Fin.eta] at h_mem ⊢
          exact h_mem
        )
      simp only at h_fiber_val
      have h_fiber_val_eq : fiber_vec.get = fun (fiberIndex : Fin (2 ^ ϑ)) => oStmtIn ⟨k.val, by
        simp only [toOutCodewordsCount_last]; omega⟩
        (getFiberPoint 𝔽q β ⟨↑k, h_k⟩ v fiberIndex) := by
        funext fiberIndex
        exact h_fiber_val fiberIndex
      simp only [h_fiber_val] at h_c_k_mem_output
      simp only [h_k_succ_sub_1_lt, h_k_succ_gt_0, ↓reduceDIte]
      -- ⊢ logical_checkSingleFoldingStep 𝔽q β oStmtIn ⟨↑k.succ - 1, ⋯⟩ v stmtIn
      dsimp only [logical_checkSingleFoldingStep]
      by_cases h_k_gt_0 : k.val > 0
      · have h_gt : (k.succ.val - 1) * ϑ > 0 := by
          have hk' : k.succ.val - 1 > 0 := by
            rw [Fin.val_succ, add_tsub_cancel_right]
            exact h_k_gt_0
          exact Nat.mul_pos hk' h_ϑ_pos
        simp only [MessageIdx, List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.val_cast,
          gt_iff_lt, h_k_gt_0, mul_pos_iff_of_pos_left, h_ϑ_pos, ↓reduceDIte, Message, _root_.OracleComp.guard_eq,
          Fin.val_last, bind_pure_comp, OptionT.simulateQ_map] at h_c_k_mem_output
        erw [simulateQ_ite] at h_c_k_mem_output
        set V_check := (c_cur = oStmtIn ⟨k, by
          simp only [toOutCodewordsCount_last]; omega⟩ (
            (getFiberPoint 𝔽q β ⟨↑k, h_k⟩ v (extractMiddleFinMask 𝔽q β v ⟨k.val * ϑ, by
              have h := oracle_index_le_ℓ (i := Fin.last ℓ)
                (j := ⟨k, by
                  rw [toOutCodewordsCount_last]
                  exact h_k⟩)
              have hd := Nat.div_mul_cancel (hdiv.out)
              have hkl := (Nat.mul_lt_mul_right (Nat.pos_of_neZero ϑ)).mpr h_k
              simp only at h; omega⟩ ϑ))
          )) with h_V_check_def
        have h_V_check_passed : V_check := by
          by_contra h_V_check_false
          rw [h_V_check_def] at h_V_check_false
          simp only [h_V_check_false, ↓reduceIte, OptionT.simulateQ_failure, OptionT.map_failure,
            OptionT.support_failure_run, Set.mem_singleton_iff, reduceCtorEq] at h_c_k_mem_output
        rw [h_V_check_def] at h_V_check_passed
        simp only [h_V_check_passed, ↓reduceIte] at h_c_k_mem_output
        erw [simulateQ_pure, support_bind] at h_c_k_mem_output
        simp only [support_pure, Set.mem_singleton_iff, Function.comp_apply,
          Set.iUnion_iUnion_eq_left, OptionT.support_OptionT_pure_run,
          Option.some.injEq] at h_c_k_mem_output
        -- dsimp only [Functor.map] at h_c_k_mem_output
        have h_k_cast_gt_0 : 0 < k.castSucc := by
          change 0 < k.val
          exact h_k_gt_0
        simp only [gt_iff_lt, h_k_cast_gt_0, ↓reduceDIte, Fin.val_last,
          Option.some.injEq] at h_rel_k
        simp only [h_gt, ↓reduceDIte]
        simp only [Fin.val_succ, add_tsub_cancel_right]
        -- Goal: LHS = RHS. We have h_c_k_mem_output.1 : b = (RHS as oStmtIn ... getFiberPoint ...).
        conv_rhs => dsimp only [logical_queryFiberPoints];
        dsimp only [logical_queryFiberPoints]
        -- ⊢ logical_computeFoldedValue 𝔽q β ⟨↑k - 1, ⋯⟩ v stmtIn (logical_queryFiberPoints 𝔽q β
          -- oStmtIn ⟨↑k - 1, ⋯⟩ v) = oStmtIn ⟨↑k, ⋯⟩ (getFiberPoint 𝔽q β ⟨↑k, ⋯⟩ v
            -- (extractMiddleFinMask 𝔽q β v ⟨↑k * ϑ, ⋯⟩ ϑ))
        dsimp only [logical_computeFoldedValue, logical_queryFiberPoints]
        constructor
        · -- V check in the current iteration passes
          rw [←h_V_check_passed]
          -- rw previous computation of c_cur (in previous iteration)
          simp only [Fin.val_last, h_rel_k.2.symm]
          rfl
        · -- prove equality relation for the output of the current iteration (i.e. c_next)
          simp only [ForInStep.state]
          rw [h_c_k_mem_output] at h_res_step1_eq
          rw [h_res_step1_eq.symm]
          dsimp only [ForInStep.state]
          rw [h_fiber_val_eq]
          simp only [Nat.add_one_sub_one, Fin.val_last]
          have h_k_fin_eq : (List.finRange (ℓ / ϑ)).get k = ⟨k, by omega⟩ := by
            apply Fin.eq_of_val_eq;
            simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.val_cast]
          let destIdx : Fin r := ⟨k.val * ϑ + ϑ, by
            apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            have h_le : k.val * ϑ + ϑ ≤ ℓ := by
              exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ)
                (j := ⟨k.val, by
                  rw [toOutCodewordsCount_last]
                  exact h_k⟩)
            exact h_le
          ⟩
          conv_lhs => rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
            dsimp only [destIdx])]
          conv_rhs => rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
            simp only [List.getElem_finRange, Fin.eta, Fin.val_cast]; dsimp only [destIdx])]
          congr 1; congr 1;
          -- only challenges equality left
          dsimp only [getChallengeSuffix]
          apply eq_of_heq
          rw [heq_eqRec_iff_heq]
          exact getChallengeSuffix_heq 𝔽q β v h_k_fin_eq.symm
      · have h_ne_gt : ¬ ((k.succ.val - 1) * ϑ > 0) := by
          intro h_gt
          have h_mul_pos : k.val * ϑ > 0 := by
            have h_gt' := h_gt
            simp only [Fin.val_succ, add_tsub_cancel_right] at h_gt'
            exact h_gt'
          have hk_pos : k.val > 0 := by
            exact Nat.pos_of_mul_pos_right h_mul_pos
          exact h_k_gt_0 hk_pos
        simp only [h_ne_gt, ↓reduceDIte, true_and]
        simp only [Fin.val_succ, add_tsub_cancel_right, Nat.add_one_sub_one, Fin.val_last,
          Option.some.injEq]
        -- ⊢ single_point_localized_fold_matrix_form 𝔽q β ⟨(↑k.succ - 1) * ϑ, ⋯⟩ ϑ ⋯ ⋯
        --     (fun j ↦ stmtIn.challenges ⟨(↑k.succ - 1) * ϑ + ↑j, ⋯⟩)
          -- (getChallengeSuffix 𝔽q β ⟨↑k.succ - 1, ⋯⟩ v)
        --     (logical_queryFiberPoints 𝔽q β oStmtIn ⟨↑k.succ - 1, ⋯⟩ v) =
        --   res_step.1.state
        simp only [MessageIdx, List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.val_cast,
          gt_iff_lt, CanonicallyOrderedAdd.mul_pos, h_k_gt_0, false_and, ↓reduceDIte, Message,
          Fin.val_last, bind_pure_comp, LawfulApplicative.map_pure] at h_c_k_mem_output
        erw [simulateQ_pure, support_pure] at h_c_k_mem_output
        simp only [Set.mem_singleton_iff, Option.some.injEq] at h_c_k_mem_output
        rw [h_c_k_mem_output] at h_res_step1_eq
        rw [h_res_step1_eq.symm]
        dsimp only [ForInStep.state]
        dsimp only [logical_queryFiberPoints]
        rw [h_fiber_val_eq]
        have h_k_fin_eq : (List.finRange (ℓ / ϑ)).get k = ⟨k, by omega⟩ := by
          apply Fin.eq_of_val_eq;
          simp only [List.get_eq_getElem, List.getElem_finRange, Fin.eta, Fin.val_cast]
        let destIdx : Fin r := ⟨k.val * ϑ + ϑ, by
          apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          have h_le : k.val * ϑ + ϑ ≤ ℓ := by
            exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ)
              (j := ⟨k.val, by
                rw [toOutCodewordsCount_last]
                exact h_k⟩)
          exact h_le
        ⟩
        conv_lhs => rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
          apply Fin.eq_of_val_eq;
          dsimp only [destIdx])]
        conv_rhs => rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
          simp only [List.getElem_finRange, Fin.eta, Fin.val_cast]; dsimp only [destIdx])]
        congr 1;
        -- only challenges equality left
        dsimp only [getChallengeSuffix]
        apply eq_of_heq
        rw [heq_eqRec_iff_heq]
        exact getChallengeSuffix_heq 𝔽q β v h_k_fin_eq.symm
    )
    (h_yield := by
      intro k c_cur s_curr res_step h_res_step_mem
      -- erw [OptionT.support_run] at h_res_step_mem
      erw [simulateQ_bind] at h_res_step_mem
      erw [simulateQ_bind, support_bind] at h_res_step_mem
      dsimp only [OptionT.run] at h_res_step_mem
      simp only [MessageIdx, Fin.isValue, Message,
        Set.mem_iUnion, exists_prop, Prod.exists] at h_res_step_mem
      rcases h_res_step_mem with
        ⟨c_next_opt, output_state_next, _h_mem_support_cur_folding_step, h_res_step_mem_yield⟩
      cases h_c : c_next_opt with
      | none =>
        have h_res_step1_mem :
            some res_step.1 ∈ support (m := OracleComp []ₒ) (α := Option (ForInStep L))
              (simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
                (pure (none : Option (ForInStep L)))) := by
          have h_proj_mem :
              some res_step.1 ∈ Prod.fst <$> support (m := ProbComp)
                (α := Option (ForInStep L) × σ)
                  ((simulateQ impl
                    (simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
                      (pure (none : Option (ForInStep L))))) output_state_next) := by
            refine ⟨(some res_step.1, res_step.2), ?_, rfl⟩
            have h_mem := h_res_step_mem_yield
            simp only [MessageIdx, simulateQ_pure, h_c] at h_mem ⊢
            exact h_mem
          have h_proj_eq := support_run_simulateQ_run_fst_eq (impl := impl)
            (oa := simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
              (pure (none : Option (ForInStep L))))
            (s := output_state_next)
            (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])
          rw [h_proj_eq] at h_proj_mem
          exact h_proj_mem
        simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at h_res_step1_mem
        cases h_res_step1_mem
      | some next =>
        have h_res_step1_mem :
            some res_step.1 ∈ support (m := OracleComp []ₒ) (α := Option (ForInStep L))
              (simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
                (pure (some (ForInStep.yield next)))) := by
          have h_proj_mem :
              some res_step.1 ∈ Prod.fst <$> support (m := ProbComp)
                (α := Option (ForInStep L) × σ)
                  ((simulateQ impl
                    (simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
                      (pure (some (ForInStep.yield next))))) output_state_next) := by
            refine ⟨(some res_step.1, res_step.2), ?_, rfl⟩
            have h_mem := h_res_step_mem_yield
            simp only [h_c] at h_mem ⊢
            exact h_mem
          have h_proj_eq := support_run_simulateQ_run_fst_eq (impl := impl)
            (oa := simulateQ (OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
              (pure (some (ForInStep.yield next))))
            (s := output_state_next)
            (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])
          rw [h_proj_eq] at h_proj_mem
          exact h_proj_mem
        simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at h_res_step1_mem
        injection h_res_step1_mem with h_yield
        exact ⟨next, h_yield⟩
    )
  -- extract the final guard relation from h_c_last_mem
  set v_challenge := (FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (tr.challenges ⟨0, rfl⟩)).challenges ⟨0, rfl⟩
      with h_v_challenge
  intro (k : Fin (ℓ / ϑ + 1))
  dsimp only [logical_stepCondition]
  by_cases h_k_lt : ↑k < ℓ / ϑ
  · simp only [h_k_lt, ↓reduceDIte]
    have h_pred_lt : k.val + 1 - 1 < ℓ / ϑ := by omega
    have res := h_inductive_relations.2
    -- 1. Unpack the existence proof
    rcases res with ⟨bs, ss, h_init, h_s_init, h_final_b, h_final_s, h_steps, h_rel_all⟩
    -- 2. Specialize the relation for the 'input' to the k-th iteration
    -- Since k : Fin (ℓ / ϑ), it can be cast into Fin (ℓ / ϑ + 1)
    have h_rel_for_k_th_level_guard := h_rel_all ⟨k + 1, by simp only [List.length_finRange]; omega⟩
    dsimp only [Rel', checkSingleRepetition_foldRel] at h_rel_for_k_th_level_guard
    have h_res := h_rel_for_k_th_level_guard
    simp only [logical_stepCondition, h_pred_lt, ↓reduceDIte, gt_iff_lt, Fin.val_last,
      dite_else_true] at h_res
    -- rw [h_v] at h_res
    exact h_res.1
  · simp only [h_k_lt, ↓reduceDIte]
    --   ⊢ logical_computeFoldedValue 𝔽q β ⟨ℓ / ϑ - 1, ⋯⟩ v stmtIn
      -- (logical_queryFiberPoints 𝔽q β oStmtIn ⟨ℓ / ϑ - 1, ⋯⟩ v) = stmtIn.final_constant
    have h_last_guard_relation := h_inductive_relations.1.2
    dsimp only [Rel', Rel, checkSingleRepetition_foldRel] at h_last_guard_relation
    simp only [List.length_finRange, gt_iff_lt, Fin.val_last,
      dite_else_true] at h_last_guard_relation
    have h_lt : 0 < (⟨ℓ/ϑ, by simp only [List.length_finRange, lt_add_iff_pos_right,
      zero_lt_one]⟩ : Fin ((List.finRange (ℓ / ϑ)).length + 1)) := by
      change (0 : ℕ) < (ℓ / ϑ)
      exact h_0_lt
    dsimp only [logical_computeFoldedValue]
    simp only [h_lt, forall_true_left] at h_last_guard_relation
    obtain ⟨rfl⟩ := h_c_last_eq_some
    simp only [Option.some.injEq] at h_last_guard_relation
    simp only [MessageIdx, h_last_guard_relation.symm, Message] at h_mem_final_guard_support
    erw [simulateQ_ite, simulateQ_ite, simulateQ_pure, simulateQ_pure] at h_mem_final_guard_support
    have h_dest_le_final : (ℓ / ϑ - 1) * ϑ + ϑ ≤ ℓ := by
      have h_dest_eq_final : (ℓ / ϑ - 1) * ϑ + ϑ = ℓ := by
        calc
          (ℓ / ϑ - 1) * ϑ + ϑ = ((ℓ / ϑ - 1) + 1) * ϑ := by
            rw [Nat.add_mul, Nat.one_mul]
          _ = (ℓ / ϑ) * ϑ := by
            rw [Nat.sub_add_cancel (Nat.succ_le_of_lt h_0_lt)]
          _ = ℓ := h_ℓ_div_mul_eq_ℓ
      exact le_of_eq h_dest_eq_final
    let destIdx : Fin r := ⟨(ℓ / ϑ - 1) * ϑ + ϑ, by
      apply lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      exact h_dest_le_final
    ⟩
    set fiber_vec := logical_queryFiberPoints 𝔽q β oStmtIn ⟨ℓ / ϑ - 1, by omega⟩ v
      with h_fiber_vec_def
    set single_point_localized_fold_matrix_form_val :=
      single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        _ _ _ _ _ _ _ with h_single_point_localized_fold_matrix_form_val_def
    conv at h_mem_final_guard_support =>
      rw [support_StateT_ite_apply]
      erw [support_pure, support_pure]
      enter [1]
      rw [h_last_guard_relation]
    have h_final_check_passed : c_last_val = stmtIn.final_constant := by
      by_contra h_neq
      simp only [h_neq, ↓reduceIte, Set.mem_singleton_iff,
        Prod.mk.injEq] at h_mem_final_guard_support
      -- h_mem_final_guard_support :
      -- output_final_guard = none ∧ output_state_final_guard = output_state_inner_forIn
      simp only [h_mem_final_guard_support, simulateQ_pure] at h_final_yield_support_mem
      erw [support_pure] at h_final_yield_support_mem
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq,
        false_and] at h_final_yield_support_mem
    simp only [h_final_check_passed, ↓reduceIte, Set.mem_singleton_iff,
      Prod.mk.injEq] at h_mem_final_guard_support -- pure equalities now
    -- h_mem_final_guard_support :
    -- output_final_guard = some () ∧ output_state_final_guard = output_state_inner_forIn
    rw [←h_final_check_passed]
    rw [←h_last_guard_relation]
    dsimp only [single_point_localized_fold_matrix_form_val]
    conv_lhs =>
      rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx)
        (h_destIdx_eq_destIdx' := by dsimp only [destIdx]) (fiber_eval_mapping := fiber_vec)]
    conv_rhs => rw [single_point_localized_fold_matrix_form_congr_dest_index 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx' := destIdx) (h_destIdx_eq_destIdx' := by
        simp only [List.length_finRange]; dsimp only [destIdx]) (fiber_eval_mapping := fiber_vec)]
    congr 1
    -- only challenges equality left
    dsimp only [getChallengeSuffix]
    apply eq_of_heq
    rw [heq_eqRec_iff_heq]
    exact getChallengeSuffix_heq 𝔽q β v
      (k := ⟨ℓ / ϑ - 1, by omega⟩)
      (k' := ⟨(List.finRange (ℓ / ϑ)).length - 1, by simp only [List.length_finRange]; omega⟩)
      (by apply Fin.ext; simp only [List.length_finRange, Fin.val_mk])

/-! Main lemma connecting verifier support to logical proximity checks.
    This is the key lemma used in toFun_full of queryKnowledgeStateFunction.
    The left side matches the hypothesis from StateT.run characterization:
      (stmtOut, oStmtOut) ∈ support ((fun x ↦ x.1) <$> simulateQ impl (Verifier.run ...) s)
    The right side gives us:
      1. stmtOut = true
      2. oStmtOut = mkVerifierOStmtOut ...
      3. ∀ rep, logical_checkSingleRepetition ... (the proximity checks spec)
-/
omit [CharP L 2] [SampleableType L] in
lemma logical_consistency_checks_passed_of_mem_support_V_run {σ : Type}
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (stmtIn : FinalSumcheckStatementOut)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (tr : FullTranscript (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
    (s : σ) (stmtOut : Bool) (oStmtOut : Empty → Unit)
    (h_mem_V_run_support :
      (stmtOut, oStmtOut) ∈
        support (OptionT.mk (Prod.fst <$> ((simulateQ.{0, 0, 0} impl
            (Verifier.run (stmtIn, oStmtIn) tr
              (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).toVerifier)) :
              StateT σ ProbComp (Option (Bool × (Empty → Unit)))).run s))) :
    (stmtOut = true ∧
      oStmtOut = OracleVerifier.mkVerifierOStmtOut
        (embed := (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).embed)
        (hEq := (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).hEq) oStmtIn tr ∧
     ∀ (rep : Fin γ_repetitions),
       logical_checkSingleRepetition 𝔽q β oStmtIn
         (tr.challenges ⟨0, rfl⟩ rep) stmtIn stmtIn.final_constant) := by
  -- dsimp only [OptionT.mk] at h_mem_V_run_support
  conv at h_mem_V_run_support =>
    dsimp only [Verifier.run, OracleVerifier.toVerifier, queryOracleVerifier]
    dsimp only [queryPhaseLogicStep]
    -- Simplify the `(fun x ↦ x.1) <$> ...` part
    -- Group the last two `bind`
    rw [pure_bind]; rw [bind_assoc]; rw [pure_bind]
    -- Distribute `simulateQ` over the `bind`
    erw [simulateQ_bind, simulateQ_bind, simulateQ_bind]
    -- Resolve the constant mappings
    simp only [Function.comp_def, simulateQ_pure, pure_bind]
    rw [OptionT.simulateQ_forIn]
    rw [OptionT.simulateQ_forIn_stateful_comp]
  conv at h_mem_V_run_support =>
    -- rw [simulateQ_forIn_stateful_comp (impl := impl)
      -- (l := List.finRange γ_repetitions) (init := PUnit.unit)]
    erw [OptionT.support_mk]
    erw [support_map]
    erw [Set.mem_image]
    erw [support_bind]
    enter [1, x]
    simp only [MessageIdx, Message, Fin.isValue, FullTranscript.mk1_eq_snoc, bind_pure_comp,
      OptionT.simulateQ_map, id_map', Set.mem_iUnion,
      exists_prop, Prod.exists]
  obtain ⟨x, hx_mem, hx_1_eq_stmtOut_oStmtOut⟩ := h_mem_V_run_support
  -- Note: hx_mem now refers to the exact simulateQ (forIn ...) block
  -- after the conv with OptionT.simulateQ_forIn
  -- The structure is: hx_mem : ∃ a b, (a, b) ∈ (simulateQ impl (forIn ...)).support
  -- where the forIn is exactly: forIn (List.finRange γ_repetitions) PUnit.unit (fun a b => ...)
  let forIn_body : Fin γ_repetitions → PUnit.{1} →
      StateT σ ProbComp (Option (ForInStep PUnit.{1})) := fun (a : Fin γ_repetitions)
      (b : PUnit.{1}) =>
    simulateQ impl (
      (((fun (_ : Unit) ↦ ForInStep.yield PUnit.unit) <$>
        ((simulateQ.{0, 0, 0} (impl := OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
          ((checkSingleRepetition 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            ((FullTranscript.mk1 (tr.challenges ⟨0, rfl⟩)).challenges ⟨0, rfl⟩ a)
            stmtIn stmtIn.final_constant) :
              OptionT (OracleComp
                ([]ₒ + ([OracleStatement 𝔽q β ϑ (Fin.last ℓ)]ₒ +
                  [(pSpecQuery 𝔽q β γ_repetitions).Message]ₒ))) Unit).run) :
            OracleComp []ₒ (Option Unit))) :
        OptionT (OracleComp []ₒ) (ForInStep PUnit.{1}))
    )
  let forIn_block : OptionT (StateT σ ProbComp) PUnit.{1} :=
    forIn (xs := List.finRange γ_repetitions) (b := PUnit.unit.{1}) (f := forIn_body)
  -- let simulateQ_forIn_block := simulateQ impl forIn_block
  -- Verify that hx_mem is about the exact simulateQ (forIn ...) block
  conv at hx_mem =>
    enter [1, x, 1, b, 1, 1, 1, 1]
    -- Unfold the set definitions to expose the structure
    change (forIn_block)
  conv at hx_mem =>
    enter [1, x_1, 1, b, 1]
    change ((x_1, b) ∈ support (((forIn_block >>=
      (fun (u : Option PUnit.{1}) => (_ : StateT σ ProbComp (Option Bool))))
        : StateT σ ProbComp (Option Bool)).run s))
    rw [OptionT.mem_support_StateT_bind_run (ma := forIn_block) (x := (x_1, b))]
  rcases hx_mem with ⟨y, s', h_y_s'_mem_support_forIn_block, h_x_eq⟩
  -- simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h_x_eq -- Future work
  have h_y_ne_none : y ≠ none := by
    intro h_y_eq_none
    simp only [h_y_eq_none, simulateQ_pure] at h_x_eq
    erw [support_pure] at h_x_eq
    simp only [Set.mem_singleton_iff] at h_x_eq
    rw [Prod.mk_inj] at h_x_eq
    rw [hx_1_eq_stmtOut_oStmtOut] at h_x_eq
    simp only [reduceCtorEq, false_and] at h_x_eq
  obtain ⟨y_val, h_y_eq⟩ := Option.ne_none_iff_exists.mp h_y_ne_none
  obtain ⟨rfl⟩ := h_y_eq
  simp only at h_x_eq
  erw [simulateQ_pure, support_pure] at h_x_eq
  rw [Set.mem_singleton_iff, Prod.mk_inj] at h_x_eq
  -- **Now we have pure equalities of x.1 and x.2**
  rcases h_y_s'_mem_support_forIn_block with ⟨z, s'', h_forIn_run_mem, h_pure⟩
  have h_z_ne_none : z ≠ none := by
    intro h_z_eq_none
    simp only [h_z_eq_none, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, reduceCtorEq, false_and] at h_pure
  obtain ⟨z_val, h_z_eq⟩ := Option.ne_none_iff_exists.mp h_z_ne_none
  obtain ⟨rfl⟩ := h_z_eq
  erw [simulateQ_pure, support_pure] at h_pure
  simp only [Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at h_pure
  -- **h_pure : y_val = true ∧ s' = s''**
  dsimp only [forIn_block] at h_forIn_run_mem
  -- 1. Apply the extraction lemma
  have h_independent_support_mem_exists := OptionT.exists_path_of_mem_support_forIn_unit.{0}
    (spec := []ₒ) (l := List.finRange γ_repetitions) (f := forIn_body) (s_init := s)
    (s_final := s'') (u := z_val)
    (h_yield := by
      intro rep s_pre res_step h_res_step_mem
      dsimp only [forIn_body] at h_res_step_mem
      set oa : OracleComp []ₒ (Option Unit) :=
       ((simulateQ.{0, 0, 0} (impl := OracleInterface.simOracle2 []ₒ oStmtIn tr.messages)
          ((checkSingleRepetition 𝔽q β (γ_repetitions := γ_repetitions) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            ((FullTranscript.mk1 (tr.challenges ⟨0, rfl⟩)).challenges ⟨0, rfl⟩ rep)
            stmtIn stmtIn.final_constant) :
              OptionT (OracleComp
                ([]ₒ + ([OracleStatement 𝔽q β ϑ (Fin.last ℓ)]ₒ +
                  [(pSpecQuery 𝔽q β γ_repetitions).Message]ₒ))) Unit).run) :
            OracleComp []ₒ (Option Unit))
      have h_fst_mem : some res_step.1 ∈ support ((simulateQ impl
          ((((fun (_ : Unit) ↦ ForInStep.yield PUnit.unit) <$> oa) :
            OptionT (OracleComp []ₒ) (ForInStep PUnit)))).run' s_pre) := by
        rw [StateT.run', support_map]
        exact Set.mem_image_of_mem Prod.fst h_res_step_mem
      have h_run'_supp_eq := support_simulateQ_run'_eq (impl := impl)
        (oa := ((((fun (_ : Unit) ↦ ForInStep.yield PUnit.unit) <$> oa) :
          OptionT (OracleComp []ₒ) (ForInStep PUnit))))
        (s := s_pre)
        (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])
      rw [h_run'_supp_eq] at h_fst_mem
      erw [OptionT.mem_support_OptionT_run_map_some] at h_fst_mem
      obtain ⟨u, _h_u_mem, h_eq⟩ := h_fst_mem
      exact h_eq.symm
    )
    (h_mem := h_forIn_run_mem)
  set γ_challenges : Fin γ_repetitions →
    sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩ := tr.challenges ⟨0, rfl⟩ with h_γ_challenges_def
  rw [h_pure.1] at h_x_eq
  rw [h_x_eq.1] at hx_1_eq_stmtOut_oStmtOut
  simp only [Option.some.injEq, Prod.mk.injEq, Bool.true_eq] at hx_1_eq_stmtOut_oStmtOut
  constructor
  · exact hx_1_eq_stmtOut_oStmtOut.1
  · constructor
    · exact Subsingleton.elim _ _
    · -- 2. Quantify over an arbitrary repetition
      intro rep
      -- ⊢ logical_checkSingleRepetition 𝔽q β oStmtIn (γ_challenges rep)
        -- stmtIn stmtIn.final_constant
      have h_rep_th_support_mem := h_independent_support_mem_exists rep
        (by simp only [List.mem_finRange])
      rcases h_rep_th_support_mem with ⟨state_pre_repetition, state_post_repetition,
        h_support_rep_ith_iteration⟩
      exact logical_checkSingleRepetition_of_mem_support_forIn_body 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (γ_repetitions := γ_repetitions) (σ := σ) (impl := impl)
        (oStmtIn := oStmtIn) (tr := tr) (stmtIn := stmtIn) (rep := rep)
        (state_pre := state_pre_repetition) (forIn_body := forIn_body) (h_forIn_body_eq := rfl)
        (h_mem := by
          use (ForInStep.yield PUnit.unit, state_post_repetition)
          exact h_support_rep_ith_iteration
        )

/-- Strong completeness for the query phase logic step.

This proves that for any valid input satisfying `strictFinalSumcheckRelOut`,
the verifier check succeeds with probability 1, and the output satisfies
`acceptRejectOracleRel` (i.e., the statement is `true`). -/
theorem queryPhaseLogicStep_isStronglyComplete :
    (queryPhaseLogicStep 𝔽q β (ℓ := ℓ) (ϑ := ϑ) γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).IsStronglyCompleteUnderSimulation := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let f₀ := getFirstOracle 𝔽q β oStmtIn
  have h_ϑ_pos : ϑ > 0 := by exact Nat.pos_of_neZero ϑ
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ); exact hdiv.out
  let step := queryPhaseLogicStep 𝔽q β (ℓ := ℓ) (ϑ := ϑ) γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  -- 1. Generate the Honest Transcript (Deterministic given challenges)
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  -- 2. Define the honest oracle simulator
  -- simOracle2 oSpec t₁ t₂ : SimOracle.Stateless (oSpec + ([T₁]ₒ + [T₂]ₒ)) oSpec
  -- This answers queries to OracleIn using oStmtIn and queries to Messages using transcript
  let so := OracleInterface.simOracle2 []ₒ oStmtIn transcript.messages
  -- We need to prove:
  -- 1. [⊥ | verifierCheck ...] = 0  (never fails)
  -- 2. [fun b => b = true | verifierCheck ...] = 1  (always returns true)
  -- 3. completeness_relOut holds
  -- 4-5. Prover and verifier agree
  -- Prove safety: verifier check never fails
  have h_guards_pass : Pr[⊥ | OptionT.mk
    (simulateQ so (step.verifierCheck stmtIn transcript))] = 0 := by
    -- Unfold the definitions
    dsimp only [step, queryPhaseLogicStep]
    rw [OptionT.probFailure_mk]
    conv_lhs => -- first summand is 0
      enter [1]; simp only [MessageIdx, Message, Fin.isValue, _root_.OracleComp.liftM_OptionT_eq, bind_pure_comp,
        _root_.map_pure, id_map', List.foldlM_range, OptionT.simulateQ_map,
        HasEvalPMF.probFailure_eq_zero]
    rw [zero_add]
    -- 2. Push simulation inside the 'bind' structure
    -- simulateQ (do a <- x; b) = do a <- simulateQ x; simulateQ b
    erw [simulateQ_bind]
    -- simp only [Function.comp_apply, probOutput_eq_zero_iff]
    -- rw [OptionT.support_run_eq]
    -- simp only [←probOutput_eq_zero_iff]
    -- erw [probOutput_none_OptionT_pure_eq_zero]
    apply OptionT.probOutput_none_run_eq_zero_of_probFailure_eq_zero
    -- rw [probFailure_bind_eq_zero_iff]
    erw [OptionT.probFailure_mk_bind_eq_zero_iff]
    -- [⊥|simulateQ so (forIn ...)] = 0 ∧ (∀ x ∈ (simulateQ so (forIn ...)).support, ...))
    -- conv => -- Simp away the second term (which is simulateQ of pure)
      -- enter [2]
      -- simp only [_root_.OracleComp.liftM_OptionT_eq, bind_pure_comp]
    set simulateQ_forIn_block :  OracleComp []ₒ (Option PUnit.{1}) :=
      simulateQ so _ with h_simulateQ_forIn_block
    have h_probFailure_simulateQ_forIn_eq_0 : Pr[⊥ | OptionT.mk simulateQ_forIn_block] = 0 := by
      dsimp only [simulateQ_forIn_block]
      rw [OptionT.simulateQ_forIn]
      dsimp only [OptionT.mk]
      -- rw [OptionT.probFailure_mk]
      -- conv_lhs =>
      --   enter [1]; simp only [MessageIdx, Message, Fin.isValue, _root_.OracleComp.liftM_OptionT_eq, bind_pure_comp,
      --     _root_.map_pure, List.forIn_yield_eq_foldlM, id_map', List.foldlM_range,
      --     HasEvalPMF.probFailure_eq_zero]
      -- rw [zero_add]
      -- -- ⊢ Pr[=none | simulateQ_forIn_block] = 0
      -- change (Pr[=none | simulateQ_forIn_block] = 0)
      -- 3. Now we are at the outer loop (forIn γ_repetitions).
      -- Push simulateQ inside the loop using the lemma that `simulateQ distributes over the loop`
      -- NOW apply the safety lemma
      -- The goal is: [⊥ | forIn ... (fun ... ↦ simulateQ so ...)] = 0
      apply _root_.probFailure_forIn_eq_zero_of_body_safe
      intro rep h_rep_mem s_rep
      -- 4. Push simulation inside the inner logic
      erw [simulateQ_bind]
      -- rw [probFailure_bind_eq_zero_iff]
      conv =>
        enter [2]
        simp only [bind_pure_comp, _root_.map_pure, Function.comp_apply, simulateQ_pure, probFailure_pure,
          implies_true]
      erw [OptionT.probFailure_mk]
      conv_lhs =>
        enter [1];
        simp only [MessageIdx, Message, Fin.isValue, _root_.OracleComp.liftM_OptionT_eq, bind_pure_comp, _root_.map_pure,
          HasEvalPMF.probFailure_eq_zero]
      rw [zero_add]
      apply OptionT.probOutput_none_run_eq_zero_of_probFailure_eq_zero
      erw [OptionT.probFailure_mk_bind_eq_zero_iff]
      set simulateQ_singleRepetition_block :  OracleComp []ₒ (Option PUnit.{1}) :=
      simulateQ so _ with h_simulateQ_singleRepetition_block
      have h_probFailure_simulateQ_singleRepetition_eq_0 :
        Pr[⊥ | OptionT.mk simulateQ_singleRepetition_block] = 0 := by
        apply checkSingleRepetition_probFailure_eq_zero (h_relIn := h_relIn)
      have h_probOutput_simulateQ_singleRepetition_eq_none :=
        OptionT.probOutput_none_run_eq_zero_of_probFailure_eq_zero
          (hfail := h_probFailure_simulateQ_singleRepetition_eq_0)
      constructor
      · simp only [HasEvalPMF.probFailure_eq_zero]
      · intro x hx -- output from the single repetition
        have h_x_eq : ∃ val, x = some (val) := by
          have h_exists_some := exists_eq_some_of_mem_support_of_probOutput_none_eq_zero (x := x)
            (hx := hx) (hnone := h_probOutput_simulateQ_singleRepetition_eq_none)
          exact h_exists_some
        rcases h_x_eq with ⟨val, h_x_eq⟩
        rw [h_x_eq]
        rw [OptionT.probFailure_mk]
        simp only [MessageIdx, Message, bind_pure_comp, HasEvalPMF.probFailure_eq_zero, zero_add]
        erw [simulateQ_pure]
        simp only [probOutput_eq_zero_iff, support_pure, Set.mem_singleton_iff, reduceCtorEq,
          not_false_eq_true]
    have h_probOutput_simulateQ_forIn_eq_none :=
      OptionT.probOutput_none_run_eq_zero_of_probFailure_eq_zero
        (hfail := h_probFailure_simulateQ_forIn_eq_0)
    constructor
    · simp only [HasEvalPMF.probFailure_eq_zero]
    · intro x hx -- output from the forIn loop
      have h_x_eq : ∃ val, x = some (val) := by
        have h_exists_some := exists_eq_some_of_mem_support_of_probOutput_none_eq_zero (x := x)
          (hx := hx) (hnone := h_probOutput_simulateQ_forIn_eq_none)
        exact h_exists_some
      rcases h_x_eq with ⟨val, h_x_eq⟩
      rw [h_x_eq]
      rw [OptionT.probFailure_mk]
      simp only [HasEvalPMF.probFailure_eq_zero, zero_add]
      erw [simulateQ_pure]
      simp only [probOutput_pure, reduceCtorEq, ↓reduceIte]
  exact ⟨h_guards_pass, rfl, rfl, rfl⟩

/-- Perfect completeness for the final query round (using the oracle queryProof). -/
theorem queryOracleProof_perfectCompleteness {σ : Type}
    (init : ProbComp σ) (hInit : NeverFail init)
  (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  OracleProof.perfectCompleteness
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (relation := strictFinalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (oracleProof := queryOracleProof 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (init := init)
    (impl := impl) := by
  unfold OracleProof.perfectCompleteness
 -- Step 1: Unroll the 2-message reduction to convert from probability to logic
  rw [OracleReduction.unroll_1_message_reduction_perfectCompleteness_V_to_P (hInit := hInit)
    (hDir0 := by rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  -- Step 2: Convert probability 1 to universal quantification over support
  rw [probEvent_eq_one_iff]
  -- Step 3: Unfold protocol definitions
  -- dsimp only [queryOracleProof, queryOracleProver, queryOracleVerifier,
  dsimp only [OracleVerifier.toVerifier, FullTranscript.mk1]
  let step := (queryPhaseLogicStep 𝔽q β (ℓ := ℓ) (ϑ := ϑ) γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
  let strongly_complete : step.IsStronglyCompleteUnderSimulation :=
    queryPhaseLogicStep_isStronglyComplete (L := L)
      𝔽q β (ϑ := ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  constructor
  -- GOAL 1: SAFETY - Prove the verifier never crashes ([⊥|...] = 0)
  · -- Peel off monadic layers to reach the core verifier logic
    -- ⊢ [⊥| do
    --   let challenge ← getChallenge          -- (A) V samples v ← B_{ℓ+R}
    --   let receiveChallengeFn ← pure (...)               -- (B) P receives challenge
      -- (pure, never fails)
    --   let __discr ← proverOut ...           -- (C) P computes output (pure, never fails)
    --   let verifierStmtOut ← simulateQ ...   -- (D) V runs verifierCheck ← THIS IS THE KEY
    --       do
    --         let _ ← liftM verifierCheck     -- The guards live here!
    --         pure verifierOut
    --   pure (...)
    -- ] = 0
    -- Step 1: Peel off the safe layers
    -- For each layer:
    --   A: neverFails_getChallenge or neverFails_query
    --   B: neverFails_pure
    --   C: neverFails_pure (after _root_.OracleComp.liftComp)
    simp only [probFailure_bind_eq_zero_iff]
    conv_lhs =>
      simp only [_root_.OracleComp.liftComp_eq_liftM, liftM_pure, probFailure_eq_zero]
      dsimp only [liftM, monadLift, MonadLift.monadLift]
      rw [OptionT.probFailure_lift]
      simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_zero, _root_.OracleComp.liftComp_eq_liftM,
        _root_.liftComp_id, HasEvalPMF.probFailure_eq_zero]
    rw [true_and]
    intro chal h_chal_support
    -- 1.B Handle the `let receiveChallengeFn ← pure (...)`
    conv =>
      enter [1]; simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_zero,
        Fin.succ_zero_eq_one, _root_.OracleComp.liftComp_eq_liftM]
      dsimp only [liftM, monadLift, MonadLift.monadLift]
      rw [OptionT.probFailure_lift]
      simp only [Fin.isValue, _root_.OracleComp.liftComp_eq_liftM, _root_.liftComp_id, HasEvalPMF.probFailure_eq_zero]
    rw [true_and]
    intro h_receiveChallengeFn h_receiveChallengeFn_support
    -- 1.B Handle the `(queryOracleReduction 𝔽q β γ_repetitions).prover.output
      -- (h_receiveChallengeFn chal)) ...`
    conv =>
      enter [1];
      simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_zero,
        Fin.succ_zero_eq_one, _root_.OracleComp.liftComp_eq_liftM]
      dsimp only [liftM, monadLift, MonadLift.monadLift]
      rw [OptionT.probFailure_lift]
      simp only [Fin.isValue, _root_.OracleComp.liftComp_eq_liftM, _root_.liftComp_id, HasEvalPMF.probFailure_eq_zero]
    rw [true_and]
    intro prover_final_output h_prover_final_output_support
    conv at h_prover_final_output_support =>
      erw [OptionT.support_mk]
      dsimp only [ChallengeIdx, Challenge, _root_.OracleComp.liftComp_eq_liftM, monadLift, MonadLift.monadLift,
        Set.mem_setOf_eq]
      simp only [Fin.reduceLast, Fin.isValue]
      dsimp only [OptionT.lift];
      erw [support_bind]; dsimp only [liftM, monadLift, MonadLift.monadLift];
      rw [_root_.support_liftComp]; erw [support_pure]
      simp only [Fin.isValue, Challenge, Matrix.cons_val_zero, Set.mem_singleton_iff, support_pure,
        Set.iUnion_iUnion_eq_left, Option.some.injEq]
      -- pure equalities now
    -- 1.C Handle the `let __discr ← proverOut ...`
    -- Note: Use simp instead of rw to avoid typeclass diamond issues with Fintype instances
    -- erw [probFailure_liftComp]
    -- split;
    simp only [ChallengeIdx, Challenge, MessageIdx, bind_pure_comp, _root_.OracleComp.liftComp_eq_liftM,
      OptionT.mem_support_iff, toPFunctor_add, toPFunctor_emptySpec, OptionT.support_run,
      Prod.mk.eta, probFailure_eq_zero, implies_true, and_true]
    -- erw [OptionT.probFailure_mk]
    erw [OptionT.probFailure_liftComp_of_OracleComp_Option]
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
    -- Apply the simulateQ safety lemma
    -- Can't apply probFailure_simulateQ_simOracle2_eq_zero here
    obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete
      (stmtIn := stmtIn) (witIn := witIn) (h_relIn := h_relIn)
      (challenges := fun ⟨j, hj⟩ => by
        match j with
        | 0 => exact chal
      )
    have h_transcript_eq : FullTranscript.mk1 ((FullTranscript.mk1 chal).challenges ⟨0, by rfl⟩) =
      FullTranscript.mk1 (pSpec := pSpecQuery 𝔽q β γ_repetitions) chal := by
      rfl
    rw [h_transcript_eq]
    have h_probOutput_none_V_check_eq_0 :=
      OptionT.probOutput_none_run_eq_zero_of_probFailure_eq_zero (hfail := h_V_check)
    have h_vStmtOut_eq : ∃ val, vStmtOut = some (val) := by
      have h_exists_some := exists_eq_some_of_mem_support_of_probOutput_none_eq_zero (x := vStmtOut)
        (hx := h_vStmtOut_mem_support) (hnone := by
          dsimp only [step] at h_probOutput_none_V_check_eq_0
          dsimp only [queryOracleProof, queryOracleReduction, queryPhaseLogicStep,
            queryOracleVerifier, OracleVerifier.toVerifier] at h_probOutput_none_V_check_eq_0 ⊢
          rw [h_transcript_eq] at h_probOutput_none_V_check_eq_0 ⊢
          simp only [MessageIdx, Message, Fin.isValue, bind_pure_comp, Functor.map_map,
            OptionT.simulateQ_map]
          simp only [MessageIdx, Message, Fin.isValue, bind_pure_comp,
            OptionT.simulateQ_map] at h_probOutput_none_V_check_eq_0
          dsimp only [OptionT.run, OptionT.mk] at h_probOutput_none_V_check_eq_0
          erw [OptionT.simulateQ_map] at h_probOutput_none_V_check_eq_0
          exact h_probOutput_none_V_check_eq_0
        )
      exact h_exists_some
    rcases h_vStmtOut_eq with ⟨val, h_vStmtOut_eq⟩
    rw [h_vStmtOut_eq]
    simp only [Function.comp_apply, probOutput_eq_zero_iff]
    rw [OptionT.support_run_eq]
    simp only [←probOutput_eq_zero_iff]
    erw [probOutput_none_pure_some_eq_zero]
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
        id_eq, _root_.OracleComp.guard_eq, bind_pure_comp,
        toPFunctor_add, toPFunctor_emptySpec, OptionT.support_run, ↓existsAndEq, and_true, true_and,
        exists_eq_right_right', liftM_pure, support_pure, exists_eq_left]
      dsimp only [monadLift, MonadLift.monadLift]
    simp only [Fin.isValue, Challenge, Matrix.cons_val_zero, ChallengeIdx,
      _root_.OracleComp.liftComp_eq_liftM, Fin.reduceLast, MessageIdx] at hx_mem_support
    -- Step 2b: Extract the challenge r1 and the trace equations
    obtain ⟨r1, ⟨_h_r1_mem_challenge_support, h_trace_support⟩⟩ := hx_mem_support
    rcases h_trace_support with ⟨prvWitOut, h_prvOut_mem_support, h_verOut_mem_support⟩
    conv at h_prvOut_mem_support => -- similar simplification as in commit step
      dsimp only [queryOracleProof, queryOracleReduction, queryPhaseLogicStep, queryOracleProver,
        queryOracleVerifier, OracleVerifier.toVerifier, FullTranscript.mk1]
      dsimp only [liftM, monadLift, MonadLift.monadLift]
      rw [_root_.support_liftComp]
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, and_true]
    -- Step 2c: Simplify the verifier computation
    conv at h_verOut_mem_support =>
      erw [simulateQ_bind]
      -- rw [OptionT.simulateQ_simOracle2_liftM_query_T2]
      -- erw [_root_.bind_pure_simulateQ_comp]
      simp only
      -- simp only [show OptionT.pure (m := (OracleComp ([]ₒ
        -- + ([OracleStatement 𝔽q β ϑ (Fin.last ℓ)]ₒ + [pSpecFold.Message]ₒ)))) = pure by rfl]
      change (some (verStmtOut, verOStmtOut)) ∈ _root_.support (_root_.OracleComp.liftComp _ _)
      rw [_root_.support_liftComp]
      dsimp only [Functor.map]
      erw [support_bind]
      simp only [Fin.isValue, MessageIdx, Message, support_bind, Set.mem_iUnion, exists_prop,
        Function.comp_apply, Set.iUnion_exists, Set.biUnion_and']
      -- erw [support_pure]
      -- simp only [Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq]
    rcases h_verOut_mem_support with ⟨VCheck_boolean, h_VCheck_boolean_mem_support,
      VOut_boolean, h_VOut_boolean_mem_support, h_VOut_mem_support⟩
    set V_check := step.verifierCheck stmtIn (FullTranscript.mk1
      (msg0 := _)) with h_V_check_def
    -- Apply the simulateQ safety lemma
    -- Can't apply probFailure_simulateQ_simOracle2_eq_zero here
    obtain ⟨h_V_check_not_fail, h_rel, h_agree⟩ := strongly_complete
      (stmtIn := stmtIn) (witIn := witIn) (h_relIn := h_relIn)
      (challenges := fun ⟨j, hj⟩ => by
        match j with
        | 0 => exact r1
      )
    have h_VOut_boolean_eq_true : VOut_boolean = true := by
      match VCheck_boolean with -- VOut_boolean depends on VCheck_boolean
      | some a =>
        simp only [Fin.isValue] at h_VOut_boolean_mem_support
        erw [simulateQ_pure] at h_VOut_boolean_mem_support
        simp only [Fin.isValue, support_pure, Set.mem_singleton_iff] at h_VOut_boolean_mem_support
        dsimp only [queryPhaseLogicStep] at h_VOut_boolean_mem_support
        exact h_VOut_boolean_mem_support
      | none =>
        simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff]
          at h_VOut_boolean_mem_support
        simp only [h_VOut_boolean_mem_support, support_pure, Set.mem_singleton_iff,
          reduceCtorEq] at h_VOut_mem_support ⊢
    simp only [h_VOut_boolean_eq_true, OptionT.support_OptionT_pure_run, Set.mem_singleton_iff,
      Option.some.injEq, Prod.mk.injEq] at h_VOut_mem_support -- pure equalities now
    have prvStmtOut_eq := h_prvOut_mem_support
    obtain ⟨verStmtOut_eq, verOStmtOut_eq⟩ := h_VOut_mem_support
    constructor
    · simpa [acceptRejectOracleRel, verStmtOut_eq]
    · constructor
      · rw [verStmtOut_eq, prvStmtOut_eq];
      · exact Subsingleton.elim _ _

open scoped NNReal

/-- The round-by-round extractor for the query phase.
Since f^(0) is always available, we can invoke the extractMLP function directly. -/
noncomputable def queryRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := (FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
      × (∀ j, OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j))
    (WitIn := Unit)
    Unit
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (fun _ => Unit) where
  eqIn := rfl
  extractMid := fun _ _ _ witMidSucc => witMidSucc
  extractOut := fun _ _ _ => ()

def queryKStateProp (m : Fin (1 + 1))
    (tr : ProtocolSpec.Transcript m
    (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
  (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
  (witMid : Unit)
  (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j) : Prop :=
  match m with
  | ⟨0, _⟩ => -- Same as last KState of finalSumcheck reduction (= relIn)
    Binius.BinaryBasefold.finalSumcheckRelOutProp 𝔽q β
      (input := ⟨⟨stmtIn, oStmtIn⟩, witMid⟩)
  | ⟨1, _⟩ => -- After V sends γ challenges: proximity tests must pass
    let γ_challenges : Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩ :=
      tr.challenges ⟨0, rfl⟩
    let fold_challenges := stmtIn.challenges
    logical_proximityChecksSpec 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ := ϑ) (γ_repetitions := γ_repetitions) (γ_challenges := γ_challenges)
      (final_constant := stmtIn.final_constant) (oStmt := oStmtIn) (stmt := stmtIn)

/-- The knowledge state function for the query phase -/
noncomputable def queryKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  (queryOracleVerifier 𝔽q β (ϑ:=ϑ) γ_repetitions).KnowledgeStateFunction init impl
  (relIn := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
  (relOut := acceptRejectOracleRel)
  (extractor := queryRbrExtractor 𝔽q β (ϑ:=ϑ)
    γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  toFun := fun m ⟨stmtIn, oStmtIn⟩ tr witMid =>
    queryKStateProp 𝔽q β (ϑ:=ϑ) (γ_repetitions:=γ_repetitions)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (m:=m) (tr:=tr) (stmtIn:=stmtIn) (witMid:=witMid) (oStmtIn:=oStmtIn)
  toFun_empty := fun ⟨stmtIn, oStmtIn⟩ witMid => by rfl
  toFun_next := fun m hDir ⟨stmtMid, oStmtMid⟩ tr msg witMid => by
    -- `pSpecQuery` has a single `V_to_P` message, so `hDir : dir m = .P_to_V` is absurd.
    simp only [pSpecQuery, Matrix.cons_val_fin_one, reduceCtorEq] at hDir
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut probEvent_relOut_gt_0 => by
    -- h_relOut: ∃ stmtOut oStmtOut, verifier outputs (stmtOut, oStmtOut) with prob > 0
    --   and ((stmtOut, oStmtOut), witOut) ∈ foldStepRelOut
    simp only [StateT.run'_eq, gt_iff_lt, probEvent_pos_iff, Prod.exists] at probEvent_relOut_gt_0
    rcases probEvent_relOut_gt_0 with ⟨stmtOut, oStmtOut, h_output_mem_V_run_support, h_relOut⟩
    have h_output_mem_V_run_support' :
        some (stmtOut, oStmtOut) ∈
          support (do
              let s ← init
              Prod.fst <$>
                (simulateQ impl
                  (Verifier.run (stmtIn, oStmtIn) tr
                    (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions
                      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).toVerifier)).run s) := by
      exact (OptionT.mem_support_iff
        (mx := OptionT.mk (do
          let s ← init
          Prod.fst <$>
            (simulateQ impl
              (Verifier.run (stmtIn, oStmtIn) tr
                (queryOracleVerifier 𝔽q β (ϑ := ϑ) γ_repetitions
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).toVerifier)).run s))
        (x := (stmtOut, oStmtOut))).1 h_output_mem_V_run_support
    simp only [support_bind, Set.mem_iUnion, exists_prop] at h_output_mem_V_run_support'
    rcases h_output_mem_V_run_support' with ⟨s, hs_init, h_output_mem_V_run_support_with_s⟩
    -- Apply the main lemma connecting verifier support to logical proximity checks
    have h_res := logical_consistency_checks_passed_of_mem_support_V_run
      (impl := impl) (stmtIn := stmtIn) (oStmtIn := oStmtIn) (tr := tr)
      (s := s) (stmtOut := stmtOut) (oStmtOut := oStmtOut)
      (h_mem_V_run_support := by
        rw [OptionT.mem_support_iff]
        dsimp only [OptionT.mk, OptionT.run]
        exact h_output_mem_V_run_support_with_s
      )
    -- The lemma gives us:
    exact h_res.2.2

/-- **Single Repetition Proximity Check Bound (Proposition 4.24)**

For a single repetition of the proximity check, the probability that a non-compliant
oracle (not close to RS codeword) passes the fold consistency check is bounded by:
  `(1/2) + 1/(2 * 2^𝓡)`

**Preconditions (from Proposition 4.24 in the archived DP24 PDF):**
- `h_not_oracleFoldingConsistent`: At least one oracle is non-compliant
- `h_no_bad_event`: No bad folding events occurred (Definition 4.20)

This is the fundamental proximity testing bound used in the soundness proof. -/
theorem prop_4_23_singleRepetition_proximityCheck_bound
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_not_oracleFoldingConsistent : ¬ finalSumcheckStepOracleConsistencyProp 𝔽q β
      (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
      (stmtOut := stmtIn) (oStmtOut := oStmtIn))
    (h_no_bad_event : ¬ blockBadEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmtIn) (challenges := stmtIn.challenges)) :
    Pr_{ let v ← $ᵖ ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
      logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        oStmtIn v stmtIn stmtIn.final_constant ] ≤
    queryRbrKnowledgeError_singleRepetition (𝓡 := 𝓡) := by
  -- Delegates to Soundness Prop 4.24 (Lemma 4.26 supplies the query-rejection property).
  have h_res :=
    (Binius.BinaryBasefold.prop_4_23_singleRepetition_proximityCheck_bound
      (stmtIn := stmtIn) (oStmtIn := oStmtIn)
      (h_not_consistent := h_not_oracleFoldingConsistent)
      (h_no_bad := h_no_bad_event)
      (h_le := by
        apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)))
  dsimp only [queryRbrKnowledgeError_singleRepetition]
  simp only [one_div, mul_inv_rev, ENNReal.coe_add, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, ENNReal.coe_inv, ENNReal.coe_ofNat, ENNReal.coe_mul, pow_eq_zero_iff',
    false_and, ENNReal.coe_pow, ge_iff_le]
  simp only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_inv,
    ENNReal.coe_ofNat, ENNReal.coe_one] at h_res
  rw [ENNReal.mul_inv (ha := by
    left; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true])
    (hb := by
      left; simp only [ne_eq, ENNReal.ofNat_ne_top, not_false_eq_true]) , mul_comm] at h_res
  exact h_res

theorem singleRepetition_proximityCheck_bound
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_not_oracleFoldingConsistent : ¬ finalSumcheckStepOracleConsistencyProp 𝔽q β
      (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
      (stmtOut := stmtIn) (oStmtOut := oStmtIn))
    (h_no_bad_event : ¬ blockBadEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (oStmt := oStmtIn) (challenges := stmtIn.challenges)) :
    Pr_{ let v ← $ᵖ ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0) }[
      logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        oStmtIn v stmtIn stmtIn.final_constant ] ≤
    queryRbrKnowledgeError_singleRepetition (𝓡 := 𝓡) := by
  -- This is Proposition 4.24 from the archived DP24 PDF specialized to a single repetition.
  exact
    prop_4_23_singleRepetition_proximityCheck_bound (𝔽q := 𝔽q) (β := β)
      (stmtIn := stmtIn) (oStmtIn := oStmtIn)
      (h_not_oracleFoldingConsistent := h_not_oracleFoldingConsistent)
      (h_no_bad_event := h_no_bad_event)

open Classical in
/-! Round-by-round knowledge soundness for the oracle verifier (query phase).

**Proof Strategy (RBR Extraction Failure Event):**

The RBR extraction failure event is: `¬ KState(0) ∧ KState(1)`, i.e.,
  - `¬ finalSumcheckRelOutProp` (KState 0 = FALSE), AND
  - `proximityChecksSpec` (KState 1 = TRUE)

By De Morgan's law:
  `¬ finalSumcheckRelOutProp = ¬ (oracleFoldingConsistency ∨ badEvent)`
                             `= ¬ oracleFoldingConsistency ∧ ¬ badEvent`

This means:
  - `¬ oracleFoldingConsistency`: Some oracle is NOT compliant (not close to correct folding)
  - `¬ badEvent`: No bad events detected

**Proposition 4.24 (archived DP24 - assuming no bad events):**
If any of the adversary's oracles is not compliant (not close to RS codeword),
then the verifier accepts with at most negligible probability:
  `Pr[V accepts] ≤ ((1/2) + 1/(2 * 2^𝓡))^γ_repetitions`

This is exactly `queryRbrKnowledgeError`. -/
theorem queryOracleVerifier_rbrKnowledgeSoundness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (queryOracleVerifier 𝔽q β (ϑ:=ϑ) γ_repetitions).rbrKnowledgeSoundness init impl
    (relIn := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
    (relOut := acceptRejectOracleRel)
    (rbrKnowledgeError := queryRbrKnowledgeError 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  classical
  apply OracleReduction.unroll_rbrKnowledgeSoundness
    (kSF := queryKnowledgeStateFunction 𝔽q β (ϑ:=ϑ) γ_repetitions init impl)
  intro stmtIn_oStmtIn witIn prover j initState
  let P := rbrExtractionFailureEvent
    (kSF := queryKnowledgeStateFunction 𝔽q β (ϑ:=ϑ) γ_repetitions init impl)
    (extractor := queryRbrExtractor 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (i := j) (stmtIn := stmtIn_oStmtIn)
  rw [OracleReduction.probEvent_soundness_goal_unroll_log' (pSpec := pSpecQuery 𝔽q β γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (P := P) (impl := impl) (prover := prover) (i := j)
    (stmt := stmtIn_oStmtIn) (wit := witIn) (s := initState)]
  have h_j_eq_1 : j = ⟨0, rfl⟩ :=
    match j with
    | ⟨0, h0⟩ => rfl
  subst h_j_eq_1
  conv_lhs => simp only [Fin.isValue, Fin.castSucc_zero];
  rw [OracleReduction.soundness_unroll_runToRound_0_pSpec_1_V_to_P
    (prover := prover) (stmtIn := stmtIn_oStmtIn) (witIn := witIn)]
  simp only [Fin.isValue, Challenge,  Matrix.cons_val_zero, ChallengeIdx,
    QueryImpl.addLift_def, QueryImpl.liftTarget_self,  bind_pure_comp,
    _root_.OracleComp.liftComp_eq_liftM, simulateQ_bind, simulateQ_map, StateT.run'_eq,
    StateT.run_bind, StateT.run_map, map_bind, Functor.map_map]
  rw [probEvent_bind_eq_tsum]
  -- erw [simulateQ_simOracle2_lift_liftComp_query_T1]
  -- conv =>
  --   enter [1]
  --   erw [probEvent_map]
  --   rw [OracleQuery.cont_apply]
  -- erw [probEvent_bind_eq_tsum]
  apply OracleReduction.ENNReal.tsum_mul_le_of_le_of_sum_le_one
  · -- Bound the conditional probability for each transcript
    intro x
    -- rw [OracleComp.probEvent_map]
    simp only [Fin.isValue, probEvent_map]
    let q : OracleQuery
        [(pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge]ₒ
        _ := query (spec := [(pSpecQuery 𝔽q β γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge]ₒ) ⟨⟨0, by rfl⟩, ()⟩
    erw [OracleReduction.probEvent_StateT_run_ignore_state
      (comp := simulateQ (impl.addLift challengeQueryImpl) (liftM (query q.input)))
      (s := x.2)
      (P := fun a => P (x.1.1) (q.cont a))]
    rw [probEvent_eq_tsum_ite]
    erw [simulateQ_query]
    simp only [ChallengeIdx, Challenge, Fin.isValue, monadLift_self,
      QueryImpl.addLift_def, QueryImpl.liftTarget_self, StateT.run'_eq, StateT.run_map,
      Functor.map_map, ge_iff_le]
    have h_L_inhabited : Inhabited L := ⟨0⟩
    letI : SampleableType (Fin γ_repetitions → ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0)) :=
      (inferInstance : ∀ j, SampleableType ((pSpecQuery 𝔽q β γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenge j)) ⟨0, rfl⟩
    conv_lhs =>
      enter [1, x_1, 2, 1, 2]
      erw [addLift_challengeQueryImpl_input_run_eq_liftM_run (impl := impl) (t := q.input)
        (s := x.2)]
    erw [StateT.run_monadLift, monadLift_self]
    rw [bind_pure_comp]
    conv =>
      enter [1, 1, x_1, 2]
      erw [Functor.map_map]
      rw [← probEvent_eq_eq_probOutput]
      rw [probEvent_map]
      rw [OracleQuery.cont_apply]
      dsimp only [MonadLift.monadLift]
      rw [OracleQuery.cont_apply]
      dsimp only [q]
    simp_rw [OracleQuery.input_query, OracleQuery.snd_query]
    conv_lhs => change (∑' (x_1 : (Fin γ_repetitions → ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0))), _)
    conv =>
      enter [1, 1, x_1, 2]
      dsimp only [Function.comp_apply, id_eq]
      erw [probEvent_eq_eq_probOutput]
      change Pr[=x_1 | $ᵗ (Fin γ_repetitions → ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0))]
      rw [OracleReduction.probOutput_uniformOfFintype_eq_Pr (L := _) (x := x_1)]
    rw [OracleReduction.tsum_uniform_Pr_eq_Pr
      (L := (Fin γ_repetitions → ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0)))
      (P := fun x_1 => P x.1.1 (q.2 x_1))]
      -- Now the goal is in do-notation form, which is exactly what Pr_ notation expands to
    -- Make this explicit using change
    conv_lhs => change (∑' (x_1 : (Fin γ_repetitions → ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0))), _)
    -- Now the goal is in do-notation form, which is exactly what Pr_ notation expands to
    -- Make this explicit using change
    change Pr_{ let y ← $ᵖ (Fin γ_repetitions → ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0)) }[(P x.1.1) y] ≤
      queryRbrKnowledgeError 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨0, rfl⟩
    -- Factor over independent repetitions using the structure of rbrExtractionFailureEvent
    --
    -- Key observations:
    -- 1. P = rbrExtractionFailureEvent = ∃ witMid : Unit, ¬kSF 0 ... ∧ kSF 1 ...
    -- 2. Since witMid : Unit, the existential is trivial (there's only ())
    -- 3. kSF 1 = logical_proximityChecksSpec = ∀ rep, single_check (challenges rep)
    -- 4. The bound follows from: P y → ∀ rep, single_check (y rep)
    --    So Pr[P y] ≤ Pr[∀ rep, single_check (y rep)] = Pr[single_check c]^γ
    --
    -- Strategy: Use monotonicity of probability, then factor the forall
    obtain ⟨stmtIn, oStmtIn⟩ := stmtIn_oStmtIn
    -- Step 1: Define the single-repetition predicate
    let single_P : ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0) → Prop := fun v =>
      logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) oStmtIn v stmtIn
        stmtIn.final_constant
    -- Case split FIRST: if P is empty, handle directly; otherwise extract preconditions
    by_cases h_P_nonempty : ∃ y, P x.1.1 y
    case neg =>
      -- If no y satisfies P x.1.1 y, then Pr[P x.1.1 _] = 0 ≤ bound trivially
      push_neg at h_P_nonempty
      -- Show Pr[P x.1.1 _] = 0 using that P is never true
      calc Pr_{ let y ← $ᵖ (Fin γ_repetitions →
            ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0)) }[ P x.1.1 y ]
        _ = Pr_{ let y ← $ᵖ (Fin γ_repetitions →
            ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0)) }[ False ] := by
          congr 1; ext y;
          simp only [Fin.isValue, h_P_nonempty, PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind,
            PMF.bind_const, PMF.pure_apply, eq_iff_iff, iff_false, ite_not]
        _ = 0 := by
          simp only [PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind, PMF.bind_const, PMF.pure_apply,
            eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte]
        _ ≤ _ := zero_le
    case pos =>
      -- P is non-empty: extract preconditions from a witness
      obtain ⟨y₀, h_P_y₀⟩ := h_P_nonempty
      -- Step 2: Show P implies the forall form
      have h_P_implies_forall : ∀ y, P x.1.1 y → (∀ rep : Fin γ_repetitions, single_P (y rep)) := by
        intro y h_P
        unfold rbrExtractionFailureEvent at h_P
        rcases h_P with ⟨witMid, h_kSF_false_before, h_kSF_true_after⟩
        unfold queryKnowledgeStateFunction queryKStateProp logical_proximityChecksSpec
          at h_kSF_true_after
        exact h_kSF_true_after
      -- Step 2b: Extract the preconditions from h_kSF_false_before via De Morgan
      have h_preconditions :
          (¬ finalSumcheckStepOracleConsistencyProp 𝔽q β
            (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
            (stmtOut := stmtIn) (oStmtOut := oStmtIn)) ∧
          (¬ blockBadEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
            (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
            (oStmt := oStmtIn) (challenges := stmtIn.challenges)) := by
        -- Use h_P_y₀ to extract preconditions
        -- First substitute P with its definition
        simp only [P] at h_P_y₀
        unfold rbrExtractionFailureEvent at h_P_y₀
        rcases h_P_y₀ with ⟨witMid, h_kSF_false_before, h_kSF_true_after⟩
        unfold queryKnowledgeStateFunction at h_kSF_false_before
        simp only [Fin.castSucc_zero, queryRbrExtractor] at h_kSF_false_before
        unfold queryKStateProp at h_kSF_false_before
        simp only at h_kSF_false_before
        unfold finalSumcheckRelOutProp at h_kSF_false_before
        rw [finalNonDoomedFoldingProp_eq_finalSumcheckStepFoldingStateProp 𝔽q β]
          at h_kSF_false_before
        unfold finalSumcheckStepFoldingStateProp at h_kSF_false_before
        simp only at h_kSF_false_before
        push_neg at h_kSF_false_before
        exact h_kSF_false_before
      obtain ⟨h_not_consistent, h_no_bad⟩ := h_preconditions
      -- Step 3: Apply monotonicity
      apply le_trans (PrUnion.Pr_mono (D := $ᵖ (Fin γ_repetitions →
        ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0))) (P x.1.1)
        (fun y => ∀ rep : Fin γ_repetitions, single_P (y rep)) h_P_implies_forall)
      -- Step 4: Factor independent repetitions
      rw [uniform_forall_fin_probability γ_repetitions single_P]
      -- Step 5: Bound single repetition using singleRepetition_proximityCheck_bound
      have h_single_repetition_bound :
          Pr_{ let v ← $ᵖ ↥(sDomain 𝔽q β h_ℓ_add_R_rate 0) }[ single_P v ] ≤
          queryRbrKnowledgeError_singleRepetition (𝓡 := 𝓡) :=
        singleRepetition_proximityCheck_bound 𝔽q β stmtIn oStmtIn h_not_consistent h_no_bad
      -- Step 6: Finalize exponential bound
      unfold queryRbrKnowledgeError
      exact ENNReal.pow_le_pow_left h_single_repetition_bound
  · -- Prove: ∑' x, [=x|transcript computation] ≤ 1
    apply tsum_probOutput_le_one

end FinalQueryRoundIOR
end
end Binius.BinaryBasefold.QueryPhase
