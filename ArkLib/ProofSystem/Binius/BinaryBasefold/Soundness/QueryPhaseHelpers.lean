/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhasePrelims

/-!
## Binary Basefold Query-Phase Helper Lemmas

Helper lemmas factored out of `QueryPhasePrelims` so the core query-phase definitions and
the cast-heavy helper layer can be checked and cached separately.
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
noncomputable section
variable [SampleableType L]
variable [hdiv : Fact (ϑ ∣ ℓ)]

section QueryPhaseHelperLemmas

open QueryPhase

set_option maxHeartbeats 800000 in
-- The dependent index alignment in `getNextOracle` can take substantial elaboration.
lemma getNextOracle_eq_oracleStatement
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (hj : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)) :
    getNextOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
      (i := Fin.last ℓ) (oStmt := oStmt) (j := j) (hj := hj)
      (destDomainIdx := ⟨j.val * ϑ + ϑ, by
        exact
          lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
              (i := Fin.last ℓ) (j := j))⟩)
      (h_destDomainIdx := by rfl) =
    fun y =>
      (oStmt ⟨j.val + 1, hj⟩)
        (cast (by
          apply congrArg (fun i => ↥(sDomain 𝔽q β h_ℓ_add_R_rate i))
          apply Fin.eq_of_val_eq
          simp only [oraclePositionToDomainIndex, toOutCodewordsCount_last]
          ring) y) := by
  funext y
  unfold getNextOracle
  simp only [cast_eq]

lemma logical_checkSingleRepetition_guard_eq
    (stmtIn : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (h_accept : logical_checkSingleRepetition 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      oStmtIn v stmtIn stmtIn.final_constant)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (h_pos : 0 < j.val) :
    let j_idx : Fin (ℓ / ϑ) := ⟨j.val, by
      have h_lt := j.isLt
      simp only [nBlocks, toOutCodewordsCount_last] at h_lt
      exact h_lt⟩
    let j_prev_idx : Fin (ℓ / ϑ) := ⟨j.val - 1, by
      have h_lt := j.isLt
      simp only [nBlocks, toOutCodewordsCount_last] at h_lt
      omega⟩
    logical_computeFoldedValue 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      j_prev_idx v stmtIn
      (logical_queryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        oStmtIn j_prev_idx v) =
    (oStmtIn j)
      (extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (v := v)
        (destIdx := ⟨j.val * ϑ, by
          exact
            lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (h := by
                have h_lt := j.isLt
                simp only [nBlocks, toOutCodewordsCount_last] at h_lt
                exact k_mul_ϑ_lt_ℓ (k := ⟨j.val, h_lt⟩))⟩)
        (h_destIdx_le := Nat.le_of_lt (by
          have h_lt := j.isLt
          simp only [nBlocks, toOutCodewordsCount_last] at h_lt
          exact k_mul_ϑ_lt_ℓ (k := ⟨j.val, h_lt⟩)))) := by
  let j_idx : Fin (ℓ / ϑ) := ⟨j.val, by
    have h_lt := j.isLt
    simp only [nBlocks, toOutCodewordsCount_last] at h_lt
    exact h_lt⟩
  let j_prev_idx : Fin (ℓ / ϑ) := ⟨j.val - 1, by
    have h_lt := j.isLt
    simp only [nBlocks, toOutCodewordsCount_last] at h_lt
    omega⟩
  have h_step := h_accept (⟨j.val, by
    have h_lt := j.isLt
    simp only [nBlocks, toOutCodewordsCount_last] at h_lt
    omega⟩ : Fin (ℓ / ϑ + 1))
  unfold logical_stepCondition at h_step
  have h_lt_div :
      (⟨j.val, by
        have h_lt := j.isLt
        simp only [nBlocks, toOutCodewordsCount_last] at h_lt
        omega⟩ : Fin (ℓ / ϑ + 1)).val < ℓ / ϑ := by
    have h_lt := j.isLt
    simp only [nBlocks, toOutCodewordsCount_last] at h_lt
    exact h_lt
  rw [dif_pos h_lt_div] at h_step
  unfold logical_checkSingleFoldingStep at h_step
  have h_i_pos : j.val * ϑ > 0 := by
    exact Nat.mul_pos h_pos (Nat.pos_of_neZero ϑ)
  rw [dif_pos h_i_pos] at h_step
  dsimp only [j_idx, j_prev_idx, logical_queryFiberPoints] at h_step
  change
    logical_computeFoldedValue 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      j_prev_idx v stmtIn
      (logical_queryFiberPoints 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        oStmtIn j_prev_idx v) =
    (oStmtIn j)
      (getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j_idx v
        (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (v := v)
          (i := ⟨j_idx.val * ϑ, k_mul_ϑ_lt_ℓ (k := j_idx)⟩)
          (steps := ϑ))) at h_step
  rw [← previousSuffix_eq_getFiberPoint_extractMiddleFinMask
    (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (j := j_idx) (v := v)] at h_step
  exact h_step

abbrev queryBlockIdx (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))) : Fin (ℓ / ϑ) := ⟨j.val, by
  have h_lt := j.isLt
  simp only [nBlocks, toOutCodewordsCount_last] at h_lt
  exact h_lt⟩

abbrev queryBlockSourceIdx (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))) : Fin r := ⟨j.val * ϑ, by
  exact
    lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h := k_mul_ϑ_lt_ℓ (k := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j))⟩

abbrev queryBlockDestIdx (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))) : Fin r :=
  ⟨j.val * ϑ + ϑ, by
    exact
      lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
          (i := Fin.last ℓ) (j := j))⟩

lemma queryBlockSourceIdx_le
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))) :
    (queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j).val ≤ ℓ := by
  exact (Nat.le_add_right _ _).trans
    (oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
      (i := Fin.last ℓ) (j := j))

lemma queryBlockDestIdx_le
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ))) :
    (queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j).val ≤ ℓ := by
  exact oracle_index_add_steps_le_ℓ (ℓ := ℓ) (ϑ := ϑ)
    (i := Fin.last ℓ) (j := j)

abbrev queryBlockSourceSuffix
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0) :
    sDomain 𝔽q β h_ℓ_add_R_rate
      (queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j) :=
  extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (v := v)
    (destIdx := queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
    (h_destIdx_le := queryBlockSourceIdx_le
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)

abbrev queryBlockDestSuffix
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0) :
    sDomain 𝔽q β h_ℓ_add_R_rate
      (queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j) :=
  extractSuffixFromChallenge 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (v := v)
    (destIdx := queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
    (h_destIdx_le := queryBlockDestIdx_le
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)

lemma queryBlockDestIdx_eq_queryBlockSourceIdx_succ
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (hj : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ)) :
    queryBlockDestIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j =
      queryBlockSourceIdx (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ)
        ⟨j.val + 1, hj⟩ := by
  apply Fin.eq_of_val_eq
  simp only [queryBlockDestIdx, queryBlockSourceIdx]
  ring

lemma queryBlockDestSuffix_eq_queryBlockSourceSuffix_succ
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (hj : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0) :
    queryBlockDestSuffix (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v =
      cast (by
        rw [queryBlockDestIdx_eq_queryBlockSourceIdx_succ
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) (j := j) (hj := hj)])
        (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) ⟨j.val + 1, hj⟩ v) := by
  dsimp only [queryBlockDestSuffix, queryBlockSourceSuffix]
  exact
    extractSuffixFromChallenge_congr_destIdx
      (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (v := v)
      (destIdx := queryBlockDestIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (destIdx' := queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) ⟨j.val + 1, hj⟩)
      (h_idx_eq := queryBlockDestIdx_eq_queryBlockSourceIdx_succ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) (j := j) (hj := hj))
      (h_le := queryBlockDestIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (h_le' := queryBlockSourceIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) ⟨j.val + 1, hj⟩)

lemma queryBlockSourceSuffix_maps_to_destSuffix
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0) :
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := ⟨(queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j).val * ϑ,
        k_mul_ϑ_lt_ℓ (k := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j)⟩)
      (k := ϑ)
      (h_bound := k_succ_mul_ϑ_le_ℓ_₂ (k := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j))
      (x := queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v) =
    queryBlockDestSuffix (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v := by
  have h_source_suffix_eq :
      queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j v =
      getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j) v
        (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (v := v)
          (i := ⟨(queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j).val * ϑ,
            k_mul_ϑ_lt_ℓ (k := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j)⟩)
          (steps := ϑ)) :=
    previousSuffix_eq_getFiberPoint_extractMiddleFinMask
      (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (j := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j) (v := v)
  -- `queryBlockDestSuffix j v` is definitionally the challenge suffix at the next block.
  show _ = getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (k := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j) (v := v)
  rw [h_source_suffix_eq]
  have h_generates :
      getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (k := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j) (v := v) =
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
        (i := ⟨(queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j).val * ϑ,
          k_mul_ϑ_lt_ℓ (k := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j)⟩)
        (k := ϑ)
        (h_bound := k_succ_mul_ϑ_le_ℓ_₂ (k := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j))
        (x := getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j) v
          (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (v := v)
            (i := ⟨(queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j).val * ϑ,
              k_mul_ϑ_lt_ℓ (k := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j)⟩)
            (steps := ϑ))) := by
    apply generates_quotient_point_if_is_fiber_of_y
      (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨(queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j).val * ϑ,
        k_mul_ϑ_lt_ℓ (k := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j)⟩)
      (steps := ϑ)
      (h_i_add_steps := k_succ_mul_ϑ_le_ℓ_₂ (k := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j))
      (x := getFiberPoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j) v
        (extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (v := v)
          (i := ⟨(queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j).val * ϑ,
            k_mul_ϑ_lt_ℓ (k := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j)⟩)
          (steps := ϑ)))
      (y := getChallengeSuffix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (k := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j) (v := v))
    refine ⟨extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (v := v)
      (i := ⟨(queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j).val * ϑ,
        k_mul_ϑ_lt_ℓ (k := queryBlockIdx (ℓ := ℓ) (ϑ := ϑ) j)⟩)
      (steps := ϑ), ?_⟩
    rw [getFiberPoint_eq_qMap_total_fiber]
  exact h_generates.symm

set_option maxHeartbeats 400000 in
lemma UDRCodeword_eval_eq_of_fin_eq
    {i j : Fin r} (hij : i = j)
    {hi : i ≤ ℓ} {hj : j ≤ ℓ}
    {f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i}
    {g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j}
    (hfg : HEq f g)
    (hf_close : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hi f)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate j) :
    let hg_close :=
      UDRClose_of_fin_eq (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        hij hfg hf_close
    UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i hi f hf_close
      (cast (by rw [hij]) y) =
    UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      j hj g hg_close y := by
  dsimp
  cases hij
  cases hfg
  exact
    congrFun
      (UDRCodeword_eq_of_close (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (h_i := hi) (f := f)
        hf_close
        (UDRClose_of_fin_eq (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          rfl HEq.rfl hf_close))
      y

set_option maxHeartbeats 400000 in
lemma successor_codeword_eval_eq
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (j : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)))
    (hj : j.val + 1 < nBlocks (ℓ := ℓ) (ϑ := ϑ))
    (v : sDomain 𝔽q β h_ℓ_add_R_rate 0)
    (h_next_close_stmt :
      let j_next : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨j.val + 1, hj⟩
      UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockDestIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (queryBlockDestIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (fun y => (oStmtIn j_next) (cast (by
          rw [queryBlockDestIdx_eq_queryBlockSourceIdx_succ
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) (j := j) (hj := hj)]) y)))
    (h_next_close :
      let j_next : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨j.val + 1, hj⟩
      UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockSourceIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        (queryBlockSourceIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        (oStmtIn j_next)) :
    let j_next : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨j.val + 1, hj⟩
    UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockDestIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (queryBlockDestIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
      (f := fun y => (oStmtIn j_next) (cast (by
        rw [queryBlockDestIdx_eq_queryBlockSourceIdx_succ
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) (j := j) (hj := hj)]) y))
      (h_within_radius := h_next_close_stmt)
      (cast (by
        rw [queryBlockDestIdx_eq_queryBlockSourceIdx_succ
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) (j := j) (hj := hj)])
        (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v)) =
    UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (queryBlockSourceIdx
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
      (queryBlockSourceIdx_le
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
      (f := oStmtIn j_next)
      (h_within_radius := h_next_close)
      (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v) := by
  let j_next : Fin (nBlocks (ℓ := ℓ) (ϑ := ϑ)) := ⟨j.val + 1, hj⟩
  dsimp only [j_next] at h_next_close_stmt h_next_close ⊢
  have h_idx_eq :=
    queryBlockDestIdx_eq_queryBlockSourceIdx_succ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) (j := j) (hj := hj)
  let f_next_cast :
      OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockDestIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j) :=
    fun y => (oStmtIn j_next) (cast (by rw [h_idx_eq]) y)
  have h_dom :
      ↥(sDomain 𝔽q β h_ℓ_add_R_rate
        (queryBlockDestIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)) =
      ↥(sDomain 𝔽q β h_ℓ_add_R_rate
        (queryBlockSourceIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)) := by
    exact
      congrArg
        (fun i => ↥(sDomain 𝔽q β h_ℓ_add_R_rate i))
        h_idx_eq
  have h_next_heq :
      HEq f_next_cast (oStmtIn j_next) := by
    exact
      funext_heq h_dom (fun _ => rfl) (by
        intro y
        apply heq_of_eq
        rfl)
  have h_next_close_cast :
      UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockDestIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (queryBlockDestIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        f_next_cast := by
    change
      UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockDestIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (queryBlockDestIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (fun y => (oStmtIn j_next) (cast (by rw [h_idx_eq]) y))
    exact h_next_close_stmt
  have h_next_close_transport :
      UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockSourceIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        (queryBlockSourceIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        (oStmtIn j_next) := by
    exact
      UDRClose_of_fin_eq (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        h_idx_eq h_next_heq h_next_close_cast
  have h_codeword_eq :
      UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockSourceIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        (queryBlockSourceIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        (f := oStmtIn j_next)
        (h_within_radius := h_next_close_transport)
        (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v) =
      UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockSourceIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        (queryBlockSourceIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        (f := oStmtIn j_next)
        (h_within_radius := h_next_close)
        (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v) := by
    exact
      congrFun
        (UDRCodeword_eq_of_close (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := queryBlockSourceIdx
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
          (h_i := queryBlockSourceIdx_le
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
          (f := oStmtIn j_next)
          h_next_close_transport h_next_close)
        (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v)
  have h_codeword_transport :
      UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockDestIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (queryBlockDestIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (f := f_next_cast)
        (h_within_radius := h_next_close_cast)
        (cast (by rw [h_idx_eq]) (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v)) =
      UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (queryBlockSourceIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        (queryBlockSourceIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        (f := oStmtIn j_next)
        (h_within_radius := h_next_close_transport)
        (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v) := by
    exact
      UDRCodeword_eval_eq_of_fin_eq (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := queryBlockDestIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (j := queryBlockSourceIdx
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        h_idx_eq
        (hi := queryBlockDestIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j)
        (hj := queryBlockSourceIdx_le
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next)
        h_next_heq h_next_close_cast
        (queryBlockSourceSuffix (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (ϑ := ϑ) j_next v)
  exact h_codeword_transport.trans h_codeword_eq

end QueryPhaseHelperLemmas

end

end Binius.BinaryBasefold
