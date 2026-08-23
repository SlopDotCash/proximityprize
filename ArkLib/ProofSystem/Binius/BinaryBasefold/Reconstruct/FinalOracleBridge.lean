/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Relations

/-!
# Final oracle bridge

This file records reusable bridges between the final committed oracle block and the honest
fold chain reconstructed from `strictOracleFoldingConsistencyProp`.
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open scoped NNReal
open ReedSolomon Code BerlekampWelch
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

noncomputable section

set_option linter.unusedDecidableInType false

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable [hdiv : Fact (ϑ ∣ ℓ)]

/-- At the final oracle frontier, `getLastOracle` is the honest prefix fold through level
`ℓ - ϑ` whenever strict oracle-folding consistency holds. -/
lemma strictOracleFoldingConsistency_last_getLastOracle_eq_prefixFold
    (t : MultilinearPoly L ℓ)
    (challenges : Fin (Fin.last ℓ) → L)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_oracle : strictOracleFoldingConsistencyProp 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := t) (i := Fin.last ℓ)
      (challenges := challenges) (oStmt := oStmt)) :
    let curDomainIdx : Fin r := ⟨ℓ - ϑ, by
      have h_le : ϑ ≤ ℓ := Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) hdiv.out
      omega⟩
    let f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 :=
      fun y =>
        (polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
          (fun ω => t.val.eval (statementOrderBitsOfIndex (L := L) ω))).val.eval y.val
    getLastOracle (h_destIdx := by
      rw [getLastOracleDomainIndex_last (ℓ := ℓ) (ϑ := ϑ)])
      (oracleFrontierIdx := Fin.last ℓ)
      𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmt) =
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := ℓ - ϑ) (destIdx := curDomainIdx)
      (h_destIdx := by simp only [curDomainIdx, Fin.val_zero, zero_add])
      (h_destIdx_le := by simp only [curDomainIdx]; omega)
      (f := f₀)
      (r_challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ℓ - ϑ)
        (i := Fin.last ℓ) challenges 0 (h := by
          simp only [zero_add, Fin.val_last]
          omega)) := by
  let jLast : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
    ⟨getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ), by omega⟩
  have h_last := h_oracle jLast
  let curDomainIdx : Fin r := ⟨ℓ - ϑ, by
    have h_le : ϑ ≤ ℓ := Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) hdiv.out
    omega⟩
  let f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 :=
    fun y =>
      (polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
        (fun ω => t.val.eval (statementOrderBitsOfIndex (L := L) ω))).val.eval y.val
  change
    getLastOracle (h_destIdx := by
      rw [getLastOracleDomainIndex_last (ℓ := ℓ) (ϑ := ϑ)])
      (oracleFrontierIdx := Fin.last ℓ)
      𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmt) =
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := ℓ - ϑ) (destIdx := curDomainIdx)
      (h_destIdx := by simp only [curDomainIdx, Fin.val_zero, zero_add])
      (h_destIdx_le := by simp only [curDomainIdx]; omega)
      (f := f₀)
      (r_challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ℓ - ϑ)
        (i := Fin.last ℓ) challenges 0 (h := by
          simp only [zero_add, Fin.val_last]
          omega))
  funext y
  let prefixIdx : Fin r :=
    ⟨(oraclePositionToDomainIndex ℓ ϑ jLast).val, by
      have h_le := oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := jLast)
      omega⟩
  have h_idx : curDomainIdx = prefixIdx := by
    apply Fin.ext
    simp only [curDomainIdx, prefixIdx, jLast]
    rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul,
      Nat.div_mul_cancel (hdiv.out)]
  have h_steps : jLast.val * ϑ = ℓ - ϑ := by
    simp only [jLast]
    rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul,
      Nat.div_mul_cancel (hdiv.out)]
  have h_eval := congr_fun h_last (cast (by rw [h_idx]) y)
  dsimp only [getLastOracle]
  change id (oStmt jLast) (cast (by rw [h_idx]) y) =
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := ℓ - ϑ) (destIdx := curDomainIdx)
      (h_destIdx := by simp only [curDomainIdx, Fin.val_zero, zero_add])
      (h_destIdx_le := by simp only [curDomainIdx]; omega)
      (f := f₀)
      (r_challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ℓ - ϑ)
        (i := Fin.last ℓ) challenges 0 (h := by
          simp only [zero_add, Fin.val_last]
          omega)) y
  rw [h_eval]
  have h_step_congr := iterated_fold_congr_steps_index 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
    (steps := jLast.val * ϑ) (steps' := ℓ - ϑ)
    (destIdx := prefixIdx)
    (h_destIdx := by
      simp only [prefixIdx, Fin.val_zero, zero_add])
    (h_destIdx_le := by
      have h_le := oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := jLast)
      simpa only [prefixIdx] using h_le)
    (h_steps_eq_steps' := h_steps)
    (f := f₀)
    (r_challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡)
      (ϑ := jLast.val * ϑ) (i := Fin.last ℓ) challenges 0 (h := by
        have h_le := oracle_block_k_le_i (ℓ := ℓ) (ϑ := ϑ)
          (i := Fin.last ℓ) (j := jLast)
        simpa only [zero_add, Fin.val_last] using h_le))
    (y := cast (by rw [h_idx]) y)
  rw [h_step_congr]
  have h_prefix_challenges :
      (fun cIdx : Fin (ℓ - ϑ) =>
        getFoldingChallenges (r := r) (𝓡 := 𝓡)
          (ϑ := jLast.val * ϑ) (i := Fin.last ℓ) challenges 0 (h := by
            have h_le := oracle_block_k_le_i (ℓ := ℓ) (ϑ := ϑ)
              (i := Fin.last ℓ) (j := jLast)
            simpa only [zero_add, Fin.val_last] using h_le)
          ⟨cIdx, by omega⟩) =
      getFoldingChallenges (r := r) (𝓡 := 𝓡)
        (ϑ := ℓ - ϑ) (i := Fin.last ℓ) challenges 0 (h := by
          simp only [zero_add, Fin.val_last]
          omega) := by
    funext cIdx
    dsimp only [getFoldingChallenges]
  rw [h_prefix_challenges]
  have h_dest_congr := iterated_fold_congr_dest_index 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
    (steps := ℓ - ϑ) (destIdx := prefixIdx) (destIdx' := curDomainIdx)
    (h_destIdx := by
      simp only [prefixIdx, Fin.val_zero, zero_add]
      rw [h_steps])
    (h_destIdx_le := by
      have h_le := oracle_index_le_ℓ (ℓ := ℓ) (ϑ := ϑ) (i := Fin.last ℓ) (j := jLast)
      simpa only [prefixIdx] using h_le)
    (h_destIdx_eq_destIdx' := h_idx.symm)
    (f := f₀)
    (r_challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡)
      (ϑ := ℓ - ϑ) (i := Fin.last ℓ) challenges 0 (h := by
        simp only [zero_add, Fin.val_last]
        omega))
    (y := cast (by rw [h_idx]) y)
  rw [h_dest_congr]
  simp [f₀]

end

end Binius.BinaryBasefold
