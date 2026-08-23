/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.BitsOfIndex
import ArkLib.ProofSystem.Binius.BinaryBasefold.Reconstruct.IteratedFoldAdvances

/-!
# Full binary Basefold evaluation

This file records the last-level specialization of the iterated fold/evaluation-polynomial bridge:
folding the level-zero novel-basis encoding of a multilinear polynomial all the way to level `ℓ`
recovers the polynomial evaluation at the statement challenge vector.
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

noncomputable section

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
/-- At the final level, the intermediate evaluation polynomial is the single refined
coefficient, i.e. the full multilinear-weight sum of the original coefficients. -/
lemma intermediateEvaluationPoly_last_iteratedRefineCoeffs_eval
    (coeffs : Fin (2 ^ ℓ) → L) (r_challenges : Fin ℓ → L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨(Fin.last ℓ).val, by omega⟩)) :
    (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
      (i := ⟨(Fin.last ℓ).val, by omega⟩)
      (iteratedRefineCoeffs (𝓡 := 𝓡) (i := 0)
        (destIdx := ⟨(Fin.last ℓ).val, by omega⟩) (Fin.last ℓ).val
        (by simp) (by simp) coeffs r_challenges)).eval y.val =
      ∑ x : Fin (2 ^ ℓ), multilinearWeight r_challenges x * coeffs x := by
  classical
  dsimp only [intermediateEvaluationPoly]
  haveI : IsEmpty (Fin (ℓ - (Fin.last ℓ).val)) := by
    simpa only [Fin.val_last, tsub_self] using (Fin.isEmpty : IsEmpty (Fin 0))
  conv_lhs =>
    dsimp only [intermediateNovelBasisX]
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    simp only [map_mul, mul_one]
    rw [← map_sum]
  haveI : Unique (Fin (2 ^ (ℓ - (Fin.last ℓ).val))) := by
    simpa only [Fin.val_last, tsub_self, pow_zero] using (Fin.instUnique : Unique (Fin 1))
  have h_default :
      (@default (Fin (2 ^ (ℓ - (Fin.last ℓ).val))) Unique.instInhabited).val = 0 := by
    have hlt := (@default (Fin (2 ^ (ℓ - (Fin.last ℓ).val))) Unique.instInhabited).isLt
    simp only [Fin.val_last, tsub_self, pow_zero] at hlt
    exact Nat.lt_one_iff.mp hlt
  simp only [Fintype.sum_unique, h_default]
  simp only [Polynomial.eval_C]
  unfold iteratedRefineCoeffs
  simp only [Fin.val_zero, zero_mul, zero_add]
  apply Finset.sum_congr rfl
  intro x _
  simp

/-- The last mid-codeword value produced by the honest fold chain is the multilinear polynomial
evaluation at the statement challenges. -/
lemma getMidCodewords_last_apply_eq_eval
    (t : MultilinearPoly L ℓ) (challenges : Fin ℓ → L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨Fin.last ℓ, by omega⟩)) :
    getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := Fin.last ℓ) t challenges y =
      t.val.eval challenges := by
  classical
  dsimp only [getMidCodewords]
  let coeffs : Fin (2 ^ ℓ) → L :=
    fun ω => t.val.eval (statementOrderBitsOfIndex (L := L) ω)
  have h_adv := iterated_fold_advances_evaluation_poly 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := 0) (steps := Fin.last ℓ) (destIdx := ⟨(Fin.last ℓ).val, by omega⟩)
    (h_destIdx := by simp) (h_destIdx_le := by simp)
    (coeffs := coeffs)
    (r_challenges := foldOrderChallenges (ℓ := ℓ) (L := L) (i := Fin.last ℓ) challenges)
  unfold polyToOracleFunc at h_adv
  simp only [Fin.val_zero] at h_adv
  have h_base := intermediate_poly_P_base 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (h_ℓ := by omega) (coeffs := coeffs)
  rw [h_base] at h_adv
  change iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := (Fin.last ℓ).val) (destIdx := ⟨Fin.last ℓ, by omega⟩)
      (by simp) (by simp)
      (fun x ↦ Polynomial.eval (↑x)
        (polynomialFromNovelCoeffs 𝔽q β ℓ (by omega) coeffs))
      (foldOrderChallenges (ℓ := ℓ) (L := L) (i := Fin.last ℓ) challenges) y =
    t.val.eval challenges
  rw [congr_fun h_adv y]
  trans ∑ x : Fin (2 ^ ℓ),
      multilinearWeight (foldOrderChallenges (ℓ := ℓ) (L := L) (i := Fin.last ℓ) challenges) x *
        coeffs x
  · convert intermediateEvaluationPoly_last_iteratedRefineCoeffs_eval 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (coeffs := coeffs)
      (r_challenges := foldOrderChallenges (ℓ := ℓ) (L := L) (i := Fin.last ℓ) challenges)
      (y := y) using 1
  rw [multilinear_eval_eq_sum_statementOrderBitsOfIndex (t := t) (r := challenges)]
  apply Finset.sum_congr rfl
  intro x _
  congr

/-- The final mid-codeword at the canonical zero point is the multilinear evaluation. -/
lemma getMidCodewords_last_zero_eq_eval
    (t : MultilinearPoly L ℓ) (challenges : Fin ℓ → L) :
    getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := Fin.last ℓ) t challenges ⟨0, by simp only [Fin.val_last, zero_mem]⟩ =
      t.val.eval challenges :=
  getMidCodewords_last_apply_eq_eval 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (t := t) (challenges := challenges) (y := ⟨0, by simp only [Fin.val_last, zero_mem]⟩)

/-- After all `ℓ` folds, the honest mid-codeword is constant on the final domain. -/
lemma getMidCodewords_last_is_constant
    (t : MultilinearPoly L ℓ) (challenges : Fin ℓ → L)
    (x y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨Fin.last ℓ, by omega⟩)) :
    getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := Fin.last ℓ) t challenges x =
    getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := Fin.last ℓ) t challenges y := by
  rw [getMidCodewords_last_apply_eq_eval 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (t := t) (challenges := challenges) (y := x),
    getMidCodewords_last_apply_eq_eval 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (t := t) (challenges := challenges) (y := y)]

#print axioms intermediateEvaluationPoly_last_iteratedRefineCoeffs_eval
#print axioms getMidCodewords_last_apply_eq_eval
#print axioms getMidCodewords_last_zero_eq_eval
#print axioms getMidCodewords_last_is_constant

end

end Binius.BinaryBasefold
