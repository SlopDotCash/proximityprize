/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors

Brick X for issue #317 (Case-2 far direction): pTC surjectivity onto the interleaved code.
Every row-wise codeword stack is the preTensorCombine of a level-i codeword — the paper's
Lemma 4.22 lift via per-row novel coefficients + coefficient interleaving.
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Lift
import ArkLib.ProofSystem.Binius.BinaryBasefold.Reconstruct.IteratedFoldAdvances

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace Binius.BinaryBasefold
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open scoped NNReal
open ReedSolomon Code BerlekampWelch
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- Refining interleaved coefficients at a binary (indicator) challenge tuple selects the
`j`-th interleaved slice. -/
lemma iteratedRefineCoeffs_bitsOfIndex {i dest : Fin r} (steps : ℕ)
    (h_dest : dest.val = i.val + steps) (h_dest_le : dest ≤ ℓ)
    (coeffs : Fin (2 ^ (ℓ - i.val)) → L) (j : Fin (2 ^ steps)) (k : Fin (2 ^ (ℓ - dest.val))) :
    iteratedRefineCoeffs (𝓡 := 𝓡) (i := i) (destIdx := dest) steps h_dest h_dest_le
      coeffs (bitsOfIndex (L := L) j) k =
    coeffs ⟨k.val * 2 ^ steps + j.val, by
      have hle : i.val + steps ≤ ℓ := by omega
      have hpow : 2 ^ (ℓ - i.val) = 2 ^ (ℓ - dest.val) * 2 ^ steps := by
        rw [← pow_add]; congr 1; omega
      rw [hpow]
      have hk := k.isLt
      have hj := j.isLt
      calc k.val * 2 ^ steps + j.val
          < k.val * 2 ^ steps + 2 ^ steps := by omega
        _ = (k.val + 1) * 2 ^ steps := by ring
        _ ≤ 2 ^ (ℓ - dest.val) * 2 ^ steps := Nat.mul_le_mul_right _ (by omega)⟩ := by
  unfold iteratedRefineCoeffs
  rw [Finset.sum_eq_single j]
  · rw [multilinearWeight_bitsOfIndex_eq_indicator]
    simp
  · intro b _ hbj
    rw [multilinearWeight_bitsOfIndex_eq_indicator]
    simp [hbj]
  · intro h
    exact absurd (Finset.mem_univ j) h

set_option maxHeartbeats 8000000 in
/-- **pTC surjectivity onto the interleaved code** (the Lemma 4.22 lift): every row-wise
codeword stack over the destination code is the `preTensorCombine_WordStack` of a level-`i`
codeword, obtained by interleaving the rows' intermediate novel coefficients. -/
lemma exists_codeword_preTensorCombine_eq_of_rows_mem
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (W : Fin (2 ^ steps) → (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L))
    (hW : ∀ j, W j ∈ BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) :
    ∃ g : sDomain 𝔽q β h_ℓ_add_R_rate (⟨i.val, by omega⟩ : Fin r) → L,
      g ∈ BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) _ ∧
      preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g = W := by
  classical
  -- per-row generating polynomials
  have hrows : ∀ j, ∃ P : L[X], P ∈ Polynomial.degreeLT L (2 ^ (ℓ - destIdx.val)) ∧
      (fun x : sDomain 𝔽q β h_ℓ_add_R_rate destIdx => P.eval x.val) = W j := by
    intro j
    have hmem := hW j
    simp only [BBF_Code, ReedSolomon.code, Submodule.mem_map] at hmem
    obtain ⟨P, hP_deg, hP_eval⟩ := hmem
    refine ⟨P, hP_deg, ?_⟩
    funext x
    have := congrFun hP_eval x
    simpa [ReedSolomon.evalOnPoints] using this
  choose Pr hPdeg hPeval using hrows
  -- per-row novel coefficients at the destination level
  let a : Fin (2 ^ steps) → Fin (2 ^ (ℓ - destIdx.val)) → L := fun j =>
    getINovelCoeffs (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      destIdx h_destIdx_le (Pr j)
  -- interleaved coefficient vector at the source level
  have hpow : 2 ^ (ℓ - i.val) = 2 ^ (ℓ - destIdx.val) * 2 ^ steps := by
    rw [← pow_add]; congr 1; omega
  let C : Fin (2 ^ (ℓ - i.val)) → L := fun m =>
    a ⟨m.val % 2 ^ steps, Nat.mod_lt _ (Nat.two_pow_pos steps)⟩
      ⟨m.val / 2 ^ steps, by
        have hm' : m.val < 2 ^ steps * 2 ^ (ℓ - destIdx.val) := by
          rw [show 2 ^ steps * 2 ^ (ℓ - destIdx.val) = 2 ^ (ℓ - i.val) from by
            rw [← pow_add]; congr 1; omega]
          exact m.isLt
        exact Nat.div_lt_of_lt_mul hm'⟩
  -- the lifted codeword
  refine ⟨fun x => (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
      ⟨i.val, by omega⟩ C).eval x.val, ?_, ?_⟩
  · -- membership: the iEP has degree < 2^(ℓ-i)
    simp only [BBF_Code, ReedSolomon.code, Submodule.mem_map]
    refine ⟨intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨i.val, by omega⟩ C, ?_, ?_⟩
    · have := degree_intermediateEvaluationPoly_lt (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i.val, by omega⟩)
        (h_i := by simp only; omega) (coeffs := C)
      simpa [Polynomial.mem_degreeLT] using this
    · rfl
  · -- row identity
    funext j
    have h_adv := iterated_fold_advances_evaluation_poly_nat 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i.val, by omega⟩) (steps := steps)
      (destIdx := destIdx) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (coeffs := C) (r_challenges := bitsOfIndex (L := L) j)
    have hsel : iteratedRefineCoeffs (𝓡 := 𝓡) (i := ⟨i.val, by omega⟩) (destIdx := destIdx)
        steps h_destIdx h_destIdx_le C (bitsOfIndex (L := L) j) = a j := by
      funext k
      rw [iteratedRefineCoeffs_bitsOfIndex]
      simp only [C]
      have hmod : (k.val * 2 ^ steps + j.val) % 2 ^ steps = j.val := by
        rw [Nat.mul_comm k.val, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
      have hdiv : (k.val * 2 ^ steps + j.val) / 2 ^ steps = k.val := by
        rw [Nat.mul_comm k.val, Nat.mul_add_div (Nat.two_pow_pos steps),
          Nat.div_eq_of_lt j.isLt, Nat.add_zero]
      simp only [hmod, hdiv, Fin.eta]
    have h1 :
        preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le
          (fun x => (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
            ⟨i.val, by omega⟩ C).eval x.val) j =
        (fun y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx =>
          (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
            ⟨destIdx.val, by omega⟩
            (iteratedRefineCoeffs (𝓡 := 𝓡) (i := ⟨i.val, by omega⟩) (destIdx := destIdx)
              steps h_destIdx h_destIdx_le C (bitsOfIndex (L := L) j))).eval y.val) :=
      h_adv
    have h2 :
        (fun y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx =>
          (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
            ⟨destIdx.val, by omega⟩
            (iteratedRefineCoeffs (𝓡 := 𝓡) (i := ⟨i.val, by omega⟩) (destIdx := destIdx)
              steps h_destIdx h_destIdx_le C (bitsOfIndex (L := L) j))).eval y.val) = W j := by
      rw [hsel]
      have hrt := intermediateEvaluationPoly_from_inovel_coeffs_eq_self 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) (h_i := h_destIdx_le)
        (P := Pr j) (hP_deg := by
          have := hPdeg j
          simpa [Polynomial.mem_degreeLT] using this)
      have haj : a j = getINovelCoeffs (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx h_destIdx_le (Pr j) := rfl
      rw [haj]
      have : (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
          ⟨destIdx.val, by omega⟩
          (getINovelCoeffs (𝔽q := 𝔽q) (β := β)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx h_destIdx_le (Pr j))) = Pr j := hrt
      rw [this]
      exact hPeval j
    exact h1.trans h2

end
end Binius.BinaryBasefold
