/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Lift
import ArkLib.ProofSystem.Binius.BinaryBasefold.Reconstruct.IteratedFoldAdvances
import ArkLib.ProofSystem.Binius.BinaryBasefold.BaseFoldDetBrick
import ArkLib.ProofSystem.Binius.BinaryBasefold.Reconstruct.FinalConstantWeld
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.PreTensorMetric

/-!
# Pre-tensor maps and distance transport

Surjectivity, injectivity, and distance bounds for the Binary Basefold pre-tensor map.
-/

section PreTensorSurjectivity

/-!
## Surjectivity onto the interleaved code via coefficient interleaving.
-/

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

end PreTensorSurjectivity

section PreTensorInjectivity

/-!
## Injectivity of binary folding and the pre-tensor map.
-/

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
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- Two single-step folds at both binary challenges pin the two fiber values:
the butterfly system has determinant `x₁ − x₀ ≠ 0`. -/
lemma fold_legacy_binary_inj (i : Fin r) (h_i : i.val + 1 < ℓ + 𝓡) (h_le : i.val + 1 ≤ ℓ)
    (F G : sDomain 𝔽q β h_ℓ_add_R_rate i → L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + 1, by omega⟩)
    (h0 : fold_legacy 𝔽q β (i := i) (h_i := h_i) (f := F) (r_chal := (0 : L)) y =
          fold_legacy 𝔽q β (i := i) (h_i := h_i) (f := G) (r_chal := (0 : L)) y)
    (h1 : fold_legacy 𝔽q β (i := i) (h_i := h_i) (f := F) (r_chal := (1 : L)) y =
          fold_legacy 𝔽q β (i := i) (h_i := h_i) (f := G) (r_chal := (1 : L)) y)
    (c : Fin 2) :
    F (qMap_total_fiber 𝔽q β (i := i) (steps := 1) (h_i_add_steps := h_i) (y := y) c) =
    G (qMap_total_fiber 𝔽q β (i := i) (steps := 1) (h_i_add_steps := h_i) (y := y) c) := by
  have hsub := qMap_total_fiber_one_sub 𝔽q β i h_i h_le y
  -- name the fiber points and values
  set x₀ := qMap_total_fiber 𝔽q β (i := i) (steps := 1) (h_i_add_steps := h_i) (y := y) 0
    with hx₀
  set x₁ := qMap_total_fiber 𝔽q β (i := i) (steps := 1) (h_i_add_steps := h_i) (y := y) 1
    with hx₁
  have hd : (↑x₁ : L) - (↑x₀ : L) ≠ 0 := by
    rw [← AddSubgroupClass.coe_sub, hsub]
    have hb := (sDomain_basis 𝔽q β h_ℓ_add_R_rate i (by omega)).ne_zero
      ⟨0, by omega⟩
    exact fun hc => hb (by exact_mod_cast Subtype.ext hc)
  unfold fold_legacy at h0 h1
  simp only [one_mul, zero_mul, sub_zero, mul_zero, zero_sub, sub_self] at h0 h1
  -- h0 : F x₀ * x₁ - ... the exact normal forms will be fixed at compile time
  set a := F x₀ - G x₀ with ha
  set b := F x₁ - G x₁ with hb
  have hsys1 : a * x₁.val - b * x₀.val = 0 := by
    simp only [a, b]
    ring_nf
    ring_nf at h0
    linear_combination h0
  have hsys2 : b - a = 0 := by
    simp only [a, b]
    ring_nf
    ring_nf at h1
    linear_combination h1
  have hab : b = a := sub_eq_zero.mp hsys2
  have hzero : a * ((↑x₁ : L) - ↑x₀) = 0 := by
    rw [hab] at hsys1
    linear_combination hsys1
  have ha0 : a = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h hd
  have hb0 : b = 0 := by rw [hab]; exact ha0
  -- conclude per c
  fin_cases c
  · exact sub_eq_zero.mp ha0
  · exact sub_eq_zero.mp hb0

end
end Binius.BinaryBasefold

namespace Binius.BinaryBasefold
noncomputable section
open Finset AdditiveNTT Polynomial Nat

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- Low bits of an index with a high bit attached. -/
lemma bitsOfIndex_combine_castSucc {s : ℕ} (jl : Fin (2 ^ s)) (c : Fin 2)
    (h : c.val * 2 ^ s + jl.val < 2 ^ (s + 1)) (b : Fin s) :
    bitsOfIndex (L := L) (⟨c.val * 2 ^ s + jl.val, h⟩ : Fin (2 ^ (s + 1))) b.castSucc =
    bitsOfIndex (L := L) jl b := by
  unfold bitsOfIndex
  simp only [Fin.coe_castSucc, Nat.getBit_eq_testBit,
    testBit_low_of_mul_two_pow_add c.val jl.val b.val jl.isLt b.isLt]

/-- The top bit of an index with a high bit attached. -/
lemma bitsOfIndex_combine_last {s : ℕ} (jl : Fin (2 ^ s)) (c : Fin 2)
    (h : c.val * 2 ^ s + jl.val < 2 ^ (s + 1)) :
    bitsOfIndex (L := L) (⟨c.val * 2 ^ s + jl.val, h⟩ : Fin (2 ^ (s + 1))) (Fin.last s) =
    if c.val = 1 then (1 : L) else 0 := by
  unfold bitsOfIndex
  have htop : (c.val * 2 ^ s + jl.val).testBit s = c.val.testBit 0 := by
    have := testBit_high_of_mul_two_pow_add c.val jl.val 0 jl.isLt
    simpa using this
  simp only [Fin.val_last, Nat.getBit_eq_testBit, htop, Nat.testBit_zero]
  have hc := c.isLt
  interval_cases h' : c.val <;> simp


set_option maxHeartbeats 8000000 in
/-- **Per-fiber disagreement is visible in the binary-fold rows** (M_y injectivity, induction
form): if all `2^s` binary-challenge iterated folds of `f` and `g` agree at `y`, then `f` and
`g` agree on the entire iterated-quotient fiber of `y`. -/
lemma fiber_agree_of_binary_folds_agree (s : ℕ) (iv : ℕ) (hiv : iv < r)
    (h_s : s < ℓ + 1) (h_is : iv + s < ℓ + 𝓡) (h_le : iv + s ≤ ℓ)
    (f g : sDomain 𝔽q β h_ℓ_add_R_rate ⟨iv, hiv⟩ → L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨iv + s, Nat.lt_trans h_is h_ℓ_add_R_rate⟩)
    (hrows : ∀ j : Fin (2 ^ s),
      iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨iv, hiv⟩)
        (steps := ⟨s, h_s⟩) (h_i_add_steps := h_is) f (bitsOfIndex (L := L) j) y =
      iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨iv, hiv⟩)
        (steps := ⟨s, h_s⟩) (h_i_add_steps := h_is) g (bitsOfIndex (L := L) j) y)
    (idx : Fin (2 ^ s)) :
    f (qMap_total_fiber 𝔽q β (i := ⟨iv, hiv⟩) (steps := s)
        (h_i_add_steps := h_is) (y := y) idx) =
    g (qMap_total_fiber 𝔽q β (i := ⟨iv, hiv⟩) (steps := s)
        (h_i_add_steps := h_is) (y := y) idx) := by
  induction s with
  | zero =>
    have h0 := hrows 0
    conv at h0 =>
      lhs
      unfold iterated_fold_steps
      rw [Fin.dfoldl_zero]
    conv at h0 =>
      rhs
      unfold iterated_fold_steps
      rw [Fin.dfoldl_zero]
    exact h0
  | succ n ih =>
    have h_s' : n < ℓ + 1 := by omega
    have h_is' : iv + n < ℓ + 𝓡 := by omega
    have h_le' : iv + n ≤ ℓ := by omega
    have h_i1 : (⟨iv + n, by omega⟩ : Fin r).val + 1 < ℓ + 𝓡 := by
      show iv + n + 1 < ℓ + 𝓡
      omega
    -- the lifted point one level below the top
    set y' : sDomain 𝔽q β h_ℓ_add_R_rate
        ⟨(⟨iv + n, by omega⟩ : Fin r).val + 1, by
          show iv + n + 1 < r
          omega⟩ :=
      ⟨y.val, by
        have := y.property
        simpa only [Nat.add_assoc] using this⟩ with hy'def
    -- binary-pair rows pin the n-step folds on the two single-step preimages of y
    have hAgree : ∀ (jl : Fin (2 ^ n)) (c : Fin 2),
        iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨iv, hiv⟩)
          (steps := ⟨n, h_s'⟩) (h_i_add_steps := h_is') f (bitsOfIndex (L := L) jl)
          (qMap_total_fiber 𝔽q β (i := ⟨iv + n, by omega⟩) (steps := 1)
            (h_i_add_steps := h_i1) (y := y') c) =
        iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨iv, hiv⟩)
          (steps := ⟨n, h_s'⟩) (h_i_add_steps := h_is') g (bitsOfIndex (L := L) jl)
          (qMap_total_fiber 𝔽q β (i := ⟨iv + n, by omega⟩) (steps := 1)
            (h_i_add_steps := h_i1) (y := y') c) := by
      intro jl c
      have hbound : ∀ cv : Fin 2, cv.val * 2 ^ n + jl.val < 2 ^ (n + 1) := by
        intro cv
        have h1 := cv.isLt
        have h2 := jl.isLt
        calc cv.val * 2 ^ n + jl.val
            < cv.val * 2 ^ n + 2 ^ n := by omega
          _ = (cv.val + 1) * 2 ^ n := by ring
          _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_right _ (by omega)
          _ = 2 ^ (n + 1) := by rw [pow_succ]; ring
      -- specialize the rows at the two combined indices
      have hrow : ∀ cv : Fin 2,
          fold_legacy 𝔽q β (i := ⟨iv + n, by omega⟩) (h_i := h_i1)
            (f := iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := ⟨iv, hiv⟩) (steps := ⟨n, h_s'⟩) (h_i_add_steps := h_is') f
              (bitsOfIndex (L := L) jl))
            (r_chal := if cv.val = 1 then (1 : L) else 0) y' =
          fold_legacy 𝔽q β (i := ⟨iv + n, by omega⟩) (h_i := h_i1)
            (f := iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := ⟨iv, hiv⟩) (steps := ⟨n, h_s'⟩) (h_i_add_steps := h_is') g
              (bitsOfIndex (L := L) jl))
            (r_chal := if cv.val = 1 then (1 : L) else 0) y' := by
        intro cv
        have hr := hrows ⟨cv.val * 2 ^ n + jl.val, hbound cv⟩
        rw [iterated_fold_succ_last_gen 𝔽q β (i := ⟨iv, hiv⟩) (n := n)
            (h_steps := h_s) (h_i_add_steps := h_is) (f := f),
          iterated_fold_succ_last_gen 𝔽q β (i := ⟨iv, hiv⟩) (n := n)
            (h_steps := h_s) (h_i_add_steps := h_is) (f := g)] at hr
        have hinit : (fun b : Fin n => bitsOfIndex (L := L)
            (⟨cv.val * 2 ^ n + jl.val, hbound cv⟩ : Fin (2 ^ (n + 1))) b.castSucc) =
            bitsOfIndex (L := L) jl :=
          funext (bitsOfIndex_combine_castSucc jl cv (hbound cv))
        rw [hinit, bitsOfIndex_combine_last jl cv (hbound cv)] at hr
        exact hr
      have h0 := hrow 0
      have h1 := hrow 1
      simp only [Fin.isValue, Fin.val_zero, Fin.val_one, one_ne_zero, ↓reduceIte,
        OfNat.ofNat_ne_one, if_false, if_true] at h0 h1
      exact fold_legacy_binary_inj 𝔽q β ⟨iv + n, by omega⟩ h_i1
        (by show iv + n + 1 ≤ ℓ; omega) _ _ y' h0 h1 c
    -- peel the fiber index and conclude with the IH at the selected preimage
    have hpeel := qMap_total_fiber_succ_peel_last 𝔽q β
      (i := (⟨iv, by omega⟩ : Fin ℓ)) (n := n)
      (h_i_add_steps := by show iv + (n + 1) ≤ ℓ; omega)
      (y' := y) (idx := idx)
    rw [hpeel]
    exact ih h_s' h_is' h_le'
      (qMap_total_fiber 𝔽q β (i := ⟨iv + n, by omega⟩) (steps := 1)
        (h_i_add_steps := h_i1) (y := y')
        ⟨idx.val / 2 ^ n, by
          have hb : idx.val < 2 ^ n * 2 := Nat.lt_of_lt_of_eq idx.isLt (by rw [pow_succ])
          exact Nat.div_lt_of_lt_mul hb⟩)
      (fun jl => hAgree jl _)
      ⟨idx.val % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩

end
end Binius.BinaryBasefold

end PreTensorInjectivity

section PreTensorFar

/-!
## Transport of distance bounds through the pre-tensor map.
-/

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
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- **Per-fiber disagreement is column-visible** (Brick-Y packaging): the per-fiber
disagreement set of `f, g` injects into the disagreeing columns of their pre-tensor stacks. -/
lemma pair_fiberwiseDistance_le_interleaved_hammingDist
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
      (by simpa using h_destIdx) h_destIdx_le f g ≤
    hammingDist
      (Code.interleaveWordStack
        (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f))
      (Code.interleaveWordStack
        (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g)) := by
  classical
  obtain ⟨dv, hdvlt⟩ := destIdx
  simp only at h_destIdx
  subst h_destIdx
  have hle' : i.val + steps ≤ ℓ := by simpa using h_destIdx_le
  have h𝓡 := Nat.pos_of_neZero 𝓡
  unfold pair_fiberwiseDistance
  rw [hammingDist]
  apply Finset.card_le_card
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  rw [mem_fiberwiseDisagreementSetPerFiber] at hy
  intro hcols
  apply absurd hy
  push_neg
  intro idx
  -- all interleaved columns equal at y → all binary rows equal at y
  have hrows : ∀ j : Fin (2 ^ steps),
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i.val, by omega⟩) (steps := steps)
        (destIdx := ⟨i.val + steps, hdvlt⟩)
        (h_destIdx := rfl) (h_destIdx_le := h_destIdx_le)
        (f := f) (r_challenges := bitsOfIndex (L := L) j) y =
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i.val, by omega⟩) (steps := steps)
        (destIdx := ⟨i.val + steps, hdvlt⟩)
        (h_destIdx := rfl) (h_destIdx_le := h_destIdx_le)
        (f := g) (r_challenges := bitsOfIndex (L := L) j) y := by
    intro j
    have := congrFun hcols j
    simpa [Code.interleaveWordStack, preTensorCombine_WordStack] using this
  -- convert to steps level and apply Brick Y
  have hfib := fiber_agree_of_binary_folds_agree 𝔽q β steps i.val (by omega)
    (by omega) (by omega) (by omega)
    f g y
    (by
      intro j
      exact hrows j)
    idx
  -- fiberEvaluations applies f at the lifted fiber point; the lift is `⟨y.val, _⟩ ≡ y` by eta
  exact hfib


set_option maxHeartbeats 8000000 in
/-- **Lemma 4.22, far direction**: joint proximity of the pre-tensor stack bounds the
fiberwise distance. Combines the Brick-X lift (every interleaved codeword is a pre-tensor
stack of a codeword) with the Brick-Y column-visibility bound. -/
lemma fiberwiseDistance_le_of_jointProximityNat
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (e : ℕ)
    (h : jointProximityNat
      (C := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
        Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L)))
      (u := preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i) e) :
    fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
      (by simpa using h_destIdx) h_destIdx_le f_i ≤ e := by
  classical
  set C_dest : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L) :=
    (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
      Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L)) with hC
  have hne : Nonempty (interleavedCodeSet (κ := Fin (2 ^ steps)) (C := C_dest)) := by
    refine ⟨⟨(0 : Matrix (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) (Fin (2 ^ steps)) L), ?_⟩⟩
    intro k
    exact (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx).zero_mem
  obtain ⟨V, hV_mem, hV_eq⟩ := @exists_closest_codeword_of_Nonempty_Code
    (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) _ (Fin (2 ^ steps) → L) _
    (interleavedCodeSet (κ := Fin (2 ^ steps)) (C := C_dest)) hne
    (Code.interleaveWordStack
      (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i))
  obtain ⟨g, hg_mem, hg_eq⟩ := exists_codeword_preTensorCombine_eq_of_rows_mem 𝔽q β
    i steps h_destIdx h_destIdx_le (fun k y => V y k) (fun k => hV_mem k)
  have hVpack : Code.interleaveWordStack
      (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g) = V := by
    rw [hg_eq]
    rfl
  -- the Nat-level chain
  have h1 : fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
      (by simpa using h_destIdx) h_destIdx_le f_i ≤
      pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        (by simpa using h_destIdx) h_destIdx_le f_i g := by
    unfold fiberwiseDistance
    exact Nat.sInf_le ⟨⟨g, by simpa [C_dest] using hg_mem⟩, Set.mem_univ _, rfl⟩
  have h2 := pair_fiberwiseDistance_le_interleaved_hammingDist 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le f_i g
  rw [hVpack] at h2
  -- ℕ∞ extraction of the closest distance
  have h3 : (hammingDist
      (Code.interleaveWordStack
        (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i)) V : ℕ∞) ≤
      (e : ℕ∞) := by
    have hh := h
    unfold jointProximityNat at hh
    calc (hammingDist _ V : ℕ∞)
        = Δ₀((Code.interleaveWordStack
            (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i)), V) := by
          rfl
      _ = Δ₀((Code.interleaveWordStack
            (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i)),
            (interleavedCodeSet (C := C_dest))) := hV_eq
      _ ≤ (e : ℕ∞) := hh
  have h3' : hammingDist
      (Code.interleaveWordStack
        (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i)) V ≤ e := by
    exact_mod_cast h3
  omega

/- A destination-radius bound on the fiberwise distance is enough to recover both conjuncts
of `fiberwiseClose`. The source UDR conjunct follows by choosing a closest source codeword
and applying the fiberwise-to-Hamming bound. -/
set_option maxHeartbeats 1200000 in
/-- Source Hamming distance is bounded by the number of bad quotient fibers times the fiber
size. Local port of the (currently commented-out) `Code.lean` lemma onto the per-fiber
disagreement surface. -/
lemma hammingDist_le_pair_fiberwiseDistance_mul_two_pow_steps
    (i : Fin ℓ) (steps : ℕ) [NeZero steps] {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    Δ₀(f, g) ≤
      (pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le f g) * 2 ^ steps := by
  classical
  -- Hoist destIdx-free bound proofs so the `subst` below is not self-referential.
  have hle : i.val + steps ≤ ℓ := by
    rw [← h_destIdx]
    exact h_destIdx_le
  have hi_lt_r : i.val < r := by
    exact lt_r_of_lt_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.isLt
  have hlt_r : i.val + steps < r := by
    have hR := h_ℓ_add_R_rate
    omega
  have hdest : destIdx = (⟨i.val + steps, hlt_r⟩ : Fin r) := Fin.eq_of_val_eq h_destIdx
  subst hdest
  have h_i_add_steps : i.val + steps ≤ ℓ := hle
  let d_fw := pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := (⟨i, by omega⟩ : Fin r))
    (destIdx := (⟨i.val + steps, hlt_r⟩ : Fin r))
    (steps := steps) h_destIdx h_destIdx_le f g
  have hNat : hammingDist f g ≤ d_fw * 2 ^ steps := by
    set ΔH := Finset.filter (fun x => f x ≠ g x) Finset.univ
    have h_dist_eq_card : hammingDist f g = ΔH.card := by
      simp only [hammingDist, ne_eq, ΔH]
    rw [h_dist_eq_card]
    set Y_bad := fiberwiseDisagreementSetPerFiber 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (⟨i, by omega⟩ : Fin r))
      (destIdx := (⟨i.val + steps, hlt_r⟩ : Fin r))
      (steps := steps) h_destIdx h_destIdx_le f g
    let fiberSet : (sDomain 𝔽q β h_ℓ_add_R_rate) (⟨i.val + steps, hlt_r⟩ : Fin r) →
        Finset ((sDomain 𝔽q β h_ℓ_add_R_rate) (⟨i.val, hi_lt_r⟩ : Fin r)) := fun y =>
      (Set.image
        (qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (⟨i.val, hi_lt_r⟩ : Fin r)) (steps := steps)
          (h_i_add_steps := by
            simp only
            exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
          (y := y))
        (Set.univ : Set (Fin (2 ^ steps)))).toFinset
    have h_subset : ΔH ⊆ Finset.biUnion Y_bad (t := fiberSet) := by
      intro x hx
      simp only [ΔH, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      let y_of_x := AdditiveNTT.iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
        i steps h_i_add_steps x
      apply Finset.mem_biUnion.mpr
      refine ⟨y_of_x, ?_, ?_⟩
      · rw [mem_fiberwiseDisagreementSetPerFiber]
        let idx := pointToIterateQuotientIndex 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (ℓ + 1)))
          (steps := steps) h_i_add_steps x
        refine ⟨idx, ?_⟩
        have hres :=
          (is_fiber_iff_generates_quotient_point 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_i_add_steps
            (x := x) (y := y_of_x)).mp rfl
        have hf :
            fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := (⟨i.val, hi_lt_r⟩ : Fin r))
              (destIdx := (⟨i.val + steps, hlt_r⟩ : Fin r)) (steps := steps)
              (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
              (f := f) (y := y_of_x) idx = f x := by
          rw [fiberEvaluations_apply_eq_qMap_total_fiber 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := (⟨i.val, hi_lt_r⟩ : Fin r)) (steps := steps)
            (h_i_add_steps_le := h_i_add_steps) (h_i_add_steps_lt_r := hlt_r)
            (f := f) (y := y_of_x) (idx := idx)]
          simpa using congrArg f hres
        have hg :
            fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := (⟨i.val, hi_lt_r⟩ : Fin r))
              (destIdx := (⟨i.val + steps, hlt_r⟩ : Fin r)) (steps := steps)
              (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
              (f := g) (y := y_of_x) idx = g x := by
          rw [fiberEvaluations_apply_eq_qMap_total_fiber 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := (⟨i.val, hi_lt_r⟩ : Fin r)) (steps := steps)
            (h_i_add_steps_le := h_i_add_steps) (h_i_add_steps_lt_r := hlt_r)
            (f := g) (y := y_of_x) (idx := idx)]
          simpa using congrArg g hres
        intro hfg
        exact hx (by simpa [hf, hg] using hfg)
      · set idx := pointToIterateQuotientIndex 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (ℓ + 1)))
          (steps := steps) h_i_add_steps x
        have hres :=
          (is_fiber_iff_generates_quotient_point 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_i_add_steps
            (x := x) (y := y_of_x)).mp rfl
        have hmem :
            x ∈ Set.image
              (qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (i := (⟨i.val, hi_lt_r⟩ : Fin r)) (steps := steps)
                (h_i_add_steps := by
                  simp only
                  exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
                (y := y_of_x))
              (Set.univ : Set (Fin (2 ^ steps))) := by
          exact ⟨idx, Set.mem_univ idx, hres⟩
        change x ∈ fiberSet y_of_x
        dsimp only [fiberSet]
        rw [Set.mem_toFinset]
        exact hmem
    refine (Finset.card_le_card h_subset).trans ?_
    rw [Finset.card_biUnion]
    · have h_each : ∀ y ∈ Y_bad, (fiberSet y).card = 2 ^ steps := by
        intro y hy
        have h := card_qMap_total_fiber 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_i_add_steps y
        have h_card :
            (fiberSet y).card =
              Fintype.card
                (Set.image
                  (qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                    (i := (⟨i.val, hi_lt_r⟩ : Fin r)) (steps := steps)
                    (h_i_add_steps := by
                      simp only
                      exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
                    (y := y))
                  (Set.univ : Set (Fin (2 ^ steps)))) := by
          dsimp only [fiberSet]
          exact Set.toFinset_card
            (s := Set.image
              (qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                (i := (⟨i.val, hi_lt_r⟩ : Fin r)) (steps := steps)
                (h_i_add_steps := by
                  simp only
                  exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
                (y := y))
              (Set.univ : Set (Fin (2 ^ steps))))
        exact h_card.trans h
      rw [Finset.sum_congr rfl h_each]
      simp [Y_bad, d_fw, pair_fiberwiseDistance]
    · intro y₁ hy₁ y₂ hy₂ hy_ne
      have h :=
        qMap_total_fiber_disjoint 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (steps := steps) (h_i_add_steps := h_i_add_steps)
        (y₁ := y₁) (y₂ := y₂) hy_ne
      simpa [fiberSet] using h
  exact hNat

lemma pairUDRClose_of_pairFiberwiseClose
    (i : Fin ℓ) (steps : ℕ) [NeZero steps] {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_fw_dist_lt : pair_fiberwiseClose 𝔽q β
      (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
      h_destIdx h_destIdx_le f g) :
    pair_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (h_i := Nat.le_of_lt i.isLt) (f := f) (g := g) := by
  unfold pair_fiberwiseClose at h_fw_dist_lt
  unfold pair_UDRClose
  set d_fw := pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := (⟨i, by omega⟩ : Fin r)) (destIdx := destIdx) (steps := steps)
    h_destIdx h_destIdx_le f g
  have h_le : 2 * Δ₀(f, g) ≤ 2 * (d_fw * 2 ^ steps) := by
    apply Nat.mul_le_mul_left
    exact hammingDist_le_pair_fiberwiseDistance_mul_two_pow_steps 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le f g
  set d_cur := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := (⟨i, by omega⟩ : Fin r))
  set d_next := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx)
  have h_2_fw_dist_le : 2 * d_fw ≤ d_next - 1 := by omega
  have hmul : 2 * (d_fw * 2 ^ steps) ≤ d_next * 2 ^ steps - 2 ^ steps := by
    rw [← mul_assoc]
    conv_rhs =>
      rw (occs := [2]) [← one_mul (2 ^ steps)]
      rw [← Nat.sub_mul (n := d_next) (m := 1) (k := 2 ^ steps)]
    exact Nat.mul_le_mul_right _ h_2_fw_dist_le
  have hdist_rel : d_next * 2 ^ steps - 2 ^ steps = d_cur - 1 := by
    dsimp only [d_next, d_cur]
    rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := destIdx) (h_i := h_destIdx_le),
      BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (⟨i, by omega⟩ : Fin r)) (h_i := Nat.le_of_lt i.isLt)]
    simp only [add_tsub_cancel_right]
    rw [Nat.add_mul, Nat.sub_mul, ← Nat.pow_add, ← Nat.pow_add]
    have h_exp1 : ℓ + 𝓡 - destIdx.val + steps = ℓ + 𝓡 - i.val := by omega
    have h_exp2 : ℓ - destIdx.val + steps = ℓ - i.val := by omega
    rw [h_exp1, h_exp2]
    omega
  have h_le_pred : 2 * (d_fw * 2 ^ steps) ≤ d_cur - 1 := by
    omega
  have hcur_pos : 0 < d_cur := by
    dsimp only [d_cur]
    rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (⟨i, by omega⟩ : Fin r)) (h_i := Nat.le_of_lt i.isLt)]
    omega
  exact lt_of_le_of_lt (le_trans h_le h_le_pred)
    (Nat.sub_one_lt (Nat.ne_of_gt hcur_pos))

lemma fiberwiseClose_of_fiberwiseDistance_le_uniqueDecodingRadius
    (i : Fin ℓ) (steps : ℕ) [NeZero steps] {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_le_udr :
      fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        (by simpa using h_destIdx) h_destIdx_le f_i ≤
      Code.uniqueDecodingRadius
        (C := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
          Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L)))) :
    fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := by
        simpa using h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i) := by
  classical
  have h_destIdx_fin : destIdx = (⟨i, by omega⟩ : Fin r).val + steps := by
    simpa using h_destIdx
  set C_dest : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L) :=
    (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
      Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L)) with hC_dest
  have h_dist_pos : 0 < ‖C_dest‖₀ := by
    have h_pos : 0 <
        BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx := by
      simp [BBF_CodeDistance_eq (L := L) 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) (h_i := h_destIdx_le)]
    simpa [C_dest, BBF_CodeDistance] using h_pos
  haveI : NeZero ‖C_dest‖₀ := NeZero.of_pos h_dist_pos
  have h_dest_lt :
      2 * fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
          h_destIdx_fin h_destIdx_le f_i <
        BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) := by
    have h' := (Code.UDRClose_iff_two_mul_proximity_lt_d_UDR (C := C_dest)).1 (by
      simpa [C_dest] using h_le_udr)
    simpa [C_dest, BBF_CodeDistance] using h'
  obtain ⟨g, hg_mem, hg_min⟩ := exists_fiberwiseClosestCodeword 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := (⟨i, by omega⟩ : Fin r)) (destIdx := destIdx) (steps := steps)
    h_destIdx_fin h_destIdx_le f_i
  have h_pair_close : pair_fiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := (⟨i, by omega⟩ : Fin r))
      (destIdx := destIdx) (steps := steps) (h_destIdx := h_destIdx_fin)
      (h_destIdx_le := h_destIdx_le) (f := f_i) (g := g) := by
    dsimp only [pair_fiberwiseClose]
    rw [← hg_min]
    exact h_dest_lt
  have h_pair_udr := pairUDRClose_of_pairFiberwiseClose 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    (destIdx := destIdx) (steps := steps) (h_destIdx := h_destIdx_fin)
    (h_destIdx_le := h_destIdx_le) (f := f_i) (g := g)
    (h_fw_dist_lt := h_pair_close)
  have h_source_lt :
      2 * Δ₀(f_i, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (⟨i, by omega⟩ : Fin r))) <
        BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (⟨i, by omega⟩ : Fin r)) := by
    calc
      2 * Δ₀(f_i, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (⟨i, by omega⟩ : Fin r))) ≤
          2 * Δ₀(f_i, g) := by
        rw [ENat.mul_le_mul_left_iff (ha := by
            simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true])
          (h_top := by simp only [ne_eq, ENat.ofNat_ne_top, not_false_eq_true])]
        exact Code.distFromCode_le_dist_to_mem
          (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (⟨i, by omega⟩ : Fin r)) (u := f_i) (v := g) hg_mem
      _ < _ := by
        exact_mod_cast h_pair_udr
  exact ⟨h_source_lt, h_dest_lt⟩

/-- Lemma 4.22, contrapositive form used by Proposition 4.21 case 2 assembly. -/
lemma not_jointProximityNat_of_not_fiberwiseClose
    (i : Fin ℓ) (steps : ℕ) [NeZero steps] {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_far : ¬ fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f := f_i)) :
    ¬ jointProximityNat
      (C := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
        Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L)))
      (u := preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i)
      (Code.uniqueDecodingRadius
        (C := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
          Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L)))) := by
  intro h_joint
  have h_le := fiberwiseDistance_le_of_jointProximityNat 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le f_i
    (Code.uniqueDecodingRadius
      (C := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
        Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L)))) h_joint
  exact h_far (fiberwiseClose_of_fiberwiseDistance_le_uniqueDecodingRadius 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le f_i h_le)

end
end Binius.BinaryBasefold

end PreTensorFar
