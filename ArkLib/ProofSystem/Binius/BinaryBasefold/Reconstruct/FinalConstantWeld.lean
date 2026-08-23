/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Relations
import ArkLib.ProofSystem.Binius.BinaryBasefold.Reconstruct.FinalOracleBridge
import ArkLib.ProofSystem.Binius.BinaryBasefold.Reconstruct.IteratedFoldToLevel

/-!
# The final-constant weld (issue #327)

The coefficient-level composition route discharging the final-sumcheck relation-out
obligation: `FinalOracleBridge` (getLastOracle = prefix fold) →
`iterated_fold_advances_evaluation_poly_nat` (twice) → `iteratedRefineCoeffs_comp` (NEW:
refinement composition over an appended challenge vector, via the tensor-weight splitting
`multilinearWeight_append`) → `getFoldingChallenges_append_finalBlock` →
`intermediateEvaluationPoly_last_iteratedRefineCoeffs_eval`.

The `Nat.testBit` block-decomposition lemmas at the top are generic and candidates for
upstreaming into `ArkLib/Data/Nat/Bitwise.lean`.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace Binius.BinaryBasefold
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open scoped NNReal

/-- Low bits of `a * 2^s + b` (with `b < 2^s`) are the bits of `b`. -/
lemma testBit_low_of_mul_two_pow_add {s : ℕ} (a b j : ℕ) (hb : b < 2 ^ s) (hj : j < s) :
    (a * 2 ^ s + b).testBit j = b.testBit j := by
  have hmod : (a * 2 ^ s + b) % 2 ^ s = b := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  have h1 : ((a * 2 ^ s + b) % 2 ^ s).testBit j = (a * 2 ^ s + b).testBit j := by
    rw [Nat.testBit_mod_two_pow]
    simp [hj]
  rw [← h1, hmod]

/-- High bits of `a * 2^s + b` (with `b < 2^s`) are the bits of `a`. -/
lemma testBit_high_of_mul_two_pow_add {s : ℕ} (a b j : ℕ) (hb : b < 2 ^ s) :
    (a * 2 ^ s + b).testBit (s + j) = a.testBit j := by
  have hdiv : (a * 2 ^ s + b) / 2 ^ s = a := by
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos s), Nat.div_eq_of_lt hb, Nat.add_zero]
  rw [Nat.add_comm s j, ← Nat.testBit_div_two_pow, hdiv]

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

/-- **Tensor-weight splitting over an appended challenge vector.** -/
lemma multilinearWeight_append {s₁ s₂ : ℕ} (r₁ : Fin s₁ → L) (r₂ : Fin s₂ → L)
    (x₁ : Fin (2 ^ s₁)) (x₂ : Fin (2 ^ s₂))
    (h : x₂.val * 2 ^ s₁ + x₁.val < 2 ^ (s₁ + s₂)) :
    multilinearWeight (Fin.append r₁ r₂) ⟨x₂.val * 2 ^ s₁ + x₁.val, h⟩ =
      multilinearWeight r₁ x₁ * multilinearWeight r₂ x₂ := by
  unfold multilinearWeight
  rw [Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [Fin.append_left]
    have hbit : (x₂.val * 2 ^ s₁ + x₁.val).testBit (Fin.castAdd s₂ j).val
        = x₁.val.testBit j.val := by
      rw [Fin.val_castAdd]
      exact testBit_low_of_mul_two_pow_add x₂.val x₁.val j.val x₁.isLt j.isLt
    simp only [hbit]
  · refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [Fin.append_right]
    have hbit : (x₂.val * 2 ^ s₁ + x₁.val).testBit (Fin.natAdd s₁ j).val
        = x₂.val.testBit j.val := by
      rw [Fin.val_natAdd]
      exact testBit_high_of_mul_two_pow_add x₂.val x₁.val j.val x₁.isLt
    simp only [hbit]

/-- **Composition law for `iteratedRefineCoeffs`.** -/
lemma iteratedRefineCoeffs_comp {i mid dest : Fin r} (s₁ s₂ : ℕ)
    (h_mid : mid.val = i.val + s₁) (h_mid_le : mid ≤ ℓ)
    (h_dest : dest.val = mid.val + s₂) (h_dest_le : dest ≤ ℓ)
    (h_dest' : dest.val = i.val + (s₁ + s₂))
    (coeffs : Fin (2 ^ (ℓ - i.val)) → L) (r₁ : Fin s₁ → L) (r₂ : Fin s₂ → L) :
    iteratedRefineCoeffs (𝓡 := 𝓡) (i := mid) (destIdx := dest) s₂ h_dest h_dest_le
      (iteratedRefineCoeffs (𝓡 := 𝓡) (i := i) (destIdx := mid) s₁ h_mid h_mid_le coeffs r₁) r₂ =
    iteratedRefineCoeffs (𝓡 := 𝓡) (i := i) (destIdx := dest) (s₁ + s₂) h_dest' h_dest_le
      coeffs (Fin.append r₁ r₂) := by
  funext j
  unfold iteratedRefineCoeffs
  simp only [Finset.mul_sum]
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (i := fun p => (⟨p.1.val * 2 ^ s₁ + p.2.val, by
      have h1 := p.1.isLt
      have h2 := p.2.isLt
      have hpow : 2 ^ (s₁ + s₂) = 2 ^ s₁ * 2 ^ s₂ := by rw [pow_add]
      rw [hpow]
      calc p.1.val * 2 ^ s₁ + p.2.val
          < p.1.val * 2 ^ s₁ + 2 ^ s₁ := by omega
        _ = (p.1.val + 1) * 2 ^ s₁ := by ring
        _ ≤ 2 ^ s₂ * 2 ^ s₁ := Nat.mul_le_mul_right _ (by omega)
        _ = 2 ^ s₁ * 2 ^ s₂ := by ring⟩ : Fin (2 ^ (s₁ + s₂))))
    (j := fun z => (⟨z.val / 2 ^ s₁, by
      have hz' : z.val < 2 ^ s₁ * 2 ^ s₂ := by
        rw [← pow_add]; exact z.isLt
      exact Nat.div_lt_of_lt_mul hz'⟩,
      ⟨z.val % 2 ^ s₁, Nat.mod_lt _ (Nat.two_pow_pos s₁)⟩))
    ?_ ?_ ?_ ?_ ?_
  · intro p _; exact Finset.mem_univ _
  · intro z _; exact Finset.mem_univ _
  · -- left inverse: j (i p) = p
    intro p _
    refine Prod.ext ?_ ?_
    · ext
      show (p.1.val * 2 ^ s₁ + p.2.val) / 2 ^ s₁ = p.1.val
      rw [Nat.mul_comm p.1.val, Nat.mul_add_div (Nat.two_pow_pos s₁),
        Nat.div_eq_of_lt p.2.isLt, Nat.add_zero]
    · ext
      show (p.1.val * 2 ^ s₁ + p.2.val) % 2 ^ s₁ = p.2.val
      rw [Nat.mul_comm p.1.val, Nat.mul_add_mod, Nat.mod_eq_of_lt p.2.isLt]
  · -- right inverse: i (j z) = z
    intro z _
    ext
    show z.val / 2 ^ s₁ * 2 ^ s₁ + z.val % 2 ^ s₁ = z.val
    rw [Nat.mul_comm]
    exact Nat.div_add_mod z.val (2 ^ s₁)
  · -- summand equality
    intro p _
    have hidx : (j.val * 2 ^ s₂ + p.1.val) * 2 ^ s₁ + p.2.val
        = j.val * 2 ^ (s₁ + s₂) + (p.1.val * 2 ^ s₁ + p.2.val) := by
      rw [pow_add]; ring
    simp only [hidx]
    rw [multilinearWeight_append (L := L) r₁ r₂ p.2 p.1]
    ring

end
end Binius.BinaryBasefold

namespace Binius.BinaryBasefold
noncomputable section

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]


/-- Steps/challenge congruence for `iteratedRefineCoeffs`. -/
lemma iteratedRefineCoeffs_congr_steps {i dest : Fin r} (s s' : ℕ) (hs : s = s')
    (h_dest : dest.val = i.val + s) (h_dest_le : dest ≤ ℓ)
    (h_dest' : dest.val = i.val + s')
    (coeffs : Fin (2 ^ (ℓ - i.val)) → L) (rc : Fin s → L) (rc' : Fin s' → L)
    (hrc : ∀ idx : Fin s, rc idx = rc' ⟨idx.val, hs ▸ idx.isLt⟩) :
    iteratedRefineCoeffs (𝓡 := 𝓡) (i := i) (destIdx := dest) s h_dest h_dest_le coeffs rc =
    iteratedRefineCoeffs (𝓡 := 𝓡) (i := i) (destIdx := dest) s' h_dest' h_dest_le coeffs rc' := by
  subst hs
  have hrc' : rc = rc' := by
    funext idx
    rw [hrc idx]
  rw [hrc']

end
end Binius.BinaryBasefold

namespace Binius.BinaryBasefold
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open scoped NNReal

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

set_option maxHeartbeats 4000000 in
seal sDomain qMap_total_fiber normalizedW intermediateEvaluationPoly in
/-- **The final-constant weld (Lemma A).** Under strict oracle-folding consistency at the
final frontier, folding `getLastOracle` through the final `ϑ`-challenge block is constantly
`t(challenges)`. -/
lemma getLastOracle_finalFold_eq_eval
    (t : MultilinearPoly L ℓ)
    (challenges : Fin (Fin.last ℓ) → L)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_oracle : strictOracleFoldingConsistencyProp 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := t) (i := Fin.last ℓ)
      (challenges := challenges) (oStmt := oStmt))
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨ℓ, by
      have := Nat.pos_of_neZero 𝓡; omega⟩)) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨ℓ - ϑ, by have := Nat.pos_of_neZero 𝓡; omega⟩) (steps := ϑ)
      (destIdx := ⟨ℓ, by have := Nat.pos_of_neZero 𝓡; omega⟩)
      (h_destIdx := by
        simp only
        have : ϑ ≤ ℓ := Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out
        omega)
      (h_destIdx_le := by simp only [Fin.mk_le_mk]; omega)
      (f := getLastOracle (h_destIdx := by
          rw [getLastOracleDomainIndex_last (ℓ := ℓ) (ϑ := ϑ)])
        (oracleFrontierIdx := Fin.last ℓ)
        𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmt))
      (r_challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
        (i := Fin.last ℓ) challenges (ℓ - ϑ) (h := by
          simp only [Fin.val_last]
          have : ϑ ≤ ℓ := Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out
          omega))
      y = t.val.eval challenges := by
  have hϑℓ : ϑ ≤ ℓ := Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out
  have h𝓡 : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
  -- the level-0 coefficients
  set coeffs₀ : Fin (2 ^ ℓ) → L :=
    fun ω => t.val.eval (statementOrderBitsOfIndex (L := L) ω) with hcoeffs₀
  -- Step 1: bridge — getLastOracle is the prefix fold of f₀.
  have h_bridge := strictOracleFoldingConsistency_last_getLastOracle_eq_prefixFold 𝔽q β
    (t := t) (challenges := challenges) (oStmt := oStmt) h_oracle
  simp only at h_bridge
  rw [h_bridge]
  -- Step 2: f₀ is the raw-eval of the level-0 intermediate evaluation polynomial.
  have h_base := intermediate_poly_P_base 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (h_ℓ := by omega) (coeffs := coeffs₀)
  have h_f₀ :
      (fun (x : sDomain 𝔽q β h_ℓ_add_R_rate 0) =>
        (polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
          (fun ω => t.val.eval (statementOrderBitsOfIndex (L := L) ω))).val.eval x.val) =
      (fun (x : sDomain 𝔽q β h_ℓ_add_R_rate 0) =>
        (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
          ⟨(0 : Fin r).val, by have h0 : (0 : Fin r).val = 0 := rfl; omega⟩ coeffs₀).eval x.val) := by
    funext x
    exact (congrArg (fun p => Polynomial.eval x.val p) h_base).symm
  rw [h_f₀]
  -- Step 3: advance the prefix fold to level ℓ - ϑ.
  have h_adv1 := iterated_fold_advances_evaluation_poly_nat 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (steps := ℓ - ϑ)
    (destIdx := ⟨ℓ - ϑ, by omega⟩)
    (h_destIdx := by simp only [Fin.val_zero, Nat.zero_add])
    (h_destIdx_le := by simp only [Fin.mk_le_mk]; omega)
    (coeffs := coeffs₀)
    (r_challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ℓ - ϑ)
      (i := Fin.last ℓ) challenges 0 (h := by
        simp only [zero_add, Fin.val_last]
        omega))
  rw [h_adv1]
  -- Step 4: advance the final ϑ-fold to level ℓ.
  have h_adv2 := iterated_fold_advances_evaluation_poly_nat 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨ℓ - ϑ, by omega⟩) (steps := ϑ)
    (destIdx := ⟨ℓ, by omega⟩)
    (h_destIdx := by simp only; omega)
    (h_destIdx_le := by simp only [Fin.mk_le_mk]; omega)
    (coeffs := iteratedRefineCoeffs (𝓡 := 𝓡) (i := 0) (destIdx := ⟨ℓ - ϑ, by omega⟩)
      (ℓ - ϑ) (by simp only [Fin.val_zero, Nat.zero_add]) (by simp only [Fin.mk_le_mk]; omega)
      coeffs₀
      (getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ℓ - ϑ)
        (i := Fin.last ℓ) challenges 0 (h := by
          simp only [zero_add, Fin.val_last]
          omega)))
    (r_challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
      (i := Fin.last ℓ) challenges (ℓ - ϑ) (h := by
        simp only [Fin.val_last]
        omega))
  rw [h_adv2]
  -- Step 5: compose the two refinements.
  rw [iteratedRefineCoeffs_comp
    (i := 0) (mid := ⟨ℓ - ϑ, by omega⟩) (dest := ⟨ℓ, by omega⟩)
    (s₁ := ℓ - ϑ) (s₂ := ϑ)
    (h_mid := by simp only [Fin.val_zero, Nat.zero_add])
    (h_mid_le := by simp only [Fin.mk_le_mk]; omega)
    (h_dest := by simp only; omega)
    (h_dest_le := by simp only [Fin.mk_le_mk]; omega)
    (h_dest' := by simp only [Fin.val_zero, Nat.zero_add]; omega)]
  -- Step 6: convert the appended challenge vector to fold-order challenges.
  rw [iteratedRefineCoeffs_congr_steps
    (i := 0) (dest := ⟨ℓ, by omega⟩)
    (s := (ℓ - ϑ) + ϑ) (s' := ℓ) (hs := by omega)
    (h_dest := by simp only [Fin.val_zero, Nat.zero_add]; omega)
    (h_dest_le := by simp only [Fin.mk_le_mk]; omega)
    (h_dest' := by simp only [Fin.val_zero, Nat.zero_add])
    (rc' := foldOrderChallenges (ℓ := ℓ) (L := L) (i := Fin.last ℓ) challenges)
    (hrc := by
      intro idx
      exact congrFun (getFoldingChallenges_append_finalBlock (r := r) (𝓡 := 𝓡)
        (challenges := challenges)) idx)]
  -- Step 7+8: the endpoint evaluation and the multilinear sum identity.
  have h_end := intermediateEvaluationPoly_last_iteratedRefineCoeffs_eval 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (coeffs := coeffs₀)
    (r_challenges := foldOrderChallenges (ℓ := ℓ) (L := L) (i := Fin.last ℓ) challenges)
    (y := y)
  have h_tail : (∑ x : Fin (2 ^ ℓ), multilinearWeight
      (foldOrderChallenges (ℓ := ℓ) (L := L) (i := Fin.last ℓ) challenges) x * coeffs₀ x)
      = t.val.eval challenges :=
    (multilinear_eval_eq_sum_statementOrderBitsOfIndex (t := t) (r := challenges)).symm
  exact Eq.trans h_end h_tail

end
end Binius.BinaryBasefold

#print axioms Binius.BinaryBasefold.multilinearWeight_append
#print axioms Binius.BinaryBasefold.iteratedRefineCoeffs_comp
#print axioms Binius.BinaryBasefold.getLastOracle_finalFold_eq_eval

namespace Binius.BinaryBasefold
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open scoped NNReal

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

set_option maxHeartbeats 4000000 in
/-- **Index-general form of the final-constant weld.** -/
lemma getLastOracle_finalFold_eq_eval'
    (t : MultilinearPoly L ℓ)
    (challenges : Fin (Fin.last ℓ) → L)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (h_oracle : strictOracleFoldingConsistencyProp 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := t) (i := Fin.last ℓ)
      (challenges := challenges) (oStmt := oStmt))
    {curIdx destIdx : Fin r}
    (hcur : curIdx.val = ℓ - ϑ) (hdest : destIdx.val = curIdx.val + ϑ)
    (hdest_le : destIdx ≤ ℓ)
    (h_destIdx_oracle : curIdx.val =
      (getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ)).val)
    (hpos : ℓ - ϑ + ϑ ≤ ℓ)
    (rchal : Fin ϑ → L)
    (hrchal : rchal = getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ)
      (i := Fin.last ℓ) challenges curIdx.val (h := by
        simp only [Fin.val_last]
        omega))
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := curIdx) (steps := ϑ) (destIdx := destIdx)
      (h_destIdx := hdest) (h_destIdx_le := hdest_le)
      (f := getLastOracle (h_destIdx := h_destIdx_oracle)
        (oracleFrontierIdx := Fin.last ℓ)
        𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmt))
      (r_challenges := rchal)
      y = t.val.eval challenges := by
  have hϑℓ : ϑ ≤ ℓ := Nat.le_of_dvd (Nat.pos_of_neZero ℓ) hdiv.out
  have h𝓡 : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
  subst hrchal
  obtain ⟨cv, hcv⟩ := curIdx
  obtain ⟨dv, hdv⟩ := destIdx
  simp only at hcur hdest
  subst hcur
  have hdv' : dv = ℓ := by omega
  subst hdv'
  exact getLastOracle_finalFold_eq_eval 𝔽q β (t := t) (challenges := challenges)
    (oStmt := oStmt) h_oracle (y := y)

end
end Binius.BinaryBasefold

#print axioms Binius.BinaryBasefold.getLastOracle_finalFold_eq_eval'
