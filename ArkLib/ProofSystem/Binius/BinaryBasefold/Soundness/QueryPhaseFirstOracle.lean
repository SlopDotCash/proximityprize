/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhasePrelims

/-!
## Binary Basefold Query-Phase First-Oracle Alignment

This module keeps the zero-step first-oracle consequence of
`strictOracleFoldingConsistencyProp` separate from the core query-phase preliminaries.
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
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
noncomputable section
variable [hdiv : Fact (ϑ ∣ ℓ)]

namespace QueryPhase

private lemma iterated_fold_congr_steps_fun
    (i : Fin r) {destIdx : Fin r} {s₁ s₂ : ℕ} (h : s₁ = s₂)
    (hd₁ : destIdx.val = i.val + s₁) (hd₂ : destIdx.val = i.val + s₂)
    (h_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (c : Fin s₁ → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := s₂)
      (destIdx := destIdx) (h_destIdx := hd₂) (h_destIdx_le := h_le) f
      (fun j => c (Fin.cast h.symm j)) =
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := s₁)
      (destIdx := destIdx) (h_destIdx := hd₁) (h_destIdx_le := h_le) f c := by
  subst h
  rfl

private lemma iterated_fold_zero_steps_fun
    (i : Fin r) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (r_challenges : Fin 0 → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := 0)
      (destIdx := destIdx) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
      (f := f) (r_challenges := r_challenges) =
    fun y => f (Eq.mp (congrArg (fun j => (sDomain 𝔽q β h_ℓ_add_R_rate j : Type))
      (Fin.eq_of_val_eq h_destIdx)) y) := by
  funext y
  exact iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
    (f := f) (r_challenges := r_challenges) y

private lemma getFirstOracle_apply_zero {i : Fin (ℓ + 1)}
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate 0) :
    getFirstOracle 𝔽q β oStmt y =
      oStmt ⟨0, (instNeZeroNatToOutCodewordsCount ℓ ϑ i).pos⟩
        ⟨y.val, by simpa only [Fin.val_mk, zero_mul, Nat.zero_mod] using y.property⟩ := by
  unfold getFirstOracle
  rfl

set_option maxHeartbeats 2000000 in
-- The final equality crosses two dependent `sDomain` transports introduced by `getFirstOracle`
-- and the zero-step fold; the extra budget keeps the proof local to this bridge lemma.
/-- **First Oracle Equals Polynomial Oracle Function**:
When `strictOracleFoldingConsistencyProp` holds, the first oracle (`getFirstOracle`) equals
the polynomial oracle function `f₀` derived from the multilinear polynomial `t`.
This follows from the consistency property for `j = 0`, where `iterated_fold` with 0 steps
is the identity function. -/
lemma polyToOracleFunc_eq_getFirstOracle
    (t : MultilinearPoly L ℓ)
    (i : Fin (ℓ + 1))
    (challenges : Fin i → L)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i j)
    (h_consistency : strictOracleFoldingConsistencyProp 𝔽q β (t := t) (i := i)
      (challenges := challenges) (oStmt := oStmt)) :
    let P₀ : Polynomial.degreeLT L (2 ^ ℓ) :=
      polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
        (fun ω => t.val.eval (statementOrderBitsOfIndex ω))
    let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
    f₀ = getFirstOracle 𝔽q β oStmt := by
  intro P₀ f₀
  let h_pos : 0 < toOutCodewordsCount ℓ ϑ i :=
    (instNeZeroNatToOutCodewordsCount ℓ ϑ i).pos
  have h_first_oracle := h_consistency ⟨0, h_pos⟩
  dsimp only [strictOracleFoldingConsistencyProp] at h_first_oracle
  dsimp only [f₀, P₀] at h_first_oracle ⊢
  simp only [id_eq] at h_first_oracle ⊢
  funext y
  rw [getFirstOracle_apply_zero 𝔽q β oStmt y]
  let j0 : Fin (toOutCodewordsCount ℓ ϑ i) := ⟨0, h_pos⟩
  let firstIdx : Fin r := ⟨j0.val * ϑ, by
    simp only [j0, Fin.val_mk, zero_mul]
    exact Nat.lt_trans (Nat.pos_of_neZero ℓ) (ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate))⟩
  have h_firstIdx_zero : firstIdx = (0 : Fin r) := by
    apply Fin.ext
    simp only [firstIdx, j0, Fin.val_mk, zero_mul, Fin.val_zero]
  let y0 : sDomain 𝔽q β h_ℓ_add_R_rate firstIdx :=
    ⟨y.val, h_firstIdx_zero.symm ▸ y.property⟩
  change f₀ y = oStmt ⟨0, h_pos⟩ y0
  rw [h_first_oracle]
  -- The three side conditions below are stated against whatever normal form the
  -- `strictOracleFoldingConsistencyProp` instance currently exposes (`↑⟨0, _⟩ * ϑ` vs `0 * ϑ`
  -- vs `0`); sibling refactors keep shifting that normal form, so each proof is a `first`
  -- ladder over the defeq-equivalent shapes instead of a single brittle `simp only`.
  rw [iterated_fold_congr_steps_index 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps' := 0)
      (h_destIdx := by
        first
          | (simp only [Fin.val_mk, zero_mul, Fin.val_zero, add_zero]; rfl)
          | (simp only [Fin.val_mk, zero_mul, Fin.val_zero, add_zero])
          | (simp only [oraclePositionToDomainIndex, Fin.val_mk, Fin.val_zero, zero_mul,
              add_zero, zero_add])
          | rfl
          | omega)
      (h_destIdx_le := by
        first
          | (simp only [zero_mul, zero_le])
          | (simp only [oraclePositionToDomainIndex, Fin.val_mk, zero_mul, zero_le])
          | (simp only [oraclePositionToDomainIndex, Fin.val_mk, zero_mul];
              exact Nat.zero_le _)
          | exact Nat.zero_le _
          | simp)
      (h_steps_eq_steps' := by
        first
          | (simp only [zero_mul])
          | (simp only [Fin.val_mk, zero_mul])
          | exact Nat.zero_mul _
          | simp)]
  rw [iterated_fold_zero_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
      (h_destIdx := by
        first
          | (simp only [firstIdx, j0, Fin.val_mk, zero_mul, Fin.val_zero])
          | (simp only [oraclePositionToDomainIndex, Fin.val_mk, Fin.val_zero, zero_mul])
          | rfl
          | simp)]
  have h_y0_to_y :
      (cast (congrArg (fun j => (sDomain 𝔽q β h_ℓ_add_R_rate j : Type))
        h_firstIdx_zero) y0) = y := by
    apply Subtype.ext
    exact (val_of_cast_sDomain 𝔽q β firstIdx (0 : Fin r) h_firstIdx_zero
      (congrArg (fun j => (sDomain 𝔽q β h_ℓ_add_R_rate j : Type)) h_firstIdx_zero)
      y0).trans rfl
  simp only [polyToOracleFunc]
  change P₀.val.eval y.val =
    P₀.val.eval (cast (congrArg (fun j => (sDomain 𝔽q β h_ℓ_add_R_rate j : Type))
      h_firstIdx_zero) y0).val
  rw [h_y0_to_y]

end QueryPhase

end

end Binius.BinaryBasefold
