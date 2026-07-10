/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.BaseFoldDetBrick
import ArkLib.ProofSystem.Binius.BinaryBasefold.FoldDetSplit

/-!
# Issue #317: `FoldMatrixDetNeZeroResidual` discharged

The recursive fold matrix `foldMatrixNat (n+1)` is, after the `rowSplit`/`colSplit`
reindexing, exactly the block matrix
`fromBlocks (x₁•M₀) ((−x₀)•M₁) ((−1)•M₀) M₁` — so by `detSplitFactor` its determinant is
`(x₁ − x₀)^{2^n} · det M₀ · det M₁`, and by the fiber-separation brick
(`qMap_total_fiber_one_sub`: `x₁ − x₀ = basis_x 0 ≠ 0`) plus induction every fold matrix in
the `destIdx ≤ ℓ` range demanded by `FoldMatrixDetNeZeroResidual` is nonsingular.
-/

namespace Binius.BinaryBasefold

open AdditiveNTT
open Binius.BinaryBasefold.DetNeZero

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

/-- The single-step fiber difference is nonzero in `L` (coerced fiber-separation brick). -/
lemma qMap_fiber_sub_ne_zero (i : Fin r) (h_i : i.val + 1 < ℓ + 𝓡) (h_le : i.val + 1 ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + 1, by omega⟩) :
    ((qMap_total_fiber 𝔽q β (i := i) (steps := 1)
        (h_i_add_steps := h_i) (y := y) 1 :
        sDomain 𝔽q β h_ℓ_add_R_rate i) : L)
      - ((qMap_total_fiber 𝔽q β (i := i) (steps := 1)
        (h_i_add_steps := h_i) (y := y) 0 :
        sDomain 𝔽q β h_ℓ_add_R_rate i) : L) ≠ 0 := by
  have hsub := qMap_total_fiber_one_sub 𝔽q β i h_i h_le y
  have hb := (sDomain_basis 𝔽q β h_ℓ_add_R_rate i
    (show i.val < ℓ + 𝓡 by omega)).ne_zero ⟨0, by omega⟩
  intro hc
  apply hb
  have : (qMap_total_fiber 𝔽q β (i := i) (steps := 1)
        (h_i_add_steps := h_i) (y := y) 1)
      - (qMap_total_fiber 𝔽q β (i := i) (steps := 1)
        (h_i_add_steps := h_i) (y := y) 0) = 0 := by
    apply Subtype.ext
    push_cast
    linear_combination hc
  rw [hsub] at this
  exact this

/-- Recast `y` from level `i + (n+1)` to level `(i + n) + 1` (associativity transport). -/
def succCast (i : Fin r) (n : ℕ) (h : i.val + (n + 1) < ℓ + 𝓡)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + (n + 1), by omega⟩) :
    sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + n + 1, by omega⟩ :=
  ⟨y.val, by have := y.property; simpa only [Nat.add_assoc] using this⟩

/-- The two single-step fiber points of `y` at level `i + n`. -/
def fibPt (i : Fin r) (n : ℕ) (h : i.val + (n + 1) < ℓ + 𝓡)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + (n + 1), by omega⟩) (c : Fin 2) :
    sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + n, by omega⟩ :=
  qMap_total_fiber 𝔽q β (i := ⟨i.val + n, by omega⟩) (steps := 1)
    (h_i_add_steps := by simp only; omega) (y := succCast 𝔽q β i n h y) c

/-- **Block form of the recursive fold matrix.**  Peeling the last fold,
`foldMatrixNat (n+1)` is the `rowSplit`/`colSplit` reindexing of
`fromBlocks (x₁•M₀) ((−x₀)•M₁) ((−1)•M₀) M₁`. -/
lemma foldMatrixNat_succ_eq_submatrix (i : Fin r) (n : ℕ)
    (h : i.val + (n + 1) < ℓ + 𝓡)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + (n + 1), by omega⟩) :
    foldMatrixNat 𝔽q β i (n + 1) h y
      = (Matrix.fromBlocks
          (((fibPt 𝔽q β i n h y 1 : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + n, by omega⟩) : L) •
            foldMatrixNat 𝔽q β i n (by omega) (fibPt 𝔽q β i n h y 0))
          ((-((fibPt 𝔽q β i n h y 0 : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + n, by omega⟩) : L)) •
            foldMatrixNat 𝔽q β i n (by omega) (fibPt 𝔽q β i n h y 1))
          ((-1 : L) • foldMatrixNat 𝔽q β i n (by omega) (fibPt 𝔽q β i n h y 0))
          (foldMatrixNat 𝔽q β i n (by omega) (fibPt 𝔽q β i n h y 1))
        ).submatrix (rowSplit n) (colSplit n) := by
  ext a b
  conv_lhs => rw [foldMatrixNat]
  simp only [Matrix.submatrix_apply]
  rcases (show a.val % 2 = 0 ∨ a.val % 2 = 1 by omega) with ha | ha <;>
    by_cases hb : (b : ℕ) < 2 ^ n
  all_goals
    first
      | (have hbd : b.val / 2 ^ n = 0 := Nat.div_eq_of_lt hb)
      | (have hbd : b.val / 2 ^ n = 1 := Nat.div_eq_of_lt_le
          (by simpa using Nat.le_of_not_lt hb)
          (by have h2 := Nat.lt_of_lt_of_eq b.isLt (pow_succ 2 n); omega))
  all_goals
    first
      | (have hbm : b.val % 2 ^ n = b.val := Nat.mod_eq_of_lt hb)
      | (have hbm : b.val % 2 ^ n = b.val - 2 ^ n := by
          have h1 := Nat.mod_eq_sub_mod (Nat.le_of_not_lt hb)
          rw [h1]
          exact Nat.mod_eq_of_lt (by have h2 := Nat.lt_of_lt_of_eq b.isLt (pow_succ 2 n); omega))
  all_goals
    simp only [rowSplit, colSplit, Equiv.coe_fn_mk]
  all_goals
    simp only [ha, hbd, reduceIte, if_true, if_false]
  all_goals split_ifs <;> try (exfalso; omega)
  all_goals
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply,
      smul_eq_mul, baseFoldMatrix, fibPt, succCast, one_mul, neg_mul, neg_neg]
  all_goals
    repeat' first
      | rfl
      | (apply Fin.ext; simp [hbm])
      | congr 1

/-- **Issue #317: every fold matrix in the `≤ ℓ` range is nonsingular.** -/
theorem foldMatrixNat_det_ne_zero (i : Fin r) (steps : ℕ)
    (h : i.val + steps < ℓ + 𝓡) (h_le : i.val + steps ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + steps, by omega⟩) :
    (foldMatrixNat 𝔽q β i steps h y).det ≠ 0 := by
  induction steps with
  | zero =>
      rw [foldMatrixNat]
      simp [Matrix.det_fin_one]
  | succ n ih =>
      rw [foldMatrixNat_succ_eq_submatrix]
      apply det_submatrix_equiv_ne_zero
      rw [detSplitFactor]
      refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr fun hc => ?_)) ?_) ?_
      · refine qMap_fiber_sub_ne_zero 𝔽q β ⟨i.val + n, by omega⟩
          (by simp only; omega) (by simp only; omega) (succCast 𝔽q β i n (by omega) y) ?_
        simpa only [fibPt] using sub_eq_zero.mpr hc
      · exact ih (by omega) (by omega) _
      · exact ih (by omega) (by omega) _

/-- Fold matrices are nonsingular in the new `{destIdx}` API. -/
theorem foldMatrix_det_ne_zero (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) :
    (foldMatrix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) y).det ≠ 0 := by
  rw [foldMatrix]
  exact foldMatrixNat_det_ne_zero 𝔽q β i steps _
    (by have : (destIdx : ℕ) ≤ ℓ := h_destIdx_le; omega) _

end

end Binius.BinaryBasefold
