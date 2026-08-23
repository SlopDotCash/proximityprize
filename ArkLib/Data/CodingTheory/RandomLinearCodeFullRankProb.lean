/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

/-!
# Full-row-rank probability for a uniform random generator matrix (issue #79)

`RandomLinearCodeCodewordCount.lean` reduced the GLMRSW22 / ABF26 T3.11 close-codeword count to
the close-message count **on the full-row-rank event** (`m ↦ m ᵥ* G` injective). The remaining
honest gap in that chain is the GLMRSW22 `1 − q^{−Ω(n)}` claim: a uniform random generator matrix
`G : Matrix (Fin k) (Fin n) F` over a finite field `F_q` (with `k ≤ n`) has full row rank with
overwhelming probability.

This file supplies that probability via finite combinatorics, reusing mathlib's exact count of
linearly independent tuples (`card_linearIndependent`, T. Lanard et al.):

* the exact count of full-row-rank `k × n` matrices is `∏_{i<k} (qⁿ − qⁱ)`;
* the probability `count / q^{k·n}` factors as `∏_{i<k}(1 − q^{i−n})`;
* a clean usable lower bound is `≥ 1 − k · q^{k−1} / q^{n} = 1 − k · q^{k−1−n}`,
  obtained from the Weierstrass product inequality `∏(1 − aᵢ) ≥ 1 − ∑ aᵢ`.

The `card_linearIndependent` count applies to a `k × n` matrix because a matrix's full row rank is
exactly linear independence of its rows `M.row : Fin k → (Fin n → F)`, and `Fin n → F` is a
finite-dimensional `F`-vector space of dimension `n` (so `{ M // LinearIndependent F M.row }` is
defeq to `{ s : Fin k → (Fin n → F) // LinearIndependent F s }`).

## Main results (`sorry`-free; axioms = `propext, Classical.choice, Quot.sound`)

* `weierstrass_one_sub_prod` — `1 − ∑ aᵢ ≤ ∏ (1 − aᵢ)` for `aᵢ ∈ [0,1]` (auxiliary).
* `card_fullRowRank_matrix` — exact count `∏_{i<k}(qⁿ − qⁱ)` of full-row-rank `k × n` matrices.
* `fullRowRank_prob_lower_bound` — `count / q^{k·n} ≥ 1 − k · q^{k−1} / q^{n}`.
-/

namespace ArkLib.RandomLinearCode

open Finset
open scoped Matrix

variable {F : Type*} [Field F] [Fintype F] {k n : ℕ}

set_option linter.unusedSectionVars false

/-- **Weierstrass product inequality.** For `aᵢ ∈ [0,1]`, `1 − ∑ aᵢ ≤ ∏ (1 − aᵢ)`. -/
theorem weierstrass_one_sub_prod (m : ℕ) (a : Fin m → ℝ) (ha0 : ∀ i, 0 ≤ a i)
    (ha1 : ∀ i, a i ≤ 1) : 1 - ∑ i, a i ≤ ∏ i, (1 - a i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
    have hih := ih (fun i => a i.castSucc) (fun i => ha0 _) (fun i => ha1 _)
    have hprodnn : 0 ≤ ∏ i : Fin m, (1 - a i.castSucc) :=
      Finset.prod_nonneg (fun i _ => by have := ha1 i.castSucc; linarith)
    have hl0 := ha0 (Fin.last m)
    have hl1 := ha1 (Fin.last m)
    simp only at hih
    have hsumnn : 0 ≤ ∑ i : Fin m, a i.castSucc :=
      Finset.sum_nonneg (fun i _ => ha0 i.castSucc)
    -- ∏(1−l) ≥ (1−∑)(1−l) ≥ 1−∑−l
    have hstep : (1 - ∑ i : Fin m, a i.castSucc) * (1 - a (Fin.last m))
        ≤ (∏ i : Fin m, (1 - a i.castSucc)) * (1 - a (Fin.last m)) :=
      mul_le_mul_of_nonneg_right hih (by linarith)
    nlinarith [hstep, hsumnn, hl0, hl1, mul_nonneg hsumnn hl0]

/-- **Exact count of full-row-rank `k × n` matrices over `F_q`.** A matrix has full row rank iff
its rows are linearly independent; mathlib's `card_linearIndependent` (over the `n`-dimensional
space `Fin n → F`) then gives the closed form `∏_{i<k}(qⁿ − qⁱ)`. Requires `k ≤ n`. -/
theorem card_fullRowRank_matrix (hk : k ≤ n) :
    Nat.card { M : Matrix (Fin k) (Fin n) F // LinearIndependent F M.row }
      = ∏ i : Fin k, (Fintype.card F ^ n - Fintype.card F ^ i.val) := by
  have hkn : k ≤ Module.finrank F (Fin n → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]; exact hk
  have := card_linearIndependent (K := F) (V := Fin n → F) (k := k) hkn
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
  rw [← this]
  exact Nat.card_congr (Equiv.refl _)

/-- The full-row-rank count, cast to `ℝ` (the natural subtraction `qⁿ − qⁱ` is honest since
`i < k ≤ n`). -/
theorem card_fullRowRank_matrix_real (hk : k ≤ n) :
    (Nat.card { M : Matrix (Fin k) (Fin n) F // LinearIndependent F M.row } : ℝ)
      = ∏ i : Fin k, ((Fintype.card F : ℝ) ^ n - (Fintype.card F : ℝ) ^ i.val) := by
  rw [card_fullRowRank_matrix (F := F) hk, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  have hq1 : 1 ≤ Fintype.card F := Fintype.card_pos
  have hle : Fintype.card F ^ i.val ≤ Fintype.card F ^ n :=
    Nat.pow_le_pow_right hq1 (le_of_lt (lt_of_lt_of_le i.isLt hk))
  push_cast [hle]
  rfl

/-- **GLMRSW22 full-row-rank probability lower bound.** A uniform random generator matrix
`G : Matrix (Fin k) (Fin n) F` over `F_q` (with `k ≤ n`) has full row rank with probability
`count / q^{k·n} ≥ 1 − k · q^{k−1} / q^{n}` (i.e. `1 − k · q^{k−1−n}`). This is the `1 − q^{−Ω(n)}`
event feeding the GLMRSW22 / ABF26 T3.11 chain. -/
theorem fullRowRank_prob_lower_bound (hk : k ≤ n) :
    1 - (k : ℝ) * (Fintype.card F : ℝ) ^ (k - 1) / (Fintype.card F : ℝ) ^ n
      ≤ (Nat.card { M : Matrix (Fin k) (Fin n) F // LinearIndependent F M.row } : ℝ)
          / (Fintype.card F : ℝ) ^ (k * n) := by
  have hq1 : (1:ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hqn : (0:ℝ) < (Fintype.card F : ℝ) ^ n := by positivity
  have hqkn : (0:ℝ) < (Fintype.card F : ℝ) ^ (k * n) := by positivity
  rw [le_div_iff₀ hqkn, card_fullRowRank_matrix_real hk]
  -- factor `q^{k·n}` out of the product: ∏(qⁿ − qⁱ) = q^{k·n} · ∏(1 − qⁱ/qⁿ)
  have hpc : (Fintype.card F : ℝ) ^ (k * n) = ∏ _i : Fin k, (Fintype.card F : ℝ) ^ n := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul']
  have hfac : ∏ i : Fin k, ((Fintype.card F : ℝ) ^ n - (Fintype.card F : ℝ) ^ i.val)
      = (Fintype.card F : ℝ) ^ (k * n)
        * ∏ i : Fin k, (1 - (Fintype.card F : ℝ) ^ i.val / (Fintype.card F : ℝ) ^ n) := by
    rw [hpc, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have : (Fintype.card F : ℝ) ^ n ≠ 0 := ne_of_gt hqn
    field_simp
  rw [hfac]
  set a : Fin k → ℝ := fun i => (Fintype.card F : ℝ) ^ i.val / (Fintype.card F : ℝ) ^ n with ha
  have ha0 : ∀ i, 0 ≤ a i := by intro i; rw [ha]; positivity
  have ha1 : ∀ i, a i ≤ 1 := by
    intro i; rw [ha, div_le_one hqn]; exact pow_le_pow_right₀ hq1 (by omega)
  have hW := weierstrass_one_sub_prod k a ha0 ha1
  -- bound the sum: ∑ qⁱ/qⁿ ≤ k · q^{k−1}/qⁿ
  have hsum : ∑ i, a i ≤ (k : ℝ) * (Fintype.card F : ℝ) ^ (k - 1) / (Fintype.card F : ℝ) ^ n := by
    have hterm : ∀ i : Fin k, a i ≤ (Fintype.card F : ℝ) ^ (k - 1) / (Fintype.card F : ℝ) ^ n := by
      intro i
      rw [ha]
      exact div_le_div_of_nonneg_right (pow_le_pow_right₀ hq1 (by omega)) hqn.le
    calc ∑ i, a i
        ≤ ∑ _i : Fin k, (Fintype.card F : ℝ) ^ (k - 1) / (Fintype.card F : ℝ) ^ n :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = (k : ℝ) * (Fintype.card F : ℝ) ^ (k - 1) / (Fintype.card F : ℝ) ^ n := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_assoc]
  have hWsum : 1 - (k : ℝ) * (Fintype.card F : ℝ) ^ (k - 1) / (Fintype.card F : ℝ) ^ n
      ≤ ∏ i, (1 - a i) := by
    calc 1 - (k : ℝ) * (Fintype.card F : ℝ) ^ (k - 1) / (Fintype.card F : ℝ) ^ n
        ≤ 1 - ∑ i, a i := by linarith
      _ ≤ ∏ i, (1 - a i) := hW
  calc (1 - (k : ℝ) * (Fintype.card F : ℝ) ^ (k - 1) / (Fintype.card F : ℝ) ^ n)
        * (Fintype.card F : ℝ) ^ (k * n)
      ≤ (∏ i, (1 - a i)) * (Fintype.card F : ℝ) ^ (k * n) :=
        mul_le_mul_of_nonneg_right hWsum (le_of_lt hqkn)
    _ = (Fintype.card F : ℝ) ^ (k * n) * ∏ i, (1 - a i) := by ring

end ArkLib.RandomLinearCode

-- Axiom audit: every public result must reduce to the standard kernel axioms only.
#print axioms ArkLib.RandomLinearCode.weierstrass_one_sub_prod
#print axioms ArkLib.RandomLinearCode.card_fullRowRank_matrix
#print axioms ArkLib.RandomLinearCode.fullRowRank_prob_lower_bound
