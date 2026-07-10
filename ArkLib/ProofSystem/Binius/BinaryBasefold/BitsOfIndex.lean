/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Basic

/-!
## Binary expansion of an index as a challenge vector

`bitsOfIndex` lives in `Basic.lean` because the core witness/oracle consistency definitions need the
Boolean-index convention for level-zero novel coefficients. This file keeps the elementary API and
dependency audit available for older imports that reached the helper through `BitsOfIndex`.
-/

namespace Binius.BinaryBasefold

open MvPolynomial Finset

variable {L : Type} [Field L]

/-- Coordinate form of `bitsOfIndex`. -/
theorem bitsOfIndex_apply {n : ℕ} (k : Fin (2 ^ n)) (j : Fin n) :
    bitsOfIndex (L := L) k j = if Nat.getBit j.val k.val = 1 then 1 else 0 :=
  rfl

/-- Coordinate form of `statementOrderBitsOfIndex`. -/
theorem statementOrderBitsOfIndex_apply {n : ℕ} (k : Fin (2 ^ n)) (j : Fin n) :
    statementOrderBitsOfIndex (L := L) k j = bitsOfIndex (L := L) k (Fin.rev j) :=
  rfl

/-- If the corresponding natural-number bit is `1`, then `bitsOfIndex` returns `1`. -/
theorem bitsOfIndex_apply_of_getBit_eq_one {n : ℕ}
    (k : Fin (2 ^ n)) (j : Fin n) (h : Nat.getBit j.val k.val = 1) :
    bitsOfIndex (L := L) k j = 1 := by
  simp [bitsOfIndex, h]

/-- If the corresponding natural-number bit is not `1`, then `bitsOfIndex` returns `0`. -/
theorem bitsOfIndex_apply_of_getBit_ne_one {n : ℕ}
    (k : Fin (2 ^ n)) (j : Fin n) (h : Nat.getBit j.val k.val ≠ 1) :
    bitsOfIndex (L := L) k j = 0 := by
  simp [bitsOfIndex, h]

/-- Every coordinate of `bitsOfIndex` is Boolean-valued. -/
theorem bitsOfIndex_apply_eq_zero_or_one {n : ℕ}
    (k : Fin (2 ^ n)) (j : Fin n) :
    bitsOfIndex (L := L) k j = 0 ∨ bitsOfIndex (L := L) k j = 1 := by
  by_cases h : Nat.getBit j.val k.val = 1
  · exact Or.inr (bitsOfIndex_apply_of_getBit_eq_one (L := L) k j h)
  · exact Or.inl (bitsOfIndex_apply_of_getBit_ne_one (L := L) k j h)

/-- `bitsOfIndex` returns `1` exactly on source coordinates whose natural bit is `1`. -/
theorem bitsOfIndex_apply_eq_one_iff {n : ℕ}
    (k : Fin (2 ^ n)) (j : Fin n) :
    bitsOfIndex (L := L) k j = 1 ↔ Nat.getBit j.val k.val = 1 := by
  constructor
  · intro h
    by_contra hbit
    have hzero := bitsOfIndex_apply_of_getBit_ne_one (L := L) k j hbit
    rw [hzero] at h
    exact zero_ne_one h
  · intro h
    exact bitsOfIndex_apply_of_getBit_eq_one (L := L) k j h

/-- `bitsOfIndex` returns `0` exactly on source coordinates whose natural bit is not `1`. -/
theorem bitsOfIndex_apply_eq_zero_iff {n : ℕ}
    (k : Fin (2 ^ n)) (j : Fin n) :
    bitsOfIndex (L := L) k j = 0 ↔ Nat.getBit j.val k.val ≠ 1 := by
  constructor
  · intro h hbit
    have hone := bitsOfIndex_apply_of_getBit_eq_one (L := L) k j hbit
    rw [hone] at h
    exact one_ne_zero h
  · intro h
    exact bitsOfIndex_apply_of_getBit_ne_one (L := L) k j h

/-- `bitsOfIndex` is the field coercion of the Boolean vector enumerated by
`finFunctionFinEquiv.symm`. -/
theorem bitsOfIndex_eq_finFunctionFinEquiv_symm {n : ℕ} (k : Fin (2 ^ n)) :
    bitsOfIndex (L := L) k = fun j : Fin n => (finFunctionFinEquiv.symm k j : L) := by
  funext j
  simp [bitsOfIndex, Nat.getBit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  by_cases h : k.val / 2 ^ j.val % 2 = 1
  · simp [h]
  · have hzero : k.val / 2 ^ j.val % 2 = 0 := by
      have hlt : k.val / 2 ^ j.val % 2 < 2 := Nat.mod_lt _ (by decide)
      omega
    simp [hzero]

/-- The equality kernel at a fold-order Boolean index is the tensor-product
`multilinearWeight` at that index. -/
theorem eqTilde_bitsOfIndex_eq_multilinearWeight {n : ℕ}
    (r : Fin n → L) (k : Fin (2 ^ n)) :
    eqTilde r (bitsOfIndex (L := L) k) = multilinearWeight r k := by
  unfold eqTilde eqPolynomial singleEqPolynomial multilinearWeight
  rw [MvPolynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j _
  simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_sub, map_one,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  by_cases htest : k.val.testBit j.val = true
  · have hbit : Nat.getBit j.val k.val = 1 := by
      rw [← Nat.testBit_true_eq_getBit_eq_1]
      exact htest
    simp [bitsOfIndex, htest, hbit]
  · have hbit_ne : Nat.getBit j.val k.val ≠ 1 := by
      intro hbit
      apply htest
      rw [Nat.testBit_true_eq_getBit_eq_1]
      exact hbit
    have hzero : Nat.getBit j.val k.val = 0 := by
      rcases Nat.getBit_eq_zero_or_one (k := j.val) (n := k.val) with h | h
      · exact h
      · exact (hbit_ne h).elim
    simp [bitsOfIndex, htest, hzero]

/-- Multilinear evaluation as the fold-order tensor-weighted sum over Boolean-index
coefficients. -/
theorem multilinear_eval_eq_sum_bitsOfIndex {n : ℕ}
    (t : MultilinearPoly L n) (r : Fin n → L) :
    t.val.eval r =
      ∑ k : Fin (2 ^ n), multilinearWeight r k * t.val.eval (bitsOfIndex (L := L) k) := by
  classical
  have h_mle : MvPolynomial.MLE t.val.toEvalsZeroOne = t.val :=
    MvPolynomial.is_multilinear_iff_eq_evals_zeroOne.mp t.property
  calc
    t.val.eval r = MvPolynomial.eval r (MvPolynomial.MLE t.val.toEvalsZeroOne) := by
      rw [h_mle]
    _ = ∑ x : Fin n → Fin 2,
        eqTilde r (fun i => (x i : L)) * t.val.toEvalsZeroOne x := by
      rw [MvPolynomial.MLE_eval_eq_sum_eqTilde]
    _ = ∑ k : Fin (2 ^ n),
        eqTilde r (fun i => (finFunctionFinEquiv.symm k i : L)) *
          t.val.toEvalsZeroOne (finFunctionFinEquiv.symm k) := by
      rw [← Equiv.sum_comp finFunctionFinEquiv.symm
        (fun x : Fin n → Fin 2 =>
          eqTilde r (fun i => (x i : L)) *
            t.val.toEvalsZeroOne x)]
    _ = ∑ k : Fin (2 ^ n), multilinearWeight r k * t.val.eval (bitsOfIndex (L := L) k) := by
      apply Finset.sum_congr rfl
      intro k _
      unfold MvPolynomial.toEvalsZeroOne
      rw [← bitsOfIndex_eq_finFunctionFinEquiv_symm (L := L) k]
      rw [eqTilde_bitsOfIndex_eq_multilinearWeight]

/-- The equality kernel at a statement-order Boolean index is the tensor-product weight for the
fold-order view of the same challenge vector. -/
theorem eqTilde_statementOrderBitsOfIndex_eq_multilinearWeight_foldOrder {n : ℕ}
    (r : Fin n → L) (k : Fin (2 ^ n)) :
    eqTilde r (statementOrderBitsOfIndex (L := L) k) =
      multilinearWeight (fun j : Fin n => r (Fin.rev j)) k := by
  unfold eqTilde eqPolynomial singleEqPolynomial multilinearWeight statementOrderBitsOfIndex
  rw [MvPolynomial.eval_prod]
  simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_sub, map_one,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [Fintype.prod_equiv Fin.revPerm
    (fun j : Fin n =>
      (1 - r j) * (1 - bitsOfIndex (L := L) k (Fin.rev j)) +
        r j * bitsOfIndex (L := L) k (Fin.rev j))
    (fun j : Fin n =>
      (1 - r (Fin.rev j)) * (1 - bitsOfIndex (L := L) k j) +
        r (Fin.rev j) * bitsOfIndex (L := L) k j)]
  · apply Finset.prod_congr rfl
    intro j _
    by_cases htest : k.val.testBit j.val = true
    · have hbit : Nat.getBit j.val k.val = 1 := by
        rw [← Nat.testBit_true_eq_getBit_eq_1]
        exact htest
      simp [bitsOfIndex, htest, hbit]
    · have hbit_ne : Nat.getBit j.val k.val ≠ 1 := by
        intro hbit
        apply htest
        rw [Nat.testBit_true_eq_getBit_eq_1]
        exact hbit
      have hzero : Nat.getBit j.val k.val = 0 := by
        rcases Nat.getBit_eq_zero_or_one (k := j.val) (n := k.val) with h | h
        · exact h
        · exact (hbit_ne h).elim
      simp [bitsOfIndex, htest, hzero]
  · intro j
    simp [Fin.rev_rev]

/-- Multilinear evaluation as the full-fold tensor-weighted sum over statement-order Boolean
indices. -/
theorem multilinear_eval_eq_sum_statementOrderBitsOfIndex {n : ℕ}
    (t : MultilinearPoly L n) (r : Fin n → L) :
    t.val.eval r =
      ∑ k : Fin (2 ^ n),
        multilinearWeight (fun j : Fin n => r (Fin.rev j)) k *
          t.val.eval (statementOrderBitsOfIndex (L := L) k) := by
  classical
  have h_mle : MvPolynomial.MLE t.val.toEvalsZeroOne = t.val :=
    MvPolynomial.is_multilinear_iff_eq_evals_zeroOne.mp t.property
  calc
    t.val.eval r = MvPolynomial.eval r (MvPolynomial.MLE t.val.toEvalsZeroOne) := by
      rw [h_mle]
    _ = ∑ x : Fin n → Fin 2,
        eqTilde r (fun i => (x i : L)) * t.val.toEvalsZeroOne x := by
      rw [MvPolynomial.MLE_eval_eq_sum_eqTilde]
    _ = ∑ k : Fin (2 ^ n),
        eqTilde r (statementOrderBitsOfIndex (L := L) k) *
          t.val.toEvalsZeroOne (fun j : Fin n =>
            finFunctionFinEquiv.symm k (Fin.rev j)) := by
      rw [← Equiv.sum_comp
        ((Equiv.arrowCongr Fin.revPerm (Equiv.refl (Fin 2))).trans finFunctionFinEquiv).symm
        (fun x : Fin n → Fin 2 =>
          eqTilde r (fun i => (x i : L)) *
            t.val.toEvalsZeroOne x)]
      apply Finset.sum_congr rfl
      intro k _
      congr
      funext j
      simp [statementOrderBitsOfIndex, bitsOfIndex_eq_finFunctionFinEquiv_symm, Equiv.arrowCongr]
    _ = ∑ k : Fin (2 ^ n),
        multilinearWeight (fun j : Fin n => r (Fin.rev j)) k *
          t.val.eval (statementOrderBitsOfIndex (L := L) k) := by
      apply Finset.sum_congr rfl
      intro k _
      unfold MvPolynomial.toEvalsZeroOne
      rw [eqTilde_statementOrderBitsOfIndex_eq_multilinearWeight_foldOrder]
      congr 1
      apply congrArg (fun x : Fin n → L => MvPolynomial.eval x t.val)
      funext j
      simp [statementOrderBitsOfIndex, bitsOfIndex_eq_finFunctionFinEquiv_symm]

#print axioms bitsOfIndex
#print axioms statementOrderBitsOfIndex
#print axioms bitsOfIndex_apply
#print axioms statementOrderBitsOfIndex_apply
#print axioms bitsOfIndex_apply_of_getBit_eq_one
#print axioms bitsOfIndex_apply_of_getBit_ne_one
#print axioms bitsOfIndex_apply_eq_zero_or_one
#print axioms bitsOfIndex_apply_eq_one_iff
#print axioms bitsOfIndex_apply_eq_zero_iff
#print axioms bitsOfIndex_eq_finFunctionFinEquiv_symm
#print axioms eqTilde_bitsOfIndex_eq_multilinearWeight
#print axioms multilinear_eval_eq_sum_bitsOfIndex
#print axioms eqTilde_statementOrderBitsOfIndex_eq_multilinearWeight_foldOrder
#print axioms multilinear_eval_eq_sum_statementOrderBitsOfIndex

end Binius.BinaryBasefold
