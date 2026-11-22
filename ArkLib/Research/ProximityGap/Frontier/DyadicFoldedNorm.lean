/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier._G87CoverageDivisibility
import ArkLib.Research.ProximityGap.Frontier._R323ResultantRecurrenceLatticeIndex

/-! # An integer norm bound for a signed vector on a dyadic quotient

The negacyclic shifts have identical squared norms. Evaluation at a root
of the modulus diagonalizes the shift and counts prime factors of its determinant.
-/
set_option autoImplicit false
namespace ProximityGap.DyadicFoldedNorm
open Finset Matrix Polynomial
open ArkLib.ProximityGap.Frontier
open R323ResultantRecurrenceLatticeIndex

variable {m : ℕ} [NeZero m]

/-- The coefficients of the shifted polynomial modulo X^m+1 form one row. -/
def shifts (a : Fin m → ℤ) : Matrix (Fin m) (Fin m) ℤ :=
  fun i j => if i.val ≤ j.val then a (j-i) else -a (j-i)

/-- Evaluation of a shift is multiplication by the corresponding power. -/
theorem eval_shifts {K : Type*} [Field K] (a : Fin m → ℤ) (z : K) (hz : z^m = -1)
    (i : Fin m) :
    (∑ j : Fin m, (shifts a i j : K)*z^j.val) = z^i.val*(∑ j : Fin m, (a j : K)*z^j.val) := by
  rw [mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight i) _ _ ?_ |>.symm
  intro j
  change z^i.val*((a j : K)*z^j.val) = (shifts a i (j+i) : K)*z^(j+i).val
  unfold shifts
  rw [add_sub_cancel_right]
  by_cases h : j.val+i.val < m
  · have hv : (j+i).val = j.val+i.val := by rw [Fin.val_add, Nat.mod_eq_of_lt h]
    rw [hv, ite_eq_left (by omega), pow_add]
    ring
  · have hv : (j+i).val + m = j.val+i.val := by
      rw [Fin.val_add, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by have := j.isLt; have := i.isLt; omega)]
      omega
    have lt : ¬i.val ≤ (j+i).val := by have := j.isLt; omega
    rw [ite_eq_right lt, Int.cast_neg]
    calc z^i.val*((a j : K)*z^j.val) = (a j : K)*z^(j.val+i.val) := by rw [pow_add]; ring
         _ = _ := by rw [← hv,pow_add,hz]; ring

/-- Negacyclic rotation preserves the sum of coefficient squares. -/
theorem row_energy (a : Fin m → ℤ) (i : Fin m) :
    ∑ j : Fin m, (shifts a i j)^2 = ∑ j, (a j)^2 := by
  symm
  refine Fintype.sum_equiv (Equiv.addRight i) _ _ ?_
  intro j
  change (a j)^2 = (if i.val ≤ (j+i).val then a (j+i-i) else -a (j+i-i))^2
  rw [add_sub_cancel_right]
  split_ifs <;> simp

private theorem eval_injective {k : ℕ} (a : Fin (2^k) → ℚ)
    (h : ∑ i, (algebraMap ℚ (AdjoinRoot (fq k)) (a i)) * (AdjoinRoot.root (fq k))^i.val = 0) :
    ∀ i, a i = 0 := by
  let pb := AdjoinRoot.powerBasis' (fq_monic k)
  let e : Fin pb.dim ≃ Fin (2^k) := finCongr (fq_natDegree k)
  have li := (pb.basis.reindex e).linearIndependent
  apply Fintype.linearIndependent_iff.mp li
  convert h using 1
  apply sum_congr rfl
  intro i _
  rw [Module.Basis.reindex_apply, pb.basis_eq_pow, Algebra.smul_def]
  rfl

/-- A nonzero integer vector has nonzero negacyclic determinant in dyadic length. -/
theorem det_ne_zero {k : ℕ} (a : Fin (2^k) → ℤ) (ha : a ≠ 0) : (shifts a).det ≠ 0 := by
  classical
  let K := AdjoinRoot (fq k)
  let : Fact (Irreducible (fq k)) := ⟨fq_irreducible k⟩
  let z := AdjoinRoot.root (fq k)
  have hz : z^(2^k) = -1 := by
    have fx : fq k = (Polynomial.X : ℚ[X])^(2^k)+1 := by simp [fq, FS2PatternAnnihilatorResultant.fpoly]
    have eq := congrArg (AdjoinRoot.mk (fq k)) fx
    simp only [AdjoinRoot.mk_self,map_add,map_pow,map_one,AdjoinRoot.mk_X] at eq
    exact eq_neg_of_add_eq_zero_left eq.symm
  have nz : (∑ j : Fin (2^k), (a j : K)*z^j.val) ≠ 0 := by
    intro h
    have zero := eval_injective (k := k) (fun i => (a i : ℚ)) (by simpa [K,z] using h)
    exact ha (funext fun j => by simpa using zero j)
  let M := (shifts a).map (Int.cast : ℤ → ℚ)
  have li : LinearIndependent ℚ M.row := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc
    have at_col (j : Fin (2^k)) : (∑ i, c i * (shifts a i j : ℚ)) = 0 := by
      simpa [M, Matrix.row, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] using congrFun hc j
    have folded : ∑ i, (algebraMap ℚ K (c i))*z^i.val = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_right nz
      rw [sum_mul]
      calc ∑ i, algebraMap ℚ K (c i)*z^i.val*(∑ j, (a j : K)*z^j.val) =
             ∑ i, algebraMap ℚ K (c i)*(∑ j, (shifts a i j : K)*z^j.val) := by
               apply sum_congr rfl; intro i _; rw [eval_shifts a z hz, mul_assoc]
           _ = ∑ j, (∑ i, (algebraMap ℚ K (c i))*(shifts a i j : K))*z^j.val := by
             simp only [mul_sum,sum_mul,mul_assoc]; rw [sum_comm]
           _ = 0 := by
             apply sum_eq_zero; intro j _
             have h := congrArg (algebraMap ℚ K) (at_col j)
             simpa only [map_sum, map_mul, map_intCast, map_zero, zero_mul] using
               congrArg (fun x : K => x*z^j.val) h
    exact eval_injective c folded
  have hdet := ((Matrix.isUnit_iff_isUnit_det M).mp (Matrix.linearIndependent_row_iff_isUnit.mp li)).ne_zero
  intro he
  apply hdet
  change ((Int.castRingHom ℚ).mapMatrix (shifts a)).det = 0
  rw [← RingHom.map_det, he, map_zero]

/-- At a root of the negacyclic modulus, top and bottom coefficients fold
by subtraction. This identifies the vector tested in the norm argument. -/
theorem fold_eval {K : Type*} [Field K] (l u : Fin m → ℤ) (x : K) (hx : x^m = -1) :
    (∑ i : Fin m, ((l i-u i : ℤ) : K)*x^i.val) =
      ∑ i : Fin m, ((l i : K)*x^i.val+(u i : K)*x^(i.val+m)) := by
  apply sum_congr rfl
  intro i _
  rw [Int.cast_sub,pow_add,hx]
  ring

/-- For a dyadic vector, sufficiently many distinct modular zeros force all
integer coefficients to vanish. B bounds its squared coefficient norm. -/
theorem zero_of_moments {k p B : ℕ} [Fact p.Prime] (a : Fin (2^k) → ℤ)
    (t : Fin (2^k) → ZMod p) (inj : Function.Injective t)
    (S : Finset (Fin (2^k))) (odd : ∀ j ∈ S, (t j)^(2^k) = -1)
    (moments : ∀ j ∈ S, ∑ i, (a i : ZMod p)*(t j)^i.val = 0)
    (energy : ∑ i, (a i)^2 ≤ (B : ℤ)) (large : B^(2^k) < p^(2*S.card)) :
    a = 0 := by
  by_contra ha
  have hn := det_ne_zero a ha
  have div := G87CoverageDivisibility.pow_dvd_det_of_vanishing_at_roots
    (Fact.out : p.Prime) (shifts a) (fun j => ((t j).val : ℤ)) S (by
      intro i j hij h
      apply hij
      apply inj
      have hzero := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h
      simpa using sub_eq_zero.mp (by simpa using hzero : t i - t j = 0)) (by
      intro i j hj
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      push_cast
      simpa [eval_shifts a _ (odd j hj),moments j hj] using
        (eval_shifts a (t j) (odd j hj) i).trans (by rw [moments j hj,mul_zero]))
  have sq : (p : ℤ)^(2*S.card) ∣ (shifts a).det^2 := by
    rw [Nat.mul_comm 2 S.card,pow_mul]
    exact pow_dvd_pow_of_dvd div 2
  have low := Int.le_of_dvd (sq_pos_of_ne_zero hn) sq
  have high := G86HadamardSupportSix.sq_det_le_pow_of_row_sq_sum_le (shifts a) B
    (fun i => (row_energy a i).le.trans energy)
  have bad : (p : ℤ)^(2*S.card) ≤ (B : ℤ)^(2^k) := low.trans high
  exact (not_le_of_gt large) (by exact_mod_cast bad)

#print axioms zero_of_moments
#print axioms eval_shifts
#print axioms det_ne_zero
end ProximityGap.DyadicFoldedNorm
