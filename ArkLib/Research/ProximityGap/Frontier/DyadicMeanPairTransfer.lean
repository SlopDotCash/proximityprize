/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicChordEnergy
import ArkLib.Research.ProximityGap.Frontier.DyadicPairMinorTransfer
import ArkLib.Research.ProximityGap.Frontier.CyclotomicProjectiveTransfer

/-! # A mean-square height bound for the dyadic transposition determinant -/

namespace ProximityGap.DyadicMeanPairTransfer
open Finset Polynomial DyadicPairMinorTransfer ArkLib.ProximityGap.Frontier.DyadicFrobeniusNorm

/-- Determinant of the three rows indexed by pairs of sites. -/
def form {R : Type*} [CommRing R] (x y : Fin 3 → R) : R :=
  minor (x 0) (y 0) (x 1) (y 1) (x 2) (y 2)

/-- The integral polynomial representing an ordered three-pair determinant. -/
noncomputable def cert {n : ℕ} (x y : Fin 3 → Fin n) : ℤ[X] :=
  form (fun i => X^(x i).val) (fun i => X^(y i).val)

/-- Evaluating the integral certificate evaluates the marked pairs. -/
theorem eval_cert {n : ℕ} (x y : Fin 3 → Fin n) {K : Type*} [Field K] (w : K) :
    (cert x y).eval₂ (Int.castRingHom K) w=form (fun i => w^(x i).val) (fun i => w^(y i).val) := by
  simp only [cert,form,minor,eval₂_mul,eval₂_add,eval₂_sub,eval₂_pow,eval₂_X]

private theorem pointwise (x y : Fin 3 → ℂ) (hx : ∀ i, ‖x i‖=1) (hy : ∀ i, ‖y i‖=1) :
    ‖form x y‖^2 ≤ 9*(∑ i,‖x i+y i‖^2) := by
  let M : Matrix (Fin 3) (Fin 3) ℂ := ![fun _ => 1, fun i => x i+y i,fun i => x i*y i]
  have matrix : M.det=form x y := by rw [Matrix.det_fin_three];simp [M,form,minor];ring
  have eq : ‖form x y‖≤Real.sqrt 3*Real.sqrt (∑ i,‖x i+y i‖^2)*Real.sqrt 3 := by
    have h := CyclotomicProjectiveTransfer.hadamard M
    rw [matrix,Fin.prod_univ_three] at h
    norm_num [M,Fin.sum_univ_three,norm_mul,hx,hy] at h ⊢
    exact h
  have sq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr eq
  rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity : (0:ℝ)≤3),Real.sq_sqrt (by positivity)] at sq
  linarith

/-- The squared absolute cyclotomic norm of a three-pair minor is at most
54^φ(n) on a dyadic grid. Each pair must have two different members. -/
theorem norm_bound {m : ℕ} (x y : Fin 3 → Fin (2^(m+1))) (different : ∀ i,x i≠y i) :
    (cycloNorm (2^(m+1)) (cert x y)).natAbs^2 ≤ 54^(2^(m+1)).totient := by
  classical
  let n := 2^(m+1)
  let J := ↥(primitiveRoots n ℂ)
  let _ : Nonempty J := ⟨⟨_,(mem_primitiveRoots (by dsimp [n];positivity)).mpr
    (Complex.isPrimitiveRoot_exp n (by dsimp [n];positivity))⟩⟩
  let f (w : J) := ‖valAt (cert x y) (w:ℂ)‖^2
  let G (i : Fin 3) (w : J) := ‖(w:ℂ)^(x i).val+(w:ℂ)^(y i).val‖^2
  have card : Fintype.card J=(2^m) := by
    change Fintype.card ↥(primitiveRoots n ℂ)=_
    rw [Fintype.card_coe,Complex.card_primitiveRoots,Nat.totient_prime_pow_succ Nat.prime_two];simp
  have pw (w : J) : f w≤9*(∑ i, G i w) := by
    have unit := (isPrimitiveRoot_of_mem_primitiveRoots w.property).norm'_eq_one (NeZero.ne n)
    dsimp only [f,valAt,G]
    rw [eval_cert]
    exact pointwise _ _ (fun i => by simp [norm_pow,unit]) (fun i => by simp [norm_pow,unit])
  have total : ∑ w,f w≤(Fintype.card J:ℝ)*54 := by
    refine (sum_le_sum (fun w _ => pw w)).trans ?_
    rw [←mul_sum,sum_comm]
    have row (i : Fin 3) : ∑ w, G i w ≤ 2*(2^m:ℕ) := DyadicChordEnergy.pair_sum (x i) (y i) (different i)
    have sum := sum_le_sum (s:=univ) (fun i _ => row i)
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at sum
    rw [card];linarith
  have prod := DyadicChordEnergy.prod_le_of_sum f (fun _ => sq_nonneg _) total
  have bound : |(cycloNorm n (cert x y):ℝ)|^2≤(54:ℝ)^n.totient := by
    rw [norm_eq_prod_abs,←prod_pow]
    have cc : Fintype.card J=n.totient := (Fintype.card_coe _).trans (Complex.card_primitiveRoots n)
    simpa only [cc] using prod
  rw [←Int.cast_abs,←Nat.cast_natAbs] at bound
  exact_mod_cast bound

/-- A vanishing modular determinant has two reciprocal roots, giving square
divisibility of its integer norm even without a height assumption. -/
theorem square_dvd {n p : ℕ} [Fact p.Prime] [NeZero n] [NeZero (n:ZMod p)]
    {z : ZMod p} (len : 2<n) (hz : IsPrimitiveRoot z n) (x y : Fin 3 → Fin n)
    (zero : form (fun i => z^(x i).val) (fun i => z^(y i).val)=0) :
    (p:ℤ)^2 ∣ cycloNorm n (cert x y) := by
  have nz := hz.ne_zero (by omega)
  apply RatioProductNorm.square_dvd_of_reciprocal_roots len hz _ (by rwa [eval_cert])
  rw [eval_cert]
  let X (i : Fin 3) := z^(x i).val
  let Y (i : Fin 3) := z^(y i).val
  have nx (i) : X i≠0 := pow_ne_zero _ nz
  have ny (i) : Y i≠0 := pow_ne_zero _ nz
  have nzp : ∏ i, X i*Y i≠0 := prod_ne_zero_iff.mpr (fun i _ => mul_ne_zero (nx i) (ny i))
  have identity : form (fun i => (X i)⁻¹) (fun i => (Y i)⁻¹)*(∏ i,X i*Y i)= -form X Y := by
    simp only [form,minor,Fin.prod_univ_three]
    field_simp [nx,ny]
    ring
  rw [show form X Y=0 from zero,neg_zero] at identity
  simpa only [inv_pow] using (mul_eq_zero.mp identity).resolve_right nzp

/-- A three-pair minor in a split prime field transfers to characteristic zero
or another coprime characteristic if 54^φ(n)<p⁴. -/
theorem transfer {m p : ℕ} [Fact p.Prime] [NeZero ((2^(m+1):ℕ):ZMod p)]
    {K : Type*} [Field K] [NeZero ((2^(m+1):ℕ):K)] {z : ZMod p} {w : K}
    (len : 2<2^(m+1)) (hz : IsPrimitiveRoot z (2^(m+1))) (hw : IsPrimitiveRoot w (2^(m+1)))
    (x y : Fin 3 → Fin (2^(m+1))) (different : ∀ i,x i≠y i)
    (zero : form (fun i => z^(x i).val) (fun i => z^(y i).val)=0)
    (large : 54^(2^(m+1)).totient<p^4) :
    form (fun i => w^(x i).val) (fun i => w^(y i).val)=0 := by
  rw [←eval_cert]
  apply eval_zero_of_cyclo_dvd hw
  apply dvd_of_norm_zero
  by_contra nonzero
  have divides := Int.natAbs_dvd_natAbs.mpr (square_dvd len hz x y zero)
  rw [Int.natAbs_pow,Int.natAbs_natCast] at divides
  have e := Nat.pow_le_pow_left (Nat.le_of_dvd (Int.natAbs_pos.mpr nonzero) divides) 2
  rw [←pow_mul] at e
  exact (not_lt_of_ge e) ((norm_bound x y different).trans_lt large)

end ProximityGap.DyadicMeanPairTransfer
#print axioms ProximityGap.DyadicMeanPairTransfer.norm_bound
#print axioms ProximityGap.DyadicMeanPairTransfer.transfer
