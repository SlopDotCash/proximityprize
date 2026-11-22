/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.RatioProductNorm
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-! # Transport of general projective cross ratios on cyclic evaluation domains

The determinant of the four rows (1,x,y,xy) is the difference of the
two cleared cross-ratio products. Each row has Euclidean norm two.
Taking the product of the Hadamard inequalities over the primitive
conjugates and using the reciprocal root gives the test 16^φ(n) < p².
-/
set_option autoImplicit false
namespace ProximityGap.CyclotomicProjectiveTransfer
open Polynomial Finset InnerProductSpace ArkLib.ProximityGap.Frontier.DyadicFrobeniusNorm
open scoped ComplexInnerProductSpace
noncomputable section

/-- Hadamard bounds a complex determinant by the product of its Euclidean row norms. -/
theorem hadamard {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ‖M.det‖ ≤ ∏ i, Real.sqrt (∑ j, ‖M i j‖^2) := by
  classical
  let f : Fin n → EuclideanSpace ℂ (Fin n) := fun i => WithLp.toLp 2 (M i)
  let e := EuclideanSpace.basisFun (Fin n) ℂ
  have rank : Module.finrank ℂ (EuclideanSpace ℂ (Fin n))=Fintype.card (Fin n) := by simp
  let b := gramSchmidtOrthonormalBasis rank f
  have change : e.toBasis.det f=e.toBasis.det ⇑b.toBasis * b.toBasis.det f := by
    conv_lhs => rw [AlternatingMap.eq_smul_basis_det b.toBasis e.toBasis.det]
    simp [smul_eq_mul]
  have dm : e.toBasis.det f=M.det := by
    rw [Module.Basis.det_apply]
    have mat : e.toBasis.toMatrix f=M.transpose := by ext; rfl
    rw [mat,Matrix.det_transpose]
  rw [← dm,change,norm_mul,OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.det_to_matrix_orthonormalBasis,one_mul,
    show b.toBasis.det f=∏ i, ⟪b i,f i⟫_ℂ from gramSchmidtOrthonormalBasis_det rank f,norm_prod]
  apply prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro i _
  have h := norm_inner_le_norm (𝕜:=ℂ) (b i) (f i)
  rwa [b.orthonormal.1 i,one_mul,EuclideanSpace.norm_eq] at h

/-- The cleared cross-ratio relation for two ordered quadruples. -/
def cross {R : Type*} [CommRing R] (x y : Fin 4 → R) : R :=
  (x 0-x 2)*(x 1-x 3)*(y 0-y 3)*(y 1-y 2) -
    (x 0-x 3)*(x 1-x 2)*(y 0-y 2)*(y 1-y 3)

private def rows {R : Type*} [CommRing R] (x y : Fin 4 → R) : Matrix (Fin 4) (Fin 4) R :=
  fun i => ![1, x i, y i, x i*y i]

private theorem det_rows {R : Type*} [CommRing R] (x y : Fin 4 → R) :
    (rows x y).det = cross x y := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four,Matrix.det_fin_three,Matrix.submatrix_apply]
  norm_num [rows,cross,Fin.succAbove]
  ring

private def cert (a b : Fin 4 → ℕ) : ℤ[X] := cross (fun i => X^(a i)) (fun i => X^(b i))

private theorem eval_cert {F : Type*} [Field F] (z : F) (a b : Fin 4 → ℕ) :
    (cert a b).eval₂ (Int.castRingHom F) z = cross (fun i => z^(a i)) (fun i => z^(b i)) := by
  simp [cert,cross,eval₂_sub,eval₂_mul,eval₂_pow]

private theorem height {z : ℂ} (hz : ‖z‖=1) (a b : Fin 4 → ℕ) :
    ‖valAt (cert a b) z‖ ≤ 16 := by
  rw [valAt,eval_cert,← det_rows]
  apply (hadamard _).trans
  norm_num [rows,Fin.sum_univ_four,norm_mul,norm_pow,hz]

/-- A general Möbius cross-ratio equality transfers to every other
primitive root under the sharp row-norm height test. -/
theorem transfer {n p : ℕ} [Fact p.Prime] [NeZero n] [NeZero (n : ZMod p)]
    {F : Type*} [Field F] [NeZero (n : F)] {z : ZMod p} {w : F}
    (hn : 2<n) (hz : IsPrimitiveRoot z n) (hw : IsPrimitiveRoot w n)
    (a b : Fin 4 → ℕ) (h : cross (fun i => z^(a i)) (fun i => z^(b i))=0)
    (large : 16^n.totient<p^2) :
    cross (fun i => w^(a i)) (fun i => w^(b i))=0 := by
  have nz : z≠0 := by intro eq; simpa [eq,NeZero.ne n] using hz.pow_eq_one
  rw [← eval_cert]
  apply eval_zero_of_cyclo_dvd hw
  refine RatioProductNorm.dvd_of_reciprocal_roots hn hz _ (by rwa [eval_cert]) ?_ ?_
  · rw [eval_cert]
    simp only [inv_pow,cross] at h ⊢
    field_simp
    linear_combination h
  · apply lt_of_le_of_lt _ large
    have realbound : |(cycloNorm n (cert a b):ℝ)| ≤ (16:ℝ)^n.totient := by
      rw [norm_eq_prod_abs]
      calc
        _ ≤ ∏ _ : primitiveRoots n ℂ, (16:ℝ) := by
          apply prod_le_prod₀ (fun _ _ => norm_nonneg _)
          intro i _
          exact height ((isPrimitiveRoot_of_mem_primitiveRoots i.2).norm'_eq_one (NeZero.ne n)) a b
        _ = _ := by simp [Complex.card_primitiveRoots]
    apply Int.ofNat_le.mp
    rw [Int.natCast_natAbs]
    exact_mod_cast realbound

/-- At length 128 the test holds for every prime greater than 2^128. -/
theorem height128 {p : ℕ} (large : 2^128<p) : 16^(Nat.totient 128)<p^2 := by
  rw [show 16^(Nat.totient 128)=(2^128)^2 by decide]
  exact Nat.pow_lt_pow_left large (by decide)

end
end ProximityGap.CyclotomicProjectiveTransfer
#print axioms ProximityGap.CyclotomicProjectiveTransfer.transfer
