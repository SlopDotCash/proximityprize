/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.CyclotomicProjectiveTransfer

/-! # Finite-field transfer for monomial interpolation matrices on a torus

Central symmetry of the exponent set makes the reversed primitive root a
second modular root of the same minor. A Hadamard inequality uses only the
number of columns, independently of coordinate degrees or the grid length.
-/
namespace ProximityGap.ToricGraphMinorTransfer
open Polynomial Finset ArkLib.ProximityGap.Frontier.DyadicFrobeniusNorm
noncomputable section

/-- The monomial interpolation matrix at prescribed pairs of powers. -/
def matrix {F : Type*} [CommRing F] {h : ℕ} (z : F) (A B u v : Fin h → ℕ) :
    Matrix (Fin h) (Fin h) F := fun i j => z^(A i*u j+B i*v j)

private theorem evaluate {F : Type*} [Field F] {h : ℕ} (z : F) (A B u v : Fin h → ℕ) :
    ((matrix (X : ℤ[X]) A B u v).det).eval₂ (Int.castRingHom F) z=(matrix z A B u v).det := by
  let φ := eval₂RingHom (Int.castRingHom F) z
  change φ ((matrix (X : ℤ[X]) A B u v).det)=_
  rw [φ.map_det]
  congr 1
  ext i j
  change φ (X^(A i*u j+B i*v j))=_
  simp [φ,matrix]

private theorem reverse_zero {F : Type*} [Field F] {h : ℕ} {z : F} (zn : z≠0)
    (A B u v : Fin h → ℕ) (rev : Equiv.Perm (Fin h)) {S T : ℕ}
    (ux : ∀ j, u j+u (rev j)=S) (vy : ∀ j, v j+v (rev j)=T)
    (zero : (matrix z A B u v).det=0) : (matrix z⁻¹ A B u v).det=0 := by
  classical
  let w (i : Fin h) := z^(A i*S+B i*T)
  have eq : Matrix.diagonal w * matrix z⁻¹ A B u v=(matrix z A B u v).submatrix id rev := by
    ext i j
    rw [Matrix.diagonal_mul]
    change z^(A i*S+B i*T)*(z⁻¹)^(A i*u j+B i*v j)=z^(A i*u (rev j)+B i*v (rev j))
    have ex : A i*S+B i*T=(A i*u (rev j)+B i*v (rev j))+(A i*u j+B i*v j) := by
      rw [←ux j,←vy j];ring
    rw [ex,pow_add,inv_pow,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ zn),mul_one]
  have e := congrArg Matrix.det eq
  rw [Matrix.det_mul,Matrix.det_diagonal,Matrix.det_permute',zero,mul_zero] at e
  exact (mul_eq_zero.mp e).resolve_left (prod_ne_zero_iff.mpr (fun _ _ => pow_ne_zero _ zn))

private theorem height {t : ℕ} (A B u v : Fin (2*t) → ℕ) {z : ℂ} (hz : ‖z‖=1) :
    ‖(matrix z A B u v).det‖≤(2*t : ℕ)^t := by
  apply (CyclotomicProjectiveTransfer.hadamard _).trans
  simp only [matrix,norm_pow,hz,one_pow,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_one,prod_const]
  rw [show 2*t=t*2 by omega,pow_mul']
  simp [mul_pow]

/-- At a split prime with (2t)^(t φ(n)) below p², vanishing of a 2t-square
centrally symmetric monomial minor transfers to every comparison field
containing a primitive root of the same order. -/
theorem transfer {n p t : ℕ} [Fact p.Prime] [NeZero n] [NeZero (n : ZMod p)]
    {F : Type*} [Field F] [NeZero (n : F)] {z : ZMod p} {w : F}
    (hn : 2<n) (hz : IsPrimitiveRoot z n) (hw : IsPrimitiveRoot w n)
    (A B u v : Fin (2*t) → ℕ) (rev : Equiv.Perm (Fin (2*t))) {S T : ℕ}
    (ux : ∀ j, u j+u (rev j)=S) (vy : ∀ j, v j+v (rev j)=T)
    (zero : (matrix z A B u v).det=0) (large : (2*t)^(t*n.totient)<p^2) :
    (matrix w A B u v).det=0 := by
  let P := (matrix (X : ℤ[X]) A B u v).det
  rw [←evaluate]
  apply eval_zero_of_cyclo_dvd hw
  apply RatioProductNorm.dvd_of_reciprocal_roots hn hz P
  · simpa only [P,evaluate] using zero
  · simpa only [P,evaluate] using reverse_zero (hz.ne_zero (by omega)) A B u v rev ux vy zero
  · apply lt_of_le_of_lt _ large
    have H : |(cycloNorm n P : ℝ)| ≤ (((2*t : ℕ):ℝ)^t)^n.totient := by
      rw [norm_eq_prod_abs]
      calc
        _ ≤ ∏ _ : primitiveRoots n ℂ, ((2*t : ℕ):ℝ)^t := by
          apply prod_le_prod₀ (fun _ _ => norm_nonneg _)
          intro i _
          simp only [valAt,P,evaluate]
          exact height A B u v ((isPrimitiveRoot_of_mem_primitiveRoots i.2).norm'_eq_one (NeZero.ne n))
        _ = _ := by simp [Complex.card_primitiveRoots]
    apply Int.ofNat_le.mp
    rw [Int.natCast_natAbs]
    exact_mod_cast (by simpa only [pow_mul] using H : |(cycloNorm n P : ℝ)| ≤ ((2*t : ℕ):ℝ)^(t*n.totient))

end
end ProximityGap.ToricGraphMinorTransfer
#print axioms ProximityGap.ToricGraphMinorTransfer.transfer
