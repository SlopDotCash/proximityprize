/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.CyclotomicProjectiveTransfer
import Mathlib.Analysis.Matrix.Order

/-! # Ordered Cauchy–Binet and the column energy bound for complex minors -/

namespace ProximityGap.JointMinorGram
open Finset Matrix Equiv
open scoped ComplexConjugate MatrixOrder ComplexOrder
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

/-- The square minor of a rectangular matrix on an ordered tuple of rows.
Repeated rows give zero. -/
noncomputable def minor {R : Type*} [CommRing R] (M : Matrix J I R) (f : I → J) : R :=
  (M.submatrix f id).det

private theorem expansion {R : Type*} [CommRing R] (A : Matrix I J R) (B : Matrix J I R) :
    (A*B).det=∑ f : I → J, (∏ i,A i (f i))*minor B f := by
  classical
  let d := (Matrix.detRowAlternating (R:=R) (n:=I)).toMultilinearMap
  have eq : A*B=fun i => ∑ j, A i j • B j := by ext i j;simp [Matrix.mul_apply,Pi.smul_apply]
  change d (A*B)=_
  rw [eq,MultilinearMap.map_sum]
  apply sum_congr rfl
  intro f _
  exact d.map_smul_univ (fun i => A i (f i)) (fun i => B (f i))

/-- Ordered Cauchy–Binet. Each unordered minor occurs once per permutation
of its rows. The formula also works when there are fewer rows than columns. -/
theorem ordered (M : Matrix J I ℂ) :
    (∑ f : I → J, conj (minor M f)*minor M f)=(Fintype.card (Perm I):ℂ)*(Mᴴ*M).det := by
  classical
  let term (f : I → J) := (∏ i,conj (M (f i) i))*minor M f
  have base : ∑ f,term f=(Mᴴ*M).det := (expansion Mᴴ M).symm
  have alter (f : I → J) (σ : Perm I) :
      minor M (f ∘ σ)=((Perm.sign σ : ℤ):ℂ)*minor M f := Matrix.det_permute σ (M.submatrix f id)
  have one (f : I → J) : conj (minor M f)*minor M f=∑ σ : Perm I,term (f ∘ σ) := by
    conv_lhs => arg 1;rw [minor,Matrix.det_apply',map_sum]
    rw [sum_mul]
    apply sum_congr rfl
    intro σ _
    simp only [term,alter,map_mul,map_intCast,map_prod,Matrix.submatrix_apply,Function.comp_apply,id_eq]
    ring
  simp_rw [one]
  rw [sum_comm]
  have perm (σ : Perm I) : (∑ f : I → J, term (f ∘ σ))=∑ f, term f := by
    exact (Equiv.arrowCongr σ.symm (Equiv.refl J)).sum_comp term
  simp_rw [perm,base]
  simp

/-- Hadamard's inequality for the Gram determinant of rectangular columns,
derived by applying the square inequality to a square factor of the Gram matrix. -/
theorem gram_le {n : ℕ} (M : Matrix J (Fin n) ℂ) : ‖(Mᴴ*M).det‖ ≤ ∏ i, ∑ j, ‖M j i‖^2 := by
  classical
  obtain ⟨S,hs⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (Matrix.posSemidef_conjTranspose_mul_self M).nonneg
  rw [Matrix.star_eq_conjTranspose] at hs
  have diag (i : Fin n) : ∑ j,‖S j i‖^2=∑ j,‖M j i‖^2 := by
    have eq := congrArg (fun H : Matrix (Fin n) (Fin n) ℂ => (H i i).re) hs
    have re (x : ℂ) : (star x*x).re=‖x‖^2 := by
      change (conj x*x).re=_
      rw [←Complex.normSq_eq_conj_mul_self,Complex.ofReal_re,Complex.sq_norm]
    simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum,re] using eq.symm
  have h := CyclotomicProjectiveTransfer.hadamard S.transpose
  rw [Matrix.det_transpose] at h
  simp only [Matrix.transpose_apply,diag] at h
  have sq := (sq_le_sq₀ (norm_nonneg _) (prod_nonneg (fun i _ => Real.sqrt_nonneg _))).mpr h
  rw [hs,Matrix.det_mul,Matrix.det_conjTranspose,norm_mul,norm_star,←pow_two]
  simpa only [←prod_pow,show ∀ i, (Real.sqrt (∑ j,‖M j i‖^2))^2=∑ j,‖M j i‖^2 from fun _ => Real.sq_sqrt (by positivity)] using sq

/-- A rectangular complex matrix pays at most the product of its column
energies for the sum of squared minors, with an ordered-tuple factorial. -/
theorem total {n : ℕ} (M : Matrix J (Fin n) ℂ) :
    ∑ f : Fin n → J, ‖minor M f‖^2 ≤ Fintype.card (Perm (Fin n))*∏ i,∑ j,‖M j i‖^2 := by
  have calcNorm := congrArg (fun x : ℂ => ‖x‖) (ordered M)
  have eq : (∑ f : Fin n → J, ‖minor M f‖^2)=(Fintype.card (Perm (Fin n)):ℝ)*‖(Mᴴ*M).det‖ := by
    have e (x : ℂ) : conj x*x=(‖x‖^2 : ℝ) := by rw [←Complex.normSq_eq_conj_mul_self,Complex.sq_norm]
    simp_rw [e] at calcNorm
    have nn : 0≤∑ f : Fin n → J, ‖minor M f‖^2 := sum_nonneg (fun _ _ => sq_nonneg _)
    simpa only [←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg nn,
      norm_mul,Complex.norm_natCast] using calcNorm
  exact eq.le.trans (mul_le_mul_of_nonneg_left (gram_le M) (Nat.cast_nonneg _))

end ProximityGap.JointMinorGram
#print axioms ProximityGap.JointMinorGram.total
