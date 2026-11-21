/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarPrimitiveKernel
import ArkLib.Research.ProximityGap.Frontier.ApolarCoordinateTransport

/-! # Bounded polynomials and the rectangular moment matrix -/

open Polynomial Finset Matrix
open ProximityGap.ApolarDividedLocator ProximityGap.ApolarCoordinateTransport
namespace ProximityGap.ApolarMomentCoordinates

variable {R : Type*} [CommRing R]

/-- The linear functional defined by a sequence of moments. -/
noncomputable def functional (m : ℕ → R) : R[X] →ₗ[R] R :=
  Polynomial.lsum fun j => (m j) • LinearMap.id

@[simp] theorem functional_X_pow (m : ℕ → R) (i : ℕ) :
    functional m (X^i) = m i := by
  simp [functional, Polynomial.lsum_apply, X_pow_eq_monomial,smul_eq_mul]

/-- A polynomial with a prescribed bounded array of coefficients. -/
noncomputable def form {r : ℕ} (w : Fin (r+1) → R) : R[X] :=
  ∑ i, C (w i)*X^i.val

theorem form_degree {r : ℕ} (w : Fin (r+1) → R) : (form w).natDegree ≤ r := by
  classical
  apply natDegree_sum_le_of_forall_le
  intro i _
  have h := natDegree_C_mul_le (w i) (X^i.val)
  exact h.trans ((natDegree_X_pow_le i.val).trans (by have := i.isLt; omega))

theorem coeff_form {r : ℕ} (w : Fin (r+1) → R) (i : Fin (r+1)) : (form w).coeff i.val = w i := by
  classical
  simp only [form, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [sum_eq_single i]
  · simp
  · intro j _ hn
    simp [show i.val ≠ j.val from fun h => hn (Fin.ext h.symm)]
  · simp

theorem form_coeff {r : ℕ} (p : R[X]) (hp : p.natDegree ≤ r) :
    form (fun i : Fin (r+1) => p.coeff i.val) = p := by
  rw [form, Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i)*X^i)]
  exact (p.as_sum_range_C_mul_X_pow' (by omega)).symm

private theorem functional_form_mul_pow (m : ℕ → R) {r : ℕ} (w : Fin (r+1) → R) (j : ℕ) :
    functional m (form w * X^j) = ∑ i, m (j+i.val) * w i := by
  classical
  rw [form,Finset.sum_mul,map_sum]
  apply sum_congr rfl
  intro i _
  rw [mul_assoc,← pow_add,Nat.add_comm,← smul_eq_C_mul,map_smul,functional_X_pow,smul_eq_mul,mul_comm]

/-- The rectangular Hankel equations and the functional apolar conditions agree
on all bounded polynomials over the coefficient ring. -/
theorem equations_iff_apolar (m : ℕ → R) {r s : ℕ} (w : Fin (r+1) → R) :
    (∀ j ≤ s, ∑ i, m (j+i.val) * w i = 0) ↔ ApolarThrough (functional m) (form w) s := by
  classical
  constructor
  · intro h B hb
    apply Polynomial.induction_with_natDegree_le (fun q => functional m (form w*q)=0) s
      (by simp) _ _ B hb
    · intro j a _ hj
      rw [show form w*(C a*X^j) = a • (form w*X^j) by rw [smul_eq_C_mul];ring,
        map_smul, functional_form_mul_pow,h j hj,smul_zero]
    · intro p q _ _ hp hq
      rw [mul_add,map_add,hp,hq,zero_add]
  · intro h j hj
    rw [← functional_form_mul_pow]
    exact h _ ((natDegree_X_pow_le j).trans hj)

/-- Recover a polynomial functional from its moments on powers of the variable. -/
theorem functional_moments (L : R[X] →ₗ[R] R) : functional (fun j => L (X^j)) = L := by
  ext j
  simp [← X_pow_eq_monomial]

/-- A bounded polynomial with coefficients constant in the parameter preserves the
affine parameter degree of the original functional. -/
theorem functional_const_degree {K : Type*} [Field K] (m : ℕ → K[X]) {d : ℕ}
    (hm : ∀ i ≤ d, (m i).natDegree ≤ 1) (p : K[X]) (hp : p.natDegree ≤ d) :
    (functional m (p.map C)).natDegree ≤ 1 := by
  apply Polynomial.induction_with_natDegree_le (fun q => (functional m (q.map C)).natDegree ≤ 1) d
    (by simp) _ _ p hp
  · intro j a _ hj
    rw [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C,← smul_eq_C_mul,
      map_smul,functional_X_pow,smul_eq_mul]
    exact (natDegree_C_mul_le _ _).trans (hm j hj)
  · intro p q _ _ h₁ h₂
    rw [Polynomial.map_add,map_add]
    exact natDegree_add_le_of_degree_le h₁ h₂

/-- A chart change over the constant field preserves the affine parameter degree
of all moments of the binary functional. -/
theorem functional_chart_degree {K : Type*} [Field K] (m : ℕ → K[X]) {d : ℕ}
    (hm : ∀ i ≤ d, (m i).natDegree ≤ 1) (x z : K) (j : ℕ) (hj : j ≤ d) :
    ((functional m).comp (substitute d (X-C (C x)) (X-C (C z))) (X^j)).natDegree ≤ 1 := by
  let A : K[X] := X-C x
  let B : K[X] := X-C z
  have ha : A.natDegree ≤ 1 := by simp [A]
  have hb : B.natDegree ≤ 1 := by simp [B]
  have hdeg : (A^j*B^(d-j)).natDegree ≤ d := by
    have h₁ := natDegree_pow_le_of_le j ha
    have h₂ := natDegree_pow_le_of_le (d-j) hb
    have h₃ := natDegree_mul_le (p:=A^j) (q:=B^(d-j))
    omega
  have he := substitute_term ((X:K[X][X])-C (C x)) (X-C (C z)) 1 hj
  simp only [map_one,one_mul] at he
  rw [LinearMap.comp_apply,he]
  convert functional_const_degree m hm (A^j*B^(d-j)) hdeg using 2
  simp [A,B,Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_pow]

/-- The ordinary coordinate polynomial and its parameter-first storage give the
same polynomial in the parameter after evaluation at a coordinate. -/
theorem eval_form (K : Type*) [Field K] {r : ℕ} (w : Fin (r+1) → K[X]) (x : K) :
    (form w).eval (C x) = (ApolarPrimitiveKernel.family w).map (evalRingHom x) := by
  classical
  simp only [form,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,ApolarPrimitiveKernel.family,
    Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_map,Polynomial.map_C,
    Polynomial.map_pow,evalRingHom,coe_eval₂RingHom,eval₂_X, map_pow]
  all_goals simp

/-- The two chart specializations become the extreme coefficients of the transformed
locator. Its parameter-polynomial coefficients retain their full values. -/
theorem transformed_endpoints (K : Type*) [Field K] {r : ℕ} (w : Fin (r+1) → K[X]) (x z : K) :
    let g := substitute r (C (C z)*X-C (C x)) (X-1) (form w)
    g.coeff 0 = (-1)^r*(ApolarPrimitiveKernel.family w).map (evalRingHom x) ∧
      g.coeff r = (ApolarPrimitiveKernel.family w).map (evalRingHom z) := by
  dsimp only
  rw [bottom_coefficient _ _ _ (form_degree w),top_coefficient _ _ _ (form_degree w),
    eval_form K,eval_form K]
  exact ⟨rfl,rfl⟩

#print axioms equations_iff_apolar
#print axioms transformed_endpoints

end ProximityGap.ApolarMomentCoordinates
