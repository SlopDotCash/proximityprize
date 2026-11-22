/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.EulerSparsePower
import CompPoly.ToMathlib.Polynomial.Roots
import Mathlib.LinearAlgebra.Lagrange

/-! # A fractional-linear map carrying almost a whole coset back to a coset -/

namespace ProximityGap.DenseMobiusRigidity
open Polynomial Finset
variable {F : Type*} [Field F]

private noncomputable def term (n : ℕ) (a b : F) (U : F[X]) := (C a*X+C b)^n*U

private theorem degree_term {n r : ℕ} (a b : F) {U : F[X]} (du : U.natDegree≤r) :
    (term n a b U).natDegree≤n+r := by
  have low : (C a*X+C b).natDegree≤1 := by compute_degree
  exact natDegree_mul_le.trans (Nat.add_le_add ((natDegree_pow_le).trans (by simpa using Nat.mul_le_mul_left n low)) du)

private theorem concentrated {n : ℕ} {a b : F} (na : a≠0) (U : F[X]) :
    (X-C (-b/a))^n∣term n a b U := by
  have eq : C a*X+C b=C a*(X-C (-b/a)) := by
    rw [mul_sub,←map_mul,show a*(-b/a)= -b by field_simp,map_neg,sub_neg_eq_add]
  rw [term,eq,mul_pow]; exact ⟨C a^n*U,by ring⟩

private theorem term_nz {n : ℕ} {a b : F} (na : a≠0) {U : F[X]} (nz : U≠0) : term n a b U≠0 := by
  have deg : (C a*X+C b).natDegree=1 := by compute_degree!
  exact mul_ne_zero (pow_ne_zero _ (fun h => by simp [h] at deg)) nz

private theorem unmixed {n r i : ℕ} (lo : r < i) (hi : i < n) {a b : F} {U : F[X]}
    (du : U.natDegree≤r) (which : a=0 ∨ b=0) : (term n a b U).coeff i=0 := by
  rcases which with rfl|rfl
  · simp only [term,map_zero,zero_mul,zero_add,←map_pow,coeff_C_mul,
      coeff_eq_zero_of_natDegree_lt (du.trans_lt lo),mul_zero]
  · rw [term,map_zero,add_zero,mul_pow,show (C a)^n*X^n*U=X^n*((C a)^n*U) by ring,coeff_X_pow_mul',ite_eq_right hi.not_ge]

private theorem no_mixed {n r : ℕ} (gap : 3*r+2<n)
    (units : ∀ i : ℕ, 0 < i → i ≤ n+r → (i:F)≠0)
    {a b c d : F} (det : a*d≠b*c) (na : a≠0) (nb : b≠0) {U V : F[X]}
    (uNZ : U≠0) (vNZ : V≠0) (du : U.natDegree≤r) (dv : V.natDegree≤r)
    (eq : ∀ i : ℕ, r < i → i < n → (term n a b U).coeff i=(term n c d V).coeff i) : False := by
  have xNZ : -b/a≠0 := div_ne_zero (neg_ne_zero.mpr nb) na
  by_cases both : c≠0 ∧ d≠0
  · have yNZ : -d/c≠0 := div_ne_zero (neg_ne_zero.mpr both.2) both.1
    have distinct : -b/a≠-d/c := by
      intro h
      have e := (div_eq_div_iff na both.1).mp h
      exact det (by linear_combination e)
    obtain ⟨i,lo,hi,diff⟩ := EulerSparsePower.middle_differs gap units xNZ yNZ distinct
      (term_nz na uNZ) (term_nz both.1 vNZ) (degree_term a b du) (degree_term c d dv)
      (concentrated na U) (concentrated both.1 V)
    exact diff (eq i lo hi)
  push Not at both
  obtain ⟨i,lo,hi,haveCoeff⟩ := EulerSparsePower.middle_nonzero (n:=n) (r:=r) (by omega) units
    xNZ (term_nz na uNZ) (degree_term a b du) (concentrated na U)
  exact haveCoeff ((eq i lo hi).trans (unmixed lo hi dv (or_iff_not_imp_left.mpr both)))

/-- Let H be all n points of Xⁿ=α and let T be r exceptions. If elsewhere a
nonsingular fractional-linear map has its n-th power constant β≠0, then the
map is a scaling or a scaled reciprocal whenever n>3r+2 and the characteristic
is zero or exceeds n+r. The evaluation is written with cleared denominators. -/
theorem rigid {n r : ℕ} (gap : 3*r+2<n)
    (units : ∀ i : ℕ, 0 < i → i ≤ n+r → (i:F)≠0)
    {α β a b c d : F} (target : β≠0) (det : a*d≠b*c) (H T : Finset F)
    (order : H.card=n) (holes : T.card≤r) (roots : ∀ z∈H, z^n=α)
    (graph : ∀ z∈H, z∉T → (a*z+b)^n=β*(c*z+d)^n) :
    (b=0 ∧ c=0) ∨ (a=0 ∧ d=0) := by
  classical
  have nonzero : n≠0 := by omega
  let U := Lagrange.nodal T id
  let V := C β*U
  have unz : U≠0 := Lagrange.nodal_ne_zero
  have vnz : V≠0 := mul_ne_zero (C_ne_zero.mpr target) unz
  have du : U.natDegree≤r := (Lagrange.natDegree_nodal (s:=T) (v:=id)).le.trans holes
  have dv : V.natDegree≤r := by rw [show V=C β*U from rfl,natDegree_C_mul target];exact du
  let P := term n a b U
  let Q := term n c d V
  have degP := degree_term (n:=n) a b du
  have degQ := degree_term (n:=n) c d dv
  let W := X^n-C α
  have mono : W.Monic := monic_X_pow_sub_C _ nonzero
  have ident : W=Lagrange.nodal H id := by
    apply eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic mono
    · exact Polynomial.prod_X_sub_C_dvd H id Function.injective_id.injOn W (by simpa [W,sub_eq_zero] using roots)
    · simp [W,order]
  have vanishes (z : F) (hz : z∈H) : (P-Q).eval z=0 := by
    by_cases miss : z∈T
    · have zero : U.eval z=0 := Lagrange.eval_nodal_at_node (v:=id) miss
      simp [P,Q,term,V,zero]
    simp [P,Q,term,V,graph z hz miss]; ring
  obtain ⟨R,rel⟩ : W∣P-Q := ident ▸ Polynomial.prod_X_sub_C_dvd H id Function.injective_id.injOn _ vanishes
  have width : R.natDegree≤r := by
    by_cases zero : R=0
    · simp [zero]
    have bound : (P-Q).natDegree≤n+r := (natDegree_sub_le P Q).trans (max_le degP degQ)
    rw [rel,natDegree_mul mono.ne_zero zero,show W.natDegree=n from natDegree_X_pow_sub_C] at bound
    omega
  have eq (i : ℕ) (lo : r < i) (hi : i < n) : P.coeff i=Q.coeff i := by
    have e := congrArg (fun f : F[X] => f.coeff i) rel
    dsimp only [W] at e
    rw [sub_mul,coeff_sub,coeff_sub,coeff_C_mul,coeff_X_pow_mul',ite_eq_right hi.not_ge,
      coeff_eq_zero_of_natDegree_lt (width.trans_lt lo),mul_zero,sub_zero] at e
    exact sub_eq_zero.mp e
  have first : a=0 ∨ b=0 := by
    by_contra! both
    exact no_mixed gap units det both.1 both.2 unz vnz du dv eq
  have second : c=0 ∨ d=0 := by
    by_contra! both
    have reverse : c*b≠d*a := by simpa [mul_comm] using det.symm
    exact no_mixed gap units reverse both.1 both.2 vnz unz dv du (fun i lo hi => (eq i lo hi).symm)
  rcases first with rfl|rfl <;> rcases second with rfl|rfl <;> simp_all

end ProximityGap.DenseMobiusRigidity
#print axioms ProximityGap.DenseMobiusRigidity.rigid
