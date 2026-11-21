/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarDividedLocator
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Polynomial representative of the divided syndrome

The quotient-ring value of a divided syndrome is the reduction of an explicit
polynomial. The polynomial commutes with specialization of the coefficients.
This turns sparsity of an actual neighboring word into divisibility on its fiber.
-/

set_option autoImplicit false
open Polynomial Finset
namespace ProximityGap.ApolarDividedPolynomial
open ApolarDividedLocator

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem split_at (f : R[X]) (a : R) :
    C (f.eval a) + (X-C a)*divided f a = f := by
  have h := f.modByMonic_add_div (X-C a)
  rw [modByMonic_X_sub_C_eq_C_eval] at h
  exact h

private theorem divided_C (c a : R) : divided (C c) a = 0 := by
  nontriviality R
  apply (divByMonic_eq_zero_iff (monic_X_sub_C a)).mpr
  exact degree_C_le.trans_lt (by rw [degree_X_sub_C]; decide)

private theorem divided_mul_X (f : R[X]) (a : R) :
    divided (f*X) a = C (f.eval a) + X*divided f a := by
  have h : f*X = C (f.eval a*a) + (X-C a)*(C (f.eval a)+X*divided f a) := by
    rw [map_mul]
    linear_combination X*(split_at f a).symm
  rw [h,divided,add_divByMonic,mul_divByMonic_cancel_left _ (monic_X_sub_C _),
    show C (f.eval a*a) /ₘ (X - C a) = 0 from divided_C _ _,zero_add]

/-- Synthetic division has a symmetric evaluation even over nonreduced rings. -/
theorem eval_divided_comm (f : R[X]) (a b : R) :
    (divided f a).eval b = (divided f b).eval a := by
  induction f using Polynomial.induction_on with
  | C c => simp only [divided_C,eval_zero]
  | add f g hf hg => simpa only [divided,add_divByMonic,eval_add] using congrArg₂ (·+·) hf hg
  | monomial n c ih =>
    rw [pow_succ,← mul_assoc,divided_mul_X,divided_mul_X]
    have h := congrArg (Polynomial.eval b) (split_at (C c * X^n) a)
    simp only [eval_add,eval_C,eval_mul,eval_sub,eval_X] at h ⊢
    rw [← ih]
    linear_combination h

/-- An actual polynomial in the root coordinate for a finitely supported functional. -/
noncomputable def representative {ι : Type*} (D : Finset ι) (site weight : ι → R)
    (f : R[X]) : R[X] := ∑ i ∈ D, C (weight i) * divided f (site i)

/-- Base change of the locator and all weights commutes with its representative. -/
theorem map_representative {ι : Type*} (D : Finset ι) (site weight : ι → R)
    (φ : R →+* S) (f : R[X]) :
    (representative D site weight f).map φ =
      representative D (φ ∘ site) (φ ∘ weight) (f.map φ) := by
  simp only [representative,Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_C,Function.comp_apply,
    divided,map_divByMonic φ (monic_X_sub_C _),Polynomial.map_sub,map_X]

variable {K : Type*} [Field K]

/-- Evaluation of the literal representative agrees with the extended syndrome in
every coefficient algebra, including the quotient by a non-squarefree locator. -/
theorem eval₂_representative (D : Finset K) (w : K → K) (φ : K →+* R) (x : R) (f : K[X]) :
    (representative D id w f).eval₂ φ x = weighted D φ w (divided (f.map φ) x) := by
  rw [← eval_map,map_representative,weighted_apply,representative,eval_finsetSum]
  apply sum_congr rfl
  intro i hi
  simp only [Function.comp_apply,id_eq,eval_mul,eval_C]
  rw [eval_divided_comm]

/-- On an actual nearby Reed–Solomon word, the complete locator divides the
domain vanisher times the representative, including all repeated factors. -/
theorem fiber_dvd (H E : Finset K) (u : K → K) (Q f : K[X]) {s : ℕ}
    (hE : E ⊆ H) (hoff : ∀ x ∈ H, x ∉ E → u x = Q.eval x)
    (hc : E.card ≤ s+1) (hd : Q.natDegree + f.natDegree + s < H.card-1)
    (ha : ApolarThrough (syndrome H (RingHom.id K) u) f s) :
    f ∣ Lagrange.nodal H id * representative H id (rowWeight H u) f := by
  apply AdjoinRoot.mk_eq_zero.mp
  rw [← AdjoinRoot.aeval_eq,aeval_def,eval₂_mul,eval₂_representative]
  convert syndrome_quotient_fiber H E u Q f hE hoff hc hd ha using 1
  simp [Lagrange.nodal, eval₂_finsetProd,eval_prod,AdjoinRoot.algebraMap_eq,syndrome]

/-- Parameter degrees of the coefficients of the representative of a pencil.
Dividing by a constant site leaves each parameter-degree bound intact. -/
theorem pencil_coefficient_degree (D : Finset K) (w : K → K[X]) (f : K[X][X]) (l : ℕ)
    (hw : ∀ i ∈ D, (w i).natDegree ≤ 1) (hf : ∀ j, (f.coeff j).natDegree ≤ l) (j : ℕ) :
    ((representative D C w f).coeff j).natDegree ≤ l+1 := by
  classical
  rw [representative,finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  rw [coeff_C_mul,divided,coeff_divByMonic_X_sub_C]
  apply natDegree_mul_le.trans
  have hs : (∑ v ∈ Icc (j+1) f.natDegree, (C i)^(v-(j+1))*f.coeff v).natDegree ≤ l := by
    apply natDegree_sum_le_of_forall_le
    intro v _
    rw [← C_pow]
    exact (natDegree_C_mul_le ..).trans (hf v)
  have := hw i hi
  omega

/-- Specializing the polynomial-weight pencil at a scalar gives precisely the
divided polynomial of the mixed received word. -/
theorem specialize_syndrome_pencil (H : Finset K) (u v : K → K) (f : K[X][X]) (t : K) :
    (representative H C (fun x => C (rowWeight H u x)+X*C (rowWeight H v x)) f).map
      (evalRingHom t) =
    representative H id (rowWeight H (fun x => u x+t*v x)) (f.map (evalRingHom t)) := by
  rw [map_representative]
  congr 1
  · funext x
    simp
  · funext x
    simp [rowWeight,add_div,mul_div_assoc]
    exact mul_comm _ _

/-- A generic minimal locator is coprime to the explicit divided polynomial.
Minimality can be tested by a nonsingular minor over the coefficient field. -/
theorem coprime_of_geometric_minimality {L : Type*} [Field L] [IsAlgClosed L] [Algebra K L]
    (D : Finset K) (w : K → K) (f : K[X]) {r s : ℕ} (hf : f.natDegree = r+1)
    (ha : ApolarThrough (weighted D (algebraMap K L) w) (f.map (algebraMap K L)) s)
    (hprev : ∀ q : L[X], q.natDegree = r → q ≠ 0 →
      ¬ ApolarThrough (weighted D (algebraMap K L) w) q (s+1)) :
    IsCoprime f (representative D id w f) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K L _ _).mpr
  intro x
  by_cases hx : aeval x f = 0
  · right
    rw [aeval_def,eval₂_representative]
    apply divided_nonzero _ _ x (by simpa using hf) _ ha hprev
    simpa only [IsRoot,eval_map,aeval_def] using hx
  · exact Or.inl hx

#print axioms pencil_coefficient_degree
#print axioms specialize_syndrome_pencil
#print axioms coprime_of_geometric_minimality
#print axioms eval_divided_comm
#print axioms map_representative
#print axioms fiber_dvd
end ProximityGap.ApolarDividedPolynomial
