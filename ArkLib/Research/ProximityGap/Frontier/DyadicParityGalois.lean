/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

/-! # Galois parity on dyadic roots and three matched projective points -/

namespace ProximityGap.DyadicParityGalois
open Polynomial Finset
variable {K : Type*} [Field K]

/-- In every normal extension of ℚ containing a primitive dyadic root of order
at least four, a rational automorphism takes that root to its negative. -/
theorem exists_flip [CharZero K] [Algebra ℚ K] [Normal ℚ K] {m : ℕ} {z : K}
    (root : IsPrimitiveRoot z (2^(m+2))) : ∃ σ : K ≃ₐ[ℚ] K, σ z= -z := by
  let h := 2^(m+1)
  have pos : 0<h := by dsimp [h];positivity
  have len : 2^(m+2)=h*2 := by dsimp [h];rw [show m+2=m+1+1 by omega,pow_succ]
  have sqr : (z^h)^2=1 := by rw [←pow_mul,←len];exact root.pow_eq_one
  have minus : z^h= -1 := (sq_eq_one_iff.mp sqr).resolve_left
    (root.pow_ne_one_of_pos_of_lt pos.ne' (by omega))
  have cop : Nat.Coprime (h+1) (2^(m+2)) := by
    apply Nat.Coprime.pow_right
    apply Nat.coprime_two_right.mpr
    refine ⟨2^m,?_⟩
    dsimp [h];rw [pow_succ];omega
  have neg : IsPrimitiveRoot (-z) (2^(m+2)) := by
    have p := root.pow_of_coprime _ cop
    rwa [pow_succ,minus,neg_one_mul] at p
  apply isConjRoot_iff_exists_algEquiv.mp
  have irreducible := cyclotomic.irreducible_rat (by positivity : 0<2^(m+2))
  exact (neg.minpoly_eq_cyclotomic_of_irreducible irreducible).symm.trans
    (root.minpoly_eq_cyclotomic_of_irreducible irreducible)

/-- The sign lift is an involution on the cyclotomic field itself. -/
theorem twice [CharZero K] [Algebra ℚ K] {m : ℕ} [IsCyclotomicExtension {2^(m+2)} ℚ K]
    {z : K} (root : IsPrimitiveRoot z (2^(m+2))) (σ : K ≃ₐ[ℚ] K) (flip : σ z= -z)
    (x : K) : σ (σ x)=x := by
  have eq : σ.toAlgHom.comp σ.toAlgHom=AlgHom.id ℚ K := by
    apply (root.powerBasis ℚ).algHom_ext
    simp [flip]
  exact DFunLike.congr_fun eq x

/-- The two parity classes are precisely the positive and negative eigensites. -/
theorem action (σ : K ≃+* K) {z : K} (flip : σ z= -z) (i : ℕ) :
    σ (z^i)=if i%2=0 then z^i else -z^i := by
  rw [map_pow,flip]
  split_ifs with even
  · exact (Nat.even_iff.mpr even).neg_pow z
  · exact (Nat.odd_iff.mpr (by omega)).neg_pow z

/-- The finite affine graph of the projectivity represented by its four coefficients. -/
def Graph (a b c d x y : K) : Prop := a*x+b=y*(c*x+d)

private theorem den {a b c d x y : K} (det : a*d≠b*c) (edge : Graph a b c d x y) : c*x+d≠0 := by
  intro zero
  apply det
  change a*x+b=y*(c*x+d) at edge
  linear_combination a*zero-c*edge-c*y*zero

/-- Three distinct matched inputs determine the whole finite graph among
nonsingular projectivities. Coefficient normalizations are unnecessary. -/
theorem three {a b c d A B C D : K} (det : a*d≠b*c) (det' : A*D≠B*C)
    (x : Fin 3 ↪ K) (y : Fin 3 → K) (one : ∀ i, Graph a b c d (x i) (y i))
    (two : ∀ i, Graph A B C D (x i) (y i)) (s t : K) :
    Graph a b c d s t ↔ Graph A B C D s t := by
  let P : K[X] := (Polynomial.C a*X+Polynomial.C b)*(Polynomial.C C*X+Polynomial.C D)-
    (Polynomial.C A*X+Polynomial.C B)*(Polynomial.C c*X+Polynomial.C d)
  have zero : P=0 := by
    apply eq_zero_of_degree_lt_of_eval_index_eq_zero univ x.injective.injOn
    · rw [card_univ,Fintype.card_fin]
      dsimp [P];compute_degree!
    · intro i _
      have h₁ := one i
      have h₂ := two i
      dsimp only [Graph] at h₁ h₂
      simp only [P,eval_sub,eval_mul,eval_add,eval_C,eval_X]
      linear_combination (C*x i+D)*h₁-(c*x i+d)*h₂
  have eq := congrArg (eval s) zero
  simp only [P,eval_sub,eval_mul,eval_add,eval_C,eval_X,eval_zero] at eq
  constructor
  · intro st
    have nz := den det st
    change a*s+b=t*(c*s+d) at st
    change A*s+B=t*(C*s+D)
    apply mul_left_cancel₀ nz
    linear_combination (C*s+D)*st-eq
  · intro st
    have nz := den det' st
    change A*s+B=t*(C*s+D) at st
    change a*s+b=t*(c*s+d)
    apply mul_left_cancel₀ nz
    linear_combination (c*s+d)*st+eq

/-- Three fixed input/output matches imply covariance of the projective graph
at every match under the field automorphism. -/
theorem three_fixed (σ : K ≃+* K) {a b c d : K} (det : a*d≠b*c)
    (x : Fin 3 ↪ K) (y : Fin 3 → K) (fixX : ∀ i, σ (x i)=x i) (fixY : ∀ i, σ (y i)=y i)
    (edges : ∀ i, Graph a b c d (x i) (y i)) {s t : K} (edge : Graph a b c d s t) :
    Graph a b c d (σ s) (σ t) := by
  have mapped {u v : K} (uv : Graph a b c d u v) : Graph (σ a) (σ b) (σ c) (σ d) (σ u) (σ v) := by
    simpa only [Graph,map_mul,map_add] using congrArg σ uv
  have det' : σ a*σ d≠σ b*σ c := by simpa only [←map_mul,ne_eq,EmbeddingLike.apply_eq_iff_eq] using det
  apply (three det det' x y edges _ (σ s) (σ t)).mpr (mapped edge)
  intro i
  simpa only [fixX,fixY] using mapped (edges i)

private theorem out_unique {a b c d s t u : K} (det : a*d≠b*c)
    (st : Graph a b c d s t) (su : Graph a b c d s u) : t=u :=
  mul_right_cancel₀ (den det st) (st.symm.trans su)

private theorem in_unique {a b c d s t u : K} (det : a*d≠b*c)
    (st : Graph a b c d s t) (ut : Graph a b c d u t) : s=u := by
  have nz : a-t*c≠0 := by
    intro zero
    apply det
    dsimp only [Graph] at st
    linear_combination d*zero-c*st+c*s*zero
  apply mul_left_cancel₀ nz
  dsimp only [Graph] at st ut
  linear_combination st-ut

/-- After three even-to-even matches the remaining matches have identical
source and target exponent parities. Every odd match brings its antipode. -/
theorem parity [CharZero K] (σ : K ≃+* K) {z : K} (flip : σ z= -z) (nz : z≠0)
    {a b c d : K} (det : a*d≠b*c) (x : Fin 3 ↪ K) (y : Fin 3 → K)
    (fixX : ∀ i, σ (x i)=x i) (fixY : ∀ i, σ (y i)=y i) (edges : ∀ i, Graph a b c d (x i) (y i))
    {i j : ℕ} (edge : Graph a b c d (z^i) (z^j)) :
    i%2=j%2 ∧ (i%2=1 → Graph a b c d (-z^i) (-z^j)) := by
  have mapped := three_fixed σ det x y fixX fixY edges edge
  rw [action σ flip,action σ flip] at mapped
  have np (s : ℕ) : z^s≠ -z^s := by
    intro eq
    have zero : (2:K)*z^s=0 := by linear_combination eq
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ nz) zero
  by_cases ei : i%2=0 <;> by_cases ej : j%2=0
  · exact ⟨by omega,by omega⟩
  · simp only [ite_eq_left ei,ite_eq_right ej] at mapped
    exact (np j (out_unique det edge mapped)).elim
  · simp only [ite_eq_right ei,ite_eq_left ej] at mapped
    exact (np i (in_unique det edge mapped)).elim
  · exact ⟨by omega,fun _ => by simpa only [ite_eq_right ei,ite_eq_right ej] using mapped⟩

/-- Two different matched antipodal source orbits force an odd projectivity,
hence a scaling or a reciprocal. -/
theorem two_antipodal [CharZero K] {a b c d : K} (det : a*d≠b*c) {s t u v : K}
    (separate : s^2≠u^2) (st : Graph a b c d s t) (st' : Graph a b c d (-s) (-t))
    (uv : Graph a b c d u v) (uv' : Graph a b c d (-u) (-v)) :
    (b=0 ∧ c=0) ∨ (a=0 ∧ d=0) := by
  have con {p q : K} (e : Graph a b c d p q) (e' : Graph a b c d (-p) (-q)) :
      a*c*p^2=b*d := by
    dsimp only [Graph] at e e'
    apply mul_left_cancel₀ (by norm_num : (2:K)≠0)
    linear_combination (c*p-d)*e+(-c*p-d)*e'
  have e₁ := con st st'
  have e₂ := con uv uv'
  have zero : (a*c)*(s^2-u^2)=0 := by linear_combination e₁-e₂
  have ac := (mul_eq_zero.mp zero).resolve_right (sub_ne_zero.mpr separate)
  have bd : b*d=0 := by rw [←e₁,ac,zero_mul]
  rcases mul_eq_zero.mp ac with ha|hc <;> rcases mul_eq_zero.mp bd with hb|hd <;> simp_all

end ProximityGap.DyadicParityGalois
#print axioms ProximityGap.DyadicParityGalois.exists_flip
#print axioms ProximityGap.DyadicParityGalois.three_fixed
#print axioms ProximityGap.DyadicParityGalois.parity
#print axioms ProximityGap.DyadicParityGalois.two_antipodal
