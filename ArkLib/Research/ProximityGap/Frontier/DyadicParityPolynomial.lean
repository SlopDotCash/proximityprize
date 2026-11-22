/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicRationalSites
import Mathlib.Algebra.Polynomial.Expand

/-! # Removing antipodal symmetries from a rational function -/
namespace ProximityGap.DyadicParityPolynomial
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

private theorem flip_coeff (P : K[X]) (i : ℕ) :
    (P.comp (-X)).coeff i = P.coeff i * (-1)^i := by
  induction P using Polynomial.induction_on' with
  | add P Q h k => simp [add_comp,h,k,add_mul]
  | monomial j a =>
    rw [← C_mul_X_pow_eq_monomial,mul_comp,C_comp,pow_comp,X_comp,
      show (-X : K[X])=C (-1)*X by simp,mul_pow,← map_pow,← mul_assoc,← C_mul]
    simp only [coeff_C_mul,coeff_X_pow]
    split_ifs with eq <;> simp_all

/-- An eigenpolynomial for X ↦ −X is a polynomial in X², possibly times X. -/
theorem split {P : K[X]} (pn : P≠0) (divides : P ∣ P.comp (-X)) :
    ∃ (r : ℕ) (V : K[X]), r≤1 ∧ V≠0 ∧ P=X^r*expand K 2 V := by
  obtain ⟨U,hu⟩ := divides
  have un : U≠0 := by intro h; rw [h,mul_zero,comp_neg_X_eq_zero_iff] at hu; exact pn hu
  have ub : U.natDegree=0 := by
    have h : (P.comp (-X)).natDegree≤P.natDegree := natDegree_comp_le.trans (by simp)
    rw [hu,natDegree_mul pn un] at h
    omega
  let a := U.coeff 0
  have mult : P.comp (-X)=C a*P := hu.trans (by rw [eq_C_of_natDegree_eq_zero ub,mul_comm])
  have sign (j : ℕ) (nz : P.coeff j≠0) : a=(-1:K)^j := by
    have h := congrArg (fun f : K[X] => f.coeff j) mult
    simp only [flip_coeff,coeff_C_mul] at h
    exact mul_right_cancel₀ nz (by linear_combination -h)
  let r := P.natDegree%2
  have parity (j : ℕ) (hj : P.coeff j≠0) : j%2=r := by
    have same := (sign j hj).symm.trans (sign _ (leadingCoeff_ne_zero.mpr pn))
    by_contra neq
    by_cases ev : j%2=0
    · have ev' : P.natDegree%2=1 := by dsimp [r] at neq;omega
      rw [(Nat.even_iff.mpr ev).neg_one_pow,(Nat.odd_iff.mpr ev').neg_one_pow] at same
      norm_num at same
    · have ev' : P.natDegree%2=0 := by dsimp [r] at neq;omega
      rw [(Nat.odd_iff.mpr (by omega : j%2=1)).neg_one_pow,(Nat.even_iff.mpr ev').neg_one_pow] at same
      norm_num at same
  have expand_even (F : K[X]) (even : ∀ i, F.coeff i≠0 → i%2=0) :
      expand K 2 (F.contract 2)=F := by
    ext i
    rw [coeff_expand (by decide),coeff_contract (by decide)]
    split_ifs with h
    · congr 1;omega
    · exact (by by_contra! bad;exact h (by have := even i bad.symm;omega) : 0=F.coeff i)
  by_cases e : r=0
  · have eq := expand_even P (by simpa only [e] using parity)
    exact ⟨0, P.contract 2,by decide,fun h => pn (by rw [←eq,h,map_zero]),by simpa using eq.symm⟩
  · have o : r=1 := by dsimp [r] at *; omega
    have c₀ : P.coeff 0=0 := by by_contra nz;have := parity 0 nz;omega
    have eq := expand_even P.divX (by
      intro i hi
      have h := parity (i+1) (by simpa only [coeff_divX] using hi)
      omega)
    have orig : X * P.divX=P := by simpa [c₀] using X_mul_divX_add P
    refine ⟨1,P.divX.contract 2,by decide,?_,by simpa [eq] using orig.symm⟩
    intro h; apply pn
    rw [←orig,←eq,h,map_zero,mul_zero]

/-- If a reduced fraction has one of the two global antipodal symmetries,
both polynomials individually have a single exponent parity. -/
theorem split_pair {P Q : K[X]} (pn : P≠0) (qn : Q≠0) (cop : IsCoprime P Q)
    {e : K} (en : e≠0) (eq : DyadicRationalSites.comparison P Q e=0) :
    ∃ (r s : ℕ) (U V : K[X]), r≤1 ∧ s≤1 ∧ U≠0 ∧ V≠0 ∧
      P=X^r*expand K 2 U ∧ Q=X^s*expand K 2 V ∧ IsCoprime U V := by
  change P.comp (-X)*Q-C e*P*Q.comp (-X)=0 at eq
  have rel := sub_eq_zero.mp eq
  have pd : P ∣ P.comp (-X) := cop.dvd_of_dvd_mul_right
    ⟨C e*Q.comp (-X),by rw [rel];ring⟩
  have qd : Q ∣ Q.comp (-X) := by
    apply cop.symm.dvd_of_dvd_mul_right
    refine ⟨C e⁻¹*P.comp (-X),?_⟩
    calc Q.comp (-X)*P = C e⁻¹*(C e*P*Q.comp (-X)) := by
           rw [show C e⁻¹*(C e*P*Q.comp (-X))=C (e⁻¹*e)*(Q.comp (-X)*P) by rw [map_mul];ring,
             inv_mul_cancel₀ en,map_one,one_mul]
         _ = _ := by rw [←rel];ring
  obtain ⟨r,U,rb,un,pu⟩ := split pn pd
  obtain ⟨s,V,sb,vn,qv⟩ := split qn qd
  refine ⟨r,s,U,V,rb,sb,un,vn,pu,qv,?_⟩
  apply (isCoprime_expand (by decide : 2≠0)).mp
  rw [pu,qv] at cop
  exact (IsCoprime.mul_right_iff.mp (IsCoprime.mul_left_iff.mp cop).2).2

end ProximityGap.DyadicParityPolynomial
#print axioms ProximityGap.DyadicParityPolynomial.split_pair
