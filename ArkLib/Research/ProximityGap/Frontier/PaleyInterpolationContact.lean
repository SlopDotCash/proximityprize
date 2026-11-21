/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PaleyDefectMinor
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Polynomial contact at a prescribed Paley shift

Lagrange weights annihilate low-degree moments. Euler's criterion then gives a polynomial
approximation supported on the minority sign at any specified shift in an odd finite field.
-/

namespace ProximityGap.PaleyInterpolationContact

open Finset Polynomial
open scoped Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

/-- The shifted moment of the leading-coefficient functional in Lagrange interpolation. -/
theorem nodalWeight_shift_moment (A : Finset K) (b : K) {k : ℕ} (hk : k < A.card) :
    ∑ u ∈ A, Lagrange.nodalWeight A id u * (b + u)^k =
      if k = A.card-1 then 1 else 0 := by
  let f : K[X] := (X + C b)^k
  have hdeg : f.natDegree = k := by simp [f, natDegree_pow]
  have h := Lagrange.coeff_eq_sum (s := A) (v := id) (P := f) (fun _ _ _ _ h => h)
    (lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hdeg.trans_lt hk))
  have hm : f.Monic := (monic_X_add_C b).pow k
  calc
    _ = f.coeff (A.card-1) := by
      rw [h]
      simp [Lagrange.nodalWeight, prod_inv_distrib, f, div_eq_mul_inv, add_comm, mul_comm]
    _ = _ := by
      split_ifs with he
      · rw [← he, ← hdeg, ← leadingCoeff, hm.leadingCoeff]
      · apply coeff_eq_zero_of_natDegree_lt
        omega

/-- The polynomial formed from Lagrange weights on a selected subset. -/
noncomputable def powerSum (A U : Finset K) (D : ℕ) : K[X] :=
  ∑ u ∈ U, C (Lagrange.nodalWeight A id u) * (X + C u)^D

private theorem shiftedCoeff (A U : Finset K) (D j : ℕ) (b : K) :
    ((powerSum A U D).comp (X + C b)).coeff j =
      (∑ u ∈ U, Lagrange.nodalWeight A id u * (b+u)^(D-j)) * D.choose j := by
  simp only [powerSum, Polynomial.sum_comp, mul_comp, C_comp, pow_comp, add_comp, X_comp,
    add_assoc, ← C_add, finsetSum_coeff, coeff_C_mul, coeff_X_add_C_pow, sum_mul, mul_assoc]

variable [Fintype K]

/-- Actual minority support at `b` yields contact to order `k+1` away from the pole and
order `k` when the pole is a site. Takes either sign, including when tied. -/
theorem minority_contact (hodd : ringChar K ≠ 2) (A : Finset K) (b : K)
    {k : ℕ} (hk : k < A.card) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    let D := Fintype.card K / 2 + k
    let E := A.filter fun u => quadraticChar K (b+u) = -σ
    (X - C b) ^ (if -b ∈ A then k else k+1) ∣
      powerSum A A D - C (if k = A.card-1 then (σ : K) else 0) -
        C 2 * powerSum A E D := by
  classical
  dsimp only
  let d := Fintype.card K / 2
  let w := Lagrange.nodalWeight A id
  change _ ∣ powerSum A A (d+k) - C _ - C 2 * powerSum A _ (d+k)
  rw [X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
  intro j hj
  have hjk : j ≤ k := by split at hj <;> omega
  have hpow (u : K) (hu : u ∈ A) :
      (if quadraticChar K (b+u) = -σ then (-1 : K) else 1) * (b+u)^(d+k-j) =
        (σ : K) * (b+u)^(k-j) := by
    rw [show d+k-j = d+(k-j) by omega, pow_add]
    by_cases hz : b+u=0
    · have hu' : -b ∈ A := by simpa [show -b = u by linear_combination -hz] using hu
      have hj' : j < k := by simpa [hu'] using hj
      simp [hz, zero_pow (show k-j ≠ 0 by omega)]
    · have hc := quadraticChar_eq_pow_of_char_ne_two' hodd (b+u)
      change (quadraticChar K (b+u) : K) = (b+u)^d at hc
      rw [← hc]
      have hs := quadraticChar_eq_pow_of_char_ne_two hodd hz
      split at hs <;> rcases hσ with rfl | rfl <;> simp [hs]
  have hsum : (∑ u ∈ A, w u * (b+u)^(d+k-j)) -
      2 * (∑ u ∈ A.filter (fun u => quadraticChar K (b+u) = -σ), w u * (b+u)^(d+k-j)) =
      (σ : K) * (if k-j = A.card-1 then 1 else 0) := by
    rw [← nodalWeight_shift_moment A b (show k-j < A.card by omega), Finset.mul_sum,
      Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    have he := hpow u hu
    split_ifs at he ⊢ <;> dsimp [w] at * <;> linear_combination Lagrange.nodalWeight A id u * he
  simp only [sub_comp, mul_comp, C_comp, coeff_sub, coeff_C_mul, shiftedCoeff]
  change (_ * _ - _) - 2 * (_ * _) = 0
  rw [show ∀ l c r t : K, l*t-c-2*(r*t)=(l-2*r)*t-c by intros; ring, hsum]
  by_cases hj0 : j=0
  · subst j
    simp [coeff_C_zero]
  · have hkj : k-j ≠ A.card-1 := by omega
    simp [hkj, coeff_C, hj0]

/-- At a specified prime-field shift the actual sign count forces determinant multiplicity.
The coordinate degree `k = A.card - 2` gives the central determinant, while
`k = A.card - 1` gives the two signed defect determinants. -/
theorem minority_determinant {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (A : Finset (ZMod p)) (b : ZMod p) {k h : ℕ} (hk : k < A.card)
    (hD : p/2+k < p)
    (hh : 2*h ≤ if -b ∈ A then k else k+1)
    {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    let D := p/2+k
    let E := A.filter fun u => quadraticChar (ZMod p) (b+u) = -σ
    let ν := if -b ∈ A then k else k+1
    let r := h+1-E.card
    let F := powerSum A A D - C (if k = A.card-1 then (σ : ZMod p) else 0)
    (X - C b) ^ (r*(ν-2*h)+r*(r-1)) ∣ (PaleyDefectMinor.normalizedHankel F D h).det := by
  classical
  let E := A.filter fun u => quadraticChar (ZMod p) (b+u) = -σ
  let D := p/2+k
  let ν := if -b ∈ A then k else k+1
  let F := powerSum A A D - C (if k = A.card-1 then (σ : ZMod p) else 0)
  let site (i : Fin E.card) : ZMod p := E.equivFin.symm i
  let w := Lagrange.nodalWeight A id
  have htwo : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hwidth : 2*h ≤ D := by
    change _ ≤ p/2+k
    split at hh <;> omega
  have hunit (j : ℕ) (hj : j ≤ 2*h) : (D.descFactorial j : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hdvd' : p ∣ D.factorial := Nat.dvd_trans hdvd
      ⟨(D-j).factorial, by rw [mul_comm, Nat.factorial_mul_descFactorial (hj.trans hwidth)]⟩
    exact (not_le.mpr hD) ((Fact.out : p.Prime).dvd_factorial.mp hdvd')
  have hc := minority_contact (K := ZMod p) (by rwa [ZMod.ringChar_zmod_n]) A b hk hσ
  have hfull : (X - C b)^ν ∣ F - C 2 * powerSum A E D := by
    simpa only [ZMod.card, D, F, ν, E] using hc
  have hsum : (∑ i : Fin E.card, C (2*w (site i))*(X+C (site i))^D) =
      C 2 * powerSum A E D := by
    let g (u : ZMod p) : (ZMod p)[X] := C (2*w u)*(X+C u)^D
    change (∑ i, g (E.equivFin.symm i)) = _
    rw [E.equivFin.symm.sum_comp (fun u : E => g u.val)]
    simp [g, w, powerSum, Finset.mul_sum, mul_assoc]
    exact E.sum_attach (fun u : ZMod p => C 2 * (C (Lagrange.nodalWeight A id u) * (X+C u)^D))
  apply PaleyDefectMinor.pow_dvd_normalizedHankel_of_contact F (X-C b)
    site (fun i => 2*w (site i)) D h (ν-2*h) hwidth hunit
  rw [hsum, Nat.sub_add_cancel hh]
  exact hfull

end ProximityGap.PaleyInterpolationContact

#print axioms ProximityGap.PaleyInterpolationContact.minority_contact

#print axioms ProximityGap.PaleyInterpolationContact.minority_determinant
