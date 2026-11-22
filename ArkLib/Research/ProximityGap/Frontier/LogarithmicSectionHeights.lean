/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PaddedPowerSpecialization
import Mathlib.RingTheory.Derivation.Basic

/-! # Local differentiation and specialization of tangent denominators

A differential ideal containing a small power of a received-branch equation
forces the derivative to vanish at its residue point. The degrees of common
denominators of two plane polynomials on distinct fibers are bounded by the
degree of their resultant.
-/
set_option autoImplicit false
open Finset Polynomial
namespace ArkLib.ProximityGap.Frontier.LogarithmicSectionHeights

variable {R : Type*} [CommRing R]

private theorem iterate_power (D : Derivation ℤ R R) (f : R) (h s : ℕ) :
    ∃ a : R, D^[h] (f^(h+s)) = f^s *
      (((h+s).descFactorial h : ℕ) * (D f)^h + f*a) := by
  induction h generalizing s with
  | zero => exact ⟨0, by simp⟩
  | succ h ih =>
    obtain ⟨a, ha⟩ := ih (s+1)
    let c : R := ((h+(s+1)).descFactorial h : ℕ)
    let v := c*(D f)^h+f*a
    have old : D^[h] (f^(h+1+s)) = f^(s+1)*v := by
      rw [show h+1+s = h+(s+1) by omega]
      exact ha
    refine ⟨((s+1:ℕ):R)*D f*a + D v, ?_⟩
    rw [Function.iterate_succ_apply', old, D.leibniz, D.leibniz_pow, Nat.descFactorial_succ]
    have arith : h+1+s-h = s+1 := by omega
    rw [arith, Nat.cast_mul]
    simp only [Nat.add_one_sub_one, smul_eq_mul, nsmul_eq_mul, pow_succ]
    have coeff : ((h+1+s).descFactorial h : R) = c := by
      rw [show h+1+s = h+(s+1) by omega]
    rw [coeff]
    dsimp only [v]
    ring

/-- If a stable ideal contains a power of f, differentiation preserves its
vanishing in any residue field where the corresponding factorial is nonzero. -/
theorem derivative_vanishes {K : Type*} [Field K] (D : Derivation ℤ R R)
    (I : Ideal R) (stable : ∀ x ∈ I, D x ∈ I) (φ : R →+* K)
    (kill : ∀ x ∈ I, φ x = 0) (f : R) (j : ℕ) (hf : φ f = 0)
    (hj : (j.factorial : K) ≠ 0) (hp : f^j ∈ I) : φ (D f) = 0 := by
  have hi (h : ℕ) : D^[h] (f^j) ∈ I := by
    induction h with
    | zero => exact hp
    | succ h ih =>
      rw [Function.iterate_succ_apply']
      exact stable _ ih
  obtain ⟨a, ha⟩ := iterate_power D f j 0
  simp only [Nat.add_zero, pow_zero, one_mul, Nat.descFactorial_self] at ha
  have hz := kill _ (hi j)
  rw [ha] at hz
  simp only [map_add, map_mul, map_pow, map_natCast, hf, zero_mul, add_zero] at hz
  exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hz).resolve_left hj)

/-- Clearing the pole of a root by differentiating an integral reciprocal. -/
theorem reciprocal_clearance (D : Derivation ℤ R R) {a y s : R} (h : a = y*s) :
    a * D y = D a * y - D s * y^2 := by
  rw [h, D.leibniz]
  simp only [smul_eq_mul]
  ring

variable {K : Type*} [Field K]

/-- Any nonzero common divisor in a specialized fiber charges the Sylvester
resultant its full degree, including when the second specialization vanishes. -/
theorem common_factor_charge (P Q : K[X][X]) (z : K) (D : K[X])
    (hP : P.map (evalRingHom z) ≠ 0) (hdP : D ∣ P.map (evalRingHom z))
    (hdQ : D ∣ Q.map (evalRingHom z)) :
    (X-C z)^D.natDegree ∣ resultant P Q P.natDegree Q.natDegree := by
  obtain ⟨p,hp⟩ := hdP
  obtain ⟨q,hq⟩ := hdQ
  have hDp : D*p ≠ 0 := hp ▸ hP
  have hd := left_ne_zero_of_mul hDp
  have hpn := right_ne_zero_of_mul hDp
  apply _root_.ProximityGap.PaddedPowerSpecialization.pow_dvd_resultant_of_syzygy
    P Q z le_rfl le_rfl p q hpn
  · rw [add_comm, ←natDegree_mul hd hpn, ←hp]
    exact natDegree_map_le
  · rcases eq_or_ne q 0 with he | he
    · exact Or.inl he
    · right
      rw [add_comm, ←natDegree_mul hd he, ←hq]
      exact natDegree_map_le
  · rw [hp,hq]
    ring

/-- Sum of all specialized common-divisor degrees over a finite scalar family. -/
theorem total_common_factor_degree (P Q : K[X][X])
    (hR : resultant P Q P.natDegree Q.natDegree ≠ 0) (S : Finset K) (D : K → K[X])
    (hP : ∀ z ∈ S, P.map (evalRingHom z) ≠ 0)
    (hdiv : ∀ z ∈ S, D z ∣ P.map (evalRingHom z) ∧ D z ∣ Q.map (evalRingHom z)) :
    ∑ z ∈ S, (D z).natDegree ≤ (resultant P Q P.natDegree Q.natDegree).natDegree := by
  apply SylvesterLocalMultiplicity.sum_local_orders_le_natDegree _ hR
  intro z hz
  exact common_factor_charge P Q z (D z) (hP z hz) (hdiv z hz).1 (hdiv z hz).2

/-- Two pairs of plane polynomials pay for every denominator dividing the
product of their specialized common factors. The rectangular degree bounds
also cover fibers in which just the second polynomial vanishes. -/
theorem two_resultant_height_budget (P Q U V : K[X][X]) (S : Finset K)
    (a b den : K → K[X]) (w m h g : ℕ)
    (hPQ : resultant P Q P.natDegree Q.natDegree ≠ 0)
    (hUV : resultant U V U.natDegree V.natDegree ≠ 0)
    (hP : ∀ z ∈ S, P.map (evalRingHom z) ≠ 0)
    (hU : ∀ z ∈ S, U.map (evalRingHom z) ≠ 0)
    (ha : ∀ z ∈ S, a z ∣ P.map (evalRingHom z) ∧ a z ∣ Q.map (evalRingHom z))
    (hb : ∀ z ∈ S, b z ∣ U.map (evalRingHom z) ∧ b z ∣ V.map (evalRingHom z))
    (hden : ∀ z ∈ S, den z ∣ a z * b z)
    (hdeg : P.natDegree ≤ w ∧ Q.natDegree ≤ w ∧ U.natDegree ≤ h ∧ V.natDegree ≤ h)
    (hcoeff : ∀ j, (P.coeff j).natDegree ≤ m ∧ (Q.coeff j).natDegree ≤ m ∧
      (U.coeff j).natDegree ≤ g ∧ (V.coeff j).natDegree ≤ g) :
    ∑ z ∈ S, (den z).natDegree ≤ 2*w*m+2*h*g := by
  have hpq := natDegree_resultant_le_of_coeff_natDegree_le P Q P.natDegree Q.natDegree m m
    (fun j => (hcoeff j).1) (fun j => (hcoeff j).2.1)
  have huv := natDegree_resultant_le_of_coeff_natDegree_le U V U.natDegree V.natDegree g g
    (fun j => (hcoeff j).2.2.1) (fun j => (hcoeff j).2.2.2)
  calc
    ∑ z ∈ S, (den z).natDegree ≤ ∑ z ∈ S, ((a z).natDegree+(b z).natDegree) := by
      apply sum_le_sum
      intro z hz
      have h₁ : a z ≠ 0 := ne_zero_of_dvd_ne_zero (hP z hz) (ha z hz).1
      have h₂ : b z ≠ 0 := ne_zero_of_dvd_ne_zero (hU z hz) (hb z hz).1
      exact (natDegree_le_of_dvd (hden z hz) (mul_ne_zero h₁ h₂)).trans natDegree_mul_le
    _ = _ := sum_add_distrib
    _ ≤ (Q.natDegree*m + P.natDegree*m) + (V.natDegree*g + U.natDegree*g) :=
      Nat.add_le_add ((total_common_factor_degree P Q hPQ S a hP ha).trans hpq)
        ((total_common_factor_degree U V hUV S b hU hb).trans huv)
    _ ≤ _ := by
      rcases hdeg with ⟨p,q,u,v⟩
      calc
        _ ≤ (w*m+w*m)+(h*g+h*g) := by gcongr
        _ = _ := by ring

/-- The two resultants give the stated numerical caps for the production sextic. -/
theorem sextic_prices (b : Fin 7) (hb : 2 ≤ b.val) :
    let n : ℕ := 1073741824
    let t : ℕ := 357913943
    let d : ℕ := 71582788
    let m : ℕ := 25
    let W := 2*t-1
    let a := (2*b.val-2)*W-b.val*(b.val-1)*d
    let g := (2*b.val-2)*m-b.val*(b.val-1)
    let h := 2*a*g+2*W*m
    let price := g+(2*b.val-1)*m+m + (2*t*(g+m)*n+n*(2*h+m*n))/(t*t-n*d)
    price = ![0,0,8489,23267,44589,70367,98657] b := by
  revert b
  decide

#print axioms derivative_vanishes
#print axioms reciprocal_clearance
#print axioms two_resultant_height_budget
#print axioms total_common_factor_degree
#print axioms sextic_prices
end ArkLib.ProximityGap.Frontier.LogarithmicSectionHeights
