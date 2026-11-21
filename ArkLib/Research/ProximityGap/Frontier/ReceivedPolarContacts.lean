/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ReceivedJetContact
import ArkLib.Research.ProximityGap.Frontier.BinaryBranchResultant
import Mathlib.RingTheory.Derivation.MapCoeffs

/-! # First partials at a received interpolation leader

A translated leader of total degree r forces each first partial into the
(r−1)st power of the point ideal. The valuation is measured on the same
projective coordinates that compute all original resultants.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset
open scoped PowerSeries BigOperators Differential

namespace ArkLib.ProximityGap.Frontier.ReceivedPolarContacts

open ReceivedJetContact BinaryBranchResultant

variable {K : Type} [Field K]

/-- Ordinary coordinate derivative, acting on the coefficients in K[X]. -/
def dx (F : K[X][X]) : K[X][X] :=
  let _ : Differential K[X] := ⟨(Polynomial.derivative' (R := K)).restrictScalars ℤ⟩
  Differential.mapCoeffs F

theorem coeff_dx (F : K[X][X]) (i : ℕ) : (dx F).coeff i = (F.coeff i).derivative := rfl

private theorem derivative_taylor {R : Type*} [CommRing R] (a : R) (F : R[X]) :
    (F.taylor a).derivative = F.derivative.taylor a := by
  simp [taylor_apply, derivative_comp]

private theorem dx_taylor (F : K[X][X]) (l : K) : dx (F.taylor (C l)) = (dx F).taylor (C l) := by
  let _ : Differential K[X] := ⟨(Polynomial.derivative' (R := K)).restrictScalars ℤ⟩
  change Differential.mapCoeffs (F.taylor (C l)) = (Differential.mapCoeffs F).taylor (C l)
  have hl : Differential.deriv (C l : K[X]) = 0 := derivative_C
  induction F using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add, hf, hg]
  | monomial k a =>
    simp [taylor_apply, monomial_comp, Derivation.leibniz, Derivation.leibniz_pow, hl, mul_comm]

theorem dx_shifted (F : K[X][X]) (α l : K) : dx (shifted F α l) = shifted (dx F) α l := by
  unfold shifted
  rw [dx_taylor]
  congr 1
  ext1 i
  simp only [coeff_dx, Polynomial.coeff_map]
  exact derivative_taylor α _

theorem dy_shifted (F : K[X][X]) (α l : K) :
    (shifted F α l).derivative = shifted F.derivative α l := by
  rw [shifted, derivative_taylor, derivative_map]
  rfl

/-- Both shifted gradients have no monomials of total degree below r−1. -/
theorem first_partials_lower (F : K[X][X]) (α l : K) (r j : ℕ)
    (hr : TruncatedJetMultipliers.Leader (shifted F α l) r j) :
    (∀ i k, i+k<r-1 → ((shifted (dx F) α l).coeff i).coeff k = 0) ∧
    (∀ i k, i+k<r-1 → ((shifted F.derivative α l).coeff i).coeff k = 0) := by
  constructor <;> intro i k hik
  · rw [← dx_shifted, coeff_dx, coeff_derivative, hr.lower i (k+1) (Or.inl (by omega)), zero_mul]
  · rw [← dy_shifted, coeff_derivative]
    have hz := hr.lower (i+1) k (Or.inl (by omega))
    rw [← Nat.cast_succ, ← Polynomial.C_eq_natCast, coeff_mul_C, hz, zero_mul]

/-- Universal local substitution of any point ideal power. -/
theorem shifted_substitution_dvd {S : Type*} [CommRing S] (H : K[X][X]) (r : ℕ)
    (h : ∀ i j, i+j<r → (H.coeff i).coeff j=0) (φ : K[X] →+* S) (d v : S)
    (hd : d ∣ φ Polynomial.X) (hv : d ∣ v) :
    d^r ∣ (H.map φ).eval v := by
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum]
  apply Finset.dvd_sum
  intro i _
  have hdiv : (Polynomial.X : K[X])^(r-i) ∣ H.coeff i := by
    rw [Polynomial.X_pow_dvd_iff]
    exact fun k hk => h i k (by omega)
  have h₁ : d^(r-i) ∣ φ (H.coeff i) := by
    apply (pow_dvd_pow_of_dvd hd (r-i)).trans
    simpa only [map_pow] using map_dvd φ hdiv
  exact (pow_dvd_pow d (show r ≤ r-i+i by omega)).trans
    (by rw [pow_add]; exact mul_dvd_mul h₁ (pow_dvd_pow_of_dvd hv _))

/-- Evaluate the translated plane polynomial using the common tame
parameter. Both sides refer to the same original point and ordinate. -/
theorem shifted_eval (G : K[X][X]) (α l : K) {n : ℕ} (hn : n ≠ 0) (v : K⟦X⟧) :
    let e := (PowerSeries.expand n hn (R := K)).toRingHom
    let χ := e.comp Polynomial.coeToPowerSeries.ringHom
    ((shifted G α l).map χ).eval (v-PowerSeries.C l) =
      ((G.map (PolynomialLocalOrder.atPoint α)).map e).eval v := by
  let e := (PowerSeries.expand n hn (R := K)).toRingHom
  let χ := e.comp Polynomial.coeToPowerSeries.ringHom
  have hl : χ (C l) = PowerSeries.C l := by
    change PowerSeries.expand n hn ((C l : K[X]) : K⟦X⟧) = _
    rw [Polynomial.coe_C, PowerSeries.expand_C]
  change ((shifted G α l).map χ).eval _ = _
  rw [shifted, Polynomial.map_taylor, taylor_apply, eval_comp, eval_add, eval_X, eval_C, hl,
    sub_add_cancel, Polynomial.map_map, Polynomial.map_map]
  rfl

/-- A shifted zero of total order m becomes a zero of order at least s*m
on a finite unit chart, using projective contact of order s≤n. -/
theorem projective_partial_order (G : K[X][X]) (α l : K) (m : ℕ)
    (hzero : ∀ i j, i+j<m → ((shifted G α l).coeff i).coeff j=0)
    {n : ℕ} (hn : n ≠ 0) (s : ℕ) (hs : s ≤ n) (a : K⟦X⟧ˣ) (b : K⟦X⟧)
    (hc : (s : ℕ∞) ≤ (PowerSeries.C l*(a:K⟦X⟧)-b).order)
    (h : ℕ) (hG : G.natDegree ≤ h) :
    let e := (PowerSeries.expand n hn (R := K)).toRingHom
    ((s*m : ℕ) : ℕ∞) ≤ (binaryValue ((G.map (PolynomialLocalOrder.atPoint α)).map e)
      h b (a:K⟦X⟧)).order := by
  let e := (PowerSeries.expand n hn (R := K)).toRingHom
  let χ := e.comp Polynomial.coeToPowerSeries.ringHom
  let t := PowerSeries.X (R := K)
  let v := (↑a⁻¹ : K⟦X⟧)*b
  have hd : t^s ∣ χ Polynomial.X := by
    change t^s ∣ PowerSeries.expand n hn ((Polynomial.X : K[X]) : K⟦X⟧)
    rw [Polynomial.coe_X, PowerSeries.expand_X]
    exact pow_dvd_pow t hs
  have hw : t^s ∣ v-PowerSeries.C l := by
    have h₀ : t^s ∣ PowerSeries.C l*(a:K⟦X⟧)-b :=
      PowerSeries.X_pow_dvd_iff.mpr (PowerSeries.nat_le_order_iff.mp hc)
    have heq : v-PowerSeries.C l = -(↑a⁻¹ : K⟦X⟧)*(PowerSeries.C l*(a:K⟦X⟧)-b) := by
      simp [v, mul_sub, mul_left_comm, mul_comm]
      ring
    rw [heq]
    exact dvd_mul_of_dvd_right h₀ _
  have H := shifted_substitution_dvd (shifted G α l) m hzero χ (t^s) _ hd hw
  rw [← pow_mul, shifted_eval G α l hn v] at H
  have hop := PowerSeries.nat_le_order_iff.mpr (PowerSeries.X_pow_dvd_iff.mp H)
  have hg := (Polynomial.natDegree_map_le (p := (G.map (PolynomialLocalOrder.atPoint α)))
    (f := e)).trans (Polynomial.natDegree_map_le.trans hG)
  change ((s*m : ℕ) : ℕ∞) ≤ (binaryValue ((G.map (PolynomialLocalOrder.atPoint α)).map e) h b (a:K⟦X⟧)).order
  rw [binaryValue_unit_right _ h hg a b, PowerSeries.order_mul, PowerSeries.order_pow]
  have hua : (a : K⟦X⟧).order = 0 := by
    by_contra! hz
    exact (PowerSeries.isUnit_iff_constantCoeff.mp a.isUnit).ne_zero
      (PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp hz)
  simpa only [hua, nsmul_zero, zero_add] using hop

/-- The two literal homogeneous first polars on a finite unit sheet have
valuation at least s*(r−1) at a received leader of multiplicity r. -/
theorem received_polar_min (F : K[X][X]) (α l : K) (r j : ℕ)
    (hr : TruncatedJetMultipliers.Leader (shifted F α l) r j)
    {n : ℕ} (hn : n ≠ 0) (s : ℕ) (hs : s ≤ n) (a : K⟦X⟧ˣ) (b : K⟦X⟧)
    (hc : (s : ℕ∞) ≤ (PowerSeries.C l*(a:K⟦X⟧)-b).order)
    (h : ℕ) (hx : (dx F).natDegree ≤ h) (hy : F.derivative.natDegree ≤ h) :
    let θ := PolynomialLocalOrder.atPoint α
    let e := (PowerSeries.expand n hn (R := K)).toRingHom
    ((s*(r-1) : ℕ) : ℕ∞) ≤ min (binaryValue (((dx F).map θ).map e) h b (a:K⟦X⟧)).order
      (binaryValue ((F.derivative.map θ).map e) h b (a:K⟦X⟧)).order := by
  obtain ⟨h₁,h₂⟩ := first_partials_lower F α l r j hr
  exact le_min (projective_partial_order _ _ _ _ h₁ hn s hs a b hc h hx)
    (projective_partial_order _ _ _ _ h₂ hn s hs a b hc h hy)

/-- Truncated integral contact with the received ordinate in projective
coordinates. The minimum is finite even for an identically matching sheet. -/
def contact (l : K) (a b : K⟦X⟧) (n : ℕ) : ℕ :=
  (min (PowerSeries.C l*a-b).order (n : ℕ∞)).toNat

theorem coe_contact (l : K) (a b : K⟦X⟧) (n : ℕ) :
    (contact l a b n : ℕ∞) = min (PowerSeries.C l*a-b).order n :=
  ENat.natCast_toNat_eq_self.mpr (ne_top_of_le_ne_top (ENat.natCast_ne_top n) (min_le_right ..))

/-- On a unimodular sheet positive finite contact forces an invertible
denominator. Every pole has zero received contact. -/
theorem denominator_unit_of_contact (l : K) (a b : K⟦X⟧) (hcop : IsCoprime b a) (n : ℕ)
    (hs : 0 < contact l a b n) : IsUnit a := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  apply isUnit_iff_ne_zero.mpr
  intro ha
  have hl : (0:ℕ∞) < (PowerSeries.C l*a-b).order := by
    calc
      _ < (contact l a b n : ℕ∞) := by exact_mod_cast hs
      _ ≤ _ := (coe_contact l a b n).trans_le (min_le_left ..)
  have hz := PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp hl.ne'
  have hb : PowerSeries.constantCoeff b = 0 := by simpa only [map_sub, map_mul, ha, mul_zero,
    zero_sub, neg_eq_zero] using hz
  obtain ⟨x,y,hxy⟩ := hcop
  have h' := congrArg (PowerSeries.constantCoeff (R := K)) hxy
  simp [ha,hb] at h'

/-- The common normalization for original finite and infinite sheets.
No assumption about which sheet passes through the received point is needed. -/
theorem received_projective_min (F : K[X][X]) (α l : K) (r j : ℕ)
    (hr : TruncatedJetMultipliers.Leader (shifted F α l) r j)
    {n : ℕ} (hn : n ≠ 0) (a b : K⟦X⟧) (hcop : IsCoprime b a)
    (h : ℕ) (hx : (dx F).natDegree ≤ h) (hy : F.derivative.natDegree ≤ h) :
    let θ := PolynomialLocalOrder.atPoint α
    let e := (PowerSeries.expand n hn (R := K)).toRingHom
    ((contact l a b n*(r-1) : ℕ) : ℕ∞) ≤ min
      (binaryValue (((dx F).map θ).map e) h b a).order
      (binaryValue ((F.derivative.map θ).map e) h b a).order := by
  by_cases hs : contact l a b n = 0
  · simp [hs]
  obtain ⟨u,rfl⟩ := denominator_unit_of_contact l a b hcop n (Nat.pos_of_ne_zero hs)
  have hcoe := coe_contact l (u:K⟦X⟧) b n
  have hsn : (contact l (u:K⟦X⟧) b n : ℕ∞) ≤ n := hcoe.trans_le (min_le_right ..)
  exact received_polar_min F α l r j hr hn _ (by exact_mod_cast hsn) u b
    (hcoe.trans_le (min_le_left ..)) h hx hy

/-- On the finite unit chart the original homogenized test has exactly
the same order as the ordinary test at the normalized ordinate B/A. -/
theorem unit_value_order (G : K⟦X⟧[X]) (h : ℕ) (hG : G.natDegree ≤ h)
    (a : K⟦X⟧ˣ) (b : K⟦X⟧) :
    (binaryValue G h b (a:K⟦X⟧)).order = (G.eval ((↑a⁻¹:K⟦X⟧)*b)).order := by
  rw [binaryValue_unit_right G h hG, PowerSeries.order_mul, PowerSeries.order_pow]
  have ha : (a:K⟦X⟧).order = 0 := by
    by_contra! hz
    exact (PowerSeries.isUnit_iff_constantCoeff.mp a.isUnit).ne_zero
      (PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp hz)
  simp [ha]

/-- The normalized affine ordinate has the same received contact as its
integral homogeneous numerator. -/
theorem unit_ordinate_contact (l : K) (a : K⟦X⟧ˣ) (b : K⟦X⟧) :
    ((↑a⁻¹:K⟦X⟧)*b-PowerSeries.C l).order = (PowerSeries.C l*(a:K⟦X⟧)-b).order := by
  have h : (↑a⁻¹:K⟦X⟧)*b-PowerSeries.C l =
      -(↑a⁻¹:K⟦X⟧)*(PowerSeries.C l*(a:K⟦X⟧)-b) := by
    simp [mul_sub, mul_left_comm, mul_comm]
    ring
  rw [h, PowerSeries.order_mul, PowerSeries.order_neg]
  have ha : (↑a⁻¹:K⟦X⟧).order = 0 := by
    by_contra! hz
    exact (PowerSeries.isUnit_iff_constantCoeff.mp a⁻¹.isUnit).ne_zero
      (PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp hz)
  simp [ha]

#print axioms unit_value_order
#print axioms unit_ordinate_contact
#print axioms received_projective_min
#print axioms received_polar_min
#print axioms first_partials_lower
#print axioms shifted_substitution_dvd

end ArkLib.ProximityGap.Frontier.ReceivedPolarContacts
