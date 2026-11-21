/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.PolynomialProjectiveHessian
import ArkLib.Research.ProximityGap.Frontier.ReceivedPolarContacts
import ArkLib.Research.ProximityGap.Frontier.WeightedHessianResultant

/-! # The polar baseline and the received-site excess on the same cubic sheet -/

set_option autoImplicit false
noncomputable section
open Polynomial Polynomial.Bivariate
open scoped Differential PowerSeries
namespace ArkLib.ProximityGap.Frontier.CubicSheetExcess

open BinaryBranchResultant (binaryValue)
open ReceivedPolarContacts (contact)

variable {K : Type} [Field K] [Differential K]

local instance : Differential K[X] := ⟨Differential.mapCoeffs⟩

/-- Evaluate a nominally homogeneous test on the projective sheet above α. -/
def sheet (α : K) (e : ℕ) (he : e ≠ 0) (b a : K⟦X⟧) (G : K[X][X]) (h : ℕ) : K⟦X⟧ :=
  binaryValue ((G.map (PolynomialLocalOrder.atPoint α)).map
    (PowerSeries.expand e he (R := K)).toRingHom) h b a

private theorem pad {R : Type*} [CommRing R] (G : R[X]) (h : ℕ) (hb : G.natDegree ≤ h)
    (b a : R) : binaryValue G (h+1) b a = a * binaryValue G h b a := by
  simp only [binaryValue, Polynomial.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjh := (le_natDegree_of_ne_zero (mem_support_iff.mp hj)).trans hb
  rw [show h+1-j=(h-j)+1 by omega, pow_succ]
  ring

theorem dx_degree (F : K[X][X]) : (ReceivedPolarContacts.dx F).natDegree ≤ F.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  simp [ReceivedPolarContacts.coeff_dx, coeff_eq_zero_of_natDegree_lt hi]

theorem hessian_degree (F : K[X][X]) (hf : F.natDegree ≤ 3) :
    (ScalarHessianLocalOrder.hessian F).natDegree ≤ 7 := by
  change Polynomial.Bivariate.natDegreeY F ≤ 3 at hf
  change Polynomial.Bivariate.natDegreeY _ ≤ 7
  rw [degreeY_as_weighted_deg] at hf ⊢
  apply WeightedHessianResultant.hessian_weight _ F 0 1 3 (by decide) hf
  intro q
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  change (Differential.mapCoeffs q).coeff i = 0
  simp [coeff_eq_zero_of_natDegree_lt hi]

/-- Every finite base point, including a sheet at value infinity: twice the
common polar order, with the explicit pole charge. -/
theorem baseline (F : K[X][X]) (hf : F.natDegree ≤ 3) (α : K)
    (e : ℕ) (he : e ≠ 0) (b a : K⟦X⟧) (ha : a ≠ 0) (j : ℕ)
    (hroot : sheet α e he b a F 3 = 0)
    (hx : (j : ℕ∞) ≤ (sheet α e he b a (ReceivedPolarContacts.dx F) 3).order)
    (hy : (j : ℕ∞) ≤ (sheet α e he b a F.derivative 3).order) :
    ((2*j : ℕ) : ℕ∞) ≤ 4 • a.order + (sheet α e he b a (ScalarHessianLocalOrder.hessian F) 7).order := by
  have hd : F.derivative.natDegree ≤ 2 := (natDegree_derivative_le F).trans
    (Nat.sub_le_sub_right hf 1)
  have h := PolynomialProjectiveHessian.sheet_order F hf α e he b a ha j
  simp only [sheet, Polynomial.map_map] at *
  apply h hroot hx
  rw [pad _ 2 (natDegree_map_le.trans hd)] at hy
  exact hy

/-- At a received affine leader the same Hessian carries the additional
contact times the leader multiplicity on top of the ordinary polar baseline. -/
theorem received (F : K[X][X]) (hf : F.natDegree ≤ 3) (α l : K) (hα : α′=0) (hl : l′′=0)
    (r i : ℕ) (hr : TruncatedJetMultipliers.Leader (ReceivedJetContact.shifted F α l) r i)
    (e : ℕ) (he : e ≠ 0) (b a : K⟦X⟧) (ha : a ≠ 0) (hab : IsCoprime b a) (j : ℕ)
    (hroot : sheet α e he b a F 3 = 0)
    (hx : (j : ℕ∞) ≤ (sheet α e he b a (ReceivedPolarContacts.dx F) 3).order)
    (hy : (j : ℕ∞) ≤ (sheet α e he b a F.derivative 3).order) :
    ((2*j+contact l a b e*r : ℕ) : ℕ∞) ≤
      4 • a.order + (sheet α e he b a (ScalarHessianLocalOrder.hessian F) 7).order := by
  by_cases hz : contact l a b e = 0
  · simpa only [hz, zero_mul, add_zero] using baseline F hf α e he b a ha j hroot hx hy
  obtain ⟨u,rfl⟩ := ReceivedPolarContacts.denominator_unit_of_contact l a b hab e
    (Nat.pos_of_ne_zero hz)
  let s := contact l (u:K⟦X⟧) b e
  let N := max j (s*(r-1))
  let φ := eval₂RingHom PowerSeries.C (PowerSeries.C α+PowerSeries.X^e)
  let ordY := (↑u⁻¹:K⟦X⟧)*b
  have hd : F.derivative.natDegree ≤ 3 := (natDegree_derivative_le F).trans (by omega)
  have hh := ReceivedPolarContacts.received_projective_min F α l r i hr he (u:K⟦X⟧) b hab
    3 ((dx_degree F).trans hf) hd
  have hN : (N : ℕ∞) ≤ (sheet α e he b u F.derivative 3).order := by
    change ((max j (s*(r-1)) : ℕ) : ℕ∞) ≤ _
    rcases le_total j (s*(r-1)) with h | h
    · rw [max_eq_right h]
      exact hh.trans (min_le_right ..)
    · simpa only [max_eq_left h] using hy
  have val (G : K[X][X]) (h : ℕ) (hG : G.natDegree ≤ h) :
      (sheet α e he b u G h).order = ((G.map φ).eval ordY).order := by
    rw [sheet, Polynomial.map_map, PolynomialProjectiveHessian.tame_substitution]
    exact ReceivedPolarContacts.unit_value_order _ _ (natDegree_map_le.trans hG) u b
  have hf0 : (F.map φ).eval ordY = 0 := by
    apply PowerSeries.order_eq_top.mp
    rw [← val F 3 hf, hroot, PowerSeries.order_zero]
  have hn : PowerSeries.X^N ∣ (F.derivative.map φ).eval ordY :=
    PowerSeries.X_pow_dvd_iff.mpr (PowerSeries.nat_le_order_iff.mp ((val _ 3 hd) ▸ hN))
  have hc : (s : ℕ∞) ≤ (ordY-PowerSeries.C l).order := by
    rw [show ordY = _ from rfl, ReceivedPolarContacts.unit_ordinate_contact]
    exact (ReceivedPolarContacts.coe_contact l (u:K⟦X⟧) b e).trans_le (min_le_left ..)
  have hs := PowerSeries.X_pow_dvd_iff.mpr (PowerSeries.nat_le_order_iff.mp hc)
  have hH := ReceivedPowerSeriesHessian.received_polynomial_site α l e N s hα hl F ordY hf0 hn hs
  have ho := PowerSeries.nat_le_order_iff.mpr (PowerSeries.X_pow_dvd_iff.mp hH)
  rw [PowerSeries.order_zero_of_isUnit u.isUnit, nsmul_zero, zero_add, val _ 7 (hessian_degree F hf)]
  have hnj : j ≤ N := le_max_left ..
  have hnr : s*(r-1) ≤ N := le_max_right ..
  have hsr : s*r ≤ N+s := by
    cases r with
    | zero => simp
    | succ k => simpa only [Nat.add_one_sub_one, Nat.mul_succ] using Nat.add_le_add_right hnr s
  exact (show ((2*j+s*r : ℕ) : ℕ∞) ≤ ((3*N+s : ℕ) : ℕ∞) by exact_mod_cast (by omega :
    2*j+s*r ≤ 3*N+s)).trans ho


open Finset in
/-- Sum the three sheet estimates at one finite coordinate. A member of the
received domain contributes six times the square of its interpolation order. -/
theorem place [Infinite K] (F : K[X][X]) (hf : F.natDegree ≤ 3) (α l : K) (r : ℕ)
    (hsite : r = 0 ∨ α′=0 ∧ l′′=0 ∧ ∃ i, TruncatedJetMultipliers.Leader
      (ReceivedJetContact.shifted F α l) r i)
    (a b : Fin 3 → K⟦X⟧) (ha : ∀ i, a i ≠ 0) (hab : ∀ i, IsCoprime (b i) (a i))
    (v : K⟦X⟧) (hv : IsUnit v)
    (hF : (F.map (PolynomialLocalOrder.atPoint α)).map
      (PowerSeries.expand 6 (by decide) (R := K)).toRingHom =
        C v * ∏ i, (C (a i)*Polynomial.X-C (b i)))
    (hroots : ∀ i, sheet α 6 (by decide) (b i) (a i) F 3 = 0)
    (j : Fin 3 → ℕ)
    (hx : ∀ i, (j i : ℕ∞) ≤ (sheet α 6 (by decide) (b i) (a i) (ReceivedPolarContacts.dx F) 3).order)
    (hy : ∀ i, (j i : ℕ∞) ≤ (sheet α 6 (by decide) (b i) (a i) F.derivative 3).order)
    (P H : ℕ) (hP : ∑ i, (a i).order = ((6*P : ℕ) : ℕ∞))
    (hH : ∑ i, (sheet α 6 (by decide) (b i) (a i) (ScalarHessianLocalOrder.hessian F) 7).order =
      ((6*H : ℕ) : ℕ∞)) :
    2*(∑ i, j i)+6*r^2 ≤ 24*P+6*H := by
  let s (i : Fin 3) := contact l (a i) (b i) 6
  have hsum (i : Fin 3) : ((2*j i+s i*r : ℕ) : ℕ∞) ≤ 4 • (a i).order +
      (sheet α 6 (by decide) (b i) (a i) (ScalarHessianLocalOrder.hessian F) 7).order := by
    rcases hsite with h | ⟨hα,hl,m,hm⟩
    · simpa only [h, mul_zero, add_zero] using baseline F hf α 6 (by decide) (b i) (a i)
        (ha i) (j i) (hroots i) (hx i) (hy i)
    · exact received F hf α l hα hl r m hm 6 (by decide) (b i) (a i) (ha i) (hab i)
        (j i) (hroots i) (hx i) (hy i)
  have hsr : 6*r ≤ ∑ i, s i := by
    rcases hsite with h | ⟨_,_,m,hm⟩
    · simp [h]
    · have Hc := ReceivedJetContact.leader_le_projective_contacts F α l r m hm (n := 6)
        (by decide) a b ha hab v hv hF
      simp only [← ReceivedPolarContacts.coe_contact, ← Nat.cast_sum, nsmul_eq_mul] at Hc
      exact_mod_cast Hc
  have h := sum_le_sum (s := univ) (fun i _ => hsum i)
  rw [sum_add_distrib, ← smul_sum, hP, hH, ← Nat.cast_sum] at h
  have hin : (∑ i, (2*j i+s i*r)) ≤ 4*(6*P)+6*H := by
    rw [nsmul_eq_mul] at h
    exact_mod_cast h
  rw [sum_add_distrib, ← mul_sum, ← sum_mul] at hin
  have hk := Nat.mul_le_mul_right r hsr
  calc
    _ = 2*(∑ i, j i)+(6*r)*r := by ring
    _ ≤ 2*(∑ i, j i)+(∑ i, s i)*r := Nat.add_le_add_left hk _
    _ ≤ _ := by omega

#print axioms place

#print axioms baseline
#print axioms received
end ArkLib.ProximityGap.Frontier.CubicSheetExcess
