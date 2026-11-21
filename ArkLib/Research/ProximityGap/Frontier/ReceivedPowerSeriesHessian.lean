/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ScalarHessianLocalOrder
import ArkLib.Research.ProximityGap.Frontier.ImplicitDerivativeNumerator
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-! # Scalar differentiation at a fixed received site in a formal power series chart

The derivation acts on series coefficients and fixes the uniformizer.
A branch's contact with an affine received ordinate contributes its entire
order in addition to three times the order of the value partial.
-/

set_option autoImplicit false
noncomputable section
open Polynomial
open scoped Differential PowerSeries

namespace ArkLib.ProximityGap.Frontier.ReceivedPowerSeriesHessian

variable {K : Type*} [CommRing K] [Differential K]

private def coefficientMap : K⟦X⟧ →+ K⟦X⟧ where
  toFun f := PowerSeries.mk (fun i => (f.coeff i)′)
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

private theorem coefficient_leibniz (f g : K⟦X⟧) :
    coefficientMap (f*g) = coefficientMap f*g + f*coefficientMap g := by
  ext n
  simp only [coefficientMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,PowerSeries.coeff_mk,
    map_add, PowerSeries.coeff_mul, map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simp [Differential.deriv.leibniz, add_comm, mul_comm]

private def derivationOfLeibniz {R : Type*} [CommRing R] (D : R →+ R)
    (h : ∀ x y, D (x*y) = D x*y+x*D y) : Derivation ℤ R R :=
  Derivation.mk' D.toIntLinearMap (fun x y => by
    change D (x*y) = x*D y + y*D x
    rw [h]; ring)

/-- Coefficientwise scalar differential structure on the power series ring. -/
@[instance_reducible] def seriesDifferential : Differential K⟦X⟧ :=
  ⟨derivationOfLeibniz coefficientMap coefficient_leibniz⟩

attribute [local instance] seriesDifferential

@[simp] theorem coeff_deriv (f : K⟦X⟧) (i : ℕ) : (f′).coeff i = (f.coeff i)′ := by
  change (PowerSeries.mk fun j => (f.coeff j)′).coeff i = _
  simp

@[simp] theorem deriv_C (a : K) : (PowerSeries.C a)′ = PowerSeries.C a′ := by
  ext n
  by_cases h : n=0 <;> simp [PowerSeries.coeff_C,h]

@[simp] theorem deriv_X : (PowerSeries.X : K⟦X⟧)′ = 0 := by
  ext i
  by_cases h : i=1 <;> simp [PowerSeries.coeff_X,h]

/-- Pullback along the tame coordinate at a fixed scalar-constant site
intertwines coefficientwise scalar derivatives on all coordinate polynomials. -/
theorem site_pullback (x : K) (hx : x′ = 0) (e : ℕ) (p : K[X]) :
    (p.eval₂ PowerSeries.C (PowerSeries.C x+PowerSeries.X^e))′ =
      (Differential.mapCoeffs p).eval₂ PowerSeries.C (PowerSeries.C x+PowerSeries.X^e) := by
  let _ : DifferentialAlgebra K K⟦X⟧ := ⟨deriv_C⟩
  have H := Differential.deriv_aeval_eq (PowerSeries.C x+PowerSeries.X^e) p
  have hz : (PowerSeries.C x+PowerSeries.X^e)′ = 0 := by
    simp [Differential.deriv.leibniz_pow,hx]
  rw [hz,mul_zero,add_zero] at H
  exact H

/-- Coefficient derivatives preserve every power of the uniformizer. -/
theorem preserve_order (a : K⟦X⟧) (n : ℕ) (h : PowerSeries.X^n ∣ a) :
    PowerSeries.X^n ∣ a′ := by
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro i hi
  simp [(PowerSeries.X_pow_dvd_iff.mp h) i hi]

private theorem eval_hessian {R : Type*} [CommRing R] [Differential R] (F : R[X])
    (Y : R) (h : F.eval Y=0) :
    (ScalarHessianLocalOrder.hessian F).eval Y = -(F.derivative.eval Y)^3 * Y′′ := by
  have hm : Differential.mapCoeffs F.derivative = (Differential.mapCoeffs F).derivative := by
    ext i
    rw [Differential.coeff_mapCoeffs, coeff_derivative, Differential.deriv.leibniz, coeff_derivative,
      Differential.coeff_mapCoeffs]
    simp [smul_eq_mul, mul_comm]
  have hp : ImplicitDerivativeNumerator.numerator F 1 = - ScalarHessianLocalOrder.hessian F := by
    simp only [ScalarHessianLocalOrder.hessian, ImplicitDerivativeNumerator.numerator,
      ImplicitDerivativeNumerator.along, map_neg, hm, Nat.mul_zero, Nat.zero_add, Nat.cast_one,
      one_mul]
    ring
  have hroot : aeval Y F = 0 := by simpa using h
  have HH := ImplicitDerivativeNumerator.numerator_aeval F Y hroot 1
  rw [hp] at HH
  have hH : -(ScalarHessianLocalOrder.hessian F).eval Y = (F.derivative.eval Y)^3 * Y′′ := by
    simpa [Function.iterate_succ_apply] using HH
  linear_combination -hH

/-- Fixed-site contact charges the actual polynomial Hessian. The statement
also applies when the evaluated Hessian vanishes identically on a sheet. -/
theorem received_charge (F : Polynomial K⟦X⟧) (Y : K⟦X⟧) (β : K) (hβ : β′′=0)
    (hF : F.eval Y=0) (j s : ℕ) (hj : PowerSeries.X^j ∣ F.derivative.eval Y)
    (hs : PowerSeries.X^s ∣ Y-PowerSeries.C β) :
    PowerSeries.X^(3*j+s) ∣ (ScalarHessianLocalOrder.hessian F).eval Y := by
  have hs' := preserve_order _ s (preserve_order _ s hs)
  simp only [map_sub, deriv_C, hβ, map_zero, sub_zero] at hs'
  rw [eval_hessian F Y hF,pow_add, Nat.mul_comm 3 j, pow_mul]
  exact mul_dvd_mul (dvd_neg.mpr (pow_dvd_pow_of_dvd hj 3)) hs'

/-- The scalar Hessian commutes with a coefficient homomorphism that respects
the two scalar derivatives. -/
theorem hessian_map {R B : Type*} [CommRing R] [CommRing B] [Differential R] [Differential B]
    (φ : R →+* B) (hφ : ∀ a, φ a′ = (φ a)′) (f : R[X]) :
    (ScalarHessianLocalOrder.hessian f).map φ = ScalarHessianLocalOrder.hessian (f.map φ) := by
  have hd (g : R[X]) : (Differential.mapCoeffs g).map φ = Differential.mapCoeffs (g.map φ) := by
    ext i
    simp [hφ]
  simp only [ScalarHessianLocalOrder.hessian, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_ofNat, ← derivative_map, hd]

local instance : Differential K[X] := ⟨Differential.mapCoeffs⟩

/-- Pull back the original bivariate equation itself to a fixed domain site.
The scalar Hessian is formed before specializing the coordinate. -/
theorem received_polynomial_site (x β : K) (e j s : ℕ) (hx : x′=0) (hβ : β′′=0)
    (F : K[X][X]) (Y : K⟦X⟧) :
    let φ := eval₂RingHom PowerSeries.C (PowerSeries.C x+PowerSeries.X^e)
    (F.map φ).eval Y=0 →
    PowerSeries.X^j ∣ (F.derivative.map φ).eval Y →
    PowerSeries.X^s ∣ Y-PowerSeries.C β →
    PowerSeries.X^(3*j+s) ∣ ((ScalarHessianLocalOrder.hessian F).map φ).eval Y := by
  intro φ hF hj hs
  have hc (a : K[X]) : φ a′ = (φ a)′ := (site_pullback x hx e a).symm
  rw [hessian_map φ hc]
  exact received_charge (F.map φ) Y β hβ hF j s (by simpa only [derivative_map] using hj) hs

#print axioms received_polynomial_site

#print axioms site_pullback
#print axioms received_charge

end ArkLib.ProximityGap.Frontier.ReceivedPowerSeriesHessian
