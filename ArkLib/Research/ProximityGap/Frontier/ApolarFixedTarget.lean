/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarChartCancellation
import Mathlib.Algebra.Polynomial.Bivariate

/-! # A bivariate locator dividing a fixed coordinate polynomial

After the parameter fraction field is cleared, interchanging the variables
turns a fixed coordinate polynomial into a constant. Its divisors therefore
have parameter degree zero.
-/

set_option autoImplicit false
open Polynomial
open ProximityGap.ApolarChartCancellation

namespace ArkLib.ProximityGap.Frontier.ApolarFixedTarget

variable {K : Type*} [Field K]

/-- Every integral polynomial factor of a nonzero fixed coordinate polynomial
has all coefficients constant in the parameter. -/
theorem fixed_of_dvd {V : K[X]} (hV : V ≠ 0) {f : K[X][X]} (hd : f ∣ V.map C) :
    ∃ g : K[X], f = g.map C := by
  obtain ⟨q,hq⟩ := hd
  have hs := congrArg Bivariate.swap hq
  rw [Bivariate.swap_map_C,map_mul] at hs
  have hf : Bivariate.swap f ∣ C V := ⟨_,hs⟩
  have hz : (Bivariate.swap f).natDegree = 0 :=
    Nat.eq_zero_of_le_zero (by simpa using natDegree_le_of_dvd hf (C_ne_zero.mpr hV))
  refine ⟨(Bivariate.swap f).coeff 0,?_⟩
  have he := congrArg Bivariate.swap (eq_C_of_natDegree_eq_zero hz)
  simpa only [Bivariate.swap_swap_apply,Bivariate.swap_C] using he

/-- If one locator coefficient has positive parameter degree, the primitive
locator cannot divide a domain vanisher times a coprime generic representative
to any positive or zero power. -/
theorem not_dvd_fixed_mul_pow {L : Type*} [IsAlgClosed K] [Field L]
    [Algebra K[X] L] [IsFractionRing K[X] L] (f P : K[X][X]) (V : K[X]) (hV : V≠0)
    (hf : ∀ t : K, f.map (evalRingHom t) ≠ 0)
    (j : ℕ) (hm : 0 < (f.coeff j).natDegree)
    (hc : IsCoprime (f.map (algebraMap K[X] L)) (P.map (algebraMap K[X] L))) (b : ℕ) :
    ¬ f ∣ V.map C * P^b := by
  intro hd
  let φ := algebraMap K[X] L
  have hfrac := Polynomial.map_dvd φ hd
  rw [Polynomial.map_mul,Polynomial.map_pow] at hfrac
  have hVf := (hc.pow_right (n:=b)).dvd_of_dvd_mul_right hfrac
  have hi := (primitive_of_no_zero_fiber f hf).dvd_of_fraction_map_dvd_fraction_map hVf
  obtain ⟨g,hg⟩ := fixed_of_dvd hV hi
  rw [hg,coeff_map,natDegree_C] at hm
  omega

#print axioms fixed_of_dvd
#print axioms not_dvd_fixed_mul_pow

end ArkLib.ProximityGap.Frontier.ApolarFixedTarget
