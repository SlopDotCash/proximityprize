/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic

/-! # Value partials from tame conjugate branches

For a root y(t) of an equation over K[[t^e]], every y(ζt) with ζ^e=1
is another root. Their differences divide the value derivative. This also
detects the extra order in the tangent case where the term of exponent e
is invariant under every such substitution.
-/

set_option autoImplicit false
noncomputable section

open scoped PowerSeries BigOperators

namespace ArkLib.ProximityGap.Frontier.TameConjugateSeparation

open Polynomial Finset

variable {A : Type*} [CommRing A] [IsDomain A]

private theorem difference_product_dvd (S : Finset A) (f : A[X]) (y : A)
    (h : ∀ q ∈ S, f.eval q = 0) : (∏ q ∈ S, (y-q)) ∣ f.eval y := by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty => simp
  | @insert q S hq ih =>
    obtain ⟨g,rfl⟩ := (dvd_iff_isRoot.mpr (h q (mem_insert_self ..)) : X-C q ∣ f)
    have hg (w : A) (hw : w ∈ S) : g.eval w = 0 := by
      have hv := h w (mem_insert_of_mem hw)
      have hne : w ≠ q := by rintro rfl; exact hq hw
      simpa [eval_mul, sub_ne_zero.mpr hne] using hv
    simpa [Finset.prod_insert hq, eval_mul] using mul_dvd_mul_left (y-q) (ih g hg)

/-- The value derivative at one root is divisible by its entire product of
differences from a finite set of other roots, also for nonmonic equations. -/
theorem difference_product_dvd_derivative (S : Finset A) (f : A[X]) (y : A) (hy : f.eval y = 0)
    (hn : y ∉ S) (h : ∀ q ∈ S, f.eval q = 0) :
    (∏ q ∈ S, (y-q)) ∣ f.derivative.eval y := by
  obtain ⟨g,rfl⟩ := (dvd_iff_isRoot.mpr hy : X-C y ∣ f)
  have hg (w : A) (hw : w ∈ S) : g.eval w = 0 := by
    have hv := h w hw
    have hne : w ≠ y := by rintro rfl; exact hn hw
    simpa [eval_mul, sub_ne_zero.mpr hne] using hv
  simpa [derivative_mul, eval_mul] using difference_product_dvd S g y hg

variable {K : Type*} [Field K]

theorem rescale_expand (e : ℕ) (he : e ≠ 0) (ζ : K) (hζ : ζ^e = 1) (a : K⟦X⟧) :
    PowerSeries.rescale ζ (PowerSeries.expand e he a) = PowerSeries.expand e he a := by
  ext i
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_expand]
  split
  next h =>
    obtain ⟨j,rfl⟩ := h
    simp [pow_mul, hζ]
  next => simp

/-- Rescaling a root by an e-th root of unity preserves the actual equation
after substitution t ↦ t^e in its coefficients. -/
theorem conjugate_root (e : ℕ) (he : e ≠ 0) (ζ : K) (hζ : ζ^e = 1) (F : Polynomial K⟦X⟧)
    (y : K⟦X⟧) (h : (F.map (PowerSeries.expand e he).toRingHom).eval y = 0) :
    (F.map (PowerSeries.expand e he).toRingHom).eval (PowerSeries.rescale ζ y) = 0 := by
  have hcomp : (PowerSeries.rescale ζ).comp (PowerSeries.expand e he).toRingHom =
      (PowerSeries.expand e he).toRingHom := RingHom.ext (rescale_expand e he ζ hζ)
  have hv := congrArg (PowerSeries.rescale ζ) h
  rw [← Polynomial.eval_map_apply, Polynomial.map_map, hcomp, map_zero] at hv
  exact hv

/-- The terms fixed by all the phases may be present at arbitrary exponents.
Every other term below s must be zero for the separation estimate. -/
theorem conjugate_difference_dvd (e s : ℕ) (ζ : K) (hζ : ζ^e = 1) (y : K⟦X⟧)
    (h : ∀ i < s, ¬e ∣ i → y.coeff i = 0) :
    (PowerSeries.X : K⟦X⟧)^s ∣ y - PowerSeries.rescale ζ y := by
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro i hi
  rw [map_sub, PowerSeries.coeff_rescale]
  by_cases hdiv : e ∣ i
  · obtain ⟨j,rfl⟩ := hdiv
    simp [pow_mul,hζ]
  · simp [h i hi hdiv]

/-- On an orbit of distinct conjugates the value partial is divisible by a
uniformizer power of exponent s times the number of other conjugates. -/
theorem orbit_derivative_dvd (e s : ℕ) (he : e ≠ 0) (O : Finset K) (F : Polynomial K⟦X⟧)
    (y : K⟦X⟧) (h : (F.map (PowerSeries.expand e he).toRingHom).eval y = 0)
    (hroot : ∀ ζ ∈ O, ζ^e = 1) (hh : ∀ ζ ∈ O, PowerSeries.rescale ζ y ≠ y)
    (hinj : Set.InjOn (fun ζ => PowerSeries.rescale ζ y) O)
    (hl : ∀ i < s, ¬e ∣ i → y.coeff i = 0) :
    (PowerSeries.X : K⟦X⟧)^(O.card*s) ∣
      (F.map (PowerSeries.expand e he).toRingHom).derivative.eval y := by
  classical
  let S := O.image (fun ζ => PowerSeries.rescale ζ y)
  have hs : y ∉ S := by
    intro hs
    obtain ⟨ζ,hζ,hy⟩ := mem_image.mp hs
    exact hh ζ hζ hy
  have hc : S.card = O.card := card_image_of_injOn hinj
  have hd := difference_product_dvd_derivative S _ y h hs (by
    intro w hw
    obtain ⟨ζ,hζ,rfl⟩ := mem_image.mp hw
    exact conjugate_root e he ζ (hroot ζ hζ) F y h)
  apply dvd_trans _ hd
  have hhprod : (∏ _ ∈ S, (PowerSeries.X : K⟦X⟧)^s) ∣ ∏ w ∈ S, (y-w) := by
    apply Finset.prod_dvd_prod_of_dvd
    intro w hw
    obtain ⟨ζ,hζ,rfl⟩ := mem_image.mp hw
    exact conjugate_difference_dvd e s ζ (hroot ζ hζ) y hl
  simpa [Finset.prod_const, ← pow_mul, hc, Nat.mul_comm] using hhprod

#print axioms orbit_derivative_dvd
#print axioms conjugate_root

end ArkLib.ProximityGap.Frontier.TameConjugateSeparation
