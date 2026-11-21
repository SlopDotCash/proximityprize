/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.SylvesterLocalMultiplicity
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.Tactic.Ring

/-! # The local order of the scalar Hessian after an affine shift

With the coordinate parameter fixed, translating the value by an affine function
of the scalar commutes with the cleared scalar Hessian. An order-`r` equation at
the translated site gives Hessian order at least `3*r-2`, proving the local
input of the Sylvester multiplicity bound over any differential coefficient ring.
-/

set_option autoImplicit false
noncomputable section

open Polynomial
open scoped Differential

namespace ArkLib.ProximityGap.Frontier.ScalarHessianLocalOrder

variable {R : Type*} [CommRing R]

/-- All monomials have joint order at least `r` in the local parameter and the value shift. -/
def HasOrder (π : R) (r : ℕ) (f : R[X]) : Prop := ∀ i, π^(r-i) ∣ f.coeff i

private theorem weaken {π : R} {f : R[X]} {r s : ℕ} (h : HasOrder π r f) (hs : s ≤ r) :
    HasOrder π s f := fun i => (pow_dvd_pow π (Nat.sub_le_sub_right hs i)).trans (h i)

private theorem add_order {π : R} {f g : R[X]} {r : ℕ} (hf : HasOrder π r f)
    (hg : HasOrder π r g) : HasOrder π r (f+g) := by
  intro i
  rw [coeff_add]
  exact dvd_add (hf i) (hg i)

private theorem sub_order {π : R} {f g : R[X]} {r : ℕ} (hf : HasOrder π r f)
    (hg : HasOrder π r g) : HasOrder π r (f-g) := by
  intro i
  rw [coeff_sub]
  exact dvd_sub (hf i) (hg i)

private theorem mul_order {π : R} {f g : R[X]} {r s : ℕ} (hf : HasOrder π r f)
    (hg : HasOrder π s g) : HasOrder π (r+s) (f*g) := by
  intro i
  rw [coeff_mul]
  apply Finset.dvd_sum
  intro v hv
  have he := Finset.mem_antidiagonal.mp hv
  have hh := mul_dvd_mul (hf v.1) (hg v.2)
  rw [← pow_add] at hh
  apply (pow_dvd_pow π _).trans hh
  omega

private theorem derivative_order {π : R} {f : R[X]} {r : ℕ} (hf : HasOrder π r f) :
    HasOrder π (r-1) f.derivative := by
  intro i
  rw [coeff_derivative, show r-1-i = r-(i+1) by omega]
  apply dvd_mul_of_dvd_left (hf (i+1))

variable [Differential R]

local notation "D" => Differential.mapCoeffs

/-- Scalar derivative is coefficientwise, and value differentiation is the ordinary
polynomial derivative. -/
def hessian (f : R[X]) : R[X] :=
  D (D f)*f.derivative^2 - 2*(D f).derivative*f.derivative*D f + f.derivative.derivative*(D f)^2

private theorem coefficient_order {π : R} (hπ : π′ = 0) {f : R[X]} {r : ℕ}
    (hf : HasOrder π r f) : HasOrder π r (D f) := by
  intro i
  obtain ⟨v,hv⟩ := hf i
  refine ⟨v′, ?_⟩
  rw [Differential.coeff_mapCoeffs, hv, Differential.deriv.leibniz, Differential.deriv.leibniz_pow,
    hπ]
  simp only [smul_zero, add_zero, smul_eq_mul, mul_zero]

/-- The Hessian loses at most two units of local order across its three factors. -/
theorem hessian_order {π : R} (hπ : π′ = 0) {f : R[X]} {r : ℕ} (hf : HasOrder π r f) :
    HasOrder π (3*r-2) (hessian f) := by
  have hD := coefficient_order hπ hf
  have hY := derivative_order hf
  have h1 := mul_order (coefficient_order hπ hD) (mul_order hY hY)
  have h2 := mul_order (mul_order (derivative_order hD) hY) hD
  have h3 := mul_order (derivative_order hY) (mul_order hD hD)
  rw [hessian, pow_two, pow_two, show 2*(D f).derivative*f.derivative*D f =
    (D f).derivative*f.derivative*D f+(D f).derivative*f.derivative*D f by ring]
  exact add_order (sub_order (weaken h1 (by omega)) (add_order (weaken h2 (by omega))
    (weaken h2 (by omega)))) (weaken h3 (by omega))

private theorem mixed (f : R[X]) : D f.derivative = (D f).derivative := by
  apply Polynomial.ext
  intro i
  rw [Differential.coeff_mapCoeffs, coeff_derivative, coeff_derivative,
    Differential.coeff_mapCoeffs, Differential.deriv.leibniz]
  simp [smul_eq_mul, mul_comm]

omit [Differential R] in
private theorem value_taylor (w : R) (f : R[X]) : (f.taylor w).derivative = f.derivative.taylor w := by
  simp [taylor_apply, derivative_comp]

private theorem scalar_taylor (w : R) (f : R[X]) :
    D (f.taylor w) = (D f).taylor w + f.derivative.taylor w * C w′ := by
  let _ : Differential R[X] := ⟨D⟩
  let _ : DifferentialAlgebra R R[X] := ⟨fun a => Differential.mapCoeffs_C a⟩
  have hx : ((Polynomial.X + C w : R[X]))′ = C w′ := by
    change D (Polynomial.X + C w) = C w′
    simp
  have he (q : R[X]) : aeval (Polynomial.X + C w) q = q.taylor w := by
    rw [aeval_def, taylor_apply]
    rfl
  have h := Differential.deriv_aeval_eq (Polynomial.X + C w) f
  rw [hx, he, he, he] at h
  exact h

/-- The scalar Hessian is invariant under a scalar-dependent affine value shift. -/
theorem hessian_taylor (w : R) (hw : (w′)′ = 0) (f : R[X]) :
    hessian (f.taylor w) = (hessian f).taylor w := by
  rw [hessian, scalar_taylor, map_add, Differential.mapCoeffs.leibniz, smul_eq_mul,
    smul_eq_mul, Differential.mapCoeffs_C, hw, map_zero, mul_zero, zero_add,
    scalar_taylor, scalar_taylor, value_taylor, derivative_add, derivative_mul,
    derivative_C, mul_zero, add_zero]
  simp only [value_taylor, mixed]
  change _ = taylorAlgHom w (hessian f)
  simp only [hessian, map_add, map_sub, map_mul, map_pow, map_ofNat, taylorAlgHom_apply]
  ring

/-- At sites whose value shift is scalar-affine and whose coordinate parameter is
scalar-constant, the actual translated Hessian has the required order. -/
theorem translated_hessian_order {π w : R} (hπ : π′ = 0) (hw : (w′)′ = 0)
    {f : R[X]} {r : ℕ} (hf : HasOrder π r (f.taylor w)) :
    HasOrder π (3*r-2) ((hessian f).taylor w) := by
  rw [← hessian_taylor w hw]
  exact hessian_order hπ hf

/-- The actual scalar Hessian, with affine site shifts, supplies the total
quartic multiplicity bound directly from the local orders of the equation. -/
theorem quartic_hessian_site_sum {K : Type*} [Field K] [Differential K[X]]
    (F : K[X][X]) (S : Finset K) (w : K → K[X]) (r : K → ℕ)
    (hm : F.natDegree = 4) (hn : (hessian F).natDegree ≤ 10)
    (hR : resultant F (hessian F) 4 10 ≠ 0) (hr : ∀ a ∈ S, r a ≤ 4)
    (hπ : ∀ a ∈ S, (Polynomial.X-C a : K[X])′ = 0)
    (hw : ∀ a ∈ S, ((w a)′)′ = 0)
    (hF : ∀ a ∈ S, HasOrder (Polynomial.X-C a) (r a) (F.taylor (w a))) :
    7*(∑ a ∈ S, r a) ≤ 6*S.card + (resultant F (hessian F) 4 10).natDegree := by
  apply SylvesterLocalMultiplicity.quartic_site_sum F (hessian F) S w r hm hn hR hr hF
  intro a ha
  exact translated_hessian_order (hπ a ha) (hw a ha) (hF a ha)

end ArkLib.ProximityGap.Frontier.ScalarHessianLocalOrder

open ArkLib.ProximityGap.Frontier.ScalarHessianLocalOrder in
#print axioms quartic_hessian_site_sum
