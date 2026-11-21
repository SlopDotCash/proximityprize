/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ProjectiveBranchHessian
import ArkLib.Research.ProximityGap.Frontier.ReceivedPowerSeriesHessian
import ArkLib.Research.ProximityGap.Frontier.ProjectiveCubicLocalOrder

/-! # The projective Hessian order after an actual local coordinate substitution -/

set_option autoImplicit false
noncomputable section
open Polynomial
open scoped PowerSeries Differential
namespace ArkLib.ProximityGap.Frontier.PolynomialProjectiveHessian
open BinaryBranchResultant (binaryValue)
open ProjectiveBranchHessian (form)

variable {K : Type*} [Field K] [Differential K]

attribute [local instance] ReceivedPowerSeriesHessian.seriesDifferential
local instance : Differential K[X] := ⟨Differential.mapCoeffs⟩
local instance : Differential K⟦X⟧[X] := ⟨Differential.mapCoeffs⟩

private theorem coord_coeff {R : Type*} [CommRing R] (F : R[X][X]) (j : ℕ) :
    (BranchHessianIdeal.coordinate F).coeff j = (F.coeff j).derivative := by
  letI : Differential R[X] := ⟨(Polynomial.derivative' (R := R)).restrictScalars ℤ⟩
  unfold BranchHessianIdeal.coordinate
  rw [Differential.coeff_mapCoeffs]
  rfl

private theorem coordinate_map (F : K[X][X]) :
    BranchHessianIdeal.coordinate (F.map (mapRingHom PowerSeries.C)) =
      (BranchHessianIdeal.coordinate F).map (mapRingHom PowerSeries.C) := by
  ext j : 1
  simp only [coord_coeff, coeff_map, coe_mapRingHom, derivative_map]

private theorem form_map (F : K[X][X]) (h : ℕ) (x B A : K⟦X⟧) :
    form (F.map (mapRingHom PowerSeries.C)) h x B A =
      binaryValue (F.map (eval₂RingHom PowerSeries.C x)) h B A := by
  have H : (evalRingHom x).comp (mapRingHom (PowerSeries.C (R := K))) =
      eval₂RingHom PowerSeries.C x := RingHom.ext fun p => eval_map PowerSeries.C x
  rw [form, Polynomial.map_map, H]

/-- The two ring homomorphisms used for sheet splitting and for the
coefficientwise differential calculation agree on all coordinate polynomials. -/
theorem tame_substitution (α : K) (e : ℕ) (he : e ≠ 0) :
    (PowerSeries.expand e he (R := K)).toRingHom.comp (PolynomialLocalOrder.atPoint α) =
      eval₂RingHom PowerSeries.C (PowerSeries.C α+PowerSeries.X^e) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [PolynomialLocalOrder.atPoint, PowerSeries.expand_C]
  · simp [PolynomialLocalOrder.atPoint, Polynomial.taylor_X, PowerSeries.expand_C, add_comm]

/-- For the original bivariate polynomial the projective order of its raw
Hessian plus four times the pole order bounds twice the common polar order. -/
theorem sheet_order (F : K[X][X]) (hf : F.natDegree ≤ 3) (α : K)
    (e : ℕ) (he : e ≠ 0) (B A : K⟦X⟧) (ha : A ≠ 0) (j : ℕ) :
    let θ := (PowerSeries.expand e he (R := K)).toRingHom.comp (PolynomialLocalOrder.atPoint α)
    let atSheet (G : K[X][X]) (h : ℕ) := binaryValue (G.map θ) h B A
    atSheet F 3 = 0 →
    (j : ℕ∞) ≤ (atSheet (BranchHessianIdeal.coordinate F) 3).order →
    (j : ℕ∞) ≤ (A * atSheet F.derivative 2).order →
    ((2*j : ℕ) : ℕ∞) ≤ 4 • A.order + (atSheet (ScalarHessianLocalOrder.hessian F) 7).order := by
  rw [tame_substitution]
  intro θ atS hroot hU hV
  let x := PowerSeries.C α+PowerSeries.X^e
  let L := mapRingHom (PowerSeries.C (R := K))
  let f := F.map L
  let I : Ideal K⟦X⟧ := Ideal.span {PowerSeries.X^j}
  have mem (v : K⟦X⟧) (hv : (j : ℕ∞) ≤ v.order) : v ∈ I :=
    Ideal.mem_span_singleton.mpr (PowerSeries.X_pow_dvd_iff.mpr (PowerSeries.nat_le_order_iff.mp hv))
  have hdiff (p : K[X]) : L p′ = (L p)′ := by
    ext i : 1
    change ((Differential.mapCoeffs p).map PowerSeries.C).coeff i =
      (Differential.mapCoeffs (p.map PowerSeries.C)).coeff i
    simp
  have hhess := ReceivedPowerSeriesHessian.hessian_map L hdiff F
  have hres := ProjectiveBranchHessian.projective_hessian_mem_square f
    (natDegree_map_le.trans hf) x B A ha ((form_map F 3 x B A).trans hroot) I
    (by rw [show f = F.map (mapRingHom PowerSeries.C) from rfl, coordinate_map, form_map]
        exact mem _ hU)
    (by rw [show f = F.map (mapRingHom PowerSeries.C) from rfl, derivative_map, form_map]
        exact mem _ hV)
  rw [← hhess, form_map, show I^2 = Ideal.span {(PowerSeries.X : K⟦X⟧)^(2*j)} by
    rw [show I = Ideal.span {(PowerSeries.X : K⟦X⟧)^j} from rfl, Ideal.span_singleton_pow,
      ← pow_mul, Nat.mul_comm]] at hres
  have h := PowerSeries.nat_le_order_iff.mpr
    (PowerSeries.X_pow_dvd_iff.mp (Ideal.mem_span_singleton.mp hres))
  simpa only [PowerSeries.order_mul, PowerSeries.order_pow] using h

#print axioms tame_substitution
#print axioms sheet_order
end ArkLib.ProximityGap.Frontier.PolynomialProjectiveHessian
