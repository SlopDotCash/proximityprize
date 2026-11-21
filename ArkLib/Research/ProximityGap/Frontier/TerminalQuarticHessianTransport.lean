/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.TerminalQuarticLocalization
import ArkLib.Research.ProximityGap.Frontier.ApolarReciprocalCharts

/-! # Scalar Hessian transport for an actual irreducible surface

The raw scalar derivative commutes with both coefficient-field presentations.
Primeness descends Hessian divisibility to the raw surface before changing
variable order, so the proper and flat tests form a single actual dichotomy.
-/

set_option autoImplicit false
noncomputable section
open Polynomial
open scoped Differential
namespace ArkLib.ProximityGap.Frontier.TerminalQuarticHessianTransport

open TerminalQuarticLocalization JetMultiplierGraph

variable {k : Type} [Field k]

/-- Exchange scalar and coordinate, fixing the outer value polynomial variable. -/
def permute : k[X][X][X] ≃+* k[X][X][X] := Polynomial.mapEquiv Bivariate.swap.toRingEquiv

theorem permute_coeff (f : k[X][X][X]) (j : ℕ) : ((permute f).coeff j) = Bivariate.swap (f.coeff j) :=
  coeff_map ..

theorem permute_degree (f : k[X][X][X]) : (permute f).natDegree = f.natDegree :=
  natDegree_map_eq_of_injective (f := Bivariate.swap.toRingEquiv.toRingHom) Bivariate.swap.injective f

/-- Derivative with respect to the middle, scalar variable in the original surface. -/
def rawD (f : k[X][X][X]) : k[X][X][X] :=
  let _ : Differential k[X][X] := ⟨(Polynomial.derivative' (R := k[X])).restrictScalars ℤ⟩
  Differential.mapCoeffs f

private theorem rawD_coeff (f : k[X][X][X]) (j : ℕ) :
    (rawD f).coeff j = (f.coeff j).derivative := rfl

def rawH (f : k[X][X][X]) : k[X][X][X] :=
  rawD (rawD f)*f.derivative^2 - 2*(rawD f).derivative*f.derivative*rawD f +
    f.derivative.derivative*(rawD f)^2

private theorem scalar_flat_derivative (f : k[X][X][X]) :
    localPlane (rawD f) = ReverseHessianAffineSection.scalarDerivative (localPlane f) := by
  apply Polynomial.ext
  intro j
  change (localPlane (rawD f)).coeff j = ((localPlane f).coeff j).derivative
  simp only [rawD_coeff,localPlane,mapPlane,coeff_map,coe_mapRingHom,derivative_map]

private theorem swap_deriv_coeff (p : k[X][X]) (i : ℕ) :
    (Bivariate.swap p.derivative).coeff i = ((Bivariate.swap p).coeff i).derivative := by
  apply Polynomial.ext
  intro j
  rw [ApolarReciprocalCharts.swap_coeff,coeff_derivative,coeff_derivative,
    ApolarReciprocalCharts.swap_coeff]
  rw [← C_eq_natCast,← C_1,← C_add,coeff_mul_C]

private theorem permute_deriv (f : k[X][X][X]) :
    permute f.derivative = (permute f).derivative := (derivative_map f Bivariate.swap.toRingEquiv.toRingHom).symm

private def scalarD (f : (RatFunc k)[X][X]) : (RatFunc k)[X][X] :=
  let _ := CanonicalQuarticSiteOrder.scalarFieldDifferential k
  let _ := ImplicitDerivativeBidegree.coefficientDifferential (K := RatFunc k)
  Differential.mapCoeffs f

private theorem scalar_proper_derivative (f : k[X][X][X]) :
    localPlane (permute (rawD f)) = scalarD (localPlane (permute f)) := by
  let _ : Differential k[X] := MovingCubicVanishingBranch.coordinateDifferential
  let _ := CanonicalQuarticSiteOrder.scalarFieldDifferential k
  let _ := ImplicitDerivativeBidegree.coefficientDifferential (K := RatFunc k)
  apply Polynomial.ext
  intro j
  apply Polynomial.ext
  intro i
  change ((localPlane (permute (rawD f))).coeff j).coeff i =
    (((localPlane (permute f)).coeff j).coeff i)′
  simp only [localPlane,mapPlane,coeff_map,coe_mapRingHom]
  rw [permute_coeff,permute_coeff,rawD_coeff,swap_deriv_coeff,
    GenericDifferentialFunctionField.fraction_deriv_algebraMap k[X] (RatFunc k)]
  rfl

theorem hessian_flat (f : k[X][X][X]) :
    localPlane (rawH f) = ReverseHessianAffineSection.hessian (localPlane f) := by
  change (rawH f).map (mapRingHom (algebraMap k[X] (RatFunc k))) = _
  simp only [rawH,Polynomial.map_add,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_pow,
    Polynomial.map_ofNat,← derivative_map]
  change localPlane (rawD (rawD f)) * _ - 2 * (localPlane (rawD f)).derivative * _ * localPlane (rawD f) +
    _ * (localPlane (rawD f))^2 = _
  rw [scalar_flat_derivative,scalar_flat_derivative]
  rfl

theorem hessian_proper (f : k[X][X][X]) :
    localPlane (permute (rawH f)) = CanonicalQuarticSiteOrder.scalarFieldHessian (localPlane (permute f)) := by
  let θ := (mapRingHom (algebraMap k[X] (RatFunc k))).comp Bivariate.swap.toRingEquiv.toRingHom
  have hh (g : k[X][X][X]) : localPlane (permute g) = g.map θ := Polynomial.map_map ..
  have hd (g : k[X][X][X]) : (rawD g).map θ = scalarD (g.map θ) := by
    simpa only [← hh] using scalar_proper_derivative g
  rw [hh,hh]
  simp only [rawH,Polynomial.map_add,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_pow,
    Polynomial.map_ofNat,← derivative_map,hd]
  rfl

/-- The divisibility hypothesis in the zero-Hessian theorem follows from the
complement of the proper-intersection test, for the original irreducible factor. -/
theorem flat_of_not_proper (f : k[X][X][X]) (hf : Irreducible f) (hy : 0 < f.natDegree)
    (h : MovingCubicVanishingBranch.genericEquation (localPlane (permute f)) ∣
      MovingCubicVanishingBranch.genericEquation
        (CanonicalQuarticSiteOrder.scalarFieldHessian (localPlane (permute f)))) :
    MovingCubicVanishingBranch.genericEquation (localPlane f) ∣
      MovingCubicVanishingBranch.genericEquation (ReverseHessianAffineSection.hessian (localPlane f)) := by
  rw [← hessian_proper] at h
  rw [← hessian_flat]
  apply (raw_dvd_iff f (rawH f) hf hy).mp
  have hd := (raw_dvd_iff (permute f) (permute (rawH f)) ((MulEquiv.irreducible_iff permute).mpr hf)
    (by rwa [permute_degree])).mpr h
  simpa only [RingEquiv.symm_apply_apply] using map_dvd permute.symm hd

end ArkLib.ProximityGap.Frontier.TerminalQuarticHessianTransport

open ArkLib.ProximityGap.Frontier.TerminalQuarticHessianTransport in
#print axioms flat_of_not_proper
