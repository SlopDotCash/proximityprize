/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeScalarChart
import ArkLib.Research.ProximityGap.Frontier.CanonicalQuarticSiteOrder
import ArkLib.Research.ProximityGap.Frontier.ReverseHessianAffineSection
import ArkLib.Research.ProximityGap.Frontier.ApolarReciprocalCharts

/-! # Scalar Hessians on the two rational-function charts

Both chart Hessians are images of differentiation in the original scalar variable
Z of K[X][Z][Y]. In particular chart changes retain the same polynomial when testing
divisibility by the surface equation.
-/

open Polynomial
open scoped Differential
namespace ArkLib.ProximityGap.Frontier.SecondPrimeHessianTransport
open SecondPrimeCoordinateWeight SecondPrimeScalarChart

variable {K : Type} [Field K]

/-- Differentiate K[X][Z] with respect to Z, keeping the coordinate polynomial fixed. -/
@[instance_reducible] noncomputable def scalarDifferential (K : Type) [Field K] :
    Differential K[X][X] :=
  ⟨(Polynomial.derivative' (R := K[X])).restrictScalars ℤ⟩

/-- The scalar Hessian in the original trivariate surface ring. -/
noncomputable def rawHessian (f : Surface K) : Surface K :=
  letI := scalarDifferential K
  ScalarHessianLocalOrder.hessian f

private theorem map_hessian {R S : Type*} [CommRing R] [CommRing S] [Differential R]
    [Differential S] (φ : R →+* S) (hφ : ∀ r : R, φ r′ = (φ r)′) (f : R[X]) :
    (ScalarHessianLocalOrder.hessian f).map φ = ScalarHessianLocalOrder.hessian (f.map φ) := by
  have hD (p : R[X]) : (Differential.mapCoeffs p).map φ = Differential.mapCoeffs (p.map φ) := by
    ext i
    simp only [coeff_map, Differential.coeff_mapCoeffs, hφ]
  simp only [ScalarHessianLocalOrder.hessian, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_ofNat, ← derivative_map, hD]

private theorem swap_derivative_coeff (p : K[X][X]) (i : ℕ) :
    (Bivariate.swap p.derivative).coeff i = ((Bivariate.swap p).coeff i).derivative := by
  ext j
  simp only [ApolarReciprocalCharts.swap_coeff, coeff_derivative, ← Nat.cast_succ,
    coeff_mul_natCast]

/-- Localizing in Z and differentiating its rational function field give the same Hessian. -/
theorem scalarChart_rawHessian (f : Surface K) :
    scalarChart (rawHessian f) = CanonicalQuarticSiteOrder.scalarFieldHessian (scalarChart f) := by
  let _ := MovingCubicVanishingBranch.coordinateDifferential (k := K)
  let _ := CanonicalQuarticSiteOrder.scalarFieldDifferential K
  let _ := ImplicitDerivativeBidegree.coefficientDifferential (K := RatFunc K)
  let _ := scalarDifferential K
  let χ := algebraMap K[X] (RatFunc K)
  let φ := (mapRingHom χ).comp Bivariate.swap.toRingHom
  have hφ (p : K[X][X]) : φ p′ = (φ p)′ := by
    ext i
    change ((Bivariate.swap p.derivative).map χ).coeff i =
      (((Bivariate.swap p).map χ).coeff i)′
    simp only [coeff_map, swap_derivative_coeff]
    exact (GenericDifferentialFunctionField.fraction_deriv_algebraMap K[X] (RatFunc K) _).symm
  unfold scalarChart
  simp only [Polynomial.map_map]
  exact map_hessian φ hφ f

/-- Localizing the coordinate X gives the scalar polynomial Hessian of the reverse chart. -/
theorem reverseChart_rawHessian (f : Surface K) :
    (rawHessian f).map (mapRingHom (algebraMap K[X] (RatFunc K))) =
      ReverseHessianAffineSection.hessian (f.map (mapRingHom (algebraMap K[X] (RatFunc K)))) := by
  let _ := scalarDifferential K
  let _ := MovingCubicVanishingBranch.coordinateDifferential (k := RatFunc K)
  exact map_hessian (mapRingHom (algebraMap K[X] (RatFunc K))) (fun p =>
    (derivative_map p _).symm) f

#print axioms scalarChart_rawHessian
#print axioms reverseChart_rawHessian
end ArkLib.ProximityGap.Frontier.SecondPrimeHessianTransport
