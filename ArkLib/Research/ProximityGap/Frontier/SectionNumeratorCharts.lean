/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FlatSectionWeightedDescent
import ArkLib.Research.ProximityGap.Frontier.TransverseSectionBudget
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeReverseChart

/-! # Implicit coordinate derivatives on both scalar charts

The weighted descent and the section resultant test a common trivariate
divisor. Polynomial sections supply all the requisite derivative zeros
after passage to the rational coordinate field.
-/

set_option autoImplicit false
noncomputable section
open Polynomial
open scoped Differential
namespace ArkLib.ProximityGap.Frontier.SectionNumeratorCharts
open SecondPrimeCoordinateWeight SecondPrimeScalarChart ImplicitDerivativeNumerator
open MovingCubicVanishingBranch GenericDifferentialFunctionField WeightedSylvesterDegree

variable {K : Type} [Field K]

/-- Coordinate differentiation on the coefficients of the scalar polynomial. -/
@[instance_reducible] def rawDifferential (K : Type) [Field K] : Differential K[X][X] :=
  let _ := coordinateDifferential (k := K)
  ⟨Differential.mapCoeffs⟩

def rawNumerator (f : Surface K) (d : ℕ) : Surface K :=
  let _ := rawDifferential K
  numerator f d

/-- The implicit numerator commutes with a coefficient map respecting the derivation. -/
theorem map_numerator {R S : Type*} [CommRing R] [CommRing S] [Differential R]
    [Differential S] (φ : R →+* S) (hc : ∀ a : R, φ a′ = (φ a)′) (f : R[X]) (d : ℕ) :
    (numerator f d).map φ = numerator (f.map φ) d := by
  have hD (P : R[X]) : (Differential.mapCoeffs P).map φ = Differential.mapCoeffs (P.map φ) := by
    ext i; simp [hc]
  have ht (P Q : R[X]) : (along P Q).map φ = along (P.map φ) (Q.map φ) := by
    simp only [along, Polynomial.map_sub, Polynomial.map_mul, ← derivative_map, hD]
  induction d with
  | zero => simp only [numerator, Polynomial.map_neg, hD]
  | succ d ih => simp only [numerator, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_natCast,
      ← derivative_map, ht, ih]

private theorem swap_coordinate (P : K[X][X]) :
    let _ := rawDifferential K
    Bivariate.swap P′ = (Bivariate.swap P).derivative := by
  let _ := coordinateDifferential (k := K)
  let _ := rawDifferential K
  ext i j
  change ((Bivariate.swap (Differential.mapCoeffs P)).coeff i).coeff j =
    (((Bivariate.swap P).derivative).coeff i).coeff j
  simp only [ApolarReciprocalCharts.swap_coeff, Differential.coeff_mapCoeffs, coeff_derivative]
  change (P.coeff j).derivative.coeff i = _
  simp only [coeff_derivative, ← Nat.cast_succ, coeff_mul_natCast, ApolarReciprocalCharts.swap_coeff]

theorem scalarChart_rawNumerator (f : Surface K) (d : ℕ) :
    scalarChart (rawNumerator f d) = coordinateNumerator (scalarChart f) d := by
  let _ := rawDifferential K
  let _ := coordinateDifferential (k := RatFunc K)
  let χ := algebraMap K[X] (RatFunc K)
  let φ := (mapRingHom χ).comp Bivariate.swap.toRingHom
  have hφ (P : K[X][X]) : φ P′ = (φ P)′ := by
    change (Bivariate.swap P′).map χ = ((Bivariate.swap P).map χ).derivative
    rw [swap_coordinate, derivative_map]
  unfold scalarChart
  simp only [Polynomial.map_map]
  exact map_numerator φ hφ f d

theorem reverseChart_rawNumerator (f : Surface K) (d : ℕ) :
    let _ := CanonicalQuarticSiteOrder.scalarFieldDifferential K
    let _ := ImplicitDerivativeBidegree.coefficientDifferential (K := RatFunc K)
    SecondPrimeReverseChart.reverseChart (rawNumerator f d) =
      numerator (SecondPrimeReverseChart.reverseChart f) d := by
  let _ := rawDifferential K
  let _ := coordinateDifferential (k := K)
  let _ := CanonicalQuarticSiteOrder.scalarFieldDifferential K
  let _ := ImplicitDerivativeBidegree.coefficientDifferential (K := RatFunc K)
  let χ := algebraMap K[X] (RatFunc K)
  apply map_numerator (mapRingHom χ) _ f d
  intro P
  ext i
  change ((Differential.mapCoeffs P).map χ).coeff i = (Differential.mapCoeffs (P.map χ)).coeff i
  simp only [coeff_map, Differential.coeff_mapCoeffs]
  exact (fraction_deriv_algebraMap K[X] (RatFunc K) _).symm

/-- Unless the derivative numerator contains the original irreducible trivariate
component, the actual specialized polynomial sections have a scalar-degree bound. -/
theorem transverse_population (f : Surface K) (hi : Irreducible f) (hpos : 0 < f.natDegree)
    (m b d : ℕ) (hb : 2 ≤ b) (hm : b ≤ m) (hf : TotalDegreeLe f m) (hfy : f.natDegree ≤ b)
    (hnd : ¬ f ∣ rawNumerator f d) (S : Finset K) (q : K → K[X])
    (hq : ∀ z ∈ S, (q z).natDegree ≤ d)
    (hs : ∀ z ∈ S, f.eval₂ (evalRingHom (C z)) (q z) = 0) :
    S.card ≤ b*(m+2*d*(m-1))+(b+2*d*(b-1))*m-b*(b+2*d*(b-1)) := by
  classical
  let _ := coordinateDifferential (k := K)
  let _ := CanonicalQuarticSiteOrder.scalarFieldDifferential K
  let _ := ImplicitDerivativeBidegree.coefficientDifferential (K := RatFunc K)
  let χ := algebraMap K[X] (RatFunc K)
  let F := SecondPrimeReverseChart.reverseChart f
  have hC (z : K) : (RatFunc.C z)′ = 0 := by
    change (χ (C z))′ = 0
    rw [fraction_deriv_algebraMap K[X] (RatFunc K)]
    change χ (derivative (C z)) = 0
    simp
  have hdiff (P : K[X]) (r : ℕ) : (Differential.deriv^[r]) (χ P) =
      χ ((derivative^[r]) P) := by
    induction r with
    | zero => rfl
    | succ r ih =>
      simp only [Function.iterate_succ_apply', ih]
      exact fraction_deriv_algebraMap K[X] (RatFunc K) _
  have hS (w) (hw : w ∈ S.image (RatFunc.C : K →+* RatFunc K)) :
      w′ = 0 ∧ ∃ y : RatFunc K, (F.map (evalRingHom w)).eval y = 0 ∧
        (Differential.deriv^[d+1]) y = 0 := by
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hw
    refine ⟨hC z, χ (q z), SecondPrimeReverseChart.root_in_reverse f z _ (hs z hz), ?_⟩
    rw [hdiff, iterate_derivative_eq_zero (Nat.lt_succ_of_le (hq z hz)), map_zero]
  have htri : TotalDegreeLe F m := by
    intro i hne
    have hcoeff : F.coeff i = (f.coeff i).map χ := coeff_map (mapRingHom χ) _
    have hn : f.coeff i ≠ 0 := fun h => hne (by rw [hcoeff,h,Polynomial.map_zero])
    rw [hcoeff]
    exact (Nat.add_le_add_right natDegree_map_le i).trans (hf i hn)
  have hr : resultant F (numerator F d) F.natDegree (numerator F d).natDegree ≠ 0 := by
    have H := SecondPrimeSectionResultant.resultant_ne_zero f (rawNumerator f d) hi hpos hnd
    let φ := mapRingHom χ
    have hφ : Function.Injective φ := Polynomial.map_injective _ (RatFunc.algebraMap_injective K)
    have hn := (map_eq_zero_iff φ hφ).not.mpr H
    rw [← reverseChart_rawNumerator]
    change resultant (f.map φ) ((rawNumerator f d).map φ) (f.map φ).natDegree
      ((rawNumerator f d).map φ).natDegree ≠ 0
    simpa only [natDegree_map_eq_of_injective hφ, resultant_map_map] using hn
  have hDeg : F.natDegree = f.natDegree := SecondPrimeReverseChart.value_degree _
  have h := TransverseSectionBudget.population F d m b hb hm htri (hDeg.le.trans hfy)
    (hDeg.trans_ne hpos.ne') _ hS hr
  simpa only [Finset.card_image_of_injective _ RatFunc.C_injective] using h

end ArkLib.ProximityGap.Frontier.SectionNumeratorCharts

open ArkLib.ProximityGap.Frontier.SectionNumeratorCharts in
#print axioms transverse_population
