/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.PrimitiveIntegralSectionChart
import ArkLib.Research.ProximityGap.Frontier.CubicPolarSiteBudget

/-! # Nonzero original resultants and the coordinate degree budgets

The proper cubic hypothesis refers to divisibility over the generic field.
It produces the two actual padded integral resultants in the scalar-field
chart. The scalar derivation fixes every ground constant.
-/
set_option autoImplicit false
noncomputable section
open Polynomial
open scoped Differential

namespace ArkLib.ProximityGap.Frontier.OriginalCubicResultants

open TerminalQuarticLocalization TerminalQuarticHessianTransport SecondPrimeCoordinateWeight
open IntegralSectionChart CanonicalQuarticSiteOrder MovingCubicVanishingBranch
variable {k : Type} [Field k]

local instance : Differential k[X] := MovingCubicVanishingBranch.coordinateDifferential
local instance : Differential (RatFunc k) := scalarFieldDifferential k
local instance : Differential (RatFunc k)[X] := ImplicitDerivativeBidegree.coefficientDifferential

/-- The canonical scalar derivation annihilates all ground-field constants. -/
theorem constant (a : k) : (RatFunc.C a)′ = 0 := by
  change (algebraMap k[X] (RatFunc k) (C a))′ = 0
  rw [GenericDifferentialFunctionField.fraction_deriv_algebraMap k[X] (RatFunc k)]
  change algebraMap k[X] (RatFunc k) (C a).derivative = 0
  simp

theorem scalar_derivative : (RatFunc.X : RatFunc k)′ = 1 := by
  change (algebraMap k[X] (RatFunc k) Polynomial.X)′ = 1
  rw [GenericDifferentialFunctionField.fraction_deriv_algebraMap k[X] (RatFunc k)]
  change algebraMap k[X] (RatFunc k) Polynomial.X.derivative = 1
  simp

private theorem deriv_mul {E : Type*} [Field E] [Differential E] (a b : E) :
    (a*b)′= a*b′+b*a′ := by simpa only [smul_eq_mul] using Differential.deriv.leibniz a b

/-- The received affine ordinate remains linear for the scalar derivation. -/
theorem line_second_derivative (u v : k) : (RatFunc.C u+RatFunc.X*RatFunc.C v)′′=0 := by
  have h : (RatFunc.C u+RatFunc.X*RatFunc.C v)′=RatFunc.C v := by
    rw [map_add,constant,deriv_mul,scalar_derivative,constant]
    simp
  rw [h,constant]

/-- Both padded resultants of the actual unreparametrized cubic are nonzero.
The Hessian assumption is the precise proper branch of the population theorem. -/
theorem nonzero (f : k[X][X][X]) (hi : Irreducible f) (hd : f.natDegree=3)
    (h₃ : (3:k) ≠ 0) (hp : ¬genericEquation (localPlane (orient f)) ∣
      genericEquation (scalarFieldHessian (localPlane (orient f)))) :
    let F := localPlane (orient f)
    F.resultant F.derivative 3 3 ≠ 0 ∧ F.resultant (scalarFieldHessian F) 3 7 ≠ 0 := by
  let F := localPlane (orient f)
  let φ := algebraMap (RatFunc k)[X] (RatFunc (RatFunc k))
  have hinj := RatFunc.algebraMap_injective (RatFunc k)
  have hF : F.natDegree=3 := by rw [show F=localPlane (permute f) from rfl,local_degree,permute_degree,hd]
  have hir : Irreducible (F.map φ) := (local_generic (permute f) ((MulEquiv.irreducible_iff permute).mpr hi)
    (by rw [permute_degree,hd]; decide)).2
  have h₃inner : (3:RatFunc k) ≠ 0 := by simpa only [map_ofNat,map_zero] using RatFunc.C_injective.ne h₃
  have h₃outer : (3:RatFunc (RatFunc k)) ≠ 0 := by simpa only [map_ofNat,map_zero] using RatFunc.C_injective.ne h₃inner
  have H := GenericProjectivePolarGcd.irreducible_cubic_separable _ hir
    ((natDegree_map_eq_of_injective hinj F).trans hF) h₃outer
  have hV : ¬ F.map φ ∣ F.derivative.map φ := by
    rw [← derivative_map]
    exact hir.coprime_iff_not_dvd.mp ((Polynomial.separable_def _).mp H)
  have hH : (scalarFieldHessian F).natDegree ≤ 7 := CubicSheetExcess.hessian_degree F hF.le
  have hv := WeightedHessianResultant.padded_ne_zero φ hinj F F.derivative 3
    ((natDegree_derivative_le _).trans (by omega)) hir hV
  have hh := WeightedHessianResultant.padded_ne_zero φ hinj F (scalarFieldHessian F) 7 hH hir hp
  rw [hF] at hv hh
  exact ⟨hv,hh⟩

/-- After any integral chart change the local cubic has the same ordinate degree,
the same weighted cap, and the complete determinant-plus-pole degree budget. -/
theorem chart_bounds (f : k[X][X][X]) (hf : f.natDegree=3) (d : ℕ) (r : k) :
    let W := weight d f
    let F := localPlane (chart r W d (orient f))
    F.natDegree=3 ∧ 3*d ≤ W ∧ Bivariate.natWeightedDegree F 1 d ≤ W ∧
      4*F.leadingCoeff.natDegree + (F.resultant (scalarFieldHessian F) 3 7).natDegree+39*d ≤ 20*W := by
  let W := weight d f
  let f' := chart r W d (orient f)
  have hfn : f ≠ 0 := fun hz => by simp [hz] at hf
  have ho : (orient f).natDegree = 3 := (permute_degree f).trans hf
  have hy : (localPlane f').natDegree = 3 := ((local_degree f').trans (chart_natDegree ..)).trans ho
  have hw := (PrimitiveIntegralSectionChart.weight_profile f hfn d).1
  have hN : orient f ≠ 0 := by intro h; simp [h] at ho
  have hl : (orient f).coeff 3 ≠ 0 := by rw [← ho]; exact leadingCoeff_ne_zero.mpr hN
  have floor : 3*d ≤ W := by
    have := hw 3 hl
    dsimp [W]
    omega
  have hc := coordinate_weight r W d (orient f) hw
  have bound : Bivariate.natWeightedDegree (localPlane f') 1 d ≤ W := by
    apply Finset.sup_le
    intro j hj
    have hn := mem_support_iff.mp hj
    have hn' : f'.coeff j ≠ 0 := fun hz => hn (by simp [localPlane,JetMultiplierGraph.mapPlane,hz])
    have h := hc j hn'
    change 1*(((localPlane f').coeff j).natDegree) + d*j ≤ W
    rw [one_mul]
    have hmap : ((localPlane f').coeff j).natDegree ≤ (f'.coeff j).natDegree := by
      simp only [localPlane,JetMultiplierGraph.mapPlane,coeff_map,coe_mapRingHom]
      exact natDegree_map_le
    exact (Nat.add_le_add_right hmap _).trans h
  exact ⟨hy,floor,bound,CubicPolarSiteBudget.weighted_degree_budget (localPlane f') hy d W floor bound⟩

#print axioms nonzero
#print axioms chart_bounds
#print axioms constant
#print axioms line_second_derivative
end ArkLib.ProximityGap.Frontier.OriginalCubicResultants
