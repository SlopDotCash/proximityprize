/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.OrdinaryPolarCappedGcd
import ArkLib.ToMathlib.BivariateGradedDvd
import ArkLib.Data.Polynomial.ResultantDegree

/-! # Integral coordinate polars of a cubic

The raw coefficient tower is scalar, coordinate, and ordinate, from inside to
outside. Both derivatives, the padded cubic resultant, and its square section
divisor commute with scalar specialization.
-/

set_option autoImplicit false
noncomputable section
open Polynomial
namespace ArkLib.ProximityGap.Frontier.IntegralOrdinaryPolars

variable {R : Type*} [CommRing R]

/-- Differentiate the coordinate polynomial in each ordinate slot. -/
def dx (F : R[X][X]) : R[X][X] :=
  let _ : Differential R[X] := ⟨(Polynomial.derivative' (R := R)).restrictScalars ℤ⟩
  Differential.mapCoeffs F

theorem coeff_dx (F : R[X][X]) (j : ℕ) : (dx F).coeff j = (F.coeff j).derivative := rfl

/-- An ordinary polar with constant slope and its nominal cubic resultant. -/
def polar (F : R[X][X]) (slope : R) := dx F + C (C slope)*F.derivative

def polarResultant (F : R[X][X]) (slope : R) := F.resultant (polar F slope) 3 3

theorem map_polar {T : Type*} [CommRing T] (φ : R →+* T) (F : R[X][X]) (slope : R) :
    (polar F slope).map (mapRingHom φ) = polar (F.map (mapRingHom φ)) (φ slope) := by
  unfold polar
  simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,coe_mapRingHom,
    ← derivative_map]
  congr 1
  ext j
  simp only [Polynomial.coeff_map,coeff_dx,coe_mapRingHom,derivative_map]

theorem map_resultant {T : Type*} [CommRing T] (φ : R →+* T) (F : R[X][X]) (slope : R) :
    (polarResultant F slope).map φ = polarResultant (F.map (mapRingHom φ)) (φ slope) := by
  unfold polarResultant
  change mapRingHom φ _ = _
  rw [← resultant_map_map, map_polar]

private theorem bound_add {f g : R[X]} {a H : ℕ} (hne : f+g ≠ 0)
    (hf : f ≠ 0 → f.natDegree+a ≤ H) (hg : g ≠ 0 → g.natDegree+a ≤ H) :
    (f+g).natDegree+a ≤ H := by
  by_cases h : f=0
  · simpa [h] using hg (by simpa [h] using hne)
  by_cases h' : g=0
  · simpa [h'] using hf h
  have := (Nat.add_le_add_right (natDegree_add_le f g) a)
  have := hf h
  have := hg h'
  omega

/-- The ordinate coefficient of the slope term is a constant multiple of the
next coefficient of the original polynomial. -/
theorem coeff_polar (F : R[X][X]) (slope : R) (j : ℕ) :
    (polar F slope).coeff j = (F.coeff j).derivative +
      C (slope * (j+1:R)) * F.coeff (j+1) := by
  rw [polar,coeff_add,coeff_dx,coeff_C_mul,coeff_derivative]
  simp only [map_mul,map_add,map_natCast,map_one]
  ring

/-- The coordinate degree of the ordinary polar resultant. -/
theorem coordinate_bound (F : R[X][X]) (slope : R) (d w : ℕ) (hd : 1 ≤ d) (hw : 1 ≤ w)
    (hF : ∀ j, F.coeff j ≠ 0 → (F.coeff j).natDegree + d*j ≤ w) :
    (polarResultant F slope).natDegree ≤ 6*w-9*d-3 := by
  have hP (j : ℕ) (hn : (polar F slope).coeff j ≠ 0) :
      ((polar F slope).coeff j).natDegree + d*j ≤ w-1 := by
    rw [coeff_polar] at hn ⊢
    apply bound_add hn
    · intro hx
      have h0 : F.coeff j ≠ 0 := fun hz => hx (by simp [hz])
      have hp : (F.coeff j).natDegree ≠ 0 := fun hz => hx (by rw [eq_C_of_natDegree_eq_zero hz,derivative_C])
      have := natDegree_derivative_lt hp
      have := hF j h0
      omega
    · intro hy
      have h0 : F.coeff (j+1) ≠ 0 := fun hz => hy (by rw [hz,mul_zero])
      have := hF (j+1) h0
      rw [Nat.mul_add,Nat.mul_one] at this
      have := natDegree_C_mul_le (slope*(j+1:R)) (F.coeff (j+1))
      omega
  have hh := WeightedHessianResultant.weighted_resultant_le F (polar F slope) 3 3 d w (w-1) hF hP
  unfold polarResultant
  omega

variable {K : Type} [Field K]

/-- The scalar degree bound counts the scalar-plus-ordinate total degree. -/
theorem scalar_bound (F : K[X][X][X]) (slope : K) (m : ℕ)
    (hF : ∀ j, F.coeff j ≠ 0 → Bivariate.degreeX (F.coeff j) + j ≤ m) :
    Bivariate.degreeX (polarResultant F (C slope)) ≤ 6*m-9 := by
  let φ := (Bivariate.swap (R := K)).toRingEquiv.toRingHom
  have hφ (u : K[X][X]) : (φ u).natDegree = Bivariate.degreeX u := Bivariate.natDegree_swap u
  have hh (j : ℕ) (hn : (F.map φ).coeff j ≠ 0) :
      ((F.map φ).coeff j).natDegree + 1*j ≤ m := by
    rw [Polynomial.coeff_map] at hn ⊢
    simpa only [hφ,one_mul] using hF j (fun h => hn (by simp [h]))
  have hP (j : ℕ) (hn : ((polar F (C slope)).map φ).coeff j ≠ 0) :
      (((polar F (C slope)).map φ).coeff j).natDegree + 1*j ≤ m := by
    rw [Polynomial.coeff_map,coeff_polar,map_add] at hn ⊢
    rw [one_mul]
    apply bound_add hn
    · intro hx
      have h0 : F.coeff j ≠ 0 := fun hz => hx (by simp [hz])
      rw [hφ]
      exact Nat.add_le_add_right (Bivariate.degreeX_derivative_le _) _ |>.trans (hF j h0)
    · intro hy
      have h0 : F.coeff (j+1) ≠ 0 := fun hz => hy (by simp [hz])
      have hc : C (C slope * ((j:K[X])+1)) = (C (C (slope*((j:K)+1))) : K[X][X]) := by simp
      rw [hc,map_mul]
      have hcc : φ (C (C (slope*((j:K)+1)))) = C (C (slope*((j:K)+1))) := Bivariate.swap_C_C _
      rw [hcc]
      have := natDegree_C_mul_le (C (slope*((j:K)+1))) (φ (F.coeff (j+1)))
      rw [hφ] at this
      have := hF (j+1) h0
      omega
  have H := WeightedHessianResultant.weighted_resultant_le (F.map φ) ((polar F (C slope)).map φ) 3 3 1 m m hh hP
  rw [resultant_map_map,hφ] at H
  unfold polarResultant
  omega

/-- Neither coordinate differentiation nor the slope term increases ordinate degree. -/
theorem polar_natDegree_le (F : R[X][X]) (slope : R) :
    (polar F slope).natDegree ≤ F.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [coeff_polar, coeff_eq_zero_of_natDegree_lt hj,derivative_zero,
    coeff_eq_zero_of_natDegree_lt (show F.natDegree < j+1 by omega),mul_zero,add_zero]

/-- A simple polynomial section contributes the square of its ordinate derivative
to the integral polar resultant in the selected scalar fiber. -/
theorem section_square (F : K[X][X][X]) (slope z : K) (q : K[X]) (hd : F.natDegree ≤ 3)
    (hroot : (F.map (mapRingHom (evalRingHom z))).eval q = 0)
    (hsimple : (F.map (mapRingHom (evalRingHom z))).derivative.eval q ≠ 0) :
    (F.map (mapRingHom (evalRingHom z))).derivative.eval q ^ 2 ∣
      (polarResultant F (C slope)).map (evalRingHom z) := by
  let f := F.map (mapRingHom (evalRingHom z))
  have hf : f.natDegree ≤ 3 := natDegree_map_le.trans hd
  have hfn : f ≠ 0 := fun hz => hsimple (by change f.derivative.eval q = 0; simp [hz])
  obtain ⟨G,hG⟩ := dvd_iff_isRoot.mpr (show f.eval q = 0 from hroot)
  have hGn : G ≠ 0 := fun hz => hfn (by simp [hG,hz])
  have hdeg : 1+G.natDegree ≤ 3 := by
    rw [hG,natDegree_mul (X_sub_C_ne_zero q) hGn,natDegree_X_sub_C] at hf
    exact hf
  let _ : Differential K[X] := ⟨(Polynomial.derivative' (R := K)).restrictScalars ℤ⟩
  have hy := (PolynomialSectionJacobian.section_partials q G f hG).2
  rw [map_resultant,show (evalRingHom z) (C slope) = slope from eval_C]
  change f.derivative.eval q ^ 2 ∣ f.resultant (Differential.mapCoeffs f + C (C slope)*f.derivative) 3 3
  rw [hy]
  apply OrdinaryPolarRankLoss.section_square_dvd_polar q (C slope) f G 3 3 hG hdeg (by decide)
  exact (polar_natDegree_le f slope).trans (natDegree_map_le.trans hd)

/-- Two actual ordinary polar resultants of a raw cubic in a chart with simple
full-degree residuals force the terminal generic gcd. -/
theorem supported_gcd_lower (F : K[X][X][X]) (c₁ c₂ : K) (w : ℕ)
    (hw : 201326589 ≤ w) (hw' : w ≤ 290805098) (hd : F.natDegree ≤ 3)
    (hW : ∀ j, F.coeff j ≠ 0 → (F.coeff j).natDegree+67108863*j ≤ w)
    (hM : ∀ j, F.coeff j ≠ 0 → Bivariate.degreeX (F.coeff j)+j ≤ 34)
    (h₁ : polarResultant F (C c₁) ≠ 0) (h₂ : polarResultant F (C c₂) ≠ 0)
    (S : Finset K) (hS : 1342177085 ≤ S.card) (q : K → K[X])
    (hroot : ∀ z ∈ S, (F.map (mapRingHom (evalRingHom z))).eval (q z) = 0)
    (hdeg : ∀ z ∈ S, ((F.map (mapRingHom (evalRingHom z))).derivative.eval (q z)).natDegree =
      w-67108863) :
    2*(w-67108863) ≤ OrdinaryPolarGcdBudget.genericDegree
      (polarResultant F (C c₁)) (polarResultant F (C c₂)) + 201 := by
  apply OrdinaryPolarCappedGcd.production_gcd_lower _ _ h₁ h₂ w hw hw'
    (coordinate_bound _ _ _ _ (by decide) (by omega) hW)
    (coordinate_bound _ _ _ _ (by decide) (by omega) hW)
    (scalar_bound _ _ 34 hM) (scalar_bound _ _ 34 hM) S hS
    (fun z => (F.map (mapRingHom (evalRingHom z))).derivative.eval (q z))
  intro z hz
  have hdeg' := hdeg z hz
  have hn : (F.map (mapRingHom (evalRingHom z))).derivative.eval (q z) ≠ 0 := by
    intro h
    rw [h,natDegree_zero] at hdeg'
    omega
  exact ⟨hn,hdeg',section_square F c₁ z _ hd (hroot z hz) hn,
    section_square F c₂ z _ hd (hroot z hz) hn⟩

#print axioms supported_gcd_lower
#print axioms section_square
#print axioms map_resultant
#print axioms coordinate_bound
#print axioms scalar_bound
end ArkLib.ProximityGap.Frontier.IntegralOrdinaryPolars
