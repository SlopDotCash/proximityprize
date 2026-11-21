/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.AlgebraicSectionSpecialization

/-! # An irreducible component with zero scalar Hessian has at most one scalar fiber

The coefficient field contains the fixed coordinate. The inner indeterminate in
this file is the scalar parameter and the outer one is the value. Divisibility
by the scalar Hessian makes the generic value affine in the scalar, with
algebraic coefficients. Each coefficient-field point lies on this same section.
Two distinct scalar labels would force the affine coefficients into the base field.
-/

set_option autoImplicit false
noncomputable section

open Polynomial
open scoped Differential

namespace ArkLib.ProximityGap.Frontier.ReverseHessianAffineSection

open MovingCubicVanishingBranch AlgebraicSectionSpecialization BoundedRationalEliminant

variable {k : Type} [Field k]

/-- Differentiate the scalar parameter and fix the value indeterminate. -/
def scalarDerivative (f : k[X][X]) : k[X][X] :=
  letI := coordinateDifferential (k := k)
  Differential.mapCoeffs f

/-- Cleared second derivative of the implicit curve, up to sign. -/
def hessian (f : k[X][X]) : k[X][X] :=
  scalarDerivative (scalarDerivative f) * f.derivative^2 -
    2*(scalarDerivative f).derivative*f.derivative*scalarDerivative f + f.derivative.derivative*(scalarDerivative f)^2

private theorem scalarDerivative_coeff (f : k[X][X]) (i : ℕ) : (scalarDerivative f).coeff i = (f.coeff i).derivative :=
  rfl

private theorem mixed (f : k[X][X]) : scalarDerivative f.derivative = (scalarDerivative f).derivative := by
  apply Polynomial.ext
  intro i
  rw [scalarDerivative_coeff, coeff_derivative, derivative_mul, coeff_derivative, scalarDerivative_coeff]
  simp

/-- Compute the recursive derivative numerator at order two. -/
theorem numerator_one (f : k[X][X]) : coordinateNumerator f 1 = - hessian f := by
  let _ : Differential k[X] := coordinateDifferential
  have hm : Differential.mapCoeffs f.derivative = (Differential.mapCoeffs f).derivative := mixed f
  unfold coordinateNumerator hessian scalarDerivative
  simp only [ImplicitDerivativeNumerator.numerator, ImplicitDerivativeNumerator.along,
    map_neg, hm, Nat.mul_zero, Nat.zero_add, Nat.cast_one, one_mul]
  ring

private def intercept (f : k[X][X]) : k[X][X] :=
  Polynomial.X * f.derivative + C Polynomial.X * scalarDerivative f

private def slope (f : k[X][X]) : k[X][X] := -scalarDerivative f

private theorem scalarDerivative_degree (f : k[X][X]) : (scalarDerivative f).natDegree ≤ f.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [scalarDerivative_coeff, coeff_eq_zero_of_natDegree_lt hi, derivative_zero]

private theorem scalarDerivative_height (f : k[X][X]) (t : ℕ) (hf : Polynomial.Bivariate.degreeX f ≤ t)
    (i : ℕ) : ((scalarDerivative f).coeff i).natDegree ≤ t := by
  rw [scalarDerivative_coeff]
  exact (natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans
    ((Polynomial.Bivariate.coeff_natDegree_le_degreeX f i).trans hf))

private theorem intercept_degree (f : k[X][X]) (hf : f.natDegree ≤ 4) :
    (intercept f).natDegree ≤ 4 := by
  apply natDegree_add_le_of_degree_le
  · have hh := natDegree_derivative_le f
    apply natDegree_mul_le.trans
    rw [natDegree_X]
    omega
  · exact (natDegree_C_mul_le _ _).trans ((scalarDerivative_degree f).trans hf)

private theorem intercept_height (f : k[X][X]) (t : ℕ) (hf : Polynomial.Bivariate.degreeX f ≤ t)
    (i : ℕ) : ((intercept f).coeff i).natDegree ≤ t+1 := by
  rw [intercept, coeff_add, coeff_C_mul]
  apply (natDegree_add_le _ _).trans
  apply max_le
  · have hJ (j : ℕ) := (coeff_derivative_natDegree_le f j).trans
      ((Polynomial.Bivariate.coeff_natDegree_le_degreeX f (j+1)).trans hf)
    cases i with
    | zero => simp
    | succ i => simpa using (hJ i).trans (Nat.le_succ t)
  · apply natDegree_mul_le.trans
    rw [natDegree_X]
    have hh := scalarDerivative_height f t hf i
    omega

private theorem flat_affine_coeffs {E L : Type*} [Field E] [Field L] [Algebra k L] [Differential L]
    {p : ℕ} [CharP k p] (hk : ∀ a : k, (algebraMap k L a)′ = 0)
    (φ : k[X] →+* E) (hinj : Function.Injective φ) (f : k[X][X])
    (hirr : Irreducible (f.map φ)) (hJ : f.derivative ≠ 0) (hpos : f.natDegree ≠ 0)
    (hf : f.natDegree ≤ 4) (t : ℕ) (ht : Polynomial.Bivariate.degreeX f ≤ t)
    (hchar : 8*t+4 < p) (z y : L) (hz : z′ = 1) (hy : (y′)′ = 0)
    (hroot : (f.map (aeval z).toRingHom).eval y = 0) :
    IsAlgebraic k (y-z*y′) ∧ IsAlgebraic k y′ := by
  let _ : Differential k := ⟨0⟩
  let _ : DifferentialAlgebra k L := ⟨fun a => by
    rw [hk]; exact (map_zero (algebraMap k L)).symm⟩
  let _ : Differential k[X] := coordinateDifferential
  let _ : Algebra k[X] L := (aeval z).toRingHom.toAlgebra
  let _ : DifferentialAlgebra k[X] L := ⟨fun q => by
    change (aeval z q)′ = aeval z q.derivative
    have hm : Differential.mapCoeffs q = 0 := by ext i; rfl
    rw [Differential.deriv_aeval_eq, hm, map_zero, hz, mul_one, zero_add]⟩
  have he (q : k[X][X]) : (q.map (aeval z).toRingHom).eval y = aeval y q := by
    rw [eval_map, aeval_def]
    rfl
  have hF : aeval y f = 0 := (he f).symm.trans hroot
  have himplicit : aeval y (scalarDerivative f) + aeval y f.derivative*y′ = 0 := by
    have hu := Differential.deriv_aeval_eq y f
    rw [hF, map_zero] at hu
    exact hu.symm
  have hden : ¬f.map φ ∣ f.derivative.map φ := by
    intro h
    rw [← derivative_map] at h
    have heq := dvd_derivative_iff.mp h
    rw [derivative_map] at heq
    apply hJ
    apply Polynomial.map_injective φ hinj
    simpa using heq
  have hdz : z′ ≠ 0 := hz.trans_ne one_ne_zero
  have hft i := (Polynomial.Bivariate.coeff_natDegree_le_degreeX f i).trans ht
  have hjt i := (coeff_derivative_natDegree_le f i).trans (hft (i+1))
  have hJy : f.derivative.natDegree ≤ 4 := (natDegree_derivative_le f).trans ((Nat.sub_le _ _).trans hf)
  have hzero : (y-z*y′)′ = 0 := by
    rw [map_sub, Differential.deriv.leibniz, hy, hz]
    simp
  constructor
  · apply isAlgebraic_of_bounded_rational_expression hk φ hinj f (intercept f) f.derivative
      hirr hden hpos _ z y hdz hzero hroot _ t (t+1) hft (intercept_height f t ht)
      (fun i => (hjt i).trans (Nat.le_succ t))
    · have ha := Nat.mul_le_mul_right t (max_le (intercept_degree f hf) hJy)
      have hb := Nat.mul_le_mul_right (t+1) hf
      omega
    · rw [he, he, intercept, map_add, map_mul, map_mul, aeval_X, aeval_C]
      change y * aeval y f.derivative + (aeval z) Polynomial.X * aeval y (scalarDerivative f) = _
      rw [aeval_X]
      linear_combination z * himplicit
  · apply isAlgebraic_of_bounded_rational_expression hk φ hinj f (slope f) f.derivative
      hirr hden hpos _ z y hdz hy hroot _ t t hft _ hjt
    · have hy' : (slope f).natDegree ≤ 4 := by simpa [slope] using (scalarDerivative_degree f).trans hf
      have ha := Nat.mul_le_mul_right t (max_le hy' hJy)
      have hb := Nat.mul_le_mul_right t hf
      omega
    · rw [he, he, slope, map_neg]
      linear_combination -himplicit
    · intro i
      simpa [slope] using scalarDerivative_height f t ht i

/-- All coefficient-field points of a primitive component annihilating its explicit
scalar Hessian lie on one affine line over algebraic constants. -/
theorem affine_section {p : ℕ} [CharP k p] (f : k[X][X])
    (hirr : Irreducible (genericEquation f)) (hprim : f.IsPrimitive)
    (hpos : f.natDegree ≠ 0) (hf : f.natDegree ≤ 4) (hcharY : f.natDegree < p)
    (t : ℕ) (ht : Polynomial.Bivariate.degreeX f ≤ t) (hchar : 8*t+4 < p)
    (hdiv : genericEquation f ∣ genericEquation (hessian f)) :
    ∃ a b : AdjoinRoot (genericEquation f), IsAlgebraic k a ∧ IsAlgebraic k b ∧
      AdjoinRoot.root (genericEquation f) = a+b*AdjoinRoot.of (genericEquation f) RatFunc.X ∧
      ∀ z w : k, (f.map (evalRingHom z)).eval w = 0 →
        a+b*algebraMap k _ z = algebraMap k _ w := by
  let g := genericEquation f
  let L := AdjoinRoot g
  let _ : Fact (Irreducible g) := ⟨hirr⟩
  have hJ : f.derivative ≠ 0 := fun hh => hpos
    (PositiveCharacteristicHeightDescent.natDegree_eq_zero_of_derivative_eq_zero f hcharY hh)
  have hN : genericEquation f ∣ genericEquation (coordinateNumerator f 1) := by
    rw [numerator_one]
    change genericEquation f ∣ (-hessian f).map _
    rw [Polynomial.map_neg, dvd_neg]
    exact hdiv
  obtain ⟨D,hk,hz,hy⟩ := exists_generic_flat_differential f hJ 1 hN
  let _ : Differential L := D
  let z : L := AdjoinRoot.of g RatFunc.X
  let y : L := AdjoinRoot.root g
  have hZ : algebraMap k[X] L Polynomial.X = z := rfl
  have heval : (aeval z).toRingHom = algebraMap k[X] L := by
    ext a
    · exact aeval_C z a
    · exact (aeval_X z).trans hZ.symm
  have hroot : (f.map (aeval z).toRingHom).eval y = 0 := by
    rw [heval, eval_map_algebraMap]
    have he : aeval y (genericEquation f) = aeval y f := by
      rw [aeval_def, aeval_def, genericEquation, eval₂_map]
      rfl
    exact he.symm.trans (AdjoinRoot.eval₂_root g)
  let a := y-z*y′
  let b := y′
  obtain ⟨ha,hb⟩ := flat_affine_coeffs hk (algebraMap k[X] (RatFunc k))
    (RatFunc.algebraMap_injective k) f hirr hJ hpos hf t ht hchar z y hz hy hroot
  let q := C a+C b*Polynomial.X
  have he (u : L) : q.eval u = a+b*u := by simp [q]
  have hv : q.eval z = y := by rw [he]; dsimp [a,b]; ring
  have hq (i : ℕ) : IsAlgebraic k (q.coeff i) := by
    cases i with
    | zero => simpa [q, coeff_C_mul] using ha
    | succ i => cases i with
      | zero => simpa [q, coeff_C_mul] using hb
      | succ i =>
        have hh : q.coeff (i+2) = 0 := by simp [q]
        rw [hh]; exact isAlgebraic_zero
  refine ⟨a,b,ha,hb, (he z).symm ▸ hv.symm, ?_⟩
  intro z₀ w hs
  rw [← he]
  exact section_at_site z y hZ f (generic_root_dvd f hprim) q hv hq z₀ w hs

/-- Every geometric root is an affine linear expression in the scalar with
coefficients algebraic over the original coefficient field. Applying this in
an algebraic closure gives the affine-line description of every linear factor. -/
theorem geometric_root_affine {p : ℕ} [CharP k p] (f : k[X][X])
    (hirr : Irreducible (genericEquation f)) (hprim : f.IsPrimitive)
    (hpos : f.natDegree ≠ 0) (hf : f.natDegree ≤ 4) (hcharY : f.natDegree < p)
    (t : ℕ) (ht : Polynomial.Bivariate.degreeX f ≤ t) (hchar : 8*t+4 < p)
    (hdiv : genericEquation f ∣ genericEquation (hessian f))
    {Ω : Type*} [Field Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω] [IsScalarTower k (RatFunc k) Ω]
    (y : Ω) (hy : aeval y (genericEquation f) = 0) :
    ∃ a b : Ω, IsAlgebraic k a ∧ IsAlgebraic k b ∧
      y = a+b*algebraMap (RatFunc k) Ω RatFunc.X := by
  let g := genericEquation f
  let ψ := Algebra.algHom k (RatFunc k) Ω
  let μ := AdjoinRoot.liftAlgHom g ψ y hy
  obtain ⟨a,b,ha,hb,hv,_⟩ := affine_section f hirr hprim hpos hf hcharY t ht hchar hdiv
  refine ⟨μ a, μ b, ha.algHom μ, hb.algHom μ, ?_⟩
  change y = μ a+μ b*ψ RatFunc.X
  have he : μ (AdjoinRoot.root g) = μ (a+b*AdjoinRoot.of g RatFunc.X) := congrArg μ hv
  rw [map_add, map_mul] at he
  have hμroot : μ (AdjoinRoot.root g) = y := AdjoinRoot.liftAlgHom_root g ψ y hy
  have hμz : μ (AdjoinRoot.of g RatFunc.X) = ψ RatFunc.X :=
    AdjoinRoot.liftAlgHom_of g ψ y hy RatFunc.X
  rw [hμroot, hμz] at he
  exact he

/-- An irreducible component of value degree two, three, or four that divides its
scalar Hessian admits at most one distinct scalar with a coefficient-field value. -/
theorem scalar_unique {p : ℕ} [CharP k p] (f : k[X][X])
    (hirr : Irreducible (genericEquation f)) (hprim : f.IsPrimitive)
    (hmin : 2 ≤ f.natDegree) (hf : f.natDegree ≤ 4) (hcharY : f.natDegree < p)
    (t : ℕ) (ht : Polynomial.Bivariate.degreeX f ≤ t) (hchar : 8*t+4 < p)
    (hdiv : genericEquation f ∣ genericEquation (hessian f))
    (z₀ z₁ w₀ w₁ : k) (h₀ : (f.map (evalRingHom z₀)).eval w₀ = 0)
    (h₁ : (f.map (evalRingHom z₁)).eval w₁ = 0) : z₀ = z₁ := by
  by_contra hz
  let g := genericEquation f
  let L := AdjoinRoot g
  let _ : Fact (Irreducible g) := ⟨hirr⟩
  let φ := algebraMap k L
  obtain ⟨a,b,_,_,hy,hs⟩ := affine_section f hirr hprim (by omega) hf hcharY t ht hchar hdiv
  have e₀ : a+b*φ z₀ = φ w₀ := hs _ _ h₀
  have e₁ : a+b*φ z₁ = φ w₁ := hs _ _ h₁
  let b₀ : k := (w₀-w₁)/(z₀-z₁)
  let a₀ : k := w₀-b₀*z₀
  have hb : b = φ b₀ := by
    rw [show b₀ = _ from rfl, map_div₀, map_sub, map_sub]
    apply (eq_div_iff (sub_ne_zero.mpr (φ.injective.ne hz))).mpr
    linear_combination e₀-e₁
  have ha : a = φ a₀ := by
    rw [show a₀ = _ from rfl, map_sub, map_mul, ← hb]
    linear_combination e₀
  let u : RatFunc k := RatFunc.C a₀ + RatFunc.C b₀*RatFunc.X
  have hlin : AdjoinRoot.root g = AdjoinRoot.of g u := by
    rw [hy, ha, hb, show u = _ from rfl, map_add, map_mul]
    rfl
  have hlinDiv : g ∣ Polynomial.X - C u := by
    apply AdjoinRoot.mk_eq_zero.mp
    rw [map_sub]
    exact sub_eq_zero.mpr hlin
  have hh := natDegree_le_of_dvd hlinDiv (X_sub_C_ne_zero u)
  rw [natDegree_X_sub_C] at hh
  have he := natDegree_map_eq_of_injective (RatFunc.algebraMap_injective k) (p := f)
  change g.natDegree = _ at he
  omega

/-- Finite scalar count for the reverse-Hessian branch. -/
theorem card_scalar_le_one {p : ℕ} [CharP k p] (f : k[X][X])
    (hirr : Irreducible (genericEquation f)) (hprim : f.IsPrimitive)
    (hmin : 2 ≤ f.natDegree) (hf : f.natDegree ≤ 4) (hcharY : f.natDegree < p)
    (t : ℕ) (ht : Polynomial.Bivariate.degreeX f ≤ t) (hchar : 8*t+4 < p)
    (hdiv : genericEquation f ∣ genericEquation (hessian f))
    (M : Finset k) (hM : ∀ z ∈ M, ∃ w : k, (f.map (evalRingHom z)).eval w = 0) :
    M.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro z hz z' hz'
  obtain ⟨w, hw⟩ := hM z hz
  obtain ⟨w', hw'⟩ := hM z' hz'
  exact scalar_unique f hirr hprim hmin hf hcharY t ht hchar hdiv z z' w w' hw hw'

/-- Count scalar labels drawn from an embedded field, as in the Reed–Solomon application. -/
theorem card_embedded_scalar_le_one {F : Type*} [Field F] (ι : F →+* k) {p : ℕ} [CharP k p]
    (f : k[X][X]) (hirr : Irreducible (genericEquation f)) (hprim : f.IsPrimitive)
    (hmin : 2 ≤ f.natDegree) (hf : f.natDegree ≤ 4) (hcharY : f.natDegree < p)
    (t : ℕ) (ht : Polynomial.Bivariate.degreeX f ≤ t) (hchar : 8*t+4 < p)
    (hdiv : genericEquation f ∣ genericEquation (hessian f))
    (M : Finset F) (hM : ∀ z ∈ M, ∃ w : k, (f.map (evalRingHom (ι z))).eval w = 0) :
    M.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro z hz z' hz'
  obtain ⟨w, hw⟩ := hM z hz
  obtain ⟨w', hw'⟩ := hM z' hz'
  exact ι.injective (scalar_unique f hirr hprim hmin hf hcharY t ht hchar hdiv _ _ w w' hw hw')

end ArkLib.ProximityGap.Frontier.ReverseHessianAffineSection

open ArkLib.ProximityGap.Frontier.ReverseHessianAffineSection in
#print axioms card_embedded_scalar_le_one
open ArkLib.ProximityGap.Frontier.ReverseHessianAffineSection in
#print axioms geometric_root_affine
