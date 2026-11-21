/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.TameBranchDerivative

/-! # Polar orders on tame Laurent branches

In the chart X = α + t^e, the coordinate derivative fixes the coefficient
field. The scalar derivative fixes X and moves the center α. We use both
on the same series to compare the two first partials with the scalar Hessian.
-/

set_option autoImplicit false
noncomputable section

open HahnSeries Polynomial
open scoped Differential

namespace ArkLib.ProximityGap.Frontier.TameBranchPolarOrders

open TameBranchDerivative

variable {K : Type*} [Field K]

@[instance_reducible] private def constantDifferential : Differential K := ⟨0⟩

/-- Coordinate differentiation on the chart, holding all coefficients fixed. -/
def coordinateDerivative (e : ℕ) (y : LaurentSeries K) : LaurentSeries K :=
  letI := constantDifferential (K := K)
  branchDerivative e (e : K)⁻¹ y

@[instance_reducible] private def coordinateDifferential (e : ℕ) : Differential (LaurentSeries K) :=
  letI := constantDifferential (K := K)
  ⟨chartDerivation e (e : K)⁻¹⟩

/-- The coordinate partial evaluated at the branch ordinate. -/
def coordinatePartial (e : ℕ) (f : Polynomial (LaurentSeries K)) (y : LaurentSeries K) : LaurentSeries K :=
  letI := coordinateDifferential (K := K) e
  (Differential.mapCoeffs f).eval y

theorem coordinate_coeff (e : ℕ) (y : LaurentSeries K) (i : ℤ) :
    (coordinateDerivative e y).coeff i = ((i+e : ℤ) : K) * y.coeff (i+e) * (e : K)⁻¹ := by
  let _ := constantDifferential (K := K)
  rw [coordinateDerivative, coeff_branchDerivative, zsmul_eq_mul]
  change 0 + _ = _
  exact zero_add _

/-- The leading term of a nonconstant ordinate of order s survives coordinate
differentiation when s and the ramification index are nonzero in the field. -/
theorem coordinate_leading (e : ℕ) (y : LaurentSeries K) (s : ℤ)
    (he : (e : K) ≠ 0) (hs : (s : K) ≠ 0) (hy : y.coeff s ≠ 0)
    (hl : ∀ i : ℤ, i ≠ 0 → i < s → y.coeff i = 0) :
    coordinateDerivative e y ≠ 0 ∧ (coordinateDerivative e y).order = s-e := by
  have hc : (coordinateDerivative e y).coeff (s-e) ≠ 0 := by
    rw [coordinate_coeff, sub_add_cancel]
    exact mul_ne_zero (mul_ne_zero hs hy) (inv_ne_zero he)
  have hn : coordinateDerivative e y ≠ 0 := by
    rintro hz
    simp [hz] at hc
  refine ⟨hn, le_antisymm (order_le_of_coeff_ne_zero hc) ((le_order_iff_forall hn).2 ?_)⟩
  intro i hi
  rw [coordinate_coeff]
  by_cases h : i+(e : ℤ) = 0
  · simp [h]
  · simp [hl _ h (by omega)]

theorem coordinate_partial_eq (e : ℕ) (f : Polynomial (LaurentSeries K)) (y : LaurentSeries K) (h : f.eval y = 0) :
    coordinatePartial e f y = -(f.derivative.eval y * coordinateDerivative e y) := by
  let _ := coordinateDifferential (K := K) e
  have hd : y′ = coordinateDerivative e y := rfl
  have root : aeval y f = 0 := by simpa using h
  have H := Differential.deriv_aeval_eq y f
  rw [root, map_zero] at H
  apply eq_neg_of_add_eq_zero_left
  rw [hd] at H
  simpa [coordinatePartial] using H.symm

/-- The coordinate partial's order equals the value partial's order plus s-e
on a nontangent ordinate. The two partials are the actual derivatives of f. -/
theorem coordinate_partial_order (e : ℕ) (f : Polynomial (LaurentSeries K)) (y : LaurentSeries K) (h : f.eval y = 0)
    (s : ℤ) (he : (e : K) ≠ 0) (hs : (s : K) ≠ 0) (hy : y.coeff s ≠ 0)
    (hl : ∀ i : ℤ, i ≠ 0 → i < s → y.coeff i = 0) (hj : f.derivative.eval y ≠ 0) :
    coordinatePartial e f y ≠ 0 ∧
      (coordinatePartial e f y).order = (f.derivative.eval y).order + (s-e) := by
  obtain ⟨hn,ho⟩ := coordinate_leading e y s he hs hy hl
  rw [coordinate_partial_eq e f y h]
  exact ⟨neg_ne_zero.mpr (mul_ne_zero hj hn), by rw [order_neg, order_mul hj hn, ho]⟩

private theorem below_cube {y : LaurentSeries K} {a : ℤ} (h : VanishesBelow y a) :
    VanishesBelow (y^3) (3*a) := by
  rw [pow_succ, pow_two, show 3*a = (a+a)+a by ring]
  exact below_mul (below_mul h h) h

variable [Differential K]

/-- With no nonconstant term below s, two moving-center scalar derivatives
lose at most 2e from that first nonconstant order, provided s ≤ 2e. -/
theorem second_from_first_term (e : ℕ) (c : K) (y : LaurentSeries K) {s : ℤ} (hs : s ≤ 2*e)
    (hl : ∀ i : ℤ, i ≠ 0 → i < s → y.coeff i = 0) :
    VanishesBelow (branchDerivative e c (branchDerivative e c y)) (s-2*e) := by
  let u := y - single 0 (y.coeff 0)
  have hu : VanishesBelow u s := by
    intro i hi
    by_cases h : i = 0
    · simp [u,h]
    · simp [u,h,hl i h hi]
  have ht := derivative_lower e c (derivative_lower e c hu)
  have heq : y = u + single 0 (y.coeff 0) := (sub_add_cancel _ _).symm
  conv_lhs => rw [heq, branch_add, branch_add]
  intro i hi
  have hiz : i ≠ 0 := by omega
  rw [HahnSeries.coeff_add, ht i (by omega), zero_add]
  simp [branch_single, hiz]

/-- The cubed scalar Hessian numerator has order at least 8ν on the
nontangent branch, with ν the smaller of the two actual partial orders. -/
theorem transverse_polar_charge (e : ℕ) (c : K) (f : Polynomial (LaurentSeries K)) (y : LaurentSeries K)
    (h : f.eval y = 0) (s : ℤ) (hlt : s < e)
    (he : (e : K) ≠ 0) (hs : (s : K) ≠ 0) (hy : y.coeff s ≠ 0)
    (hl : ∀ i : ℤ, i ≠ 0 → i < s → y.coeff i = 0) (hj : f.derivative.eval y ≠ 0)
    (hν : 3*(s-1) ≤ (coordinatePartial e f y).order) :
    VanishesBelow ((sectionNumerator e c f y)^3)
      (8 * min (coordinatePartial e f y).order (f.derivative.eval y).order) := by
  obtain ⟨_,ho⟩ := coordinate_partial_order e f y h s he hs hy hl hj
  rw [min_eq_left (by omega : (coordinatePartial e f y).order ≤ (f.derivative.eval y).order)]
  have bound := below_cube (sectionNumerator_below e c f y h
    ((le_order_iff_forall hj).1 le_rfl) (second_from_first_term e c y (by omega) hl))
  intro i hi
  exact bound i (by omega)

/-- A tangent branch uses the cancellation of the first regular term after
twice differentiating. The hypothesis ν ≥ 3(e-1) is the local singularity bound. -/
theorem tangent_polar_charge (e : ℕ) (c : K) (f : Polynomial (LaurentSeries K)) (y : LaurentSeries K)
    (h : f.eval y = 0) (he : 0 < e) (ν : ℤ)
    (hj : VanishesBelow (f.derivative.eval y) ν) (hν : 3*((e : ℤ)-1) ≤ ν)
    (hl : ∀ i : ℤ, i ≠ 0 → i < e → y.coeff i = 0) :
    VanishesBelow ((sectionNumerator e c f y)^3) (8*ν) := by
  have H := below_cube (sectionNumerator_below e c f y h hj (second_tangent e he c hl))
  intro i hi
  exact H i (by omega)

private theorem inverse_second (e : ℕ) (c : K) (T : LaurentSeries K) (hn : T ≠ 0) :
    T^4 * branchDerivative e c (branchDerivative e c T⁻¹) =
      2*T*(branchDerivative e c T)^2 - T^2*branchDerivative e c (branchDerivative e c T) := by
  let D := branchDerivative e c
  have h0 : D (0 : LaurentSeries K) = 0 := by ext i; simp [D]
  have h1 : D (1 : LaurentSeries K) = 0 := by
    have hh := branch_mul e c (1 : LaurentSeries K) 1
    simpa [D] using (show branchDerivative e c 1 = 0 by simpa using hh)
  have hfirst : D T*T⁻¹ + T*D T⁻¹ = 0 := by
    rw [← branch_mul, mul_inv_cancel₀ hn]
    exact h1
  have hsecond := congrArg D hfirst
  change D (D T*T⁻¹ + T*D T⁻¹) = D 0 at hsecond
  rw [h0] at hsecond
  change branchDerivative e c (D T*T⁻¹ + T*D T⁻¹) = 0 at hsecond
  rw [branch_add, branch_mul, branch_mul] at hsecond
  change T^4 * D (D T⁻¹) = 2*T*(D T)^2 - T^2*D (D T)
  linear_combination (norm := (field_simp [hn]; ring)) T^3*hsecond - 2*T^2*D T*hfirst

/-- The reciprocal-chart numerator, expressed without a pole in the value
coordinate. The first implicit derivative numerator is minus the scalar partial. -/
def reciprocalNumerator (e : ℕ) (c : K) (f : Polynomial (LaurentSeries K))
    (T : LaurentSeries K) : LaurentSeries K :=
  letI : Differential (LaurentSeries K) := ⟨chartDerivation e c⟩
  2*T*f.derivative.eval T*((ImplicitDerivativeNumerator.numerator f 0).eval T)^2 -
    T^2 * sectionNumerator e c f T

/-- The regular reciprocal-chart polynomial at the branch is the cleared
second derivative of the original, possibly unbounded, ordinate. -/
theorem reciprocalNumerator_eq (e : ℕ) (c : K) (f : Polynomial (LaurentSeries K))
    (T : LaurentSeries K) (h : f.eval T = 0) (hn : T ≠ 0) :
    reciprocalNumerator e c f T = T^4*(f.derivative.eval T)^3 *
      branchDerivative e c (branchDerivative e c T⁻¹) := by
  let _ : Differential (LaurentSeries K) := ⟨chartDerivation e c⟩
  have root : aeval T f = 0 := by simpa using h
  have hfirst : (ImplicitDerivativeNumerator.numerator f 0).eval T =
      f.derivative.eval T * branchDerivative e c T := by
    have hD : T′ = branchDerivative e c T := rfl
    simpa [hD] using ImplicitDerivativeNumerator.numerator_aeval f T root 0
  rw [reciprocalNumerator, hfirst, sectionNumerator_eq e c f T h]
  linear_combination -(f.derivative.eval T)^3 * inverse_second e c T hn

/-- At a pole of the original ordinate, after reserving the zero of the
leading coefficient the cubed numerator supplies 8ν−2s more orders. Here
s is the order of T and ν the order of the first coordinate partial. -/
theorem infinity_polar_charge (e : ℕ) (c : K) (f : Polynomial (LaurentSeries K))
    (T : LaurentSeries K) (h : f.eval T = 0) (hT : T ≠ 0) (hj : f.derivative.eval T ≠ 0)
    (he : (e : K) ≠ 0) (hs : (T.order : K) ≠ 0) (hj0 : 0 ≤ (f.derivative.eval T).order) :
    VanishesBelow ((reciprocalNumerator e c f T)^3)
      (8 * (coordinatePartial e f T).order + T.order) := by
  have low := (le_order_iff_forall hT).1 le_rfl
  obtain ⟨_,ho⟩ := coordinate_partial_order e f T h T.order he hs
    (coeff_order_eq_zero.not.2 hT) (fun i _ hi => low i hi) hj
  have hmul := order_mul hT (inv_ne_zero hT)
  rw [mul_inv_cancel₀ hT, order_one] at hmul
  have hinv : VanishesBelow T⁻¹ (-T.order) :=
    (le_order_iff_forall (inv_ne_zero hT)).1 (by omega)
  have h4 := below_mul (below_cube low) low
  have h3 := below_cube ((le_order_iff_forall hj).1 le_rfl)
  have h2 := derivative_lower e c (derivative_lower e c hinv)
  rw [reciprocalNumerator_eq e c f T h hT, show T^4 = T^3*T by ring]
  have H := below_cube (below_mul (below_mul h4 h3) h2)
  intro i hi
  exact H i (by omega)

#print axioms infinity_polar_charge

#print axioms coordinate_partial_order
#print axioms transverse_polar_charge
#print axioms tangent_polar_charge

end ArkLib.ProximityGap.Frontier.TameBranchPolarOrders
