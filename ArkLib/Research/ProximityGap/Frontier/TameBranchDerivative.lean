/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ImplicitDerivativeNumerator
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.Tactic

/-! # Scalar differentiation of Laurent expansions on a tame branch

If the coordinate is held fixed in the chart `X = α + t^e`, the scalar
derivative has the form `D_coeff + c t^(1-e) ∂_t` with `c = -Dα/e`.
The support estimates also apply to the zero series.
-/

open HahnSeries
open scoped Differential

namespace ArkLib.ProximityGap.Frontier.TameBranchDerivative

variable {K : Type*} [Field K] [Differential K]

/-- Absence of terms of exponent less than the specified integer. -/
def VanishesBelow (f : LaurentSeries K) (a : ℤ) : Prop := ∀ i < a, f.coeff i = 0

/-- The chain rule operator on actual Laurent series, with the base coefficient
derivative extended coefficientwise. -/
noncomputable def branchDerivative (e : ℕ) (c : K) (f : LaurentSeries K) : LaurentSeries K :=
  f.map (Differential.deriv : Derivation ℤ K K).toLinearMap +
    LaurentSeries.derivative K f * single (1-(e : ℤ)) c

@[simp]
theorem coeff_branchDerivative (e : ℕ) (c : K) (f : LaurentSeries K) (i : ℤ) :
    (branchDerivative e c f).coeff i =
      (f.coeff i)′ + (i+(e : ℤ) : ℤ) • f.coeff (i+e) * c := by
  simp only [branchDerivative, coeff_add, map_coeff, coeff_mul_single,
    LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff]
  simp [show i - (1-(e : ℤ)) + 1 = i+e by omega]

/-- At a moving center a single derivative loses at most its ramification index. -/
theorem derivative_lower {f : LaurentSeries K} {a : ℤ} (e : ℕ) (c : K)
    (h : VanishesBelow f a) : VanishesBelow (branchDerivative e c f) (a-e) := by
  intro i hi
  simp [h i (by omega), h (i+e) (by omega)]

/-- With constant center, arbitrary iterates preserve the lower bound. -/
theorem fixed_lower {f : LaurentSeries K} {a : ℤ} (e j : ℕ) (h : VanishesBelow f a) :
    VanishesBelow ((branchDerivative e (0 : K))^[j] f) a := by
  induction j with
  | zero => exact h
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    intro i hi
    simp [ih i hi]

/-- A derivative of a regular expansion has no term below `1-e`: its constant
term has no uniformizer derivative. -/
theorem derivative_regular {f : LaurentSeries K} (e : ℕ) (he : 0 < e) (c : K)
    (h : VanishesBelow f 0) : VanishesBelow (branchDerivative e c f) (1-e) := by
  intro i hi
  have hneg : i < 0 := by omega
  by_cases hzero : i + e = 0
  · simp [h i hneg, hzero]
  · simp [h i hneg, h (i+e) (by omega)]

/-- If all positive powers below the ramification index vanish, the first
derivative is regular and the second has the improved lower bound `1-e`. -/
theorem second_tangent {f : LaurentSeries K} (e : ℕ) (he : 0 < e) (c : K)
    (h : ∀ i : ℤ, i ≠ 0 → i < e → f.coeff i = 0) :
    VanishesBelow (branchDerivative e c (branchDerivative e c f)) (1-e) := by
  apply derivative_regular e he
  intro i hi
  by_cases hzero : i + e = 0
  · simp [h i (by omega) (by omega), hzero]
  · simp [h i (by omega) (by omega), h (i+e) hzero (by omega)]

private noncomputable def euler (f : LaurentSeries K) : LaurentSeries K :=
  LaurentSeries.derivative K f * single 1 1

omit [Differential K] in
@[simp] private theorem euler_coeff (f : LaurentSeries K) (i : ℤ) :
    (euler f).coeff i = (i : K) * f.coeff i := by
  simp [euler, coeff_mul_single, LaurentSeries.derivative_apply,
    zsmul_eq_mul]

omit [Differential K] in
private theorem euler_support (f : LaurentSeries K) : (euler f).support ⊆ f.support := by
  intro i hi h
  exact hi (by simp [h])

omit [Differential K] in
private theorem euler_mul (f g : LaurentSeries K) : euler (f*g) = euler f*g + f*euler g := by
  ext i
  rw [euler_coeff, coeff_add, coeff_mul,
    coeff_mul_left' f.isPWO_support (euler_support f),
    coeff_mul_right' g.isPWO_support (euler_support g),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hij := (Finset.mem_antidiagonal.mp hj).2.2
  simp only [euler_coeff]
  rw [← hij, Int.cast_add]
  ring

private noncomputable def coeffD (f : LaurentSeries K) : LaurentSeries K :=
  f.map (Differential.deriv : Derivation ℤ K K).toLinearMap

private theorem coeffD_support (f : LaurentSeries K) : (coeffD f).support ⊆ f.support := by
  intro i hi h
  exact hi (by simp [coeffD, h])

private theorem coeffD_mul (f g : LaurentSeries K) :
    coeffD (f*g) = coeffD f*g + f*coeffD g := by
  ext i
  rw [coeff_add, coeff_mul_left' f.isPWO_support (coeffD_support f),
    coeff_mul_right' g.isPWO_support (coeffD_support g), ← Finset.sum_add_distrib]
  simp only [coeffD, map_coeff, Derivation.coeFn_coe, coeff_mul, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Derivation.leibniz, mul_comm, add_comm]

private theorem branch_eq (e : ℕ) (c : K) (f : LaurentSeries K) :
    branchDerivative e c f = coeffD f + single (-(e : ℤ)) c * euler f := by
  ext i
  rw [coeff_branchDerivative, coeff_add, mul_comm (single _ _), coeff_mul_single]
  simp [coeffD, zsmul_eq_mul]

/-- The chain rule on the tame chart is a derivation on the Laurent series field. -/
theorem branch_mul (e : ℕ) (c : K) (f g : LaurentSeries K) :
    branchDerivative e c (f*g) = branchDerivative e c f*g + f*branchDerivative e c g := by
  simp only [branch_eq, euler_mul, coeffD_mul]
  ring

theorem branch_add (e : ℕ) (c : K) (f g : LaurentSeries K) :
    branchDerivative e c (f+g) = branchDerivative e c f + branchDerivative e c g := by
  ext i
  simp [coeff_branchDerivative, coeff_add, smul_add]
  ring

private def derivationOfLeibniz {L : Type*} [Field L] (D : L →+ L)
    (h : ∀ x y, D (x*y) = D x*y + x*D y) : Derivation ℤ L L :=
  Derivation.mk' D.toIntLinearMap (fun x y => by
    change D (x*y) = x*D y + y*D x
    rw [h]
    ring)

/-- The additive chart operator as a derivation over the integers. -/
noncomputable def chartDerivation (e : ℕ) (c : K) :=
  derivationOfLeibniz
    { toFun := branchDerivative e c
      map_zero' := by ext i; simp [coeff_branchDerivative]
      map_add' := branch_add e c }
    (branch_mul e c)

/-- Differentiating a single term of exponent r on the moving chart. -/
theorem branch_single (e : ℕ) (c : K) (r : ℤ) (a : K) :
    branchDerivative e c (single r a) =
      single r a′ + single (r-e) ((r : K)*a*c) := by
  ext i
  simp only [coeff_branchDerivative, coeff_add, coeff_single, zsmul_eq_mul]
  have heq : i = r-(e : ℤ) ↔ i+(e : ℤ) = r := by omega
  simp only [heq]
  by_cases h : i + (e : ℤ) = r
  · simp only [h, ite_true]
    split <;> simp
  · simp only [h, ite_false, mul_zero, zero_mul, add_zero]
    split <;> simp

/-- With c = -Dα/e the chart really holds the original coordinate fixed. -/
theorem coordinate_fixed (e : ℕ) (he : (e : K) ≠ 0) (α : K) :
    branchDerivative e (-α′/(e : K)) (single 0 α + single (e : ℤ) (1 : K)) = 0 := by
  rw [branch_add, branch_single, branch_single]
  simp [← single_add]
  field_simp [he]
  ring

omit [Differential K] in
/-- Two lower bounds on Laurent exponents add under multiplication, also
when one of the series is zero. -/
theorem below_mul {f g : LaurentSeries K} {a b : ℤ}
    (hf : VanishesBelow f a) (hg : VanishesBelow g b) : VanishesBelow (f*g) (a+b) := by
  rcases eq_or_ne f 0 with rfl | hfn
  · simp [VanishesBelow]
  rcases eq_or_ne g 0 with rfl | hgn
  · simp [VanishesBelow]
  apply (le_order_iff_forall (mul_ne_zero hfn hgn)).1
  rw [order_mul hfn hgn]
  exact add_le_add ((le_order_iff_forall hfn).2 hf) ((le_order_iff_forall hgn).2 hg)

/-- The cleared second implicit derivative evaluated in the Laurent chart. -/
noncomputable def sectionNumerator (e : ℕ) (c : K) (f : Polynomial (LaurentSeries K))
    (y : LaurentSeries K) : LaurentSeries K :=
  letI : Differential (LaurentSeries K) := ⟨chartDerivation e c⟩
  (ImplicitDerivativeNumerator.numerator f 1).eval y

theorem sectionNumerator_eq (e : ℕ) (c : K) (f : Polynomial (LaurentSeries K))
    (y : LaurentSeries K) (h : f.eval y = 0) :
    sectionNumerator e c f y = (f.derivative.eval y)^3 *
      branchDerivative e c (branchDerivative e c y) := by
  let _ : Differential (LaurentSeries K) := ⟨chartDerivation e c⟩
  have hd (v : LaurentSeries K) : v′ = branchDerivative e c v := rfl
  have root : Polynomial.aeval y f = 0 := by simpa using h
  simpa [sectionNumerator, Function.iterate_succ_apply, hd] using
    ImplicitDerivativeNumerator.numerator_aeval f y root 1

/-- Transfer the actual twice-differentiated support and the value partial's
vanishing to the cleared numerator at a root. -/
theorem sectionNumerator_below (e : ℕ) (c : K) (f : Polynomial (LaurentSeries K))
    (y : LaurentSeries K) (h : f.eval y = 0) {j b : ℤ}
    (hj : VanishesBelow (f.derivative.eval y) j)
    (hb : VanishesBelow (branchDerivative e c (branchDerivative e c y)) b) :
    VanishesBelow (sectionNumerator e c f y) (3*j+b) := by
  rw [sectionNumerator_eq _ _ _ _ h, pow_succ, pow_two]
  convert below_mul (below_mul (below_mul hj hj) hj) hb using 1
  ring

/-- A fixed received ordinate with zero second derivative contributes its full
contact order in addition to three times the order of the value partial. -/
theorem received_order (e : ℕ) (f : Polynomial (LaurentSeries K)) (y : LaurentSeries K)
    (h : f.eval y = 0) (β : K) (hβ : β′′ = 0) {j s : ℤ}
    (hj : VanishesBelow (f.derivative.eval y) j) (hs : VanishesBelow (y-single 0 β) s) :
    VanishesBelow (sectionNumerator e 0 f y) (3*j+s) := by
  apply sectionNumerator_below _ _ _ _ h hj
  have H := fixed_lower e 2 hs
  have hconst : branchDerivative e 0 (branchDerivative e 0 (single 0 β)) = 0 := by
    simp [branch_single, hβ]
  rw [← sub_add_cancel y (single 0 β), branch_add, branch_add, hconst, add_zero]
  exact H

#print axioms received_order
#print axioms chartDerivation
#print axioms coordinate_fixed
#print axioms branch_mul

#print axioms second_tangent
#print axioms fixed_lower

end ArkLib.ProximityGap.Frontier.TameBranchDerivative
