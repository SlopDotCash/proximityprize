/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.Polynomial.SpecializationAvoidance
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuarticInterpolation
import ArkLib.ToMathlib.BivariateGradedDvd

/-! # The simple quadratic interpolation barrier at the quarter-rate successor

Assign three distinct received affine functions, one to each coordinate block.
After specializing the affine parameter away from their crossings, root counting
in the three blocks forces each coefficient of a bounded quadratic to vanish.
The argument also works over the scalar function field, with no scalar-degree bound.
-/

namespace ArkLib.ProximityGap.Frontier.QuarterSuccessorQuadraticObstruction

open Polynomial Finset

variable {n : ℕ} {F K : Type*} [Field F] [CommRing K] [IsDomain K]

/-- The intercept of the received row pair, equal to one on the second block. -/
def intercept (a b : ℕ) (i : Fin n) : F := if a ≤ i.val ∧ i.val < a + b then 1 else 0

/-- The slope of the received row pair, equal to one on the last block. -/
def slope (a b : ℕ) (i : Fin n) : F := if a + b ≤ i.val then 1 else 0

/-- More roots on a coordinate block than the polynomial degree force the polynomial to vanish. -/
theorem zero_on_block (D : Fin n ↪ K) (s m : ℕ) (hsm : s + m ≤ n) (P : K[X])
    (hdeg : P.natDegree < m) (hroot : ∀ i : Fin n, s ≤ i.val → i.val < s + m →
      P.eval (D i) = 0) : P = 0 := by
  classical
  let f : Fin m ↪ Fin n := ⟨fun j => ⟨s + j.val, by omega⟩, fun i j h => Fin.ext (by
    have := congrArg Fin.val h
    change s + i.val = s + j.val at this
    omega)⟩
  by_contra hn
  have h := card_le_natDegree_of_injOn_of_eval_eq_zero hn (s := univ)
    (x := f.trans D) (f.trans D).injective.injOn (fun j _ => hroot (f j)
      (by change s ≤ s + j.val; omega) (by change s + j.val < s + m; omega))
  rw [card_univ, Fintype.card_fin] at h
  omega

/-- On the displayed, fixed received row pair, the evaluation map on quadratics
with coefficient degree bounds `a,b,c` has zero kernel. The assertion holds under
every coefficient field extension and at every parameter other than zero and one. -/
theorem injective_on_three_blocks (D : Fin n ↪ F) (φ : F →+* K) (a b c : ℕ)
    (hsize : a + b + c ≤ n) (hcb : c ≤ b) (z : K) (hz : z ≠ 0) (hz' : z ≠ 1)
    (A B C : K[X]) (ha : A.natDegree < a) (hb : B.natDegree < b) (hc : C.natDegree < c)
    (hall : ∀ i : Fin n, let x := φ (D i)
      let y := φ (intercept a b i) + z * φ (slope a b i)
      A.eval x + B.eval x * y + C.eval x * y ^ 2 = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  let E := D.trans (⟨φ, φ.injective⟩ : F ↪ K)
  have hA : A = 0 := by
    apply zero_on_block E 0 a (by omega) A ha
    intro i _ hi
    simpa [intercept, slope, show ¬a ≤ i.val by omega, show ¬a + b ≤ i.val by omega, E]
      using hall i
  subst A
  have hBC : B + C = 0 := by
    apply zero_on_block E a b (by omega) (B + C)
      (lt_of_le_of_lt (natDegree_add_le ..) (max_lt hb (hc.trans_le hcb)))
    intro i hi hj
    simpa [intercept, slope, hi, hj, show ¬a + b ≤ i.val by omega, E] using hall i
  have hC : C = 0 := by
    apply zero_on_block E (a + b) c hsize C hc
    intro i hi _
    have hr := hall i
    simp only [intercept, slope, show ¬i.val < a + b by omega, and_false, ite_false,
      ite_eq_left hi, map_zero, map_one, mul_one, zero_add, eval_zero] at hr
    have hs := congrArg (fun Q : K[X] => Q.eval (φ (D i))) hBC
    rw [eval_add, eval_zero] at hs
    have h : C.eval (φ (D i)) * z * (z - 1) = 0 := by linear_combination hr - z * hs
    have hzC := (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hz')
    exact (mul_eq_zero.mp hzC).resolve_right hz
  exact ⟨rfl, by simpa only [hC, add_zero] using hBC, hC⟩

/-- At 447392428 errors and dimension 268435456 no nonzero quadratic of coordinate
and ordinate weight below the agreement count fits these received affine lines.
The three blocks use 1073741823 of the 1073741824 available positions. -/
theorem quarter_successor (D : Fin 1073741824 ↪ F) (φ : F →+* K) (z : K)
    (hz : z ≠ 0) (hz' : z ≠ 1) (A B C : K[X]) (ha : A.natDegree < 626349396)
    (hb : B.natDegree + 268435455 < 626349396)
    (hc : C.natDegree + 2 * 268435455 < 626349396)
    (hall : ∀ i : Fin 1073741824, let x := φ (D i)
      let y := φ (intercept 626349396 357913941 i) + z * φ (slope 626349396 357913941 i)
      A.eval x + B.eval x * y + C.eval x * y ^ 2 = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 :=
  injective_on_three_blocks D φ 626349396 357913941 89478486 (by decide) (by decide)
    z hz hz' A B C ha (by omega) (by omega) hall

open SecondPrimeQuarticInterpolation

private theorem eval_swap (p : F[X][X]) (x : F) :
    (Bivariate.swap p).eval (C x) = p.map (evalRingHom x) := by
  simpa only [Bivariate.evalY, Bivariate.evalX_eq_map, Bivariate.swap_swap_apply] using
    Bivariate.evalY_eq_evalX_swap x (Bivariate.swap p)

/-- A test on the three coordinate-polynomial coefficients suffices to rule out every
simple quadratic interpolant, with no restriction on its scalar degree. -/
theorem kernel_of_coordinate_test {s : ℕ} (D : Fin 1073741824 ↪ F)
    (u₀ u₁ : Fin 1073741824 → F)
    (htest : ∀ A B C' : F[X][X], A.natDegree < 626349396 →
      B.natDegree + 268435455 < 626349396 → C'.natDegree + 2 * 268435455 < 626349396 →
      (∀ i, let x := C (D i)
        let y := C (u₀ i) + X * C (u₁ i)
        A.eval x + B.eval x * y + C'.eval x * y ^ 2 = 0) → A = 0 ∧ B = 0 ∧ C' = 0)
    (c : Monomials s 2 268435455 626349396 → F)
    (hall : ∀ i, receivedLine c (D i) (u₀ i) (u₁ i) = 0) : c = 0 := by
  by_contra hc
  let Q := surface c
  let v (j : ℕ) := Bivariate.swap (Q.coeff j)
  have hQ : Q ≠ 0 := surface_ne_zero hc
  have top := leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hQ))
  have hd : Q.natDegree ≤ 2 := (surface_support c top).1
  have hdeg (j : ℕ) (hj : j ≤ 2) : (v j).natDegree + j * 268435455 < 626349396 := by
    by_cases he : Q.coeff j = 0
    · simp only [v, he, map_zero, natDegree_zero, zero_add]
      omega
    obtain ⟨i, hi, ht, _⟩ := Bivariate.exists_max_index_degreeX (Q.coeff j) he
    have h := (surface_support c (leadingCoeff_ne_zero.mpr (mem_support_iff.mp hi))).2.2
    change ((Q.coeff j).coeff i).natDegree + j * 268435455 < 626349396 at h
    change (Bivariate.swap (Q.coeff j)).natDegree + j * 268435455 < 626349396
    rw [show (Bivariate.swap (Q.coeff j)).natDegree = Bivariate.degreeX (Q.coeff j) from
      Bivariate.natDegreeY_swap _, ← ht]
    exact h
  have hits (i : Fin 1073741824) := hall i
  have hfit (i : Fin 1073741824) :
      let x := C (D i)
      let y := C (u₀ i) + X * C (u₁ i)
      (v 0).eval x + (v 1).eval x * y + (v 2).eval x * y ^ 2 = 0 := by
    have h := hits i
    rw [← surface_received_line] at h
    rw [eval₂_eq_sum_range' _ (show Q.natDegree < 3 by omega)] at h
    simpa only [v, eval_swap, coe_mapRingHom, sum_range_succ, sum_range_zero, zero_add,
      pow_zero, mul_one, pow_one] using h
  obtain ⟨h₀, h₁, h₂⟩ := htest (v 0) (v 1) (v 2) (by simpa using hdeg 0 (by decide))
    (by simpa using hdeg 1 (by decide)) (hdeg 2 (by decide)) hfit
  apply hQ
  ext1 j
  rw [coeff_zero]
  by_cases hj : j ≤ 2
  · apply Bivariate.swap.injective
    rw [map_zero]
    interval_cases j <;> assumption
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- The actual simple interpolation operator in `QuarterRateRichSecants.shared_equations`
has trivial kernel at the successor on these received rows. This holds for every scalar
degree cap `s` and every supplied domain of the production length. -/
theorem simple_kernel {s : ℕ} (D : Fin 1073741824 ↪ F)
    (c : Monomials s 2 268435455 626349396 → F)
    (hall : ∀ i, receivedLine c (D i) (intercept 626349396 357913941 i)
      (slope 626349396 357913941 i) = 0) : c = 0 := by
  apply kernel_of_coordinate_test D _ _ _ c hall
  exact quarter_successor D (C : F →+* F[X]) X X_ne_zero
    (by simpa [sub_ne_zero] using (X_sub_C_ne_zero (1 : F)))

end ArkLib.ProximityGap.Frontier.QuarterSuccessorQuadraticObstruction
