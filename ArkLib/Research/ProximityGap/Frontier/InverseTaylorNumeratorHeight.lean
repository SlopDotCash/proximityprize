/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ImplicitDerivativeBidegree
import ArkLib.Research.ProximityGap.Frontier.InverseTaylorFlat
import ArkLib.Research.ProximityGap.Frontier.BoundedRationalEliminant

/-! # Clearing the implicit denominators of the inverse Taylor polynomial

For an equation of value degree three and coordinate degree `t`, a single power
of the value derivative clears all coefficients of the inverse Taylor polynomial.
The resulting value degrees are bounded by `4*d+1` and the coordinate degrees
by `2*d*t+d`.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Polynomial.Bivariate Finset
open scoped Differential BigOperators

namespace ArkLib.ProximityGap.Frontier.InverseTaylorNumeratorHeight

open ImplicitDerivativeNumerator ImplicitDerivativeBidegree InverseTaylorFlat BoundedRationalEliminant

variable {k : Type} [Field k] [Differential k[X]]

/-- Power of the value derivative common to every Taylor coefficient. -/
def denominator (f : k[X][X]) (d : ℕ) : k[X][X] := f.derivative^(2*d)

/-- Polynomial obtained by multiplying the order-`i` implicit derivative by the
common denominator. -/
def piece (f : k[X][X]) (d : ℕ) : ℕ → k[X][X]
  | 0 => Polynomial.X * denominator f d
  | i+1 => numerator f i * f.derivative^(2*d-(2*i+1))

/-- Antidiagonal coefficient of a centered power, including its inverse factorial. -/
def multiplier (i j : ℕ) : k[X] := C ((i.choose j : k)/(i.factorial : k)) * (-Polynomial.X)^(i-j)

/-- Cleared numerator representing the coefficient at exponent `j`. -/
def cleared (f : k[X][X]) (d j : ℕ) : k[X][X] :=
  ∑ i ∈ range (d+1), C (multiplier (k := k) i j) * piece f d i

section Evaluation
variable {L : Type*} [Field L] [Differential L] [Algebra k[X] L] [DifferentialAlgebra k[X] L]

private theorem piece_aeval (f : k[X][X]) (d i : ℕ) (y : L) (hf : aeval y f = 0) (hi : i ≤ d) :
    aeval y (piece f d i) = (Differential.deriv^[i]) y * aeval y (denominator f d) := by
  cases i with
  | zero => simp [piece]
  | succ i =>
      rw [piece, denominator, map_mul, map_pow, map_pow, numerator_aeval f y hf i]
      let z := aeval y f.derivative
      change z^(2*i+1) * _ * z^(2*d-(2*i+1)) = _ * z^(2*d)
      rw [mul_comm (z^(2*i+1)), mul_assoc, ← pow_add]
      congr 2
      omega

omit [Differential k[X]] [Differential L] [DifferentialAlgebra k[X] L] in
private theorem multiplier_image (i j : ℕ) (x : L) (hx : algebraMap k[X] L Polynomial.X = x) :
    algebraMap k[X] L (multiplier (k := k) i j) =
      ((i.choose j : L)/(i.factorial : L)) * (-x)^(i-j) := by
  let φ : k →+* L := (algebraMap k[X] L).comp C
  have hφ : φ ((i.choose j : k)/(i.factorial : k)) = (i.choose j : L)/(i.factorial : L) := by
    rw [map_div₀, map_natCast, map_natCast]
  rw [multiplier, map_mul, map_pow, map_neg, hx]
  exact congrArg (fun z : L => z*(-x)^(i-j)) hφ

/-- Evaluating the polynomial numerator gives the actual Taylor coefficient times the
common denominator, even at a singular root. -/
theorem cleared_aeval (f : k[X][X]) (d j : ℕ) (x y : L)
    (hx : algebraMap k[X] L Polynomial.X = x) (hf : aeval y f = 0) :
    aeval y (cleared f d j) = (expansion x y d).coeff j * aeval y (denominator f d) := by
  rw [cleared, map_sum, coeff_expansion, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul, aeval_C, multiplier_image i j x hx, piece_aeval f d i y hf (by simpa using hi),
    dividedDerivative]
  ring

end Evaluation

private abbrev height (f : k[X][X]) : ℕ := (swap f).natDegree

omit [Differential k[X]] in
private theorem height_eq (f : k[X][X]) : height f = degreeX f := natDegreeY_swap f

private theorem height_mapCoeffs (hD : ∀ q : k[X], q′.natDegree ≤ q.natDegree) (f : k[X][X]) :
    height (Differential.mapCoeffs f) ≤ height f := by
  rw [height_eq, height_eq]
  refine Finset.sup_le fun i _ => ?_
  exact (hD (f.coeff i)).trans (coeff_natDegree_le_degreeX f i)

omit [Differential k[X]] in
private theorem height_derivative (f : k[X][X]) : height f.derivative ≤ height f := by
  rw [height_eq, height_eq]
  exact degreeX_derivative_le f

omit [Differential k[X]] in
private theorem height_mul (f g : k[X][X]) :
    height (f*g) ≤ height f + height g := by
  change (swap (f*g)).natDegree ≤ _
  rw [map_mul]
  exact natDegree_mul_le

omit [Differential k[X]] in
private theorem height_pow (f : k[X][X]) (i : ℕ) : height (f^i) ≤ i*height f := by
  change (swap (f^i)).natDegree ≤ _
  rw [map_pow]
  exact natDegree_pow_le

omit [Differential k[X]] in
private theorem height_sub (f g : k[X][X]) :
    height (f-g) ≤ max (height f) (height g) := by
  change (swap (f-g)).natDegree ≤ _
  rw [map_sub]
  exact natDegree_sub_le _ _

private theorem height_along (hD : ∀ q : k[X], q′.natDegree ≤ q.natDegree) (f g : k[X][X]) :
    height (along f g) ≤ height f + height g := by
  apply (height_sub _ _).trans
  apply max_le
  · exact (height_mul _ _).trans (Nat.add_le_add (height_derivative f) (height_mapCoeffs hD g))
  · exact (height_mul _ _).trans (Nat.add_le_add (height_mapCoeffs hD f) (height_derivative g))

private theorem height_numerator (hD : ∀ q : k[X], q′.natDegree ≤ q.natDegree)
    (f : k[X][X]) (i : ℕ) : height (numerator f i) ≤ (2*i+1)*height f := by
  induction i with
  | zero =>
      change (swap (-Differential.mapCoeffs f)).natDegree ≤ _
      simpa using height_mapCoeffs hD f
  | succ i ih =>
      rw [numerator]
      apply (height_sub _ _).trans
      apply max_le
      · apply (height_mul _ _).trans
        have h := height_along hD f (numerator f i)
        have h' := height_derivative f
        rw [show 2*(i+1)+1 = (2*i+1)+2 by omega, Nat.add_mul]
        omega
      · apply (height_mul _ _).trans
        have h1 := height_along hD f f.derivative
        have h2 := height_derivative f
        have h3 : height ((↑(2*i+1) : k[X][X]) * numerator f i) ≤ height (numerator f i) := by
          change (swap _).natDegree ≤ _
          rw [map_mul, map_natCast, ← map_natCast (C : k[X] →+* k[X][X])]
          apply natDegree_C_mul_le
        rw [show 2*(i+1)+1 = (2*i+1)+2 by omega, Nat.add_mul]
        omega

private theorem value_numerator (hD : ∀ q : k[X], q′.natDegree ≤ q.natDegree)
    (f : k[X][X]) (hf : f.natDegree ≤ 3) (i : ℕ) : (numerator f i).natDegree ≤ 3+4*i := by
  change natDegreeY f ≤ 3 at hf
  rw [degreeY_as_weighted_deg] at hf
  change natDegreeY (numerator f i) ≤ _
  rw [degreeY_as_weighted_deg]
  convert numerator_weight_le hD f (by decide : 2 ≤ 3) hf i using 1
  omega

private theorem piece_value (hD : ∀ q : k[X], q′.natDegree ≤ q.natDegree)
    (f : k[X][X]) (hf : f.natDegree ≤ 3) (d i : ℕ) (hi : i ≤ d) :
    (piece f d i).natDegree ≤ 4*d+1 := by
  have hJ : f.derivative.natDegree ≤ 2 := by have := natDegree_derivative_le f; omega
  cases i with
  | zero =>
      apply natDegree_mul_le.trans
      have hpow := natDegree_pow_le_of_le (2*d) hJ
      change (Polynomial.X : k[X][X]).natDegree + (f.derivative^(2*d)).natDegree ≤ _
      rw [natDegree_X]
      omega
  | succ i =>
      apply natDegree_mul_le.trans
      have hpow := natDegree_pow_le_of_le (2*d-(2*i+1)) hJ
      have hnum := value_numerator hD f hf i
      change (numerator f i).natDegree + (f.derivative^(2*d-(2*i+1))).natDegree ≤ _
      omega

private theorem piece_height (hD : ∀ q : k[X], q′.natDegree ≤ q.natDegree)
    (f : k[X][X]) (d i : ℕ) (hi : i ≤ d) : height (piece f d i) ≤ 2*d*height f := by
  have hJ := height_derivative f
  cases i with
  | zero =>
      apply (height_mul _ _).trans
      have hz : height (Polynomial.X : k[X][X]) = 0 := by simp [height, swap_Y]
      have hh := (height_pow f.derivative (2*d)).trans (Nat.mul_le_mul_left _ hJ)
      change height (Polynomial.X : k[X][X]) + height (f.derivative^(2*d)) ≤ _
      omega
  | succ i =>
      apply (height_mul _ _).trans
      have hh := (height_pow f.derivative (2*d-(2*i+1))).trans (Nat.mul_le_mul_left _ hJ)
      have hn := height_numerator hD f i
      have he : (2*i+1) + (2*d-(2*i+1)) = 2*d := by omega
      exact (Nat.add_le_add hn hh).trans_eq ((Nat.add_mul _ _ _).symm.trans (congrArg (·*height f) he))

omit [Differential k[X]] in
private theorem multiplier_degree (i j : ℕ) :
    (multiplier (k := k) i j).natDegree ≤ i-j := by
  apply (natDegree_C_mul_le _ _).trans
  simp

/-- The exact support rectangle of the common numerator and denominator is bounded
uniformly in the coefficient index. -/
theorem cleared_degrees (hD : ∀ q : k[X], q′.natDegree ≤ q.natDegree)
    (f : k[X][X]) (hf : f.natDegree ≤ 3) (t d j : ℕ) (ht : degreeX f ≤ t) :
    (cleared f d j).natDegree ≤ 4*d+1 ∧ (denominator f d).natDegree ≤ 4*d ∧
    degreeX (cleared f d j) ≤ 2*d*t+d ∧ degreeX (denominator f d) ≤ 2*d*t := by
  have ht' : height f ≤ t := (height_eq f).le.trans ht
  have hJ : f.derivative.natDegree ≤ 2 := by have := natDegree_derivative_le f; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply natDegree_sum_le_of_forall_le
    intro i hi
    exact (natDegree_C_mul_le _ _).trans (piece_value hD f hf d i (by simpa using hi))
  · exact (natDegree_pow_le_of_le (2*d) hJ).trans (by omega)
  · rw [← height_eq]
    change (swap (∑ i ∈ range (d+1), _)).natDegree ≤ _
    rw [map_sum]
    apply natDegree_sum_le_of_forall_le
    intro i hi
    have hin : i ≤ d := by simpa using hi
    apply (height_mul _ _).trans
    have hmul : height (C (multiplier (k := k) i j)) ≤ i-j := by
      change (swap _).natDegree ≤ _
      rw [swap_C]
      exact natDegree_map_le.trans (multiplier_degree i j)
    have hpiece := (piece_height hD f d i hin).trans (Nat.mul_le_mul_left _ ht')
    omega
  · rw [← height_eq]
    exact (height_pow f.derivative (2*d)).trans (Nat.mul_le_mul_left _ ((height_derivative f).trans ht'))

omit [Differential k[X]] in
private theorem denominator_not_dvd {E : Type*} [Field E] (φ : k[X] →+* E)
    (hinj : Function.Injective φ) (f : k[X][X]) (hirr : Irreducible (f.map φ))
    (hJ : f.derivative ≠ 0) (d : ℕ) : ¬f.map φ ∣ (denominator f d).map φ := by
  rw [denominator, Polynomial.map_pow]
  intro hd
  have hh := hirr.prime.dvd_of_dvd_pow hd
  have hg : (f.derivative.map φ) ≠ 0 := by
    intro h0
    apply hJ
    apply Polynomial.map_injective φ hinj
    simpa using h0
  rw [← derivative_map] at hh hg
  exact hg (dvd_derivative_iff.mp hh)

omit [Differential k[X]] in
/-- Every coefficient in the actual inverse Taylor expansion is algebraic over the
constant coefficient field. The equation is irreducible over a field containing the
coordinate polynomial ring, has value degree at most three and coordinate degree
at most `t`, and the explicit characteristic budget is `10*d*t+t+3*d < p`. -/
theorem expansion_coeff_isAlgebraic {E L : Type*} [Field E] [Field L] [Algebra k L]
    [Differential L] {p : ℕ} [CharP k p] (hp : p.Prime)
    (hk : ∀ a : k, (algebraMap k L a)′ = 0) (φ : k[X] →+* E) (hinj : Function.Injective φ)
    (f : k[X][X]) (hirr : Irreducible (f.map φ)) (hpos : f.natDegree ≠ 0)
    (hf : f.natDegree ≤ 3) (hcharY : f.natDegree < p) (t d : ℕ) (ht : degreeX f ≤ t)
    (hd : d < p) (hchar : 10*d*t+t+3*d < p) (x y : L) (hx : x′ = 1)
    (hFxy : (f.map (aeval x).toRingHom).eval y = 0) (hy : (Differential.deriv^[d+1]) y = 0)
    (j : ℕ) : IsAlgebraic k ((expansion x y d).coeff j) := by
  let _ : Differential k := ⟨0⟩
  let _ : DifferentialAlgebra k L := ⟨fun a => by
    rw [hk]; exact (map_zero (algebraMap k L)).symm⟩
  let _ : Differential k[X] := ⟨(Polynomial.derivative' (R := k)).restrictScalars ℤ⟩
  let _ : Algebra k[X] L := (aeval x).toRingHom.toAlgebra
  let _ : DifferentialAlgebra k[X] L := ⟨fun q => by
    change (aeval x q)′ = aeval x q.derivative
    have hm : Differential.mapCoeffs q = 0 := by ext i; rfl
    rw [Differential.deriv_aeval_eq, hm, map_zero, hx, mul_one, zero_add]⟩
  let _ : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
  have hD (q : k[X]) : q′.natDegree ≤ q.natDegree :=
    (natDegree_derivative_le q).trans (Nat.sub_le _ _)
  have he (q : k[X][X]) : aeval y q = (q.map (aeval x).toRingHom).eval y := by
    rw [aeval_def, eval_map]
    rfl
  have hroot : aeval y f = 0 := (he f).trans hFxy
  have hxmap : algebraMap k[X] L Polynomial.X = x := aeval_X x
  have hJ : f.derivative ≠ 0 := fun h0 => hpos
    (PositiveCharacteristicHeightDescent.natDegree_eq_zero_of_derivative_eq_zero f hcharY h0)
  obtain ⟨hA,hB,hAx,hBx⟩ := cleared_degrees hD f hf t d j ht
  apply isAlgebraic_of_bounded_rational_expression hk φ hinj f (cleared f d j) (denominator f d)
    hirr (denominator_not_dvd φ hinj f hirr hJ d) hpos _ x y (by rw [hx]; exact one_ne_zero)
    ((expansion_spec hp x y hx d hd hy).2.2 j) hFxy _ t (2*d*t+d)
    (fun i => (coeff_natDegree_le_degreeX f i).trans ht)
    (fun i => (coeff_natDegree_le_degreeX _ i).trans hAx)
    (fun i => (coeff_natDegree_le_degreeX _ i).trans (by omega))
  · calc
      _ ≤ (4*d+1)*t+3*(2*d*t+d) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ (max_le hA (by omega))) (Nat.mul_le_mul_right _ hf)
      _ = 10*d*t+t+3*d := by ring
      _ < p := hchar
  · rw [← he, ← he]
    exact cleared_aeval f d j x y hxmap hroot

end ArkLib.ProximityGap.Frontier.InverseTaylorNumeratorHeight

open ArkLib.ProximityGap.Frontier.InverseTaylorNumeratorHeight in
#print axioms cleared_aeval
open ArkLib.ProximityGap.Frontier.InverseTaylorNumeratorHeight in
#print axioms expansion_coeff_isAlgebraic
