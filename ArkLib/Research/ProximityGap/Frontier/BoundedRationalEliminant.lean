/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.ResultantDegree
import ArkLib.Data.Polynomial.ResultantSpecialization
import ArkLib.Research.ProximityGap.Frontier.PositiveCharacteristicHeightDescent

/-! # An annihilator of the value of a rational expression on a plane curve

For an irreducible equation `F(X,Y)=0` and `c=A(X,Y)/B(X,Y)`, the explicit
resultant `Res_Y(F,A-WB)` is a nonzero annihilator. Its coordinate degree is
bounded directly from the input heights. Nonvanishing uses only the two scalar
specializations zero and one, so it applies over finite coefficient fields.
-/

set_option autoImplicit false
noncomputable section

open Polynomial
open scoped Differential

namespace ArkLib.ProximityGap.Frontier.BoundedRationalEliminant

variable {k : Type*} [Field k]

/-- Insert a free scalar parameter below the original coordinate indeterminate. -/
def coefficientLift : k[X] →+* k[X][X] := mapRingHom C

/-- The new parameter resides in the coefficient ring of the coordinate variable. -/
def parameter : k[X][X] := C X

/-- The numerator of the equation asserting that the rational expression equals the parameter. -/
def relation (a b : k[X][X]) : k[X][X][X] :=
  a.map coefficientLift - C parameter * b.map coefficientLift

/-- Eliminate the value coordinate. The result has inner variable `W` and outer variable `X`. -/
def eliminant (f a b : k[X][X]) : k[X][X] :=
  resultant (f.map coefficientLift) (relation a b) f.natDegree (max a.natDegree b.natDegree)

private theorem relation_natDegree_le (a b : k[X][X]) :
    (relation a b).natDegree ≤ max a.natDegree b.natDegree := by
  apply (natDegree_sub_le _ _).trans
  exact max_le_max natDegree_map_le ((natDegree_C_mul_le _ _).trans natDegree_map_le)

/-- Coordinate degree of the annihilator from the coefficient degrees of all three inputs. -/
theorem degree_eliminant (f a b : k[X][X]) (t h : ℕ)
    (hf : ∀ i, (f.coeff i).natDegree ≤ t) (ha : ∀ i, (a.coeff i).natDegree ≤ h)
    (hb : ∀ i, (b.coeff i).natDegree ≤ h) :
    (eliminant f a b).natDegree ≤ max a.natDegree b.natDegree * t + f.natDegree * h := by
  apply natDegree_resultant_le_of_coeff_natDegree_le
  · intro i
    rw [coeff_map]
    change ((f.coeff i).map (C : k →+* k[X])).natDegree ≤ t
    exact natDegree_map_le.trans (hf i)
  · intro i
    rw [relation, coeff_sub, coeff_C_mul, coeff_map, coeff_map]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact natDegree_map_le.trans (ha i)
    · exact (natDegree_C_mul_le _ _).trans (natDegree_map_le.trans (hb i))

private theorem map_eliminant {E : Type*} [Field E] (f a b : k[X][X])
    (ρ : k[X][X] →+* E) :
    ρ (eliminant f a b) = resultant (f.map (ρ.comp coefficientLift))
      (a.map (ρ.comp coefficientLift) - C (ρ parameter) * b.map (ρ.comp coefficientLift))
      f.natDegree (max a.natDegree b.natDegree) := by
  rw [eliminant, ← resultant_map_map, relation, Polynomial.map_sub, Polynomial.map_mul, map_C]
  rw [Polynomial.map_map, Polynomial.map_map, Polynomial.map_map]

/-- The resultant vanishes under every simultaneous evaluation respecting the equation
and the rational expression. -/
theorem map_eliminant_eq_zero {E : Type*} [Field E] (f a b : k[X][X])
    (hpos : f.natDegree ≠ 0) (ρ : k[X][X] →+* E) (y : E)
    (hf : (f.map (ρ.comp coefficientLift)).eval y = 0)
    (ha : (a.map (ρ.comp coefficientLift)).eval y =
      ρ parameter * (b.map (ρ.comp coefficientLift)).eval y) :
    ρ (eliminant f a b) = 0 := by
  apply map_resultant_eq_zero_of_common_root ρ _ _ natDegree_map_le
    (relation_natDegree_le a b) (Or.inl hpos) y
  · simpa only [map_map] using hf
  · simpa only [relation, Polynomial.map_sub, Polynomial.map_mul, map_C,
      map_map, eval_sub, eval_mul, eval_C, sub_eq_zero] using ha

private theorem padded_ne_zero {E : Type*} [Field E] (f g : E[X]) {s : ℕ}
    (hF : f ≠ 0) (hg : g.natDegree ≤ s) (hc : IsCoprime f g) :
    resultant f g f.natDegree s ≠ 0 := by
  have hb : resultant f g f.natDegree g.natDegree ≠ 0 :=
    fun h => (resultant_eq_zero_iff.mp h).2 hc
  rw [← Nat.add_sub_of_le hg, resultant_add_right_deg _ _ _ _ _ le_rfl, coeff_natDegree]
  exact mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hF)) hb

private abbrev spec {E : Type*} [Field E] (φ : k[X] →+* E) (w : k) : k[X][X] →+* E :=
  φ.comp (mapRingHom (evalRingHom w))

private theorem spec_lift {E : Type*} [Field E] (φ : k[X] →+* E) (w : k) :
    (spec φ w).comp coefficientLift = φ := by
  ext a <;> simp [spec, coefficientLift]

private theorem spec_parameter {E : Type*} [Field E] (φ : k[X] →+* E) (w : k) :
    spec φ w parameter = φ (C w) := by simp [parameter, spec]

/-- Irreducibility over a field containing the coordinate ring and nonvanishing of the
denominator on the generic component make the annihilator nonzero. -/
theorem eliminant_ne_zero {E : Type*} [Field E] (φ : k[X] →+* E) (hinj : Function.Injective φ)
    (f a b : k[X][X]) (hirr : Irreducible (f.map φ)) (hb : ¬f.map φ ∣ b.map φ) :
    eliminant f a b ≠ 0 := by
  intro hz
  have hspec (w : k) := map_eliminant f a b (spec φ w)
  rw [hz] at hspec
  have hfd := natDegree_map_eq_of_injective hinj (p := f)
  by_cases ha : f.map φ ∣ a.map φ
  · have hcop : IsCoprime (f.map φ) (a.map φ - b.map φ) :=
      hirr.coprime_iff_not_dvd.mpr fun hh => hb (by simpa using dvd_sub ha hh)
    have hh := hspec 1
    rw [spec_lift φ 1, spec_parameter φ 1] at hh
    rw [show C (φ (C 1))*b.map φ = b.map φ by simp, map_zero] at hh
    have hg : (a.map φ-b.map φ).natDegree ≤ max a.natDegree b.natDegree :=
      (natDegree_sub_le _ _).trans (max_le_max natDegree_map_le natDegree_map_le)
    apply padded_ne_zero _ _ hirr.ne_zero hg hcop
    simpa only [hfd] using hh.symm
  · have hh := hspec 0
    rw [spec_lift φ 0, spec_parameter φ 0] at hh
    rw [show a.map φ - C (φ (C 0))*b.map φ = a.map φ by simp, map_zero] at hh
    have hg : (a.map φ).natDegree ≤ max a.natDegree b.natDegree :=
      natDegree_map_le.trans (le_max_left _ _)
    apply padded_ne_zero _ _ hirr.ne_zero hg (hirr.coprime_iff_not_dvd.mpr ha)
    simpa only [hfd] using hh.symm

/-- Evaluation at the two coordinates in a field extension. -/
def evaluate {E : Type*} [Field E] [Algebra k E] (w x : E) : k[X][X] →+* E :=
  eval₂RingHom (aeval w).toRingHom x

private theorem evaluate_lift {E : Type*} [Field E] [Algebra k E] (w x : E) :
    (evaluate (k := k) w x).comp coefficientLift = (aeval x).toRingHom := by
  ext a <;> simp [evaluate, coefficientLift]

/-- Direct substitution at a point on the curve with the specified rational value. -/
theorem eval_eliminant_eq_zero {E : Type*} [Field E] [Algebra k E] (f a b : k[X][X])
    (hpos : f.natDegree ≠ 0) (w x y : E)
    (hf : (f.map (aeval x).toRingHom).eval y = 0)
    (hab : (a.map (aeval x).toRingHom).eval y = w*(b.map (aeval x).toRingHom).eval y) :
    (eliminant f a b).eval₂ (aeval w).toRingHom x = 0 := by
  have hw : evaluate w x (parameter (k := k)) = w := by simp [evaluate, parameter]
  apply map_eliminant_eq_zero f a b hpos (evaluate w x) y
  · rw [evaluate_lift]; exact hf
  · rw [evaluate_lift, hw]; exact hab

/-- A derivative-flat rational expression of bounded height on an irreducible
component is algebraic over the coefficient field. No perfectness assumption occurs. -/
theorem isAlgebraic_of_bounded_rational_expression {E L : Type*} [Field E] [Field L]
    [Algebra k L] [Differential L] {p : ℕ} [CharP k p]
    (hk : ∀ a : k, (algebraMap k L a)′ = 0)
    (φ : k[X] →+* E) (hinj : Function.Injective φ) (f a b : k[X][X])
    (hirr : Irreducible (f.map φ)) (hden : ¬f.map φ ∣ b.map φ) (hpos : f.natDegree ≠ 0)
    (w x y : L) (hx : x′ ≠ 0) (hw : w′ = 0)
    (hf : (f.map (aeval x).toRingHom).eval y = 0)
    (hab : (a.map (aeval x).toRingHom).eval y = w*(b.map (aeval x).toRingHom).eval y)
    (t h : ℕ) (hfdeg : ∀ i, (f.coeff i).natDegree ≤ t)
    (hadeg : ∀ i, (a.coeff i).natDegree ≤ h) (hbdeg : ∀ i, (b.coeff i).natDegree ≤ h)
    (hchar : max a.natDegree b.natDegree * t + f.natDegree * h < p) : IsAlgebraic k w :=
  PositiveCharacteristicHeightDescent.isAlgebraic_of_low_coordinate_degree hk x w hx hw
    (eliminant f a b) (eliminant_ne_zero φ hinj f a b hirr hden)
    ((degree_eliminant f a b t h hfdeg hadeg hbdeg).trans_lt hchar)
    (eval_eliminant_eq_zero f a b hpos w x y hf hab)

end ArkLib.ProximityGap.Frontier.BoundedRationalEliminant

open ArkLib.ProximityGap.Frontier.BoundedRationalEliminant in
#print axioms eliminant_ne_zero
open ArkLib.ProximityGap.Frontier.BoundedRationalEliminant in
#print axioms isAlgebraic_of_bounded_rational_expression
