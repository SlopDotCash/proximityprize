/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.GenericDifferentialFunctionField
import ArkLib.Research.ProximityGap.Frontier.InverseTaylorNumeratorHeight

/-! # The vanishing derivative branch of a moving cubic

The coefficient field `k` contains the scalar parameter (in the application
`k = 𝔽_p(Γ)`). The indeterminate of `RatFunc k` is the coordinate `X`. For an
irreducible equation of value degree at most three, divisibility by its order-`d+1`
implicit derivative numerator implies that its generic root is a polynomial in
`X` of degree at most `d`, with coefficients algebraic over `k`.
-/

set_option autoImplicit false
noncomputable section

open Polynomial
open scoped Differential

namespace ArkLib.ProximityGap.Frontier.MovingCubicVanishingBranch

open GenericDifferentialFunctionField InverseTaylorNumeratorHeight ImplicitDerivativeNumerator

variable {k : Type} [Field k]

/-- Ordinary coordinate differentiation on `k[X]` fixes all of `k`, including
any scalar parameter already in the coefficient field. -/
@[instance_reducible] def coordinateDifferential : Differential k[X] :=
  ⟨(Polynomial.derivative' (R := k)).restrictScalars ℤ⟩

/-- The implicit numerator for coordinate differentiation. -/
def coordinateNumerator (f : k[X][X]) (d : ℕ) : k[X][X] :=
  letI := coordinateDifferential (k := k)
  numerator f d

/-- Scalar extension to the coordinate rational-function field. -/
abbrev genericEquation (f : k[X][X]) : (RatFunc k)[X] :=
  f.map (algebraMap k[X] (RatFunc k))

set_option backward.isDefEq.respectTransparency false in
/-- Pure field statement of the vanishing branch. The function field, compatible
derivations, algebraic coefficients, and polynomial representation are all constructed. -/
theorem polynomial_generic_root {p : ℕ} [CharP k p] (hp : p.Prime) (f : k[X][X])
    (hirr : Irreducible (genericEquation f)) (hpos : f.natDegree ≠ 0)
    (hf : f.natDegree ≤ 3) (hcharY : f.natDegree < p) (t d : ℕ)
    (ht : Polynomial.Bivariate.degreeX f ≤ t) (hd : d < p)
    (hchar : 10*d*t+t+3*d < p)
    (hdiv : genericEquation f ∣ genericEquation (coordinateNumerator f d)) :
    ∃ q : (AdjoinRoot (genericEquation f))[X], q.natDegree ≤ d ∧
      q.eval (AdjoinRoot.of (genericEquation f) RatFunc.X) = AdjoinRoot.root (genericEquation f) ∧
      ∀ j, IsAlgebraic k (q.coeff j) := by
  let g := genericEquation f
  let L := AdjoinRoot g
  let _ : Fact (Irreducible g) := ⟨hirr⟩
  let _ : Differential k[X] := coordinateDifferential
  let _ : Differential (RatFunc k) := fractionDifferential k[X] (RatFunc k)
  have hJf : f.derivative ≠ 0 := fun h => hpos
    (PositiveCharacteristicHeightDescent.natDegree_eq_zero_of_derivative_eq_zero f hcharY h)
  have hJ : g.derivative ≠ 0 := by
    change (f.map _).derivative ≠ 0
    rw [derivative_map]
    intro hh
    apply hJf
    apply Polynomial.map_injective _ (RatFunc.algebraMap_injective k)
    simpa using hh
  let _ : Differential L := adjointDifferential g hJ
  let _ : DifferentialAlgebra k[X] L := ⟨fun r => by
    change (algebraMap (RatFunc k) L (algebraMap k[X] (RatFunc k) r))′ =
      algebraMap (RatFunc k) L (algebraMap k[X] (RatFunc k) r′)
    rw [adjoint_deriv_algebraMap g hJ, fraction_deriv_algebraMap k[X] (RatFunc k)]⟩
  let x : L := AdjoinRoot.of g RatFunc.X
  let y : L := AdjoinRoot.root g
  have hX : algebraMap k[X] L Polynomial.X = x := rfl
  have hx : x′ = 1 := by
    rw [← hX, deriv_algebraMap]
    change algebraMap k[X] L (Polynomial.X : k[X]).derivative = 1
    simp
  have hk (a : k) : (algebraMap k L a)′ = 0 := by
    change (algebraMap k[X] L (C a))′ = 0
    rw [deriv_algebraMap]
    change algebraMap k[X] L (C a).derivative = 0
    simp
  have hroot : aeval y g = 0 := AdjoinRoot.eval₂_root g
  have he (P : k[X][X]) : aeval y (genericEquation P) = aeval y P := by
    rw [aeval_def, aeval_def, genericEquation, eval₂_map]
    rfl
  have hfroot : aeval y f = 0 := (he f).symm.trans hroot
  have hN : aeval y (numerator f d) = 0 := by
    rw [← he]
    obtain ⟨b,hb⟩ := hdiv
    change aeval y (genericEquation (coordinateNumerator f d)) = 0
    rw [hb, map_mul, hroot, zero_mul]
  have hjroot : aeval y f.derivative ≠ 0 := by
    rw [← he]
    change aeval y (f.derivative.map _) ≠ 0
    rw [← derivative_map]
    change aeval (AdjoinRoot.root g) g.derivative ≠ 0
    rw [AdjoinRoot.aeval_eq]
    exact fun hh => hJ (dvd_derivative_iff.mp (AdjoinRoot.mk_eq_zero.mp hh))
  have hy : (Differential.deriv^[d+1]) y = 0 :=
    (mul_eq_zero.mp ((numerator_aeval f y hfroot d).symm.trans hN)).resolve_left
      (pow_ne_zero _ hjroot)
  have heval : (aeval x).toRingHom = algebraMap k[X] L := by
    ext a
    · change (aeval x) (C a) = algebraMap k L a
      exact aeval_C x a
    · exact (aeval_X x).trans hX.symm
  have hxy : (f.map (aeval x).toRingHom).eval y = 0 := by
    rw [heval, eval_map_algebraMap]
    exact hfroot
  let _ : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
  obtain ⟨hdeg, hv, _⟩ := InverseTaylorFlat.expansion_spec hp x y hx d hd hy
  exact ⟨InverseTaylorFlat.expansion x y d, hdeg, hv, fun j =>
    expansion_coeff_isAlgebraic hp hk (algebraMap k[X] (RatFunc k)) (RatFunc.algebraMap_injective k)
      f hirr hpos hf hcharY t d ht hd hchar x y hx hxy hy j⟩

end ArkLib.ProximityGap.Frontier.MovingCubicVanishingBranch

open ArkLib.ProximityGap.Frontier.MovingCubicVanishingBranch in
#print axioms polynomial_generic_root
