/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicSevenPrime

/-! # Projectivities between two prescribed dyadic cosets -/
namespace ProximityGap.DyadicProjectiveCosets
open DyadicParityGalois DyadicSevenDescent
variable {K : Type*} [Field K]

private theorem coordinates {n : ℕ} [NeZero n] {z : K} (hz : IsPrimitiveRoot z n)
    (x : Fin 7 → K) (nz : x 0≠0) (hx : ∀ i, (x i)^n=(x 0)^n) :
    ∃ A : Fin 7 → ℕ, ∀ i, x i=x 0*z^(A i) := by
  have rep (i : Fin 7) := hz.eq_pow_of_pow_eq_one (ξ:=x i/x 0)
    (by rw [div_pow,hx,div_self (pow_ne_zero n nz)])
  choose A _ ea using rep
  exact ⟨A,fun i => by rw [ea]; field_simp⟩

/-- Seven matches between any two prescribed nonzero multiplicative cosets
inherit rigidity from the underlying orbit, with independent nonzero normalizing constants for source and target. -/
theorem of_rigid {n : ℕ} [NeZero n] {z : K} (hz : IsPrimitiveRoot z n) (rigid : Rigid z)
    (x y : Fin 7 → K) (xi : Function.Injective x) (yi : Function.Injective y)
    (xn : x 0≠0) (yn : y 0≠0) (hx : ∀ i, (x i)^n=(x 0)^n) (hy : ∀ i, (y i)^n=(y 0)^n)
    (a b c d : K) (det : a*d≠b*c) (law : ∀ i, Graph a b c d (x i) (y i)) :
    (b=0 ∧ c=0) ∨ (a=0 ∧ d=0) := by
  obtain ⟨A,ea⟩ := coordinates hz x xn hx
  obtain ⟨B,eb⟩ := coordinates hz y yn hy
  have ix : Function.Injective (fun i => z^(A i)) := by
    intro i j h
    exact xi ((ea i).trans ((congrArg (fun t => x 0*t) h).trans (ea j).symm))
  have iy : Function.Injective (fun i => z^(B i)) := by
    intro i j h
    exact yi ((eb i).trans ((congrArg (fun t => y 0*t) h).trans (eb j).symm))
  have dg : (a*x 0)*(y 0*d)≠b*(c*x 0*y 0) := by
    intro h
    apply det
    apply mul_left_cancel₀ (mul_ne_zero xn yn)
    linear_combination h
  have eg (i : Fin 7) : Graph (a*x 0) b (c*x 0*y 0) (y 0*d) (z^(A i)) (z^(B i)) := by
    have e := law i
    dsimp only [Graph] at e ⊢
    rw [ea i,eb i] at e
    linear_combination e
  simpa [xn,yn] using rigid A B ix iy _ _ _ _ dg eg

/-- The seven-site classification for two arbitrary smooth dyadic cosets in a
prime field. The input and output lists can be any orderings of the selected sites. -/
theorem prime {p m : ℕ} [Fact p.Prime] {z : ZMod p} (hz : IsPrimitiveRoot z (2^m))
    (large : 2^(2^m)<p) (x y : Fin 7 → ZMod p) (xi : Function.Injective x)
    (yi : Function.Injective y) (xn : x 0≠0) (yn : y 0≠0)
    (hx : ∀ i, (x i)^(2^m)=(x 0)^(2^m)) (hy : ∀ i, (y i)^(2^m)=(y 0)^(2^m))
    (a b c d : ZMod p) (det : a*d≠b*c) (law : ∀ i, Graph a b c d (x i) (y i)) :
    (b=0 ∧ c=0) ∨ (a=0 ∧ d=0) :=
  of_rigid hz (DyadicSevenPrime.rigid hz large) x y xi yi xn yn hx hy a b c d det law

end ProximityGap.DyadicProjectiveCosets
#print axioms ProximityGap.DyadicProjectiveCosets.prime
