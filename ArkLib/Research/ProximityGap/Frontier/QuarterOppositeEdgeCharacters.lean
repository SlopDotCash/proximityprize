/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Opposite edge locators for a saturated four-head configuration

The monic locators of six disjoint edge classes are paired as `(a,a'), (b,b'), (c,c')`.
The four signed face determinants give a single relation between their products.
Its evaluation and its factorization constrain the partition before any splines are built.
-/

namespace ProximityGap.QuarterOppositeEdgeCharacters

/-- After a square-root extension, the signed face equation factors in Cayley coordinates. -/
theorem cayley_factorization {R : Type*} [CommRing R] {a a' b b' c c' z u v w t : R}
    (h : t*a*b*c + u*a*b'*c' + v*a'*b*c' + w*a'*b'*c = 0)
    (hz : z^2*u*v*w = t) :
    (a' + z*u*a)*(b' + z*v*b)*(c' + z*w*c) =
      (a' - z*u*a)*(b' - z*v*b)*(c' - z*w*c) := by
  linear_combination (2*z)*h + (2*z*a*b*c)*hz

/-- Product one for the three rational functions, with their nonzero denominators explicit. -/
theorem torus_product {F : Type*} [Field F] {a a' b b' c c' z u v w t : F}
    (h : t*a*b*c + u*a*b'*c' + v*a'*b*c' + w*a'*b'*c = 0)
    (hz : z^2*u*v*w = t)
    (ha : a' - z*u*a ≠ 0) (hb : b' - z*v*b ≠ 0) (hc : c' - z*w*c ≠ 0) :
    ((a' + z*u*a)/(a' - z*u*a))*((b' + z*v*b)/(b' - z*v*b))*
      ((c' + z*w*c)/(c' - z*w*c)) = 1 := by
  rw [div_mul_div_comm, div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (mul_ne_zero ha hb) hc)]
  exact cayley_factorization h hz

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem char_of_square_factor {x y t : F} (ht : t ≠ 0) (h : x = y*t^2) :
    quadraticChar F x = quadraticChar F y := by
  rw [h, map_mul, quadraticChar_sq_one' ht, mul_one]

/-- On the first side of a pair, the other two opposite edge products have fixed character. -/
theorem first_side {a' b b' c c' v w : F}
    (h : v*a'*b*c' + w*a'*b'*c = 0) (ha : a' ≠ 0) (hv : v ≠ 0)
    (hb : b' ≠ 0) (hc : c ≠ 0) :
    quadraticChar F (b*b'*c*c') = quadraticChar F (-w/v) := by
  apply char_of_square_factor (mul_ne_zero hb hc)
  field_simp
  apply mul_left_cancel₀ ha
  linear_combination h

/-- On its opposite side the sign is controlled by the other two coefficients. -/
theorem opposite_side {a b b' c c' t u : F}
    (h : t*a*b*c + u*a*b'*c' = 0) (ha : a ≠ 0) (ht : t ≠ 0)
    (hb : b' ≠ 0) (hc : c' ≠ 0) :
    quadraticChar F (b*b'*c*c') = quadraticChar F (-u/t) := by
  apply char_of_square_factor (mul_ne_zero hb hc)
  field_simp
  apply mul_left_cancel₀ ha
  linear_combination h

/-- The product of the two signs is the same discriminant character for every opposite pair. -/
theorem common_sign_product {t u v w : F} (ht : t ≠ 0) (hv : v ≠ 0) :
    quadraticChar F (-w/v) * quadraticChar F (-u/t) = quadraticChar F (t*u*v*w) := by
  rw [← map_mul]
  apply char_of_square_factor (inv_ne_zero (mul_ne_zero ht hv))
  field_simp

open Polynomial

/-- The other two block locators at a root can be recovered from the holes and the
derivative of its own locator. The finite field characteristic may be arbitrary. -/
theorem derivative_at_site {K : Type*} [Field K] {a b c holes : K[X]} {x : K} {m : ℕ}
    (hprod : a*b*c*holes = X^(m+1) - 1) (ha : a.eval x = 0) (hx : x^(m+1) = 1) :
    x * a.derivative.eval x * b.eval x * c.eval x * holes.eval x = (m+1 : ℕ) := by
  have he := congrArg (fun f : K[X] => f.derivative.eval x) hprod
  simp [derivative_mul, ha] at he
  calc
    _ = x * (a.derivative.eval x * b.eval x * c.eval x * holes.eval x) := by ring
    _ = _ := by rw [he, Nat.cast_succ]; linear_combination ((m : K)+1)*hx

#print axioms cayley_factorization
#print axioms torus_product
#print axioms first_side
#print axioms opposite_side
#print axioms common_sign_product
#print axioms derivative_at_site

end ProximityGap.QuarterOppositeEdgeCharacters
