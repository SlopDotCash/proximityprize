/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-! # The Fano obstruction for agreement masks in odd characteristic

The coordinate identity rules out the Fano collinearities for seven distinct
points spanning a plane. The root count bounds residual differences obtained
from the polynomial line relations for seven Reed–Solomon words. -/

namespace ProximityGap.FanoMaskRigidity
variable {K : Type*} [Field K]

/-- In odd characteristic the three side points on a projective triangle whose
opposite lines concur with nonzero coordinates cannot themselves be collinear.
The displayed equations are homogeneous coordinates for the seven Fano lines. -/
theorem triangle_obstruction (h2 : (2 : K) ≠ 0)
    (a b c d e f x y z : K) (hb : b ≠ 0) (hc : c ≠ 0) (hf : f ≠ 0) (hx : x ≠ 0)
    (hxy : a*y = b*x) (hxz : c*z = d*x) (hyz : e*z = f*y)
    (hline : a*d*e + b*c*f = 0) : False := by
  have heq : (a*d*e - b*c*f)*x = 0 := by
    linear_combination c*f*hxy - a*e*hxz + a*c*hyz
  have hzero := (mul_eq_zero.mp heq).resolve_right hx
  have : (2 : K) * b * c * f = 0 := by linear_combination hline - hzero
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hb) hc) hf) this

open Polynomial Finset

/-- Whenever a base polynomial times a short numerator equals the product of
a denominator with a difference vanishing on a prescribed finite set, only
the roots of the numerator can be missing base roots there. -/
theorem roots_after_clearing [DecidableEq K] (S : Finset K) (P A B R : K[X])
    (hA : A ≠ 0) (hid : B * R = A * P) (hz : ∀ x ∈ S, R.eval x = 0) :
    S.card ≤ (S.filter (fun x => P.eval x = 0)).card + A.natDegree := by
  have hn : (S.filter (fun x => ¬ P.eval x = 0)).card ≤ A.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hs, hp⟩
    apply (Polynomial.mem_roots hA).mpr
    have he := congrArg (Polynomial.eval x) hid
    rw [eval_mul, eval_mul, hz x hs, mul_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_right hp
  have hc := S.card_filter_add_card_filter_not (fun x => P.eval x = 0)
  omega

/-- Seven disjoint nonzero classes supply more roots than the residual degree
after at most h deletions from each of the seven binary hyperplane masks. -/
theorem seven_class_surplus (b h : ℕ) (hh : 1 ≤ h) (hlarge : 63*h < b+6) :
    b+7*h-1 < 7*(b-3*h-5*(10*h-1)) := by omega

end ProximityGap.FanoMaskRigidity
#print axioms ProximityGap.FanoMaskRigidity.triangle_obstruction

#print axioms ProximityGap.FanoMaskRigidity.roots_after_clearing
#print axioms ProximityGap.FanoMaskRigidity.seven_class_surplus
