/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Equiv
import Mathlib.Tactic

/-! # Conjugating marked evaluations of monic root products

A field automorphism stabilizing two supports fixes their ratio at a fixed
marked point. Consequently its entire orbit of every other marked point
has the same ratio. For dyadic roots this gives the third odd centre in
the five-consecutive-site theorem.
-/

namespace ProximityGap.LocatorConjugateCentres

variable {K : Type*} [Field K] [DecidableEq K]

private def loc (S : Finset K) (x : K) := ∏ a ∈ S, (x-a)

private theorem loc_map (σ : K ≃+* K) (S : Finset K) (x : K) :
    σ (loc S x) = loc (S.image σ) (σ x) := by
  simp only [loc, map_prod, map_sub, Finset.prod_image σ.injective.injOn]

/-- When both supports are stable, a conjugate of a marked centre still has
the ratio of the fixed base centre. -/
theorem conjugate_centre (σ : K ≃+* K) (P Q : Finset K)
    (hP : P.image σ = P) (hQ : Q.image σ = Q) (a x : K) (ha : σ a = a)
    (hx : (∏ r ∈ P, (x-r)) / (∏ r ∈ Q, (x-r)) =
      (∏ r ∈ P, (a-r)) / (∏ r ∈ Q, (a-r))) :
    (∏ r ∈ P, (σ x-r)) / (∏ r ∈ Q, (σ x-r)) =
      (∏ r ∈ P, (a-r)) / (∏ r ∈ Q, (a-r)) := by
  change loc P x / loc Q x = loc P a / loc Q a at hx
  change loc P (σ x) / loc Q (σ x) = loc P a / loc Q a
  simpa only [map_div₀, loc_map, hP, hQ, ha] using congrArg σ hx

/-- The same orbit extension applies to squared complex magnitudes. In a
cyclotomic field complex conjugation commutes with every field automorphism. -/
theorem conjugate_squared_value (σ τ : K ≃+* K) (hc : Function.Commute σ τ)
    (r : K → K) (hs : ∀ x, σ (r x) = r (σ x)) (a x : K) (ha : σ a = a)
    (hx : r x * τ (r x) = r a * τ (r a)) :
    r (σ x) * τ (r (σ x)) = r a * τ (r a) := by
  have e (z : K) : σ (r z * τ (r z)) = r (σ z) * τ (r (σ z)) := by
    rw [map_mul, hc (r z), hs]
  simpa only [e, ha] using congrArg σ hx

#print axioms conjugate_squared_value
#print axioms conjugate_centre

end ProximityGap.LocatorConjugateCentres
