/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FourHeadCrossRatio

/-! # Rigidity of scalar polynomial rows on a saturated triangle -/

set_option autoImplicit false
noncomputable section
open Polynomial Finset
namespace ArkLib.ProximityGap.Frontier.SaturatedTripleRows
variable {F : Type*} [Field F]

private theorem multiple {P Q : F[X]} (S : Finset F) (D : ℕ) (hs : S.card = D)
    (hp : P ≠ 0) (hP : P.natDegree ≤ D) (hQ : Q.natDegree ≤ D)
    (hrP : ∀ x ∈ S, P.eval x = 0) (hrQ : ∀ x ∈ S, Q.eval x = 0) :
    ∃ c : F, Q = C c * P := by
  by_contra! h
  have bound := _root_.ProximityGap.FourHeadCrossRatio.pencil_charge_lt S (fun _ => 1) Q P D hp h hQ hP
    (fun x hx => by simpa only [pow_one] using dvd_iff_isRoot.mpr (hrQ x hx))
    (fun x hx => by simpa only [pow_one] using dvd_iff_isRoot.mpr (hrP x hx))
  simp [hs] at bound

/-- If the three pair strata exhaust the determinant degree, every compatible
scalar polynomial row of the same degree is a constant combination of the two
given rows. The three rows have each been translated to vanish on the first head. -/
theorem scalar_rows_span (a b c e u v : F[X]) (D : ℕ)
    (ha : a.natDegree ≤ D) (hb : b.natDegree ≤ D) (hc : c.natDegree ≤ D) (he : e.natDegree ≤ D)
    (hu : u.natDegree ≤ D) (hv : v.natDegree ≤ D)
    (hdet : a*e-c*b ≠ 0) (S : Finset F) (hs : S.card = 2*D)
    (hmatch : ∀ x ∈ S,
      (a.eval x = 0 ∧ b.eval x = 0 ∧ u.eval x = 0) ∨
      (c.eval x = 0 ∧ e.eval x = 0 ∧ v.eval x = 0) ∨
      (a.eval x = c.eval x ∧ b.eval x = e.eval x ∧ u.eval x = v.eval x)) :
    ∃ α β : F, u = C α*a+C β*b ∧ v = C α*c+C β*e := by
  have hdeg (x y z t : F[X]) (hx : x.natDegree ≤ D) (hy : y.natDegree ≤ D)
      (hz : z.natDegree ≤ D) (ht : t.natDegree ≤ D) :
      (x*t-z*y).natDegree ≤ 2*D := (natDegree_sub_le ..).trans
        (max_le (natDegree_mul_le.trans (by omega)) (natDegree_mul_le.trans (by omega)))
  have hD := hdeg a b c e ha hb hc he
  have roots (x : F) (hx : x ∈ S) : (a*e-c*b).eval x = 0 ∧ (u*e-v*b).eval x = 0 ∧
      (a*v-c*u).eval x = 0 := by
    rcases hmatch x hx with ⟨h₁,h₂,h₃⟩ | ⟨h₁,h₂,h₃⟩ | ⟨h₁,h₂,h₃⟩ <;> simp [h₁,h₂,h₃]
  obtain ⟨α,hα⟩ := multiple S _ hs hdet hD (hdeg u b v e hu hb hv he)
    (fun x hx => (roots x hx).1) (fun x hx => (roots x hx).2.1)
  obtain ⟨β,hβ⟩ := multiple S _ hs hdet hD (hdeg a u c v ha hu hc hv)
    (fun x hx => (roots x hx).1) (fun x hx => (roots x hx).2.2)
  refine ⟨α,β,sub_eq_zero.mp ((mul_eq_zero.mp ?_).resolve_left hdet),
    sub_eq_zero.mp ((mul_eq_zero.mp ?_).resolve_left hdet)⟩
  · linear_combination a*hα+b*hβ
  · linear_combination c*hα+e*hβ

/-- No lower-degree scalar row can satisfy the three saturated pair constraints.
This gives the degree obstruction for the relation obtained from rotated minors. -/
theorem short_row_zero (a b c e u v : F[X]) (D : ℕ)
    (ha : a.natDegree ≤ D) (hb : b.natDegree ≤ D) (hc : c.natDegree ≤ D) (he : e.natDegree ≤ D)
    (hu : u.natDegree < D) (hv : v.natDegree < D)
    (hdet : a*e-c*b ≠ 0) (S : Finset F) (hs : S.card = 2*D)
    (hmatch : ∀ x ∈ S,
      (a.eval x = 0 ∧ b.eval x = 0 ∧ u.eval x = 0) ∨
      (c.eval x = 0 ∧ e.eval x = 0 ∧ v.eval x = 0) ∨
      (a.eval x = c.eval x ∧ b.eval x = e.eval x ∧ u.eval x = v.eval x)) :
    u = 0 ∧ v = 0 := by
  have roots (x : F) (hx : x ∈ S) : (u*e-v*b).eval x = 0 ∧ (a*v-c*u).eval x = 0 := by
    rcases hmatch x hx with ⟨h₁,h₂,h₃⟩ | ⟨h₁,h₂,h₃⟩ | ⟨h₁,h₂,h₃⟩ <;> simp [h₁,h₂,h₃]
  have R := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (u*e-v*b) S
    (fun x hx => (roots x hx).1) (by
      rw [hs]
      exact (natDegree_sub_le ..).trans_lt
        (max_lt (natDegree_mul_le.trans_lt (by omega)) (natDegree_mul_le.trans_lt (by omega))))
  have T := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (a*v-c*u) S
    (fun x hx => (roots x hx).2) (by
      rw [hs]
      exact (natDegree_sub_le ..).trans_lt
        (max_lt (natDegree_mul_le.trans_lt (by omega)) (natDegree_mul_le.trans_lt (by omega))))
  constructor
  · exact (mul_eq_zero.mp (show (a*e-c*b)*u = 0 by linear_combination a*R+b*T)).resolve_left hdet
  · exact (mul_eq_zero.mp (show (a*e-c*b)*v = 0 by linear_combination c*R+e*T)).resolve_left hdet

/-- Repeated double fibers can supply at most two projective directions each,
and four singletons can supply at most twelve. -/
theorem repeated_fiber_budget {n q fibers : ℕ} (hn : 8 ≤ n) (hq : 2 ≤ q)
    (hfibers : q*fibers = n-4) : 2*fibers+12 ≤ 2*n := by
  have := Nat.mul_le_mul_right fibers hq
  omega

#print axioms scalar_rows_span
#print axioms short_row_zero
#print axioms repeated_fiber_budget
end ArkLib.ProximityGap.Frontier.SaturatedTripleRows
