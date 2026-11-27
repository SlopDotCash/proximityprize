/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterSplitWronskianSuborbits

/-! # Odd-degree split pencils at the production length

Numerical consequences of the Wronskian bound on a component of an odd-degree
split pencil. The application to rational maps and their intermediate fields is
given in the accompanying research note.
-/

namespace ProximityGap.HalfSuccessorPencilMonodromy

/-- Combine the Wronskian inequality with the adjunction genus bound and
cancel the common positive component degree. -/
theorem subdegree_bound {d a : ℕ} (ha : 0 < a) (chi : ℝ)
    (wronskian : 3 * (d : ℝ) * a ≤ (2 / 3 : ℝ) * 1073741824 * a + chi)
    (adjunction : chi ≤ 2 * (a : ℝ) ^ 2) :
    9 * d ≤ 2 * 1073741824 + 6 * a := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have bound : 9 * (d : ℝ) ≤ 2 * 1073741824 + 6 * a := by
    apply (mul_le_mul_iff_of_pos_right ha').mp
    nlinarith only [wronskian, adjunction]
  exact_mod_cast bound

/-- The ceilings for the two odd degrees on either side of a quarter of
the production length. -/
theorem named_subdegree_floors {d a : ℕ}
    (bound : 9 * d ≤ 2 * 1073741824 + 6 * a) :
    (d = 268435455 → 44739242 ≤ a) ∧ (d = 268435457 → 44739245 ≤ a) := by
  omega

/-- A right factor of the lower odd degree may have outer degree one,
three, or five. These are the exact possible stage degrees after the bound. -/
theorem lower_factor_degrees {s m : ℕ} (prod : s * m = 268435455)
    (size : 44739242 ≤ m - 1) :
    (s = 1 ∧ m = 268435455) ∨ (s = 3 ∧ m = 89478485) ∨
      (s = 5 ∧ m = 53687091) := by
  have hs : s ≤ 5 := by
    by_contra! hs
    have := Nat.mul_le_mul hs (show 44739243 ≤ m by omega)
    omega
  interval_cases s <;> omega

/-- The same argument forces the upper odd pencil to be indecomposable. -/
theorem upper_factor_degree {s m : ℕ} (prod : s * m = 268435457)
    (size : 44739245 ≤ m - 1) : s = 1 ∧ m = 268435457 := by
  have hs : s ≤ 5 := by
    by_contra! hs
    have := Nat.mul_le_mul hs (show 44739246 ≤ m by omega)
    omega
  interval_cases s <;> omega

/-- The compositum of two intermediate fields of degree three or five
over the target has degree at most 25. Its own permitted degree can only
be three or five, so it coincides with both intermediate fields. -/
theorem compositum_degrees {s t u : ℕ}
    (hs : s = 3 ∨ s = 5) (ht : t = 3 ∨ t = 5)
    (hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 268435455)
    (bound : u ≤ s * t) (left : s ∣ u) (right : t ∣ u) :
    s = u ∧ t = u := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    rcases hu with rfl | rfl | rfl | rfl <;> norm_num at *

/-- The degree of the common source over the field of two half-successor
pencils divides their odd degree and the degree of their quotient. -/
theorem joint_degree {k e : ℕ} (hk : k ∣ 268435455) (he : k ∣ e)
    (low : e = 1 ∨ e = 2) : k = 1 := by
  have he_pos : 0 < e := by omega
  have k_le : k ≤ 2 := (Nat.le_of_dvd he_pos he).trans (by omega)
  interval_cases k <;> norm_num at *

/-- A non-natural subset action of an alternating group would have a
suborbit too small. Here t is the subset size and a the natural degree. -/
theorem subset_neighbor_bound {a t : ℕ} (ha : a ≤ 24000) (ht : t ≤ 5) :
    t * (a - t) < 44739242 := by
  have := Nat.mul_le_mul ht ((Nat.sub_le a t).trans ha)
  omega

/-- The explicit adjunction degree in a pair of simultaneous compositions
with outer degrees three or five. -/
theorem joint_adjunction_lower {s t u v : ℕ} (hs : s = 3 ∨ s = 5) (ht : t = 3 ∨ t = 5)
    (hu : s * u = 268435455) (hv : t * v = 268435455) :
    178956970 ≤ (s - 2) * u + (t - 2) * v := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> omega

/-- The height required by the two low outer degrees exceeds the genus
bound for their one-point S₃ cover, even after the tame base different. -/
theorem joint_height_contradiction {H b : ℝ} (hb : 0 < b)
    (adjunction : 178956970 * b ≤ H + 133 * b)
    (szpiro : (16 / 3 : ℝ) * H ≤ 4 * 93 * 92 * 131 * b) : False := by
  linarith

/-- Lower bounds for the degree of a nonconstant quotient of two
compositions, in the cubic-cubic, cubic-quintic and quintic-quintic cases. -/
theorem quotient_degree_floors (e : ℕ) :
    (178957286 ≤ 5689 * e → 31457 ≤ e) ∧
    (250541244 ≤ 50525 * e → 4959 ≤ e) ∧
    (322128964 ≤ 423589 * e → 761 ≤ e) := by omega

#print axioms subdegree_bound
#print axioms named_subdegree_floors
#print axioms lower_factor_degrees
#print axioms upper_factor_degree
#print axioms compositum_degrees
#print axioms joint_degree
#print axioms subset_neighbor_bound
#print axioms joint_adjunction_lower
#print axioms joint_height_contradiction
#print axioms quotient_degree_floors

end ProximityGap.HalfSuccessorPencilMonodromy
