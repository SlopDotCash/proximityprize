/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import ArkLib.Research.ProximityGap.Frontier.PaleyBipartiteCrossRatio

/-!
# A quartic moment test for singular Paley minors

Restrict a degree-four pseudoexpectation to polynomials in its cardinality
variable. Positivity on squares of quadratics already bounds its expected
fourth falling factorial from below in terms of the first moment. On a
four-clique the Paley minor is singular modulo three.
-/

namespace ProximityGap.PaleyQuarticCertificate

open Polynomial

private theorem variance_bound (L : ℝ[X] →ₗ[ℝ] ℝ) (hL : L 1 = 1)
    (Q : ℝ[X]) (h : 0 ≤ L ((Q - C (L Q)) ^ 2)) :
    (L Q) ^ 2 ≤ L (Q ^ 2) := by
  have hC (t : ℝ) : L (C t) = t := by
    simpa [Polynomial.smul_eq_C_mul, hL] using L.map_smul t (1 : ℝ[X])
  have hpoly : (Q - C (L Q)) ^ 2 =
      Q ^ 2 - (2 * L Q) • Q + C ((L Q) ^ 2) := by
    simp [Polynomial.smul_eq_C_mul, map_ofNat]
    ring
  rw [hpoly, map_add, map_sub, map_smul, hC] at h
  change 0 ≤ L (Q ^ 2) - 2 * L Q * L Q + L Q ^ 2 at h
  nlinarith

/-- The first four moments use only the values of the functional on polynomials
of degree at most four. At first moment at least three, the expected number of
ordered four-tuples is at least the fourth falling factorial of that moment. -/
theorem falling_four_lower (L : ℝ[X] →ₗ[ℝ] ℝ) (hL : L 1 = 1)
    (hpos : ∀ Q : ℝ[X], Q.natDegree ≤ 2 → 0 ≤ L (Q ^ 2))
    (hsize : 3 ≤ L X) :
    L X * (L X - 1) * (L X - 2) * (L X - 3) ≤
      L (X * (X - 1) * (X - 2) * (X - 3)) := by
  let Q : ℝ[X] := X ^ 2 - (3 : ℝ) • X + 1
  have hdeg : Q.natDegree ≤ 2 := by
    dsimp [Q]
    compute_degree
  have hX := variance_bound L hL X (hpos _ (by compute_degree; decide))
  have hQ := variance_bound L hL Q (hpos _ ((natDegree_sub_le ..).trans (max_le hdeg (by simp))))
  have hmean : L Q = L (X ^ 2) - 3 * L X + 1 := by simp [Q, hL]
  have hnonneg : 0 ≤ (L X) ^ 2 - 3 * L X + 1 := by
    nlinarith [mul_nonneg (show 0 ≤ L X by linarith) (sub_nonneg.mpr hsize)]
  have hsquare : ((L X) ^ 2 - 3 * L X + 1) ^ 2 ≤ (L Q) ^ 2 :=
    pow_le_pow_left₀ hnonneg (by rw [hmean]; linarith) 2
  have hpoly : X * (X - 1) * (X - 2) * (X - 3) = Q ^ 2 - (1 : ℝ[X]) := by
    simp [Q, Polynomial.smul_eq_C_mul, map_ofNat]
    ring
  rw [hpoly, map_sub, hL]
  linarith only [hQ, hsquare, (by ring :
    L X * (L X - 1) * (L X - 2) * (L X - 3) =
      ((L X) ^ 2 - 3 * L X + 1) ^ 2 - 1)]

/-- All four-subsets carrying clique mass contribute to the singular-minor objective. -/
theorem clique_minor_singular :
    (((PaleyBipartiteCrossRatio.fourSiteMatrix 1 1 1 1 1 1 1).det : ℤ) : ZMod 3) = 0 := by
  rw [PaleyBipartiteCrossRatio.four_site_singular_mod_three] <;> norm_num

#print axioms falling_four_lower
#print axioms clique_minor_singular

end ProximityGap.PaleyQuarticCertificate
