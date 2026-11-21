/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.SplitPrimeSixthDensity

/-!
# Simultaneous fourth, sixth and eighth moment bounds in the production band

The finite-set deductions use the aggregate rank bound at each of three
moment orders. The eighth-moment allowance varies with the chosen density.
-/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.SplitPrimeJointMoments
open Finset Real SplitPrimeSixthDensity

private theorem weight_union_le (A B : Finset ℕ) : weight (A∪B) ≤ weight A+weight B := by
  have he : weight (A∪B) + weight (A∩B) = weight A + weight B := Finset.sum_union_inter
  have hz : 0 ≤ weight (A∩B) := Finset.sum_nonneg fun p _ => Real.log_natCast_nonneg p
  linarith

/-- Combine the three exceptional masses. The parameter q is the reciprocal of the
allowed eighth-moment excess in units of n⁴. -/
theorem combined_weight (A B C : Finset ℕ) {q : ℝ} (hq : 0 ≤ q)
    (hA : (2:ℝ)^30 * weight A ≤ 2^120 * (log 4/2))
    (hB : weight B < 2^120/50)
    (hC : weight C ≤ q*2^120*(log 8/2)) :
    weight (A∪B∪C) < 2^90 + 2^120/50 + q*2^120*(1.04:ℝ) := by
  have h4 : log (4:ℝ) < 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num1
    linarith [log_two_lt_d9]
  have h8 : log (8:ℝ)/2 ≤ 1.04 := by
    rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
    norm_num1
    linarith [log_two_lt_d9]
  have hA' : weight A < 2^90 := by linarith
  have hC' := hC.trans (mul_le_mul_of_nonneg_left h8 (by positivity))
  linarith [weight_union_le A B, weight_union_le (A∪B) C]

/-- Full-band cardinality tradeoffs at extra eighth allowances n⁴ and n⁴/200. -/
theorem band_fractions {P U : Finset ℕ} (hsub : U ⊆ P)
    (hp : ∀ p ∈ P, 2^158 ≤ p ∧ p ≤ 2^159)
    (hP : 2^129-2^92 < weight P) :
    (weight U < 2^90+2^120/50+2^120*1.04 → 470*U.card < P.card) ∧
    (weight U < 2^90+2^120/50+200*2^120*1.04 → 12*U.card < 5*P.card) := by
  have low := (weight_bounds (fun p h => hp p (hsub h))).1
  have high := (weight_bounds hp).2
  constructor <;> intro hU
  · exact_mod_cast (show 470*(U.card:ℝ)<P.card by linarith)
  · exact_mod_cast (show 12*(U.card:ℝ)<5*P.card by linarith)

/-- On any short production window, doubling the eighth Wick allowance
leaves more than 2^103 simultaneous successes. -/
theorem short_count {P U : Finset ℕ} (hsub : U ⊆ P)
    (hp : ∀ p ∈ P, 2^158 ≤ p ∧ p ≤ 2^159)
    (hP : 2^115-2^92 < weight P)
    (hU : weight U < 2^90+2^120/50+1/105*2^120*1.04) :
    2^103 < (P \ U).card := by
  have hs : weight (P \ U) + weight U = weight P := Finset.sum_sdiff hsub
  have high := (weight_bounds (P := P \ U) (fun p h => hp p (Finset.mem_sdiff.mp h).1)).2
  exact_mod_cast (show (2:ℝ)^103 < (P \ U).card by linarith)

#print axioms combined_weight
#print axioms band_fractions
#print axioms short_count
end ArkLib.ProximityGap.Frontier.SplitPrimeJointMoments
