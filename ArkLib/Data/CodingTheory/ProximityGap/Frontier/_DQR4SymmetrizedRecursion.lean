/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DQR23TwoScaleCenteredRecursion
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DQR4StratumPalindrome

/-!
# DQR-4 symmetrized recursion: the working equation of the dyadic tower — #466

Thirteenth result; the capstone assembly of the ledger. Combining
`offZero_fourteenth_two_scale` (the signed binomial ledger), the frequency reindex of the
`k = 0` diagonal (`∑ η_{b·a}^{14} = ∑ η_b^{14}`), and `stratum_palindrome`
(`T_k = T_{14−k}` for tower twists), the depth-14 moment recursion collapses to its minimal
form:

* `symmetrized_recursion` — for a dyadic tower step `G' = G ⊔ aG` with `a·a ∈ G`:

    `S₁₄(G') = 2·S₁₄(G) + 2·∑_{k=1}^{6} C(14,k)·T_k + 3432·T_7`,

  where `S₁₄ = ∑_{b≠0} η_b^{14}` and `T_k = ∑_{b≠0} η_b^k·η_{b·a}^{14−k}` — SEVEN unknown
  strata per level, each an exact dilated rep-rep correlation
  (`crossMoment_eq_mixedCount`), integrality-constrained (`mul_dvd_repCount_zero` via the
  power sums), with a closed-form twist average (`twistAverage_factorizes`).

This is the exact working equation any tower-based proof of the depth-seven gate must solve,
now fully machine-checked; the open content is the size of `T_1, …, T_7` at the 29 production
levels. Nothing here discharges it. Issue #466. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.BGKCosetAmplification
open ArkLib.ProximityGap.Frontier.DQR23TwoScaleCenteredRecursion
open ArkLib.ProximityGap.Frontier.DQR4StratumPalindrome

namespace ArkLib.ProximityGap.Frontier.DQR4SymmetrizedRecursion

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The frequency reindex of the dilated diagonal: `∑_{b≠0} η_{b·a}^m = ∑_{b≠0} η_b^m`. -/
theorem dilated_powerSum_reindex (ψ : AddChar F ℂ) (G : Finset F) {a : F} (ha : a ≠ 0)
    (m : ℕ) :
    ∑ b ∈ Finset.univ.erase (0 : F), (eta ψ G (b * a)) ^ m
      = ∑ b ∈ Finset.univ.erase (0 : F), (eta ψ G b) ^ m := by
  apply Finset.sum_nbij' (i := fun b => b * a) (j := fun c => c * a⁻¹)
  · intro b hb
    have hb0 : b ≠ 0 := Finset.ne_of_mem_erase (by exact_mod_cast hb)
    simp [Finset.mem_coe, Finset.mem_erase, mul_ne_zero hb0 ha]
  · intro c hc
    have hc0 : c ≠ 0 := Finset.ne_of_mem_erase (by exact_mod_cast hc)
    simp [Finset.mem_coe, Finset.mem_erase, mul_ne_zero hc0 (inv_ne_zero ha)]
  · intro b _
    rw [mul_assoc, mul_inv_cancel₀ ha, mul_one]
  · intro c _
    rw [mul_assoc, inv_mul_cancel₀ ha, mul_one]
  · intro b _
    rfl

/-- **The symmetrized tower recursion**: for `G' = G ⊔ aG` (disjoint) with `a·a ∈ G`,

  `S₁₄(G') = 2·S₁₄(G) + ∑_{k=1}^{13} C(14,k)·T_k
           = 2·S₁₄(G) + 2·∑_{k∈{1..6}} C(14,k)·T_k + 3432·T_7`.

Stated in the ledger form with the diagonal collapsed; the palindromic pairing is applied to
exhibit the seven independent strata. -/
theorem symmetrized_recursion {G : Finset F} (hG : MulClosed G)
    (ψ : AddChar F ℂ) {a : F} (ha : a ≠ 0) (ha2 : a * a ∈ G)
    (hdisj : Disjoint G (G.image (fun y => a * y))) :
    ∑ b ∈ Finset.univ.erase (0 : F), (eta ψ (G ∪ G.image (fun y => a * y)) b) ^ 14
      = 2 * (∑ b ∈ Finset.univ.erase (0 : F), (eta ψ G b) ^ 14)
        + (2 * ∑ k ∈ Finset.range 6, (Nat.choose 14 (k + 1) : ℂ) *
            ∑ b ∈ Finset.univ.erase (0 : F),
              (eta ψ G b) ^ (k + 1) * (eta ψ G (b * a)) ^ (14 - (k + 1)))
        + (3432 : ℂ) * ∑ b ∈ Finset.univ.erase (0 : F),
            (eta ψ G b) ^ 7 * (eta ψ G (b * a)) ^ 7 := by
  -- start from the signed binomial ledger.
  have hledger := offZero_fourteenth_two_scale ψ G ha hdisj
  rw [hledger]
  -- name the strata.
  set T : ℕ → ℂ := fun k => ∑ b ∈ Finset.univ.erase (0 : F),
    (eta ψ G b) ^ k * (eta ψ G (b * a)) ^ (14 - k) with hT
  -- the k = 0 and k = 14 strata are both S₁₄ (reindex / trivial power).
  have h0 : T 0 = ∑ b ∈ Finset.univ.erase (0 : F), (eta ψ G b) ^ 14 := by
    rw [hT]
    simp only [pow_zero, one_mul, Nat.sub_zero]
    exact dilated_powerSum_reindex ψ G ha 14
  have h14 : T 14 = ∑ b ∈ Finset.univ.erase (0 : F), (eta ψ G b) ^ 14 := by
    rw [hT]
    simp
  -- the palindrome pairs the upper strata with the lower ones.
  have hpal : ∀ k j : ℕ, k + j = 14 → T k = T j := by
    intro k j hkj
    have h14k : 14 - k = j := by omega
    have h14j : 14 - j = k := by omega
    show (∑ b ∈ Finset.univ.erase (0 : F),
        (eta ψ G b) ^ k * (eta ψ G (b * a)) ^ (14 - k))
      = ∑ b ∈ Finset.univ.erase (0 : F),
        (eta ψ G b) ^ j * (eta ψ G (b * a)) ^ (14 - j)
    rw [h14k, h14j]
    exact stratum_palindrome hG ψ ha ha2 k j
  have hp8 : T 8 = T 6 := hpal 8 6 (by norm_num)
  have hp9 : T 9 = T 5 := hpal 9 5 (by norm_num)
  have hp10 : T 10 = T 4 := hpal 10 4 (by norm_num)
  have hp11 : T 11 = T 3 := hpal 11 3 (by norm_num)
  have hp12 : T 12 = T 2 := hpal 12 2 (by norm_num)
  have hp13 : T 13 = T 1 := hpal 13 1 (by norm_num)
  -- expand all range sums explicitly and collect.
  show ∑ k ∈ Finset.range 15, (Nat.choose 14 k : ℂ) * T k = _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [h0, h14, hp8, hp9, hp10, hp11, hp12, hp13]
  show _ = 2 * (∑ b ∈ Finset.univ.erase (0 : F), (eta ψ G b) ^ 14)
    + (2 * (0 + (Nat.choose 14 1 : ℂ) * T 1 + (Nat.choose 14 2 : ℂ) * T 2
        + (Nat.choose 14 3 : ℂ) * T 3 + (Nat.choose 14 4 : ℂ) * T 4
        + (Nat.choose 14 5 : ℂ) * T 5 + (Nat.choose 14 6 : ℂ) * T 6))
    + (3432 : ℂ) * T 7
  norm_num [Nat.choose]
  ring

end ArkLib.ProximityGap.Frontier.DQR4SymmetrizedRecursion

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms
  ArkLib.ProximityGap.Frontier.DQR4SymmetrizedRecursion.dilated_powerSum_reindex
#print axioms
  ArkLib.ProximityGap.Frontier.DQR4SymmetrizedRecursion.symmetrized_recursion
