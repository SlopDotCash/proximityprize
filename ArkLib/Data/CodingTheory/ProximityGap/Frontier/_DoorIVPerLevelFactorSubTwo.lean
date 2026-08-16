/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVTwoDilateNoJointExtreme
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVXGatePrizeBudget

/-!
# Door-(iv) Lane-3: per-level factor bookkeeping for the two-dilate recursion (#444)

The empirical door-(iv) object now lives at the dyadic recursion

`M_n = S(b*) + S(g b*)`,

where `Smax = M_{n/2}` is the thinner-level marginal maximum.  The probe
`probe_dooriv_perlevel_factor_law.py` measured the normalized per-level multiplier

`c_n = M_n / M_{n/2}`

and found it stable near `√2`, strictly below the trivial co-peak ceiling `2`, and not drifting upward
toward the Johnson/trivial doubling wall.  This file does **not** kernel any empirical numeric claim.
It records the real-algebra bookkeeping that makes that probe citable:

* `H ≤ 2 Smax` is exactly `c ≤ 2` once `H = c Smax` and `Smax > 0`.
* a strict two-dilate no-co-peak gap `H < 2 Smax` is exactly `c < 2`.
* the corrected `√2` gate already landed in `_DoorIVXGatePrizeBudget`: once every per-level factor is
  bounded by `√2`, the telescope gives the prize-shaped `C √(n L)` budget.

No CORE upper bound, cancellation, completion, moment, anti-concentration, or capacity claim is made.
The open content remains the arithmetic proof of the `√2` per-level gate.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.DoorIVTwoDilateNoJointExtreme
open ArkLib.ProximityGap.Frontier.DoorIVXGatePrizeBudget
open ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge

open scoped BigOperators

/-- **Per-level factor ceiling from the two-dilate envelope.**  If the measured two-dilate maximum is
written as `H = c·Smax` with positive thinner-level maximum `Smax`, then the unconditional envelope
`H ≤ 2·Smax` is exactly the normalized ceiling `c ≤ 2`.  This packages the probe's ratio
`c(n)=M(n)/M(n/2)` in the same units as the no-co-peak theorem. -/
theorem perLevelFactor_le_two_of_dilate_le_two_mul
    {H Smax c : ℝ} (hSmax : 0 < Smax) (hH : H = c * Smax) (hbound : H ≤ 2 * Smax) :
    c ≤ 2 := by
  nlinarith

/-- **Strict no-co-peak gap ⇔ strict sub-doubling per-level factor.**  With `H = c·Smax` and
`Smax > 0`, the strict two-dilate gap `H < 2·Smax` is equivalent to `c < 2`.  Thus the empirical
statement `M(n)/M(n/2) < 2` is not a new analytic assumption: it is the normalized form of the
already-kernelled no-co-peak obstruction. -/
theorem perLevelFactor_lt_two_iff_dilate_lt_two_mul
    {H Smax c : ℝ} (hSmax : 0 < Smax) (hH : H = c * Smax) :
    c < 2 ↔ H < 2 * Smax := by
  constructor
  · intro hc
    nlinarith
  · intro hHlt
    nlinarith

/-- **No-co-peak certificate as a normalized factor bound.**  Applying
`not_both_max_of_lt_two_mul` to a two-dilate frequency with envelope `H = c·Smax`, `c < 2`, says the
normalized sub-doubling factor rules out a perfect joint marginal extreme at that same frequency. -/
theorem no_copeak_of_perLevelFactor_lt_two
    {ι : Type*} {s : ι → ℝ} {σ : ι → ι} {Smax c : ℝ} {b : ι}
    (hc : c < 2) (hSmax : 0 < Smax)
    (hfactor : twoDilate s σ b = c * Smax) :
    s b + s (σ b) < 2 * Smax := by
  exact not_both_max_of_lt_two_mul hc hSmax (le_of_eq hfactor)

/-- **The `√2` factor is a strict sub-doubling factor.**  This is the scalar separation that the
per-level-factor probe localizes: the prize gate `√2` is genuinely below the co-peak ceiling `2`. -/
theorem sqrt_two_lt_two : Real.sqrt 2 < (2 : ℝ) := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- **Variable per-level-factor telescope.**  If `M (k+1) ≤ c k · M k` at each dyadic level,
with nonnegative factors, then the whole tower is bounded by the product of the measured factors.  This
is the exact algebra behind reading the probe's list of ratios `c(k)=M(2^{k+1})/M(2^k)` as a growth law;
it makes no claim about the arithmetic size of any `c k`. -/
theorem telescope_variable_perLevelFactors (M c : ℕ → ℝ)
    (hc : ∀ k, 0 ≤ c k)
    (hstep : ∀ k, M (k + 1) ≤ c k * M k) (a : ℕ) :
    M a ≤ (∏ k ∈ Finset.range a, c k) * M 0 := by
  induction a with
  | zero => simp
  | succ n ih =>
    calc M (n + 1) ≤ c n * M n := hstep n
      _ ≤ c n * ((∏ k ∈ Finset.range n, c k) * M 0) :=
          mul_le_mul_of_nonneg_left ih (hc n)
      _ = (∏ k ∈ Finset.range (n + 1), c k) * M 0 := by
          rw [Finset.prod_range_succ]
          ring

/-- **Product gate for the variable per-level factors.**  Once the product of the level ratios is bounded
by some budget `B`, the same budget controls the top level.  The theorem separates the honest empirical
question (`∏ c_k ≤ B`) from the kernel-checked telescope algebra. -/
theorem telescope_of_factorProduct_le (M c : ℕ → ℝ) {a : ℕ} {B : ℝ}
    (hc : ∀ k, 0 ≤ c k) (hM0 : 0 ≤ M 0)
    (hprod : (∏ k ∈ Finset.range a, c k) ≤ B)
    (hstep : ∀ k, M (k + 1) ≤ c k * M k) :
    M a ≤ B * M 0 := by
  have ht := telescope_variable_perLevelFactors M c hc hstep a
  have hprod_nonneg : 0 ≤ ∏ k ∈ Finset.range a, c k := by
    exact Finset.prod_nonneg (by intro k _hk; exact hc k)
  have hB_nonneg : 0 ≤ B := le_trans hprod_nonneg hprod
  exact le_trans ht (mul_le_mul_of_nonneg_right hprod hM0)

/-- **Pointwise `√2` factor gate controls the product.**  If every measured per-level factor in the
finite tower is at most `√2`, then their product is at most `(√2)^a`.  This is deliberately only a
finite product lemma: the arithmetic proof of the pointwise `√2` gate is not supplied here. -/
theorem factorProduct_le_sqrtTwo_pow {c : ℕ → ℝ} {a : ℕ}
    (hc0 : ∀ k, 0 ≤ c k) (hc2 : ∀ k ∈ Finset.range a, c k ≤ Real.sqrt 2) :
    (∏ k ∈ Finset.range a, c k) ≤ (Real.sqrt 2) ^ a := by
  calc (∏ k ∈ Finset.range a, c k)
      ≤ ∏ _k ∈ Finset.range a, Real.sqrt 2 :=
        Finset.prod_le_prod (by intro k _hk; exact hc0 k) (by intro k hk; exact hc2 k hk)
    _ = (Real.sqrt 2) ^ a := by
        rw [Finset.prod_const, Finset.card_range]

/-- **Variable-factor `√2` telescope.**  A pointwise `√2` bound on every finite per-level multiplier
implies the expected `M(a) ≤ (√2)^a M(0)` tower bound.  This is the product form of the existing
`LevelRatioBoundNZ … √2` capstone, specialized to explicitly measured factors. -/
theorem telescope_of_pointwise_sqrtTwo_factors (M c : ℕ → ℝ) {a : ℕ}
    (hc0 : ∀ k, 0 ≤ c k) (hM0 : 0 ≤ M 0)
    (hc2 : ∀ k ∈ Finset.range a, c k ≤ Real.sqrt 2)
    (hstep : ∀ k, M (k + 1) ≤ c k * M k) :
    M a ≤ (Real.sqrt 2) ^ a * M 0 := by
  exact telescope_of_factorProduct_le M c hc0 hM0 (factorProduct_le_sqrtTwo_pow hc0 hc2) hstep

/-- **Failure of the finite `√2` product gate is localized at a bad rung.**  If the product of the
nonnegative measured per-level factors exceeds `(√2)^a`, then at least one finite rung has factor
strictly bigger than `√2`.  This is the exact obstruction certificate for a finite telescope: any
failure of the product gate must be witnessed locally, rather than hidden in an average. -/
theorem exists_factor_gt_sqrtTwo_of_factorProduct_gt {c : ℕ → ℝ} {a : ℕ}
    (hc0 : ∀ k, 0 ≤ c k)
    (hprod : (Real.sqrt 2) ^ a < ∏ k ∈ Finset.range a, c k) :
    ∃ k ∈ Finset.range a, Real.sqrt 2 < c k := by
  by_contra hnone
  have hall : ∀ k ∈ Finset.range a, c k ≤ Real.sqrt 2 := by
    intro k hk
    exact le_of_not_gt (by
      intro hgt
      exact hnone ⟨k, hk, hgt⟩)
  have hle := factorProduct_le_sqrtTwo_pow (c := c) (a := a) hc0 hall
  linarith

/-- **A top-level excess over the `√2` telescope forces product-gate failure.**  If the top level is
strictly larger than `(√2)^a M(0)` while the variable-factor telescope already bounds it by
`(∏ c_k) M(0)` and the base is positive, then the finite product of the measured factors must exceed
`(√2)^a`.  No arithmetic estimate is asserted; this only localizes where a counterexample must live. -/
theorem factorProduct_gt_of_telescope_counterexample {M c : ℕ → ℝ} {a : ℕ}
    (hM0 : 0 < M 0)
    (htelescope : M a ≤ (∏ k ∈ Finset.range a, c k) * M 0)
    (hcounter : (Real.sqrt 2) ^ a * M 0 < M a) :
    (Real.sqrt 2) ^ a < ∏ k ∈ Finset.range a, c k := by
  by_contra hnot
  have hprod_le : (∏ k ∈ Finset.range a, c k) ≤ (Real.sqrt 2) ^ a := le_of_not_gt hnot
  have hmul : (∏ k ∈ Finset.range a, c k) * M 0 ≤ (Real.sqrt 2) ^ a * M 0 := by
    exact mul_le_mul_of_nonneg_right hprod_le (le_of_lt hM0)
  linarith

/-- **A finite counterexample to the `√2` telescope has a local super-`√2` rung.**  Combining the
variable-factor telescope with the preceding two lemmas: if `M(a)` beats the `√2` tower budget, then
some measured rung in `0,…,a-1` satisfies `√2 < c_k`.  This is a Lane-3 constraint on the recursion:
the missing door-(iv) arithmetic input is exactly to rule out (or compensate) those super-`√2` rungs. -/
theorem exists_super_sqrtTwo_factor_of_telescope_counterexample (M c : ℕ → ℝ) {a : ℕ}
    (hc0 : ∀ k, 0 ≤ c k) (hM0 : 0 < M 0)
    (hstep : ∀ k, M (k + 1) ≤ c k * M k)
    (hcounter : (Real.sqrt 2) ^ a * M 0 < M a) :
    ∃ k ∈ Finset.range a, Real.sqrt 2 < c k := by
  have ht := telescope_variable_perLevelFactors M c hc0 hstep a
  have hprod := factorProduct_gt_of_telescope_counterexample (M := M) (c := c) hM0 ht hcounter
  exact exists_factor_gt_sqrtTwo_of_factorProduct_gt (c := c) (a := a) hc0 hprod

/-- **A super-`√2` rung requires strict compensation from the remaining product.**  If a tower of
positive height still satisfies the total `√2` product budget and one isolated rung has factor
`c_bad > √2`, then the product of all other rungs, represented here by `R`, must be strictly below the
remaining `(√2)^(a-1)` budget.  This is the finite compensation law behind the localization theorem. -/
theorem remainderProduct_lt_sqrtTwo_pow_pred_of_bad_rung {a : ℕ} {cBad R : ℝ}
    (ha : 0 < a) (hR : 0 ≤ R) (hbad : Real.sqrt 2 < cBad)
    (htotal : cBad * R ≤ (Real.sqrt 2) ^ a) :
    R < (Real.sqrt 2) ^ (a - 1) := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  rw [Nat.succ_sub_one]
  by_contra hnot
  have hRge : (Real.sqrt 2) ^ b ≤ R := le_of_not_gt hnot
  have hpow_pos : 0 < (Real.sqrt 2) ^ b := pow_pos hspos b
  have hcb_nonneg : 0 ≤ cBad := le_of_lt (lt_trans hspos hbad)
  have hstrict : Real.sqrt 2 * (Real.sqrt 2) ^ b < cBad * R := by
    exact mul_lt_mul hbad hRge hpow_pos hcb_nonneg
  have hpow : (Real.sqrt 2) ^ (b + 1) = Real.sqrt 2 * (Real.sqrt 2) ^ b := by
    rw [pow_succ']
  rw [hpow] at htotal
  linarith


/-- **Two super-`√2` rungs require two units of strict compensation.**  This is the two-rung
version of `remainderProduct_lt_sqrtTwo_pow_pred_of_bad_rung`: if two isolated rungs are both
strictly above the `√2` gate and the total product over a height `b+2` tower still meets the
`√2` budget, then the remaining product must be strictly below `(√2)^b`.  It records the exact
finite slack accounting for clustered bad rungs without asserting that such rungs occur. -/
theorem remainderProduct_lt_sqrtTwo_pow_of_two_bad_rungs {b : ℕ} {cBad₁ cBad₂ R : ℝ}
    (hR : 0 ≤ R) (hbad₁ : Real.sqrt 2 < cBad₁) (hbad₂ : Real.sqrt 2 < cBad₂)
    (htotal : cBad₁ * cBad₂ * R ≤ (Real.sqrt 2) ^ (b + 2)) :
    R < (Real.sqrt 2) ^ b := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2)
  by_contra hnot
  have hRge : (Real.sqrt 2) ^ b ≤ R := le_of_not_gt hnot
  have hpow_pos : 0 < (Real.sqrt 2) ^ b := pow_pos hspos b
  have hcb₁_nonneg : 0 ≤ cBad₁ := le_of_lt (lt_trans hspos hbad₁)
  have hcb₂_nonneg : 0 ≤ cBad₂ := le_of_lt (lt_trans hspos hbad₂)
  have hpair : Real.sqrt 2 * Real.sqrt 2 < cBad₁ * cBad₂ := by
    exact mul_lt_mul hbad₁ (le_of_lt hbad₂) hspos hcb₁_nonneg
  have hpair_nonneg : 0 ≤ cBad₁ * cBad₂ := mul_nonneg hcb₁_nonneg hcb₂_nonneg
  have hstrict : (Real.sqrt 2 * Real.sqrt 2) * (Real.sqrt 2) ^ b <
      (cBad₁ * cBad₂) * R := by
    exact mul_lt_mul hpair hRge hpow_pos hpair_nonneg
  have hpow : (Real.sqrt 2) ^ (b + 2) = (Real.sqrt 2 * Real.sqrt 2) * (Real.sqrt 2) ^ b := by
    rw [show b + 2 = (b + 1) + 1 by omega, pow_succ, pow_succ]
    ring
  rw [hpow] at htotal
  linarith


/-- **Any super-budget block requires matching strict compensation.**  This packages the finite
cluster law behind the one- and two-bad-rung lemmas.  If a block of rungs has product `badBlock`
strictly larger than its own `√2` budget `(√2)^r`, while the total height `b+r` product still meets the
`√2` budget, then the complementary product must be strictly below `(√2)^b`.  This is pure
bookkeeping: proving that the door-(iv) arithmetic supplies such compensated blocks remains open. -/
theorem remainderProduct_lt_sqrtTwo_pow_of_superBudget_block {b r : ℕ} {badBlock R : ℝ}
    (hR : 0 ≤ R) (hbad : (Real.sqrt 2) ^ r < badBlock)
    (htotal : badBlock * R ≤ (Real.sqrt 2) ^ (b + r)) :
    R < (Real.sqrt 2) ^ b := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2)
  by_contra hnot
  have hRge : (Real.sqrt 2) ^ b ≤ R := le_of_not_gt hnot
  have hpowb_pos : 0 < (Real.sqrt 2) ^ b := pow_pos hspos b
  have hbad_nonneg : 0 ≤ badBlock := le_of_lt (lt_trans (pow_pos hspos r) hbad)
  have hstrict : (Real.sqrt 2) ^ r * (Real.sqrt 2) ^ b < badBlock * R := by
    exact mul_lt_mul hbad hRge hpowb_pos hbad_nonneg
  have hpow : (Real.sqrt 2) ^ (b + r) = (Real.sqrt 2) ^ r * (Real.sqrt 2) ^ b := by
    rw [pow_add]
    ring
  rw [hpow] at htotal
  linarith

/-- **Uncompensated super-budget blocks break the finite `√2` telescope.**  This is the contrapositive
form of `remainderProduct_lt_sqrtTwo_pow_of_superBudget_block`: a block already above its own `√2`
budget cannot be paired with a complementary product still at or above its own `√2` budget.  If both
happen, the total product is strictly above the height-`b+r` `√2` product budget.  Thus any door-(iv)
recursion with a bad block must pay a real, localized compensation debt outside that block. -/
theorem totalProduct_gt_sqrtTwo_pow_of_uncompensated_superBudget_block {b r : ℕ}
    {badBlock R : ℝ} (hbad : (Real.sqrt 2) ^ r < badBlock)
    (hR : (Real.sqrt 2) ^ b ≤ R) :
    (Real.sqrt 2) ^ (b + r) < badBlock * R := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2)
  have hpowb_pos : 0 < (Real.sqrt 2) ^ b := pow_pos hspos b
  have hbad_nonneg : 0 ≤ badBlock := le_of_lt (lt_trans (pow_pos hspos r) hbad)
  have hstrict : (Real.sqrt 2) ^ r * (Real.sqrt 2) ^ b < badBlock * R := by
    exact mul_lt_mul hbad hR hpowb_pos hbad_nonneg
  have hpow : (Real.sqrt 2) ^ (b + r) = (Real.sqrt 2) ^ r * (Real.sqrt 2) ^ b := by
    rw [pow_add]
    ring
  rwa [hpow]

/-- **Scaled uncompensated super-budget blocks also break the finite `√2` telescope.**  The previous
lemma is the special case `K = 1`.  More generally, if a block is a factor `K` above its own `√2`
budget and the complementary product is still at least the reciprocal `1/K` of its own budget, then
the total product is strictly above the height-`b+r` `√2` budget.  This is the exact quantitative
compensation ledger for localized bad blocks: every `K` units of block overshoot require more than
`1/K` units of deficit outside the block. -/
theorem totalProduct_gt_sqrtTwo_pow_of_scaled_uncompensated_block {b r : ℕ}
    {K badBlock R : ℝ} (hK : 0 < K) (hbad : K * (Real.sqrt 2) ^ r < badBlock)
    (hR : (1 / K) * (Real.sqrt 2) ^ b ≤ R) :
    (Real.sqrt 2) ^ (b + r) < badBlock * R := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2)
  have hpowb_pos : 0 < (Real.sqrt 2) ^ b := pow_pos hspos b
  have hscaled_pos : 0 < (1 / K) * (Real.sqrt 2) ^ b := by
    positivity
  have hbad_nonneg : 0 ≤ badBlock := by
    have hpos : 0 < K * (Real.sqrt 2) ^ r := mul_pos hK (pow_pos hspos r)
    exact le_of_lt (lt_trans hpos hbad)
  have hstrict : (K * (Real.sqrt 2) ^ r) * ((1 / K) * (Real.sqrt 2) ^ b) <
      badBlock * R := by
    exact mul_lt_mul hbad hR hscaled_pos hbad_nonneg
  have hleft : (K * (Real.sqrt 2) ^ r) * ((1 / K) * (Real.sqrt 2) ^ b) =
      (Real.sqrt 2) ^ (b + r) := by
    rw [pow_add]
    field_simp [ne_of_gt hK]
  rwa [hleft] at hstrict

/-- **Prize budget from the normalized `√2` per-level factor.**  This restates the existing corrected
x-gate capstone in the per-level-factor language: once the single open arithmetic gate supplies
`LevelRatioBoundNZ … √2`, the telescope and base estimate yield `C√(nL)`.  It deliberately contains no
proof of the gate; it is bookkeeping tying the empirical factor target `c≈√2` to the citable prize
budget. -/
theorem prizeBudget_of_sqrtTwo_perLevelFactor
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nontrivial F]
    {ψ : AddChar F ℂ} {G : Finset F} {ζ : F} {C L n : ℝ} {μ : ℕ}
    (hr : LevelRatioBoundNZ ψ G ζ μ (Real.sqrt 2))
    (h_dim : (Real.sqrt 2) ^ μ ≤ Real.sqrt n)
    (h_base : levelWorst ψ G ζ 0 ≤ C * Real.sqrt L)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hn : 0 ≤ n) :
    levelWorst ψ G ζ μ ≤ C * Real.sqrt (n * L) := by
  exact levelWorst_le_prize_budget_of_xgate hr h_dim h_base hC hL hn

end ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo

#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.perLevelFactor_le_two_of_dilate_le_two_mul
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.perLevelFactor_lt_two_iff_dilate_lt_two_mul
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.no_copeak_of_perLevelFactor_lt_two
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.sqrt_two_lt_two
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.telescope_variable_perLevelFactors
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.telescope_of_factorProduct_le
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.factorProduct_le_sqrtTwo_pow
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.telescope_of_pointwise_sqrtTwo_factors
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.exists_factor_gt_sqrtTwo_of_factorProduct_gt
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.factorProduct_gt_of_telescope_counterexample
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.exists_super_sqrtTwo_factor_of_telescope_counterexample
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.remainderProduct_lt_sqrtTwo_pow_pred_of_bad_rung
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.remainderProduct_lt_sqrtTwo_pow_of_two_bad_rungs
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.remainderProduct_lt_sqrtTwo_pow_of_superBudget_block
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.totalProduct_gt_sqrtTwo_pow_of_uncompensated_superBudget_block
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.totalProduct_gt_sqrtTwo_pow_of_scaled_uncompensated_block
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.prizeBudget_of_sqrtTwo_perLevelFactor
