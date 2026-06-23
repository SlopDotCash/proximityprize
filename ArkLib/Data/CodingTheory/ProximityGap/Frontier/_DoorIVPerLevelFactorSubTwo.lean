/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVTwoDilateNoJointExtreme
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVXGatePrizeBudget

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

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
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.prizeBudget_of_sqrtTwo_perLevelFactor
