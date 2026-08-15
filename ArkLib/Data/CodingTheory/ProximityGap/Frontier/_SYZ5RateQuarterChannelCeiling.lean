/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Defs
import Mathlib.Data.NNReal.Basic

/-!
# SYZ5: the degenerate-channel ceiling does **not** sharpen at rate `1/4` (issue #466 / #507)

This file records the honest outcome of porting the SYZ degenerate-subset channel (SYZ1 probe →
SYZ2 pencil → SYZ3 witness → SYZ4 rate-`1/2` ceiling `11/32 − 2^-30`) to production rate `1/4`
(`n = 2^30`, `k = 2^28`, first certified prize field `P = 2^30·(2^128 + 192) + 1`).

**The prediction, and why it fails.**  SYZ4's kb note predicted a rate-`1/4` analogue at the
channel infimum `(1−ρ)/(2−ρ) = 3/7 ≈ 0.4286`, strictly below the current unconditional in-tree
rate-`1/4` ceiling

  `mcaDeltaStar (evalCode g (2^30) (2^28 − 1)) epsStar ≤ 480946859/2^30 = 43/96 + 1/(3·2^30) ≈ 0.44792`

(landed in `Frontier/_P1RateQuarterAdjacentExactPin.lean`, theorem
`canonical_mcaDeltaStar_le_common_delta`, the common-factor construction).  **That prediction is
unattainable.**  The infimum `(1−ρ)/(2−ρ)` is a *continuous-`D`* optimum, achieved only at the
non-integer subset count `D = (1−ρ)/((1−ρ)²/(2−ρ)) = 7/3`.  With a *whole number* of degenerate
subsets the achievable floor is

  `min_{D ∈ ℕ} max( 1/D , (1−ρ)(1 − 1/D) )`,

and at `ρ = 1/4` this equals `1/2` for both admissible integers `D = 2` and `D = 3` (and grows for
`D ≥ 4`).  Since `1/2 > 43/96`, **the SYZ degenerate channel cannot beat the current rate-`1/4`
ceiling**; it produces at best a *weaker* one.

**Why `1/2` is a hard floor at rate `1/4`.**  Write `c_j = n − t_j` for the bad-scalar block count
(complement) of degenerate subset `j`, with agreement `t_j = core + a_j`: a shared vanishing `core`
(free agreement, `Z_core = 0`) plus a private zero-multiplier region `a_j`.  Two structural facts
pin the radius:

* **degree cap** (rate `1/4`): the vanishing-core codeword `c_j·Z_core` must have degree below the
  RS dimension `k = 2^28 = n/4`, so `4·core ≤ n`;
* **region disjointness**: the private regions live in the non-core, so `core + Σ_j a_j ≤ n`.

For `D = 3` (the optimal integer count) these two facts *alone* force `Σ_j c_j = 3n − 3·core − Σa_j
≥ 3n − 3(n/4) − (n − core) = 2n − 2·core ≥ 3n/2`, so the largest complement is at least the average
`≥ n/2` — independently of any budget hypothesis.  For `D ≤ 2` the same conclusion follows from the
`ε*`-budget (`Σ_j c_j > n`).  Hence every valid integer-`D` degenerate configuration has a subset
whose bad-scalar radius is `≥ 1/2 > 43/96`.

**What is landed here.**  The two structural no-go lemmas (`D = 3`, budget-free; and `D = 2`, from
budget), both axiom-clean pure-`ℕ` facts, together with the rational comparison `43/96 < 1/2`.
These certify that the degenerate-channel *radius reduction* — the very object SYZ2/SYZ3/SYZ4
feed to `mcaDeltaStar_le_of_bad` — cannot land below `1/2` at rate `1/4`, so wiring it through the
same operational consumer would only reprove a ceiling strictly *weaker* than the extant
`43/96 + 1/(3·2^30)`.  No production `mcaDeltaStar` ceiling is claimed, precisely because the
channel does not sharpen the existing one.

**Untouched.**  The unconditional rate-`1/4` good-side floor `3/8` (`_P1RateQuarterOperationalBracket`,
`threeEighths_le_rateQuarter_mcaDeltaStar`) and the CORE exact pin remain as they were: this file
is a barrier, not a pin.  (Consistency check: the naive `D = 3, 64-block, core = 15` rung would give
radius `33/64 ≈ 0.516`; a finer grading pushes it toward `1/2⁺` — both above the `3/8` floor and
above `43/96`, so no contradiction and no progress.)

Axiom-clean (pure `ℕ`/`ℚ` arithmetic; `#print axioms` below).  No `sorry`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.SYZ5RateQuarterChannelCeiling

/-! ## The structural no-go at rate `1/4` -/

/-- **Rate-`1/4` channel no-go, `D = 3` (the optimal integer subset count).**

For three degenerate subsets with shared vanishing `core` and private regions `a₀, a₁, a₂`,
subject only to the rate-`1/4` degree cap (`4·core ≤ n`) and region disjointness
(`core + a₀ + a₁ + a₂ ≤ n`), at least one subset's complement (bad-scalar block count)
`cⱼ = n − core − aⱼ` is at least `n/2`.  Its predecessor radius is therefore `≥ 1/2`.

No `ε*`-budget hypothesis is needed: the degree cap plus disjointness already force it. -/
theorem rateQuarter_channel_D3_radius_ge_half
    {n core a0 a1 a2 : ℕ}
    (hcore : 4 * core ≤ n)
    (hdisj : core + a0 + a1 + a2 ≤ n) :
    n ≤ 2 * (n - core - a0) ∨ n ≤ 2 * (n - core - a1) ∨ n ≤ 2 * (n - core - a2) := by
  omega

/-- **Rate-`1/4` channel no-go, `D = 2`.**

With only two degenerate subsets, meeting the `ε*`-budget (total bad-scalar block count exceeds
`n`) forces one complement to be at least `n/2`, so the predecessor radius is again `≥ 1/2`.
(The degree cap is not even needed here.) -/
theorem rateQuarter_channel_D2_radius_ge_half
    {n core a0 a1 : ℕ}
    (hbudget : n < (n - core - a0) + (n - core - a1)) :
    n ≤ 2 * (n - core - a0) ∨ n ≤ 2 * (n - core - a1) := by
  omega

/-- **General-`D` structural lower bound on the total bad-scalar block count.**

For `D` degenerate subsets with disjoint private regions inside the non-core, the total complement
`Σⱼ cⱼ` is at least `(D−1)·(n − core)`.  Combined with the degree cap `core ≤ n/4` this is the
`Σⱼ cⱼ ≥ (D−1)·(3n/4)` that drives the `1/2` floor at every `D ≥ 3` (via `Σⱼ cⱼ / D ≥ n/2`). -/
theorem total_complement_lower_bound
    {D n core : ℕ} {a : Fin D → ℕ}
    (hdisj : (∑ j, a j) + core ≤ n) :
    (D - 1) * (n - core) ≤ ∑ j, (n - core - a j) := by
  -- each private region fits in the non-core, so the truncated subtraction is exact
  have hpt : ∀ j, a j ≤ n - core := by
    intro j
    have : a j ≤ ∑ i, a i := Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hid : ∑ j, ((n - core - a j) + a j) = D * (n - core) := by
    rw [Finset.sum_congr rfl (fun j _ => by have := hpt j; omega :
        ∀ j ∈ (Finset.univ : Finset (Fin D)), (n - core - a j) + a j = n - core)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Finset.sum_add_distrib] at hid
  have hle : (∑ j, a j) ≤ n - core := by omega
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; simp
  · have hstep : (D - 1) * (n - core) + (n - core) = D * (n - core) := by
      rcases Nat.exists_eq_succ_of_ne_zero hD.ne' with ⟨D', rfl⟩
      simp [Nat.succ_sub_one, Nat.succ_mul]
    -- generalize the two products so omega sees only linear atoms
    generalize hQ : (D - 1) * (n - core) = Q at *
    generalize hPp : D * (n - core) = Pp at *
    omega

/-! ## The rational verdict: `1/2` is above the current ceiling -/

/-- The current unconditional in-tree rate-`1/4` production ceiling
(`_P1RateQuarterAdjacentExactPin.canonical_mcaDeltaStar_le_common_delta`,
`= 480946859/2^30 = 43/96 + 1/(3·2^30)`) is strictly below `1/2`. -/
theorem currentCeiling_lt_half :
    (480946859 : ℚ) / 2 ^ 30 < 1 / 2 := by norm_num

/-- A fortiori the exact common-factor endpoint `43/96 + 1/(3·2^30)` is below `1/2`. -/
theorem fortyThree_over_ninetySix_correction_lt_half :
    (43 : ℚ) / 96 + 1 / (3 * 2 ^ 30) < 1 / 2 := by norm_num

/-- **The SYZ5 verdict.**  The channel infimum `(1−ρ)/(2−ρ) = 3/7` at `ρ = 1/4` is realized only at
the non-integer subset count `D = 7/3`; every integer-`D` rung has radius `≥ 1/2`, and `1/2` is
strictly above the current rate-`1/4` ceiling `480946859/2^30`.  Hence the degenerate channel does
**not** sharpen the rate-`1/4` ceiling. -/
theorem channel_does_not_sharpen_rateQuarter_ceiling :
    (480946859 : ℚ) / 2 ^ 30 < 1 / 2 ∧ ((3 : ℚ) / 7 < 1 / 2) := by
  refine ⟨currentCeiling_lt_half, by norm_num⟩

end ArkLib.ProximityGap.Frontier.SYZ5RateQuarterChannelCeiling

-- Axiom audit (expected: no axioms, or propext/Classical.choice/Quot.sound only)
#print axioms
  ArkLib.ProximityGap.Frontier.SYZ5RateQuarterChannelCeiling.rateQuarter_channel_D3_radius_ge_half
#print axioms
  ArkLib.ProximityGap.Frontier.SYZ5RateQuarterChannelCeiling.rateQuarter_channel_D2_radius_ge_half
#print axioms
  ArkLib.ProximityGap.Frontier.SYZ5RateQuarterChannelCeiling.total_complement_lower_bound
#print axioms
  ArkLib.ProximityGap.Frontier.SYZ5RateQuarterChannelCeiling.channel_does_not_sharpen_rateQuarter_ceiling
