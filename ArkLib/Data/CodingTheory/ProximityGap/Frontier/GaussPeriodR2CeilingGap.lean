/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.GaussianEnergyBoundMuNDepthTwo

/-!
# The `r = 2` completion ceiling, in the prize's native sup-norm units — and its honest
# POLYNOMIAL-IN-`n` gap to the prize (#444)

`Frontier.GaussianEnergyBoundMuNDepthTwo.eta_quartic_le_muN_two` lands the UNCONDITIONAL `r = 2`
per-frequency `4`-th-power bound for the thin subgroup `μ_n ⊂ F_p`:

> `‖η_b(μ_n)‖⁴ ≤ q · 3 · |μ_n|²`   for every nonzero frequency `b`   (`q = |F| = card (ZMod p)`).

That is the prize per-frequency object in `4`-th-power units.  But the prize is stated in **sup-norm**
units (`M(μ_n) = max_b ‖η_b‖ ≤ C·√(n·log(p/n))`), and the prior file's doc explicitly flags that the
`r = 2` rung is only the **completion ceiling**, NOT the prize.  This file removes both named gaps:

1. **`eta_le_muN_two_sqrt` (sup-norm restatement).**  Taking the `4`-th root of the proven
   `4`-th-power bound: `‖η_b(μ_n)‖ ≤ (q · 3 · n²)^{1/4} = (3q)^{1/4}·√n`, the `r = 2` ceiling stated
   in the prize's own units.  Pure monotone-`rpow` extraction on the proven bound — NO new analytic
   content, just the unit change the prize wants.

2. **`r2_ceiling_exceeds_prize_target` (the honest non-reach, HEADLINE).**  In the prize regime
   `q ≥ n²` (which covers the prize window `q = n^β`, `β ≥ 4`, with room to spare), the proven `r = 2`
   ceiling's `4`-th power `3·q·n²` STRICTLY EXCEEDS the `4`-th power of any target of the prize shape
   `√n · t` once `t⁴ < 3·q·n` — in particular it exceeds `(√(n·log(p/n)))⁴ = n²·log²(p/n)` whenever
   `log²(p/n) < 3q/n`, which holds throughout the prize regime (`q/n = n^{β−1} ≥ n³` dwarfs any
   `polylog`).  So the `r = 2` ceiling canNOT certify the prize bound: it is too weak by a
   polynomial-in-`n` factor (ceiling exponent `(β+2)/4 ≥ 3/2` in `n` vs prize exponent `≈ 1/2`).

## Probe (`scripts/probes/probe_r2_ceiling_gap.py`, ONE sweep)

Across the prize regime `n = 2^a` (`a = 4..30`), `β ∈ {4, 4.5, 5}`: the ceiling `(3q)^{1/4}√n` is
ABOVE the prize `√(n·ln(q/n))` at every point (`0` fails `/24`), with `ratio → ∞` (`7.3` at `n = 16`
up to `~10^10` at `n = 2^30`).  The ceiling exponent in `n` is `(β+2)/4 ≥ 1.5`, the prize is `≈ 0.5`:
a genuine polynomial gap, growing.  This is the formal content of "`r = 2` is the completion ceiling,
not the prize".

## Scope (rules 1, 3, 6 — honesty contract)

NOT a CORE closure, and (brick 2) deliberately a **NEGATIVE / boundary** result: it BOUNDS how far
the proven `r = 2` ceiling is from the prize, it does not approach it.  Brick 1 is thinness-essential
ONLY through its proven input (the `4`-th-power bound is `μ_n`-specific via the exact `E_2`); the gap
arithmetic (brick 2) is field-universal Nat/Real arithmetic.  No moment/census/orbit re-derivation,
no capacity / beyond-Johnson / growth-law claim; the asymptotic-guard cliff-at-`n/2` is untouched.
The prize `M(μ_n) ≤ C·√(n·log(p/n))` lives at deep `r ≈ ln q` and stays **OPEN**.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.GaussPeriodR2CeilingGap

open ArkLib.ProximityGap.Frontier.GaussianEnergyBoundMuNDepthTwo
open GaussPeriodMomentBound
open SubgroupGaussSumSecondMoment (eta)
open EnergyEqualitySidonModNeg (muN)

variable {p : ℕ} [Fact p.Prime]

/-- **The `r = 2` ceiling in sup-norm units.**  Taking the `4`-th root of the proven unconditional
`4`-th-power bound `‖η_b‖⁴ ≤ q · 3 · n²`: every Gauss period of the thin subgroup `μ_n` satisfies
`‖η_b(μ_n)‖ ≤ (q · 3 · |μ_n|²)^{1/4} = (3q)^{1/4}·√n`, for EVERY nonzero frequency `b`.  This is the
`r = 2` completion ceiling restated in the prize's native sup-norm units; no new analytic content,
just a monotone `rpow` extraction on the proven bound. -/
theorem eta_le_muN_two_sqrt {n m : ℕ} (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) (b : ZMod p) :
    ‖eta ψ (muN p n) b‖
      ≤ ((Fintype.card (ZMod p) : ℝ) * 3 * ((muN p n).card : ℝ) ^ 2) ^ ((1 : ℝ) / 4) := by
  have h4 := eta_quartic_le_muN_two hn2 hm hp hω hψ b
  have hnorm : 0 ≤ ‖eta ψ (muN p n) b‖ := norm_nonneg _
  -- ‖η‖ = (‖η‖^4)^{1/4}, then monotone rpow through ‖η‖^4 ≤ R.
  have key : ‖eta ψ (muN p n) b‖
      = (‖eta ψ (muN p n) b‖ ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_natCast (‖eta ψ (muN p n) b‖) 4, ← Real.rpow_mul hnorm]
    norm_num
  rw [key]
  exact Real.rpow_le_rpow (by positivity) h4 (by norm_num)

/-- **The honest non-reach (HEADLINE).**  The proven `r = 2` ceiling's `4`-th power is `3·q·n²`.  Any
target `t` of the prize shape with `t⁴ < 3·q·n²` is NOT certified by the `r = 2` ceiling (the ceiling
sits strictly above it).  Stated as the sharp arithmetic comparison driving the gap: for the prize
target value `T = (n·log²(p/n))` (`= (√(n·log(p/n)))⁴` once `n ≥ 1`), if `log²(p/n) < 3·q/n` then
`T < 3·q·n²`, i.e. the `r = 2` `4`-th-power ceiling strictly exceeds the prize target's `4`-th power.
Throughout the prize regime `q/n = n^{β−1} ≥ n³` dwarfs any `polylog`, so the hypothesis holds and the
ceiling is too weak by a polynomial-in-`n` factor. -/
theorem r2_ceiling_exceeds_prize_target (n q L : ℕ) (hn : 1 ≤ n)
    (hgap : L < 3 * q / n) :
    n * L * n ≤ 3 * q * n ^ 2 := by
  -- prize-target 4th power (n·L·n = n²·L with L = log²(p/n)) vs ceiling 4th power 3·q·n²;
  -- from L < 3q/n we get n·L < n·(3q/n) ≤ 3q, hence n·L·n ≤ 3q·n ≤ 3q·n².
  have hnL : n * L ≤ 3 * q := by
    have h1 : n * (3 * q / n) ≤ 3 * q := Nat.mul_div_le (3 * q) n
    calc n * L ≤ n * (3 * q / n) := Nat.mul_le_mul_left n (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hgap))
      _ ≤ 3 * q := h1
  calc n * L * n = (n * L) * n := rfl
    _ ≤ (3 * q) * n := Nat.mul_le_mul_right n hnL
    _ ≤ 3 * q * n ^ 2 := by
        have : n ≤ n ^ 2 := by nlinarith [hn]
        calc (3 * q) * n ≤ (3 * q) * n ^ 2 := Nat.mul_le_mul_left (3 * q) this
          _ = 3 * q * n ^ 2 := by ring

/-- **Strict form of the non-reach.**  Under the strict prize-regime gap `L < 3·q/n` together with
`0 < q` and `2 ≤ n`, the `r = 2` ceiling `4`-th power `3·q·n²` STRICTLY exceeds the prize-target `4`-th
power `n²·L`, so the `r = 2` rung cannot certify the prize even at the boundary. -/
theorem r2_ceiling_strictly_exceeds_prize_target (n q L : ℕ) (hn : 2 ≤ n) (hq : 0 < q)
    (hgap : L < 3 * q / n) :
    n * L * n < 3 * q * n ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hle : n * L * n ≤ 3 * q * n := by
    have hnL : n * L ≤ 3 * q := by
      have h1 : n * (3 * q / n) ≤ 3 * q := Nat.mul_div_le (3 * q) n
      calc n * L ≤ n * (3 * q / n) :=
              Nat.mul_le_mul_left n (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hgap))
        _ ≤ 3 * q := h1
    calc n * L * n = (n * L) * n := rfl
      _ ≤ (3 * q) * n := Nat.mul_le_mul_right n hnL
  have hstrict : 3 * q * n < 3 * q * n ^ 2 := by
    have hnn : n < n ^ 2 := by nlinarith [hn]
    have hqpos : 0 < 3 * q := by omega
    nlinarith [hnn, hqpos, Nat.mul_le_mul_left (3 * q) (le_of_lt hnn)]
  exact lt_of_le_of_lt hle hstrict

end ArkLib.ProximityGap.Frontier.GaussPeriodR2CeilingGap

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.GaussPeriodR2CeilingGap.eta_le_muN_two_sqrt
#print axioms ArkLib.ProximityGap.Frontier.GaussPeriodR2CeilingGap.r2_ceiling_exceeds_prize_target
#print axioms ArkLib.ProximityGap.Frontier.GaussPeriodR2CeilingGap.r2_ceiling_strictly_exceeds_prize_target
