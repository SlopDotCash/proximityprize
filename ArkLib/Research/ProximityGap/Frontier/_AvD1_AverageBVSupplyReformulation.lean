/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Angle D1_average_BV: the Bombieri–Vinogradov average reformulation of the KKH26 good-prime
supply, and why it is supply-magnitude-neutral (issue #444 / #334 B3, s=128 row)

## The question

The s=128 row of the [KKH26] `δ*`-ceiling consumes the named hypothesis
`TZPrimeSupply n β supply` (`KKH26ThornerZaman.lean`): at least `supply` primes
`p ≡ 1 (mod n)` in the window `[n^β, 2n^β]`, with the EXACT smooth modulus `q = n = 2^μ·m`.
The real Thorner–Zaman PNT-in-APs ([TZ24] = arXiv:2108.10878, *Refinements to the prime
number theorem for arithmetic progressions*, Math. Z. 2024 — VERIFIED real) is uniform over
moduli, and its individual-modulus form for a single fixed `q = n` at a fixed `β` is exactly
the open analytic input. This angle asks: can an **average / positive-density** input, where
**Bombieri–Vinogradov (BV)** applies unconditionally, substitute for the per-`n`
fixed-modulus statement?

## The two facts proven here (pure arithmetic; the number theory is named-hypothesis)

The analysis splits the consumed hypothesis into two independent requirements:

* **(R-exist)** primes `p ≡ 1 (mod n)`, `p ∈ [n^β, 2n^β]`, exist; and
* **(R-many)** they NUMBER more than the bad-prime budget
  `B(n) = a² · log(s^{s/2}) / log(n^β)` of `kkh26_good_prime_of_TZ`.

**Logical adequacy of the average input.** [KKH26] is a *ceiling* (a counterexample
construction): it refutes a `∀ n` proximity claim by exhibiting a bad family along an
INFINITE sequence of `n`. The smooth modulus `n = 2^μ·m` has a free parameter `m`; sweeping
`m` makes `n` range over a positive-density set of moduli, and BV controls a DENSITY-1 set of
moduli `q ≤ x^{1/2-ε}` (here `x = n^β`, so `q = n ≪ n^{β/2}` is deep in range, and the window
`[n^β, 2n^β]` has length `~x`, not short). Hence BV yields (R-exist) with the SAME count
order `~ n^{β-1}` as TZ, for a density-1 set of `n` — and density-1 ⊋ "an infinite sequence",
so the average input is logically SUFFICIENT for the ceiling. This is encoded by
`AverageSupply` below (the BV-flavoured drop-in for `TZPrimeSupply`), which feeds the same
pigeonhole unchanged.

**Supply-magnitude neutrality (the refutation of the hope).** Both TZ and BV deliver supply of
the SAME order `Θ(n^{β-1})`. The bad-budget, with the in-tree resultant bound
`|Res| ≤ s^{s/2}` (`natAbs_resultant_cyclotomic_le`) and `m = a² = (2^r·C(2^{μ-1},r))²`
sum-polynomial pairs, is — for a FIXED bad-line degree `r` and `n = 2^μ` —
`B(n) ~ a²·(s/2)log s / (β log n) ~ n^{2r}·(n/2 · log n)/(β log n) = Θ(n^{2r+1})`.
So `supply > B(n)` reduces to `n^{β-1} > n^{2r+1}`, i.e. `β > 2r + 2`. Switching the analytic
input from TZ to BV changes neither side. **Therefore BV cannot help the s=128 row:** the
binding constraint is the bad-budget exponent `2r+2` (the `a²` collision resultants of size
`s^{s/2}`), not the prime supply, and the prize thin regime `β ≈ 4` (with `r ≥ 2`) sits below
`2r+2 ≥ 6`.

`exponent_supply_budget_iff` proves the clean exponent comparison powering this conclusion;
`average_supply_neutral` records that the pigeonhole admissibility is identical for the two
inputs.

## References

* [KKH26] Krachun, Kazanin, Haböck, *Failure of proximity gaps close to capacity*, ePrint
  2026/782 (Lemma 2). In-tree: `KKH26ThornerZaman.lean`, `KKH26PolyFieldCeiling.lean`.
* [TZ24] Thorner, Zaman, *Refinements to the prime number theorem for arithmetic
  progressions*, Math. Z. 307 (2024), arXiv:2108.10878 (VERIFIED real).
* Bombieri–Vinogradov theorem (Bombieri 1965; A. I. Vinogradov 1965): mean value of the
  error in PNT-in-APs over moduli `q ≤ x^{1/2-ε}`. Issue #334 / #444.
-/

namespace ArkLib.ProximityGap.AvD1

open Real

/-! ### The average / Bombieri–Vinogradov supply input (named hypothesis, never an axiom) -/

/-- **The average/positive-density supply hypothesis** — the Bombieri–Vinogradov drop-in for
`TZPrimeSupply`. It asserts only the cardinality bound that the KKH26 pigeonhole consumes
(`supply ≤ #window`), but is intended to be instantiated *unconditionally on average* over the
free modulus parameter `m` (BV), rather than per-`n` (TZ). Structurally identical to
`TZPrimeSupply`; the distinction is the intended instantiation, recorded in the module
docstring. Encoded abstractly: `windowCard` is whatever the analytic input certifies, and the
hypothesis is the same `supply ≤ windowCard`. -/
structure AverageSupply (windowCard supply : ℕ) : Prop where
  /-- The window contains at least `supply` good primes (BV density-1 instantiation). -/
  le_card : supply ≤ windowCard

/-- **Pigeonhole admissibility is input-agnostic.** Whatever certifies `supply ≤ windowCard`
(TZ per-`n` OR BV on-average), if `supply` strictly exceeds the bad-prime budget `badBudget`,
then the good set `windowCard - badBudget` is nonempty. This is the *only* property of the
analytic input the KKH26 pigeonhole (`kkh26_good_prime_of_TZ`) uses, so the BV input is a
valid drop-in. -/
theorem average_supply_neutral {windowCard supply badBudget : ℕ}
    (hsup : AverageSupply windowCard supply) (hlt : badBudget < supply) :
    0 < windowCard - badBudget := by
  have : badBudget < windowCard := lt_of_lt_of_le hlt hsup.le_card
  omega

/-! ### Supply-magnitude neutrality: the binding constraint is the budget exponent -/

/-- **The exponent comparison.** For `n ≥ 2` and real exponents `e₁, e₂`, the supply
`n^{e₁}` strictly exceeds the budget `n^{e₂}` iff `e₂ < e₁`. With `e₁ = β - 1` (the order of
BOTH the TZ and BV supplies) and `e₂ = 2r + 1` (the order of the KKH26 bad-budget at fixed
bad-line degree `r`), this is the clean statement that the s=128 row needs `β - 1 > 2r + 1`,
i.e. `β > 2r + 2` — a condition on the budget, untouched by the choice of analytic input. -/
theorem exponent_supply_budget_iff {n : ℕ} (hn : 2 ≤ n) (e₁ e₂ : ℝ) :
    (n : ℝ) ^ e₂ < (n : ℝ) ^ e₁ ↔ e₂ < e₁ := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact Real.rpow_lt_rpow_left_iff hn1

/-- **Supply-magnitude neutrality (headline of the angle).** Suppose the analytic input
(TZ *or* BV) supplies `≥ n^{β-1}` good primes and the KKH26 bad-budget is `≤ n^{2r+1}` (the
fixed-`r`, `m = a² ~ n^{2r}`, `M = s^{s/2}` regime). Then the good-prime existence the ceiling
needs holds iff `β > 2r + 2` — **independent of whether the supply came from TZ or from BV**,
since both have the identical order `n^{β-1}`. Hence the average/BV reformulation does NOT
move the s=128 wall: the binding obstruction is the bad-budget exponent, not the prime supply.

(Formally: with the supply lower bound `supplyR` and budget upper bound `budgetR` of the stated
orders, the pigeonhole-feeding strict inequality `budgetR < supplyR` is *equivalent* to the
exponent gap `2r + 2 < β`.) -/
theorem average_supply_neutral_exponent {n r : ℕ} (β : ℝ) (hn : 2 ≤ n)
    (supplyR budgetR : ℝ)
    (hsupply : supplyR = (n : ℝ) ^ (β - 1))
    (hbudget : budgetR = (n : ℝ) ^ ((2 * r : ℝ) + 1)) :
    budgetR < supplyR ↔ (2 * (r : ℝ) + 2) < β := by
  subst hsupply hbudget
  rw [exponent_supply_budget_iff hn]
  constructor <;> intro h <;> linarith

/-- **Corollary — the prize thin regime fails the budget for every bad-line degree `r ≥ 1`.**
At `β = 4` (the `n ≈ p^{1/4}` thin regime central to the prize) and any fixed bad-line degree
`r ≥ 1`, the budget order `n^{2r+1}` is NOT exceeded by the supply order `n^{β-1} = n^3`,
because `2r + 2 ≥ 4 = β` fails the strict gap. The average/BV input cannot rescue this. -/
theorem prize_regime_budget_fails {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r)
    (supplyR budgetR : ℝ)
    (hsupply : supplyR = (n : ℝ) ^ ((4 : ℝ) - 1))
    (hbudget : budgetR = (n : ℝ) ^ ((2 * r : ℝ) + 1)) :
    ¬ (budgetR < supplyR) := by
  rw [average_supply_neutral_exponent (4 : ℝ) hn supplyR budgetR hsupply hbudget]
  have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  push_neg
  linarith

end ArkLib.ProximityGap.AvD1

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.AvD1.average_supply_neutral
#print axioms ArkLib.ProximityGap.AvD1.exponent_supply_budget_iff
#print axioms ArkLib.ProximityGap.AvD1.average_supply_neutral_exponent
#print axioms ArkLib.ProximityGap.AvD1.prize_regime_budget_fails
