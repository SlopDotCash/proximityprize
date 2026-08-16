/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.NormNum

/-!
# Round 14b (Issue #232) — the EXACT reach of the averaging method: the matching no-go

Round 14 (`DeltaStarConstantGapBelowCapacity`) proved the averaging list lower bound
`maxList(1−(k+t)/n) ≥ C(n,k+t)/q^t` beats the prize threshold `ε*·|F|` for `t ≲ n/258` (rate 1/2,
fields up to `2^256`). This file proves the **matching method no-go**: for near-maximal prize
fields (`q ≥ 2^255`), the averaging *bound itself* is provably below the threshold once
`t ≥ (n−127)/255` — because `C(n,a) ≤ 2^n` caps the numerator while `q^t` grows by `≥ 255` bits
per step.

Together the two results pin the averaging method's reach to the window

  `t/n ∈ [~1/258 works, ~1/255 provably exhausted]`   (rate 1/2, `q ≈ 2^256`),

a ~1% indeterminacy: **Round 14 is essentially optimal for the averaging route, and the route is
now closed as a method.** Any refutation deeper into the interior (larger `t`, smaller `δ`)
requires a non-averaging input (concentration — provably symmetry-impossible by the
depth-collapse wall — or genuinely new counting).

Honest scope: this bounds the averaging *lower bound* `C(n,k+t)/q^t`, not the true list size; the
true list could exceed the threshold deeper in — deciding that is (part of) the open prize.
-/

open Nat

namespace Round14bAveragingNoGo

/-- Binomial coefficients are at most `2^n` (one term of `∑_i C(n,i) = 2^n`). -/
theorem choose_le_two_pow {n a : ℕ} : n.choose a ≤ 2 ^ n := by
  by_cases ha : a ≤ n
  · calc n.choose a ≤ ∑ i ∈ Finset.range (n + 1), n.choose i :=
          Finset.single_le_sum (fun i _ => Nat.zero_le _)
            (Finset.mem_range.mpr (Nat.lt_succ_of_le ha))
      _ = 2 ^ n := Nat.sum_range_choose n
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_le ha)]
    exact Nat.zero_le _

/-- **The averaging-method no-go.** For near-maximal prize fields (`2^255 ≤ q`) and depth
`t` with `n + 128 ≤ 255·(t+1)` (i.e. `t ≥ (n−127)/255`), the averaging numerator is provably
below the prize threshold in the exact multiplicative form:

  `C(n, k+t) · 2^128 ≤ q^{t+1}`,

equivalently `C(n,k+t)/q^t ≤ q/2^128 = ε*·|F|` — the averaging lower bound cannot reach the
threshold. Combined with Round 14 (`crossover_rate_half`: the bound DOES exceed the threshold for
`258t + 193 ≤ n`), the averaging method's reach at `q ≈ 2^256` is pinned to within ~1%. -/
theorem averaging_reach_no_go {n k t q : ℕ}
    (hq : 2 ^ 255 ≤ q) (ht : n + 128 ≤ 255 * (t + 1)) :
    n.choose (k + t) * 2 ^ 128 ≤ q ^ (t + 1) := by
  calc n.choose (k + t) * 2 ^ 128
      ≤ 2 ^ n * 2 ^ 128 := Nat.mul_le_mul_right _ choose_le_two_pow
    _ = 2 ^ (n + 128) := by rw [← Nat.pow_add]
    _ ≤ 2 ^ (255 * (t + 1)) := Nat.pow_le_pow_right (by norm_num) ht
    _ = (2 ^ 255) ^ (t + 1) := by rw [← Nat.pow_mul]
    _ ≤ q ^ (t + 1) := Nat.pow_le_pow_left hq _

/-- **The ~1% pinch, concretely.** At `n = 2^20` and `q ≥ 2^255`: the averaging route *works* at
`t = 4063` (Round 14, `258·4063+193 ≤ 2^20`) and is *provably exhausted* at `t = 4112`
(`2^20 + 128 ≤ 255·4113`). The method's exact reach is trapped in `t ∈ (4063, 4112]` — a window
of width `49/2^20 < 0.005%` of the radius. -/
theorem reach_pinch_n_2_20 :
    (258 * 4063 + 193 ≤ 2 * 2 ^ 19) ∧ (2 ^ 20 + 128 ≤ 255 * (4112 + 1)) := by
  refine ⟨by norm_num, by norm_num⟩

end Round14bAveragingNoGo

#print axioms Round14bAveragingNoGo.choose_le_two_pow
#print axioms Round14bAveragingNoGo.averaging_reach_no_go
#print axioms Round14bAveragingNoGo.reach_pinch_n_2_20
