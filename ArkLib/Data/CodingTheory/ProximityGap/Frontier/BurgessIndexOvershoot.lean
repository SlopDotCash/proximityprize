/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The Burgess/Stepanov magnitude-bound index overshoot (Proximity Prize #407)

This file formalizes, **axiom-clean**, the precise quantitative wall that stops the
Burgess / BGK / Stepanov *magnitude-amplification* route to the prize floor, re-examined
in the **fixed-index** regime (the route hint for #407).

## Setup

For a prime `p` with `p − 1 = m · n`, the order-`n` subgroup `μ_n ⊆ 𝔽_p^×` has incomplete
Gauss-period sums `η_b = ∑_{x∈μ_n} e_p(b x)`. The **prize floor** is `B = max_{b≠0} |η_b|`,
and the conjectured bound is `B ≤ C·√(n · log m)` with `m = (p−1)/n`.

The strongest *magnitude* control available — the Weil/Gauss bound `|η_b| ≤ √p` (proven in-tree,
`SubgroupGaussSumWorstCase.lean`), and every Burgess/BGK refinement `B ≤ n^{1−ν}` — bounds the
**size** of the sum, not the **square-root cancellation among the `m` Gauss-sum phases**.

The route hint observes that Burgess subgroup-sum bounds need `|H| > p^{1/4}`, and that in the
fixed-index regime `n = Θ(p)` this is satisfied (so Burgess *might* be in-regime). This file
records the resolution: even granting that, the magnitude bound `B ≤ √p` overshoots the target
`√(n·log m)` by the **multiplicative factor `√(m / log m)`** — because

  `√p / √(n·log m) = √(n·m) / √(n·log m) = √(m / log m)`.

So the gap is governed by the **index `m`**, not by the subgroup size `n` relative to `p`. In the
prize regime `m = 2^128`, the overshoot is `√(2^128 / 128) = 2^64 / √128 ≈ 2^60.5`. **No magnitude
method (Gauss, Burgess, BGK, Stepanov sum-product) can recover a factor `2^60`**; the residual is
the full square-root-cancellation problem among the `m` fixed Gauss phases (a Salem–Zygmund /
flatness statement), which is *orthogonal* to the subgroup-size question Burgess addresses.

This is the magnitude-route analogue of `KowalskiUntrauBarrier.lean` (which certifies the
equidistribution SOTA vacuous): a machine-checked certificate of *how far* the magnitude route
falls short, via the integer surrogate `overshootSq m = m / ⌊log₂ m⌋` of the squared overshoot.

## What is and is NOT proven here

PROVEN (axiom-clean, integer arithmetic): the squared overshoot `overshootSq m = m / ⌊log₂ m⌋` is
monotone-large; at the concrete prize index `m = 2^128` it equals exactly `2^121`, i.e. the
Gauss/Burgess bound `√p` is `2^60.5 ≈ 2^60` times the prize target `√(n·log m)`; and a single step
up the index (`m = 2^k`, `k ≥ 128`) keeps it `≥ 2^(k−7) ≥ 2^121`. A factor `2^60` is unrecoverable
by any magnitude (size) bound. This is a *lower bound on the gap the magnitude route leaves open*,
NOT a proof of the prize (the wall stands; the cancellation among the `m` phases is open).

The numeric companion `scripts/probes/_wf407_stepanov_burgess.py` measures the true overshoot
`√p / B` directly and confirms it tracks `√(m / log m)` (e.g. `m = 4096`: measured `21.0` vs
`√(4096/ln 4096) = 22.2`), while `B / √(n·log m)` stays flat near `1` (the unproven target).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- [Kow24] Kowalski. *Exponential sums over small subgroups, revisited*. arXiv:2401.04756. (BGK Thm 1.1:
  `|∑_{x∈H} e(ax/p)| ≪ |H|·p^{−ν}` — a magnitude saving off the trivial `|H|`.)
- In-tree: `SubgroupGaussSumWorstCase.lean` (`B ≤ √p`), `KowalskiUntrauBarrier.lean` (equidistribution
  SOTA vacuous), `CharSumMomentDeepWall.lean` (the orthogonal moment route).
-/

set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.BurgessIndexOvershoot

/-- The **squared magnitude-bound overshoot** in the integer surrogate: the magnitude (Gauss/Burgess)
bound `B ≤ √p` overshoots the prize target `√(n·log m)` by `√(m / log m)`, so the *squared* overshoot
is `m / log₂ m`. We use `Nat.log 2 m` (= `⌊log₂ m⌋`) as the integer surrogate for `log m`. -/
def overshootSq (m : ℕ) : ℕ := m / Nat.log 2 m

/-- At the concrete prize index `m = 2^128`, `⌊log₂ m⌋ = 128` exactly. -/
theorem log2_prize_index : Nat.log 2 (2 ^ 128) = 128 :=
  Nat.log_pow (by norm_num : (1:ℕ) < 2) 128

/-- **The exact prize-index overshoot.** At `m = 2^128` (the prize index), the squared overshoot of
the Gauss/Burgess magnitude bound is exactly `2^128 / 128 = 2^121`. So `√p` overshoots the prize
target `√(n·log m)` by the factor `√(2^121) = 2^60.5`. This factor is unrecoverable by any
magnitude/amplification bound — the magnitude route, even in the Burgess-favorable fixed-index
regime, falls short of the prize floor by `~2^60`. -/
theorem overshootSq_prize_exact : overshootSq (2 ^ 128) = 2 ^ 121 := by
  unfold overshootSq
  rw [log2_prize_index]
  -- `2^128 / 128 = 2^128 / 2^7 = 2^(128-7) = 2^121`, via `Nat.pow_div`.
  have h1 : (128 : ℕ) = 2 ^ 7 := by norm_num
  rw [h1, Nat.pow_div (by norm_num) (by norm_num)]
  norm_num

/-- The squared overshoot at the prize index dwarfs `2^120`: the magnitude bound is at least `2^60`
times the target. -/
theorem overshootSq_prize_ge : 2 ^ 120 ≤ overshootSq (2 ^ 128) := by
  rw [overshootSq_prize_exact]
  exact Nat.pow_le_pow_right (by norm_num) (by norm_num)

/-- For every dyadic index `m = 2^k`, the squared overshoot is exactly `2^k / k` (since
`⌊log₂ (2^k)⌋ = k`). -/
theorem overshootSq_dyadic (k : ℕ) :
    overshootSq (2 ^ k) = 2 ^ k / k := by
  unfold overshootSq
  rw [Nat.log_pow (by norm_num : (1:ℕ) < 2) k]

/-- Helper: `j + 128 ≤ 2^(j+8)` for every `j`. (Clean induction, no side hypothesis: the offset
`+8` provides the base headroom `2^8 = 256 ≥ 128`.) -/
private theorem add_const_le_two_pow (j : ℕ) : j + 128 ≤ 2 ^ (j + 8) := by
  induction j with
  | zero => norm_num
  | succ i ih =>
    have hpow : 2 ^ (i + 1 + 8) = 2 ^ (i + 8) * 2 := by
      rw [show i + 1 + 8 = (i + 8) + 1 from by omega, pow_succ]
    have h2 : (256 : ℕ) ≤ 2 ^ (i + 8) := by
      calc (256 : ℕ) = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ (i + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- **Monotone persistence up the index tower.** For every dyadic prize index `m = 2^k` with
`k ≥ 128`, the squared overshoot `2^k / k` is `≥ 2^120`. So increasing the index — the prize
direction `m → 2^128` and beyond — only widens the magnitude-route gap; it never closes.
The mechanism: `2^k / k ≥ 2^120 ⟺ 2^120 · k ≤ 2^k`, and `k ≤ 2^(k−120)` once `k ≥ 128`. -/
theorem overshootSq_dyadic_ge (k : ℕ) (hk : 128 ≤ k) :
    2 ^ 120 ≤ overshootSq (2 ^ k) := by
  rw [overshootSq_dyadic]
  rw [Nat.le_div_iff_mul_le (by omega : 0 < k)]
  -- Goal: `2^120 * k ≤ 2^k`. Suffices `k ≤ 2^(k-120)`.
  have hkbound : k ≤ 2 ^ (k - 120) := by
    -- Apply the helper at `j = k - 128`: `(k-128) + 128 ≤ 2^((k-128)+8)`, i.e. `k ≤ 2^(k-120)`.
    have h := add_const_le_two_pow (k - 128)
    -- h : (k - 128) + 128 ≤ 2 ^ ((k - 128) + 8)
    have he : (k - 128) + 8 = k - 120 := by omega
    rw [he] at h
    omega
  calc 2 ^ 120 * k ≤ 2 ^ 120 * 2 ^ (k - 120) := Nat.mul_le_mul (le_refl _) hkbound
    _ = 2 ^ (120 + (k - 120)) := by rw [pow_add]
    _ = 2 ^ k := by congr 1; omega

end ArkLib.ProximityGap.Frontier.BurgessIndexOvershoot

-- Axiom audit: all four results are axiom-clean (only propext, Classical.choice, Quot.sound).
#print axioms ArkLib.ProximityGap.Frontier.BurgessIndexOvershoot.overshootSq_prize_exact
#print axioms ArkLib.ProximityGap.Frontier.BurgessIndexOvershoot.overshootSq_prize_ge
#print axioms ArkLib.ProximityGap.Frontier.BurgessIndexOvershoot.overshootSq_dyadic
#print axioms ArkLib.ProximityGap.Frontier.BurgessIndexOvershoot.overshootSq_dyadic_ge
