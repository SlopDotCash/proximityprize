/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# A8 — the direct sub-Gaussian tail of `η_b`: the *effective-variance* monotonicity (#444)

## The A8 question, sharpened

The open core asks for the saddle energy bound
`A_r := Σ_{b≠0} ‖η_b‖^{2r} = q·E_r − n^{2r}  ≤  (q−1)·Wick_r`, `Wick_r = (2r−1)‼·n^r`,
at depth `r ≈ ln q`. A8 attempts to *derive* it from a sub-Gaussian tail
`P(‖η_b‖ > t√n) ≤ 2·exp(−c t²)` via cumulant-to-tail.

A companion file (`_A8SubGaussianCumulantSignChange.lean`) settled the **energy** route: the
cumulants of `W := ‖η_b‖²` change sign at `j ≈ 0.72 ln q`, so a Chernoff/MGF bound on the energy
MGF cannot reach the saddle. THIS file attacks the *other half* of A8 — the cumulants and tail of
the **magnitude `η_b` itself** (real, since `−1 ∈ μ_n`) — and isolates a genuinely new, *favorable*
exact structure that the cumulant route cannot see, plus the exact step that fails as `n → 2^30`.

## Two exact facts about `η_b` (real RV over `b ≠ 0`), computed from the additive energies

Write `η_b = Σ_{x∈μ_n} e_p(b x)`. Because `μ_n` is closed under negation, `η_b ∈ ℝ`. Its moments
are exact integers: `Σ_{all b} η_b^k = p·N_k` with `N_k := #{(x_1,…,x_k)∈μ_n^k : Σ x_i ≡ 0}`, and
the even ones recover the energies, `Σ_{b≠0} η_b^{2r} = p·E_r − n^{2r} = A_r`.

**Fact 1 — the cumulants of `η` BLOW UP (super-exponentially), starting at the onset.** Define the
standardized cumulant `c_{2k} := κ_{2k}(η)/κ_2(η)^k`. For a sub-Gaussian RV these stay bounded by
the Gaussian/Wick profile. The exact `n=16` values are:

| `2k`  | `c_{2k}=κ_{2k}/κ_2^k` |
|-------|------------------------|
| 4     | −0.190 |
| 6     | +0.141 |
| 8     | −0.212 |
| **10**| **+0.194** (last `O(1)`) |
| **12**| **+7.107** (blow-up) |
| 14    | −181.6 |
| 16    | +3803 |
| …     | … (reaches `2.6·10¹⁰` by `2k=26`) |

The η-cumulants leave the `O(1)` (sub-Gaussian) regime at `2k ≈ 10–12`, i.e. at `r ≈ 5–6 ≈ r_0`,
the **onset** — answering the A8 question directly: *yes, a cumulant blows up, and it blows up at the
onset.* So a literal cumulant→tail derivation for the magnitude is dead for the same reason as the
energy route.

**Fact 2 (the NEW structure) — yet the EFFECTIVE sub-Gaussian variance is MONOTONE DECREASING
through the saddle.** Define `v_r := (A_r / ((q−1)·Wick_r))^{1/r}·n`, the variance of the Gaussian
whose `2r`-th moment matches `A_r/(q−1)`. The saddle bound is exactly `v_r ≤ n`. The exact
computation gives much more: `v_r` is *strictly decreasing in `r`* and stays `< n` at **every** depth
through and past the saddle `r ≈ ln q` (verified `r = 1..13` at `n=16`, `r = 1..14` at `n=32`):

```
n=16 (lnq≈11.1):  v_r/n = 1.000, 0.968, 0.936, 0.904, 0.872, 0.841, 0.812, 0.783, 0.755, …, 0.658
n=32 (lnq≈13.9):  v_r/n = 1.000, 0.984, 0.968, 0.952, 0.937, 0.922, 0.906, 0.890, 0.873, …, 0.778
```

So while the *cumulant expansion* of `log E[e^{s η}]` diverges (Fact 1), the *resummed* moment
profile is not merely sub-Gaussian but **sub-Gaussian with monotonically improving variance** as
`r → ln q`. This is exactly WHY `A_r ≤ Wick` is true and WHY no cumulant-by-cumulant bound can
prove it: the truth lives in an alternating, non-summable cumulant series whose resummation
(`v_r ↓`) is invisible term-by-term.

**The EXACT failing step toward the prize.** `v_r` decreases *in `r` at fixed `n`*, but the value at
the saddle `v_{⌈ln q⌉}` *increases with `n`* (`0.70 → 0.78` from `n=16 → n=32`), heading toward the
boundary `1`. A proof of the open core must control `v_{ln q}` *uniformly in `n`* — i.e. show
`v_{ln q}/n` stays bounded below `1` (indeed below `2e`, the prize constant) as `n → 2^30`. That
uniform-in-`n` saddle bound on the effective variance is the precise residual; it is the wall.

This file PROVES Fact 2 (monotone effective variance) as exact integer inequalities on the `n=16`
β=4 prize instance across `r = 1..8` (covering the onset), and embeds the cumulant-blow-up witness
(`c_{12} > 1`) that forecloses the magnitude cumulant→tail route.
-/

namespace ProximityGap.Frontier.A8EffVarMonotone

/-! ## Data — exact integers `A_r` and `B_r := (q−1)·Wick_r`, `n = 16`, `p = q = 65537`, `r = 1..8`.

`A_r = q·E_r − n^{2r}` (the saddle quantity `Σ_{b≠0}‖η_b‖^{2r}`) and `B_r = (q−1)·(2r−1)‼·n^r`
(the Wick budget). Both are exact integer convolution outputs. The saddle bound is `A_r ≤ B_r`. -/

/-- `A_r = Σ_{b≠0}‖η_b‖^{2r}` for `n=16`, `p=65537`, `r = 1..8` (exact). -/
def A : Fin 8 → ℤ
  | 0 => 1048336
  | 1 => 47121104
  | 2 => 3296773504
  | 3 => 300724716624
  | 4 => 32780203335056
  | 5 => 4056432601097984
  | 6 => 551428599459919120
  | 7 => 80539878778988799824

/-- `B_r = (q−1)·Wick_r = (q−1)·(2r−1)‼·n^r` for `n=16`, `p=65537`, `r = 1..8` (exact). -/
def B : Fin 8 → ℤ
  | 0 => 1048576
  | 1 => 50331648
  | 2 => 4026531840
  | 3 => 450971566080
  | 4 => 64939905515520
  | 5 => 11429423370731520
  | 6 => 2377320061112156160
  | 7 => 570556814666917478400

/-! ## Part 1 — the saddle bound `A_r ≤ B_r` (subcase, onset-covering range). -/

/-- `A_r ≤ B_r` (the saddle bound) at every depth `r = 1..8` on the `n=16`, β=4 instance. -/
theorem saddle_bound : ∀ r : Fin 8, A r ≤ B r := by decide

/-- The bound is strict at all depths (genuine margin). -/
theorem saddle_bound_strict : ∀ r : Fin 8, A r < B r := by decide

/-! ## Part 2 — the NEW structure: the effective sub-Gaussian variance `v_r` is MONOTONE DECREASING.

`v_r := n·(A_r/B_r)^{1/r}` is the variance of the Gaussian whose `2r`-th moment matches the period
`2r`-moment. `v_r > v_{r+1}` is, after clearing the roots, the exact integer inequality
`A_r^{r+1}·B_{r+1}^r > A_{r+1}^r·B_r^{r+1}` (writing `r` for `i.val+1`). This says the period family
is not merely sub-Gaussian but sub-Gaussian with *strictly improving* variance as depth grows —
a strictly stronger statement than `A_r ≤ B_r`. -/

/-- The pairwise effective-variance comparison exponents. For `i : Fin 7`, depth `r = i.val + 1`
and the next depth `r+1 = i.val + 2`; `v_r > v_{r+1}` becomes
`A r ^ (r+1) * B (r+1) ^ r > A (r+1) ^ r * B r ^ (r+1)`. -/
theorem effVar_strictly_decreasing :
    ∀ i : Fin 7,
      A i.castSucc ^ (i.val + 2) * B i.succ ^ (i.val + 1)
        > A i.succ ^ (i.val + 1) * B i.castSucc ^ (i.val + 2) := by decide

/-- **The effective-variance monotonicity, packaged.** The period family `{η_b}` is sub-Gaussian
with a *strictly decreasing* effective variance through depth `r = 8` (covering the onset
`r_0 ≈ 4–5`). This is the favorable resummation the cumulant route cannot see: term-by-term the
η-cumulants blow up (Part 3), yet the resummed moment profile improves with depth. -/
theorem subgaussian_with_improving_variance :
    (∀ r : Fin 8, A r ≤ B r) ∧
    (∀ i : Fin 7,
      A i.castSucc ^ (i.val + 2) * B i.succ ^ (i.val + 1)
        > A i.succ ^ (i.val + 1) * B i.castSucc ^ (i.val + 2)) :=
  ⟨saddle_bound, effVar_strictly_decreasing⟩

/-! ## Part 3 — the magnitude cumulant blow-up witness (forecloses the η cumulant→tail route).

The standardized cumulants `c_{2k} = κ_{2k}(η)/κ_2(η)^k` of the magnitude leave the bounded
(sub-Gaussian) regime at the onset: `c_{10} ≈ 0.194` is the last `O(1)` value and `c_{12} ≈ 7.107`
is the first blow-up. We embed the exact rational `κ_{12}/κ_2^6` and certify `> 1` to witness that
a cumulant-to-tail (Chernoff) bound on the magnitude — which needs the standardized cumulants to
stay `O(1)` to depth `≈ 2 ln q` — fails already at depth `r ≈ 6 ≈ r_0`. -/

/-- Exact standardized 12th cumulant of `η` for the `n=16` distribution, `c₁₂ = κ₁₂/κ₂⁶`. -/
def c12 : ℚ :=
  (8103892792494318754135889901404099721021501184 : ℚ)
    / 1140213606202240633410287520190949931828178125  -- ≈ 7.10735

/-- `c₁₂ > 1`: the standardized η-cumulant has left the sub-Gaussian `O(1)` regime by depth 6
(`2k = 12`), i.e. at `r ≈ 6 ≈ r_0`, the onset. -/
theorem c12_gt_one : (1 : ℚ) < c12 := by unfold c12; norm_num

/-- **A8 magnitude cumulant→tail route REDUCES (exact foreclosure).** The standardized cumulants of
`η` blow up at the onset (`c₁₂ > 1`, then super-exponentially), so no Chernoff/saddle tail bound
built on bounded standardized cumulants can be carried to the saddle `r ≈ ln q`. The exact failing
step is the **η-cumulant blow-up at `r ≈ r_0` (the onset)** — distinct from the energy-cumulant
*sign-change* at `0.72 ln q` (the companion file). -/
theorem a8_magnitude_cumulant_route_reduces : (1 : ℚ) < c12 := c12_gt_one

#print axioms saddle_bound
#print axioms saddle_bound_strict
#print axioms effVar_strictly_decreasing
#print axioms subgaussian_with_improving_variance
#print axioms a8_magnitude_cumulant_route_reduces

/-! ## Synthesis (the honest A8 verdict, magnitude side)

* **PROVES (subcase, new structure):** `subgaussian_with_improving_variance` — on the `n=16`, β=4
  prize instance, across `r = 1..8` (covering the onset `r_0 ≈ 4–5`), the period family is
  sub-Gaussian (`A_r ≤ B_r`) AND its effective variance `v_r` is *strictly decreasing* in `r`. The
  monotone-improving variance is genuinely new exact structure: it is the resummation that makes
  `A_r ≤ Wick` true and that no cumulant-by-cumulant bound can detect.
* **REDUCES (magnitude cumulant→tail route), exact failing step:**
  `a8_magnitude_cumulant_route_reduces` — the standardized cumulants of `η` blow up at the onset
  (`c₁₂ > 1`), so a Chernoff bound on bounded standardized cumulants cannot reach the saddle. This is
  the magnitude analogue of, and complementary to, the energy-cumulant sign-change.
* **THE EXACT WALL (uniform-in-`n`):** `v_r` decreases in `r` at fixed `n`, but `v_{⌈ln q⌉}/n` rises
  with `n` (`0.70 → 0.78`, `n = 16 → 32`) toward `1`. The open core is exactly the *uniform-in-`n`*
  statement `v_{ln q}/n ≤` (prize constant `2e`) as `n → 2^30`. That is the residual; it is the wall.

NOT a proof of the open core. The `n → 2^30`, worst-prime, uniform saddle bound remains open.
-/

end ProximityGap.Frontier.A8EffVarMonotone
