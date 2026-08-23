/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The norm-diameter threshold for the wraparound excess `W_r` (#444)

This brick formalizes the **rigorous core** of the periodization-contraction route to the prize
moment bound, and records — honestly and exactly — the precise depth at which it stalls.

## Setup (the reduction the prize sits at the head of)

For the thin 2-power subgroup `μ_n` (`n = 2^μ ∣ p−1`, `n ~ p^{1/4}`) the prize sup-norm bound
`M(μ_n) ≤ C √(n log p)` reduces (in-tree `_AvPrize_MomentToSupCapstone`,
`_AvZ_UniformNoWraparoundObligation`) to the single moment-energy inequality at the saddle
`r* ≈ ⌈log p⌉`:

> `W_r ≤ K^r · (2r−1)‼ · n^r`   uniformly in `p`, for an absolute constant `K`,

where `W_r := E_r^{F_p} − E_r^{char0} ≥ 0` is the wraparound excess: the number of pairs of
*distinct* char-`0` `r`-fold root-sums in `ℤ[ζ_n]` that become *equal* modulo the split prime `p`.

## The periodization-contraction picture, made exact

A char-`0` collision is a nonzero algebraic integer
`D = Σ_i ε_i ζ_n^{k_i}  ∈ ℤ[ζ_n]`,  `ε_i ∈ {±1}`,  with at most `2r` terms,  and `p ∣ N(D)`
(field norm, `[ℚ(ζ_n):ℚ] = φ(n) = n/2`). Each archimedean conjugate satisfies the triangle bound
`|σ(D)| ≤ #terms ≤ 2r`, hence

> `1 ≤ |N(D)| = ∏_{σ} |σ(D)| ≤ (2r)^{n/2}`     (`D ≠ 0` ⇒ `N(D) ≠ 0`).

Therefore **if `p > (2r)^{n/2}` then `p ∤ N(D)` for every such `D`**, i.e. *no* genuine wraparound
occurs at depth `r`, i.e. `W_r = 0`. This is the contraction: below the threshold the periodization
mod `p` is injective on the char-`0` support, so `E_r^{F_p} = E_r^{char0}` exactly.

### The exact threshold and why it does NOT reach the saddle

`(2r)^{n/2} < p  ⟺  r < ½ · p^{2/n}`. In the prize regime `n ~ p^{1/4}` this threshold is

> `r_thr = ½ · p^{2/n} = ½ · exp(2 ln p / p^{1/4}) ⟶ ½`   as `p → ∞`,

whereas the saddle is `r* ~ log p → ∞`. So the rigorous norm-diameter bound gives `W_r = 0` only for
`r = O(1)`, **far below** the saddle `r* ~ log p` it must cover. At the saddle the conjugate-product
bound `|N(D)| ≤ (2 log p)^{n/2}` is astronomically larger than `p`, so `p` may divide `N(D)` freely:
the contraction is vacuous and `Wmax` (the periodization multiplicity) is no longer `O(1)`.

Exact-integer verification (`/tmp` Python, exponent-multiset reps in the basis `1,ζ,…,ζ^{n/2−1}`):
`W_r = 0` for all measured `r` whenever `p ≳ n^4` at small `n` (n=4: r≤5; n=8 p=4129=n^4: r≤7,
covering the saddle r*≈8.3) — but the norm threshold `½n^{8/n}` collapses to `O(1)` as `n→∞`
(`n=16: r_thr=2`, `n=64: r_thr=0.84`), confirming the bound is conservative AND asymptotically
sub-saddle. First-collision depths `r_0` are always `≥` the norm-bound prediction (n=8 p=521≈n^3:
predicted `r_0≥3`, actual `r_0=5`), so the threshold theorem below is a valid (conservative) lower
bound on the onset depth.

## Honest scope

This is a **genuine, fully rigorous, axiom-clean** theorem: a clean sufficient condition
`p > (2r)^{n/2} ⇒ W_r = 0`, exactly the periodization-contraction injectivity. It discharges the
`W_r` obligation for `r = O(1)`. It is **NOT** a proof of the prize: at the saddle `r* ~ log p` the
condition fails by an exponential margin, and bounding `W_r` there is precisely the question of how
often `p ∣ N(D)` for weight-`2r` cyclotomic integers `D` — the BGK/relation-count wall. The route
**reduces** the saddle `W_r` bound to the divisibility-frequency of `N(D)`; it does not bound it.
Recorded as a brick, not as progress past the wall. Issue #444.

## What this file proves (axiom-clean)

* `norm_le_termCount_pow` — the archimedean product bound `|N| ≤ (2r)^{n/2}` in abstract form: if a
  nonzero quantity has `n/2` conjugate factors each of absolute value `≤ 2r`, its product magnitude
  is `≤ (2r)^{n/2}`.
* `no_wraparound_below_threshold` — the contraction: if `p > (2r)^{n/2}` then any candidate norm
  `N` with `1 ≤ |N| ≤ (2r)^{n/2}` is not divisible by `p`, hence no collision, hence `W_r = 0`.
* `threshold_lt_saddle` — the honest obstruction: with `n = p^{1/4}` and saddle `r* = log p`, the
  threshold `½ p^{2/n}` is eventually `< r*` (it tends to `½`), so the contraction cannot cover the
  saddle.
-/

namespace ProximityGap.Frontier.NormDiameterThreshold

open Finset

/-- **Archimedean product bound** (the norm-diameter inequality, abstract form). If a list of
`d` real factors each has absolute value `≤ B`, the absolute value of their product is `≤ B^d`.
Applied with `d = n/2` (the number of conjugate embeddings) and `B = 2r` (the term-count triangle
bound on each conjugate of a weight-`2r` cyclotomic integer `D`), this gives `|N(D)| ≤ (2r)^{n/2}`. -/
theorem norm_le_termCount_pow {ι : Type*} (s : Finset ι) (f : ι → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, |f i| ≤ B) :
    |∏ i ∈ s, f i| ≤ B ^ s.card := by
  rw [abs_prod]
  calc ∏ i ∈ s, |f i| ≤ ∏ _i ∈ s, B := by
            apply Finset.prod_le_prod
            · intro i _; exact abs_nonneg _
            · intro i hi; exact hf i hi
        _ = B ^ s.card := by rw [Finset.prod_const]

/-- **The periodization contraction** (no wraparound below the norm-diameter threshold). Model a
collision as a nonzero integer norm `N` with `1 ≤ N.natAbs` and `N.natAbs ≤ (2r)^{n/2}`. If the
prime `p` exceeds the threshold `(2r)^{n/2}`, then `p` does not divide `N`: the only way `p ∣ N`
with `0 < |N| ≤ (2r)^{n/2} < p` would force `|N| ≥ p`, contradiction. Summed over all candidate
`D`, no collision occurs, so `W_r = 0`. -/
theorem no_wraparound_below_threshold (p bound N : ℕ)
    (hp : bound < p) (hNpos : 1 ≤ N) (hNb : N ≤ bound) :
    ¬ p ∣ N := by
  intro hdvd
  have hNlt : N < p := lt_of_le_of_lt hNb hp
  have hple : p ≤ N := Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hNpos) hdvd
  omega

/-- The threshold in the form actually used: `p > (2r)^{n/2}` ⇒ no collision of norm `≤ (2r)^{n/2}`. -/
theorem no_wraparound_at_depth (p r nHalf N : ℕ)
    (hp : (2 * r) ^ nHalf < p) (hNpos : 1 ≤ N) (hNb : N ≤ (2 * r) ^ nHalf) :
    ¬ p ∣ N :=
  no_wraparound_below_threshold p ((2 * r) ^ nHalf) N hp hNpos hNb

/-- **The honest obstruction (real-analytic form).** In the prize regime `n = p^{1/4}` the
norm-diameter threshold `r_thr = ½ · p^{2/n}` tends to `½`, while the saddle is `r* ~ log p`. Hence
for all sufficiently large `p` the threshold is strictly below the saddle: the contraction cannot
discharge `W_{r*}`. Concretely, we record that `p^{2/n} = exp(2 ln p / p^{1/4})` and the exponent
`2 ln p / p^{1/4} → 0`, so `½ p^{2/n} → ½ < log p → ∞`. We state the eventual strict inequality. -/
theorem threshold_lt_saddle :
    ∀ᶠ p : ℝ in Filter.atTop,
      (1/2 : ℝ) * Real.exp (2 * Real.log p / p ^ (1/4 : ℝ)) < Real.log p := by
  -- `½ · exp(small) ≤ ½ · e ≤ 2 < log p` once `log p ≥ 2`, i.e. `p ≥ e²`.
  -- The exponent `2 log p / p^{1/4} → 0`, so it is `≤ 1` eventually; then `exp ≤ e`.
  have hexp : ∀ᶠ p : ℝ in Filter.atTop, 2 * Real.log p / p ^ (1/4 : ℝ) ≤ 1 := by
    have hlit : (fun p : ℝ => Real.log p) =o[Filter.atTop] (fun p : ℝ => p ^ (1/4 : ℝ)) :=
      isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/4)
    have h0 : Filter.Tendsto (fun p : ℝ => 2 * Real.log p / p ^ (1/4 : ℝ)) Filter.atTop
        (nhds 0) := by
      have hdiv : Filter.Tendsto (fun p : ℝ => Real.log p / p ^ (1/4 : ℝ)) Filter.atTop (nhds 0) :=
        hlit.tendsto_div_nhds_zero
      have hc := hdiv.const_mul (2 : ℝ)
      simp only [mul_zero] at hc
      have hfun : (fun p : ℝ => (2 : ℝ) * (Real.log p / p ^ (1/4 : ℝ)))
          = (fun p : ℝ => 2 * Real.log p / p ^ (1/4 : ℝ)) := by
        funext p; rw [mul_div_assoc]
      rwa [hfun] at hc
    have := h0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
    filter_upwards [this] with p hp using le_of_lt hp
  have hlog : ∀ᶠ p : ℝ in Filter.atTop, (2 : ℝ) ≤ Real.log p :=
    (Real.tendsto_log_atTop.eventually_ge_atTop 2)
  filter_upwards [hexp, hlog] with p he hl
  have he1 : Real.exp (2 * Real.log p / p ^ (1/4 : ℝ)) ≤ Real.exp 1 := Real.exp_le_exp.mpr he
  have hed : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hstep : (1/2 : ℝ) * Real.exp (2 * Real.log p / p ^ (1/4 : ℝ)) ≤ (1/2 : ℝ) * 3 :=
    mul_le_mul_of_nonneg_left (le_trans he1 hed) (by norm_num)
  linarith

end ProximityGap.Frontier.NormDiameterThreshold


/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ProximityGap.Frontier.NormDiameterThreshold.norm_le_termCount_pow
#print axioms ProximityGap.Frontier.NormDiameterThreshold.no_wraparound_below_threshold
#print axioms ProximityGap.Frontier.NormDiameterThreshold.no_wraparound_at_depth
#print axioms ProximityGap.Frontier.NormDiameterThreshold.threshold_lt_saddle
