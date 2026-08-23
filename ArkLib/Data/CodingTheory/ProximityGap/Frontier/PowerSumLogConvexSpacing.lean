/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PowerSumRatioMonotone

/-!
# General-spacing log-convexity of power sums (#444)

**What this generalizes.** `PowerSumRatioMonotone.powerSum_sq_le_mul` proved the ADJACENT
log-convexity backbone `(S_{t+1})^2 ≤ S_t · S_{t+2}` (the `k = 1` case). This file proves the
GENERAL-SPACING form, for any gap `k`:

> **For any nonnegative finite spectrum `a` and any `t, k`,
> `(S_{t+k})^2 ≤ S_t · S_{t+2k}`** where `S_t = ∑_i a_i^t`.

This is the full discrete log-convexity of `t ↦ log S_t` read at arbitrary symmetric spacing
`(t, t+k, t+2k)` rather than only adjacent triples, via the SAME single Cauchy–Schwarz with the
exponent split `a_i^{t+k} = √(a_i^t)·√(a_i^{t+2k})`. The adjacent case `powerSum_sq_le_mul` is the
`k = 1` specialization. The general-gap form yields the WIDER-bracket ratio monotonicity
`S_{t+k}/S_t ≤ S_{t+1+k}/S_{t+1}` reusable for any localization window, not only the unit window.

## What is PROVEN here (axiom target `{propext, Classical.choice, Quot.sound}`)

* `powerSum_sq_le_mul_spacing` — `(S_{t+k})^2 ≤ S_t · S_{t+2k}` for any nonnegative `a`, any `t, k`.
* `powerSum_ratio_spacing_monotone` — the same-gap ratio rises one rung:
  `S_{t+k}/S_t ≤ S_{t+2k}/S_{t+k}`.
* `powerSum_ratio_spacing_le_max_pow` — the gap-`k` ratio is bounded by `M^k` when
  every spectral entry is at most `M`.

## Honesty / scope (rules 1,3,6 + ASYMPTOTIC GUARD)

Field-universal structural identity on an arbitrary nonnegative spectrum (holds for the thick group
too; by rule 3 it cannot and does not prove the thinness-essential prize). It is the log-convexity
backbone underlying the LOWER (easy/honest) side of the moment localization of `max a = M(n)^2`, NOT
the wall-bearing upper bound. No CORE closure, no char-p transfer, no capacity / beyond-Johnson /
growth-law claim; orthogonal to the cliff-at-n/2 (a convexity/lower-bracket fact). Pure Cauchy–
Schwarz, no new analytic input.

Probe `scripts/probes/probe_psratio_logconvex_spacing.py`: `0 fails / 58994` random nonnegative
spectra (`S_t · S_{t+2k} ≥ (S_{t+k})^2` over `t = 0..4`, `k = 0..3`; the wider-gap ratio
monotonicity `S_{t+k}/S_t ≤ S_{t+1+k}/S_{t+1}` also `0 fails`).

## References
- `PowerSumRatioMonotone.powerSum_sq_le_mul` (the adjacent `k = 1` case generalized here).
- `PowerSumRatioMonotone.powerSum_ratio_monotone` (the adjacent ratio rise this widens).
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. #444.
-/

open Finset

namespace ProximityGap.Frontier.PowerSumLogConvexSpacing

variable {ι : Type*}

/-- **General-spacing log-convexity of power sums.** For a nonnegative family `a : ι → ℝ` over a
finite index and any `t, k`, the symmetric spacing inequality `(∑ a_i^{t+k})^2 ≤ (∑ a_i^t)·(∑
a_i^{t+2k})` holds. Proof: write `a_i^{t+k} = √(a_i^t)·√(a_i^{t+2k})` and apply the squared
Cauchy–Schwarz `sum_mul_sq_le_sq_mul_sq`. The adjacent backbone `powerSum_sq_le_mul` is `k = 1`. -/
theorem powerSum_sq_le_mul_spacing [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (t k : ℕ) :
    (∑ i, (a i) ^ (t + k)) ^ 2 ≤ (∑ i, (a i) ^ t) * (∑ i, (a i) ^ (t + 2 * k)) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ)
    (fun i => Real.sqrt ((a i) ^ t)) (fun i => Real.sqrt ((a i) ^ (t + 2 * k)))
  -- `√(a^t) * √(a^{t+2k}) = a^{t+k}`
  have hprod : ∀ i, Real.sqrt ((a i) ^ t) * Real.sqrt ((a i) ^ (t + 2 * k)) = (a i) ^ (t + k) := by
    intro i
    rw [← Real.sqrt_mul (pow_nonneg (ha i) t)]
    rw [show (a i) ^ t * (a i) ^ (t + 2 * k) = ((a i) ^ (t + k)) ^ 2 by
          rw [← pow_add, ← pow_mul]; ring_nf]
    exact Real.sqrt_sq (pow_nonneg (ha i) (t + k))
  have hsqL : ∀ i, (Real.sqrt ((a i) ^ t)) ^ 2 = (a i) ^ t := fun i =>
    Real.sq_sqrt (pow_nonneg (ha i) t)
  have hsqR : ∀ i, (Real.sqrt ((a i) ^ (t + 2 * k))) ^ 2 = (a i) ^ (t + 2 * k) := fun i =>
    Real.sq_sqrt (pow_nonneg (ha i) (t + 2 * k))
  simp_rw [hprod] at hcs
  simp_rw [hsqL, hsqR] at hcs
  exact hcs

/-- **Same-gap ratio monotonicity.** The general-spacing log-convexity inequality can be read as
one rung of monotonicity for the `k`-spaced lower-bracket ratio: `S_{t+k}/S_t ≤ S_{t+2k}/S_{t+k}`.
This is the direct gap-`k` analogue of `powerSum_ratio_monotone`, with no new analytic input beyond
`powerSum_sq_le_mul_spacing`. -/
theorem powerSum_ratio_spacing_monotone [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (t k : ℕ)
    (hSt : 0 < ∑ i, (a i) ^ t) (hStk : 0 < ∑ i, (a i) ^ (t + k)) :
    (∑ i, (a i) ^ (t + k)) / (∑ i, (a i) ^ t)
      ≤ (∑ i, (a i) ^ (t + 2 * k)) / (∑ i, (a i) ^ (t + k)) := by
  rw [div_le_div_iff₀ hSt hStk]
  have hkey := powerSum_sq_le_mul_spacing a ha t k
  nlinarith [hkey]

/-- **Gap-`k` ratio bounded by the spectral max to the `k`.** If every entry of the nonnegative
spectrum is at most `M`, then `S_{t+k}/S_t ≤ M^k`. This is the general-gap version of
`PowerSumRatioMonotone.powerSum_ratio_le_max` (`k = 1`). -/
theorem powerSum_ratio_spacing_le_max_pow [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (M : ℝ) (hM : ∀ i, a i ≤ M) (t k : ℕ) (hSt : 0 < ∑ i, (a i) ^ t) :
    (∑ i, (a i) ^ (t + k)) / (∑ i, (a i) ^ t) ≤ M ^ k := by
  rw [div_le_iff₀ hSt, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hpow : (a i) ^ k ≤ M ^ k := pow_le_pow_left₀ (ha i) (hM i) k
  have hsplit : (a i) ^ (t + k) = (a i) ^ k * (a i) ^ t := by
    rw [Nat.add_comm t k, pow_add]
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hpow (pow_nonneg (ha i) t)

end ProximityGap.Frontier.PowerSumLogConvexSpacing

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.PowerSumLogConvexSpacing.powerSum_sq_le_mul_spacing
#print axioms ProximityGap.Frontier.PowerSumLogConvexSpacing.powerSum_ratio_spacing_monotone
#print axioms ProximityGap.Frontier.PowerSumLogConvexSpacing.powerSum_ratio_spacing_le_max_pow
