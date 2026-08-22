/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The power-sum ratio is monotone increasing — the LOWER bracket companion of `ladder_antitone` (#444)

**What this extends.** `_MomentLadderAntitone.ladder_antitone` proved the UPPER side of the moment
localization of the spectral max: the even-moment root `r ↦ (∑_i a_i^{2r})^{1/(2r)}` is *antitone*
(decreases toward `max_i a_i` from above). This file proves the matching reusable LOWER side as an
abstract power-sum fact (the companion that was only present in tree in the energy-specific form
`EnergyLogConvexRatioMonotone.energy_ratio_monotone_nat`):

> **For any nonnegative finite spectrum `a` and `t ≥ 0`, the consecutive power-sum ratio
> `S_{t+1}/S_t` is MONOTONE INCREASING in `t` and bounded above by `max_i a_i`** (so it approaches
> `max_i a_i` from BELOW), where `S_t = ∑_i a_i^t`.

Together with `ladder_antitone` (upper, antitone) and `MomentSupNormBridge.sup_le_moment_root`
(upper bracket) and `EnergyRatioSupNormLower.maxSq_ge_energy_ratio` (lower bracket), this completes
the *nested two-sided localization* of `max_i a_i`: the ratio lower bound rises, the root upper bound
falls, both squeezing the prize sup-norm. The genuinely new content here is the ABSTRACT
monotonicity of the lower side, reusable on any spectrum (not tied to the `rEnergy` definition).

## The mechanism (log-convexity / Cauchy–Schwarz on power sums)

The single inequality `S_t · S_{t+2} ≥ S_{t+1}^2` (discrete Cauchy–Schwarz: `a_i^{t+1} =
√(a_i^t) · √(a_i^{t+2})`) immediately gives `S_{t+1}/S_t ≤ S_{t+2}/S_{t+1}` once `S_{t+1} > 0`. This
is the log-convexity of `t ↦ log S_t`. The boundedness `S_{t+1}/S_t ≤ max a` is the elementary
`∑ a^{t+1} = ∑ a·a^t ≤ (max a)·∑ a^t`.

## What is PROVEN here (axiom target `{propext, Classical.choice, Quot.sound}`)

* `powerSum_sq_le_mul` — the log-convexity backbone `(∑ a_i^{t+1})^2 ≤ (∑ a_i^t)·(∑ a_i^{t+2})` for
  any nonnegative `a` over a finite index. (The abstract Cauchy–Schwarz core of the in-tree
  `energy_logConvex`, lifted off the `rEnergy` spectrum.)
* `powerSum_ratio_monotone` — `S_{t+1}/S_t ≤ S_{t+2}/S_{t+1}` whenever `S_{t+1} > 0`: the ratio
  ladder is monotone increasing. The reusable lower-bracket companion of `ladder_antitone`.
* `powerSum_ratio_le_max` — `S_{t+1}/S_t ≤ max_i a_i` (bounded by the spectral max). With the
  monotonicity this gives a lower bound on `max a` that TIGHTENS with `t`.

## Honesty / scope (rules 1,3,6 + ASYMPTOTIC GUARD)

This is a field-universal structural identity on an arbitrary nonnegative spectrum (it holds for the
thick group too). It is the EASY/honest LOWER direction of the moment localization: a lower bound on
`max_i a_i = M(n)²` (the prize sup-norm squared, on the `b≠0` spectrum), NOT the wall-bearing upper
bound. By rule 3 it cannot prove the thinness-essential prize and does not pretend to — it bounds the
prize quantity from the WRONG (easy) side. No CORE closure, no char-p transfer, no capacity /
beyond-Johnson / growth-law claim; it does not touch the cliff-at-n/2 (a lower bound is structurally
orthogonal to the over-det face).

Probe `scripts/probes/probe_powersum_ratio_mono.py`: `0 fails / 55000` random nonnegative spectra
(`S_{t+1}/S_t` monotone ↑ and `≤ max a` at every depth). Probe
`scripts/probes/probe_bracket_width.py`: on PROPER subgroups `μ_n ⊊ 𝔽_p^*` (`n=2^a`, primes incl.
prize-regime `p=65537,n=16,β=4`, NEVER `n=q−1`), the ratio-lower `(A_{r+1}/A_r)^{1/2}` rises and the
root-upper `A_r^{1/(2r)}` falls, bracketing `max_{b≠0}‖η_b‖` at every `r` (`0 fails/9`).

## References
- `_MomentLadderAntitone.ladder_antitone` (#407, the antitone UPPER side this is the LOWER companion of).
- `EnergyLogConvexRatioMonotone.energy_ratio_monotone_nat` (the `rEnergy`-specific instance).
- `EnergyRatioSupNormLower.maxSq_ge_energy_ratio` (the lower bracket on the Gauss-period spectrum).
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. #444.
-/

open Finset

namespace ProximityGap.Frontier.PowerSumRatioMonotone

variable {ι : Type*}

/-- **Log-convexity backbone (discrete Cauchy–Schwarz on power sums).** For a nonnegative family
`a : ι → ℝ` over a finite index, `(∑ a_i^{t+1})^2 ≤ (∑ a_i^t)·(∑ a_i^{t+2})`. Proof: write
`a_i^{t+1} = √(a_i^t)·√(a_i^{t+2})` and apply the squared Cauchy–Schwarz `sum_mul_sq_le_sq_mul_sq`. -/
theorem powerSum_sq_le_mul [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (t : ℕ) :
    (∑ i, (a i) ^ (t + 1)) ^ 2 ≤ (∑ i, (a i) ^ t) * (∑ i, (a i) ^ (t + 2)) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ)
    (fun i => Real.sqrt ((a i) ^ t)) (fun i => Real.sqrt ((a i) ^ (t + 2)))
  -- `√(a^t) * √(a^{t+2}) = a^{t+1}`
  have hprod : ∀ i, Real.sqrt ((a i) ^ t) * Real.sqrt ((a i) ^ (t + 2)) = (a i) ^ (t + 1) := by
    intro i
    rw [← Real.sqrt_mul (pow_nonneg (ha i) t)]
    rw [show (a i) ^ t * (a i) ^ (t + 2) = ((a i) ^ (t + 1)) ^ 2 by ring]
    exact Real.sqrt_sq (pow_nonneg (ha i) (t + 1))
  -- `(√(a^t))^2 = a^t`, `(√(a^{t+2}))^2 = a^{t+2}`
  have hsqL : ∀ i, (Real.sqrt ((a i) ^ t)) ^ 2 = (a i) ^ t := fun i =>
    Real.sq_sqrt (pow_nonneg (ha i) t)
  have hsqR : ∀ i, (Real.sqrt ((a i) ^ (t + 2))) ^ 2 = (a i) ^ (t + 2) := fun i =>
    Real.sq_sqrt (pow_nonneg (ha i) (t + 2))
  simp_rw [hprod] at hcs
  simp_rw [hsqL, hsqR] at hcs
  exact hcs

/-- **The power-sum ratio is monotone increasing.** With `S_t = ∑ a_i^t` and `S_{t+1} > 0`, the
consecutive ratio rises: `S_{t+1}/S_t ≤ S_{t+2}/S_{t+1}`. The reusable LOWER-bracket companion of
`ladder_antitone`. -/
theorem powerSum_ratio_monotone [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (t : ℕ)
    (hSt : 0 < ∑ i, (a i) ^ t) (hSt1 : 0 < ∑ i, (a i) ^ (t + 1)) :
    (∑ i, (a i) ^ (t + 1)) / (∑ i, (a i) ^ t)
      ≤ (∑ i, (a i) ^ (t + 2)) / (∑ i, (a i) ^ (t + 1)) := by
  rw [div_le_div_iff₀ hSt hSt1]
  -- goal: S_{t+1} * S_{t+1} ≤ S_{t+2} * S_t
  have hkey := powerSum_sq_le_mul a ha t
  nlinarith [hkey]

/-- **Two-step ratio chaining.** The adjacent monotonicity can be composed without re-opening the
Cauchy--Schwarz proof: if `S_t`, `S_{t+1}`, and `S_{t+2}` are positive, then the lower-bracket
ratio at depth `t` is already below the ratio two rungs later. -/
theorem powerSum_ratio_two_step [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (t : ℕ)
    (hSt : 0 < ∑ i, (a i) ^ t) (hSt1 : 0 < ∑ i, (a i) ^ (t + 1))
    (hSt2 : 0 < ∑ i, (a i) ^ (t + 2)) :
    (∑ i, (a i) ^ (t + 1)) / (∑ i, (a i) ^ t)
      ≤ (∑ i, (a i) ^ (t + 3)) / (∑ i, (a i) ^ (t + 2)) := by
  calc
    (∑ i, (a i) ^ (t + 1)) / (∑ i, (a i) ^ t)
        ≤ (∑ i, (a i) ^ (t + 2)) / (∑ i, (a i) ^ (t + 1)) :=
          powerSum_ratio_monotone a ha t hSt hSt1
    _ ≤ (∑ i, (a i) ^ ((t + 1) + 2)) / (∑ i, (a i) ^ ((t + 1) + 1)) :=
          powerSum_ratio_monotone a ha (t + 1) hSt1 hSt2
    _ = (∑ i, (a i) ^ (t + 3)) / (∑ i, (a i) ^ (t + 2)) := by ring_nf

/-- **The ratio is bounded by the spectral max.** With `S_t = ∑ a_i^t`, `M` an entrywise upper bound
(`∀ i, a_i ≤ M`) and `S_t > 0`, the ratio `S_{t+1}/S_t ≤ M`. With `powerSum_ratio_monotone` the lower
bound on `M = max a` tightens with depth, approaching `max a` from below. -/
theorem powerSum_ratio_le_max [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (M : ℝ)
    (hM : ∀ i, a i ≤ M) (t : ℕ) (hSt : 0 < ∑ i, (a i) ^ t) :
    (∑ i, (a i) ^ (t + 1)) / (∑ i, (a i) ^ t) ≤ M := by
  rw [div_le_iff₀ hSt, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hstep : (a i) ^ (t + 1) = a i * (a i) ^ t := by rw [pow_succ]; ring
  rw [hstep]
  exact mul_le_mul_of_nonneg_right (hM i) (pow_nonneg (ha i) t)

end ProximityGap.Frontier.PowerSumRatioMonotone

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.PowerSumRatioMonotone.powerSum_sq_le_mul
#print axioms ProximityGap.Frontier.PowerSumRatioMonotone.powerSum_ratio_monotone
#print axioms ProximityGap.Frontier.PowerSumRatioMonotone.powerSum_ratio_two_step
#print axioms ProximityGap.Frontier.PowerSumRatioMonotone.powerSum_ratio_le_max
