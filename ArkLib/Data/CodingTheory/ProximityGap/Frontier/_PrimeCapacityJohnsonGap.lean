/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrimeCapacityUncertainty

/-!
# Quantitative content of the [349] capacity-vs-Johnson dichotomy gap (#407)

`_PrimeCapacityUncertainty.lean` lands the two halves of the [349] uncertainty dichotomy and the
*directional* comparison `capacity_le_johnson_radius`: for `1 ≤ t ≤ n`,

> `(t − 1)  ≤  n·(1 − 1/t)`,

i.e. the prime/additive zero bound `t − 1` is at most the composite/multiplicative zero bound
`n·(1 − 1/t)`.  Its docstring asserts (in prose only) that the gap
`g(n,t) := n·(1 − 1/t) − (t − 1)` is *`0` at the degenerate `t = n`* and *`Θ(n)` for `t = O(1)`*
(the prize regime).  This file hardens those two quantitative claims into kernel-checked lemmas, so
the dichotomy's separation magnitude is backed by proofs rather than prose.

* `johnson_gap_eq` — the exact closed form `g(n,t) = n − n/t − t + 1` (for `t ≠ 0`).
* `johnson_gap_zero_at_t_eq_n` — the gap **vanishes** at `t = n`: `g(n,n) = 0` (the two doors
  coincide at the degenerate full-spectrum endpoint).
* `johnson_gap_ge_half_n_sub` — for `2 ≤ t ≤ n` the gap is **`≥ n/2 − (t − 1)`** (since
  `1 − 1/t ≥ 1/2 ⟺ t ≥ 2`).  Hence in the prize regime `t = O(1)` the gap is `≥ n/2 − O(1) = Θ(n)`:
  the additive (capacity) and multiplicative (Johnson) doors diverge **linearly in `n`**.

This is pure real arithmetic on the two PROVEN zero-count bounds; it consumes neither the open
`TaoUncertainty` input nor any analytic estimate.  It quantifies the gap whose existence is the
whole point of the [349] dichotomy, but asserts nothing new about CORE: which side `n = 2^μ` lands
on (Johnson) is the *composite* half, already mapped; the gap lemma only measures the separation.
No cancellation, completion, anti-concentration, moment, or capacity-for-`2^μ` claim.  Axiom-clean.
Issue #407.
-/

namespace ProximityGap.Frontier.PrimeCapacityJohnsonGap

/-- The dichotomy gap `g(n,t) := n·(1 − 1/t) − (t − 1)` (Johnson zero bound minus capacity zero
bound), as a real-valued function of the dimension `n` and Fourier-sparsity `t`. -/
noncomputable def johnsonGap (n t : ℝ) : ℝ := n * (1 - 1 / t) - (t - 1)

/-- **Closed form of the gap.**  For `t ≠ 0`, `g(n,t) = n − n/t − t + 1`. -/
theorem johnson_gap_eq {n t : ℝ} (ht : t ≠ 0) :
    johnsonGap n t = n - n / t - t + 1 := by
  unfold johnsonGap
  field_simp
  ring

/-- **The gap vanishes at the degenerate endpoint `t = n`.**  `g(n,n) = 0`: the additive (capacity)
and multiplicative (Johnson) zero bounds coincide when the obstruction is full-spectrum `t = n`.
This is the `0` endpoint of the [349] separation. -/
theorem johnson_gap_zero_at_t_eq_n {n : ℝ} (hn : n ≠ 0) :
    johnsonGap n n = 0 := by
  rw [johnson_gap_eq hn, div_self hn]
  ring

/-- **The gap is `Θ(n)` in the prize regime.**  For `2 ≤ t ≤ n`, the dichotomy gap is at least
`n/2 − (t − 1)`.  Mechanism: `1 − 1/t ≥ 1/2 ⟺ t ≥ 2`, so `n·(1 − 1/t) ≥ n/2`.  Hence for bounded
`t = O(1)` (prize regime) the additive (capacity) and multiplicative (Johnson) doors diverge by
`≥ n/2 − O(1) = Θ(n)`, linear in `n`: the [349] separation is not a lower-order effect.
PROVEN, real arithmetic, unconditional (no `TaoUncertainty`). -/
theorem johnson_gap_ge_half_n_sub {n t : ℝ} (ht2 : 2 ≤ t) (htn : t ≤ n) :
    (n : ℝ) / 2 - (t - 1) ≤ johnsonGap n t := by
  have htpos : (0 : ℝ) < t := by linarith
  have hnpos : (0 : ℝ) ≤ n := le_trans (by linarith) htn
  unfold johnsonGap
  -- it suffices that `n·(1 − 1/t) ≥ n/2`, i.e. `1 − 1/t ≥ 1/2`, i.e. `1/t ≤ 1/2`.
  have hinv : 1 / t ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2)
    linarith
  have hfac : (1 : ℝ) / 2 ≤ 1 - 1 / t := by linarith
  have hmul : n * (1 / 2) ≤ n * (1 - 1 / t) := by
    exact mul_le_mul_of_nonneg_left hfac hnpos
  linarith [hmul]

end ProximityGap.Frontier.PrimeCapacityJohnsonGap

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.PrimeCapacityJohnsonGap.johnson_gap_eq
#print axioms ProximityGap.Frontier.PrimeCapacityJohnsonGap.johnson_gap_zero_at_t_eq_n
#print axioms ProximityGap.Frontier.PrimeCapacityJohnsonGap.johnson_gap_ge_half_n_sub
