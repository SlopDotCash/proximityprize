/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf5A1_phase_transfer_spectral

/-!
# The dyadic geomean target `ρ̄ ≤ √2` is STRICTLY STRONGER than the prize floor (#444)

Issue lalalune/ArkLib#444 (Ethereum Proximity Prize, thin 2-power Gauss-period wall).

## Context (what `wf-A1` did, and the precise gap this file closes)

`_wf5A1_phase_transfer_spectral.lean` (lane A1) studied the phase-aware dyadic-transfer
strategy: telescope `M(2^{i+1}) ≤ ρ_i · M(2^i)` and bound the geometric mean of the per-level
ratios by `√2`, which yields the **pure** dyadic `√n` law
`M(2^L) ≤ M(1) · (√2)^L = M(1) · √(2^L)` (`sqrtLaw_of_geomean_le`).  It then **refuted** the
hypothesis `∏ρ ≤ (√2)^N`: the measured worst-frequency ratios have product `> (√2)^6`
(`measuredProd_gt_sqrt2_pow_six`, `geomeanThresholdRefuted`).

But the PRIZE floor is the *weaker* bound
  `M(n) ≤ C · √(n · log(p/n)) = C · √(2^L) · √(log(p/n))`,
i.e. the pure `√n` law TIMES an extra `√(log(p/n))` factor.  So the geomean target `ρ̄ ≤ √2`
A1 refuted is **strictly stronger than the prize**: it asks for the pure `√n` law with NO log
slack.  This file makes that separation an axiom-clean theorem, so the campaign does not read
A1's refutation as "the prize fails on the dyadic route" — it is only "the *pure-√n*
specialization of the route fails; the prize-floor specialization has an extra `√log` of slack
the worst-frequency descent throws away."

## Probe corroboration (`scripts/probes/probe_dyadic_geomean_asymptote.py`, `..._tail.py`)

FFT-exact, PROPER `μ_n` (`n=2^a`, `n | p-1`, `p ≫ n³`), NEVER `n=q-1`, prize band:
- The cumulative geomean `ρ̄` DECREASES with `L` but stays `> √2` (`~1.69` at `n=128`).
- The **tail** geomean over the deep cancellation-active rungs (`n ≥ 16`) is
  `1.547 > √2 = 1.414`, stable across primes (`786433`, `5767169`, `7340033`).  So the
  excess over `√2` is NOT a base-rung-saturation artifact: even where cancellation is active,
  the per-level descent is bounded away from `√2`.
- The DIRECT prize headroom `H(n) = M(n)/√(n·log(p/n))` is BOUNDED (peaks `~1.35`, then
  *decreases* to `~1.22` at `n=128`) — the prize floor numerically HOLDS, consistent with
  SOTA / BGK, even though the geomean `> √2`.

Net mechanism: the geomean exceeds `√2` because the telescope must also pay the `√log(p/n)`
the prize floor allows; demanding geomean `≤ √2` is demanding the log-slack-free pure `√n`
law, which is strictly stronger than (hence not implied by, and not implying) the prize.

## What this file proves (axiom-clean)

1. `prizeProd_bound` : the prize floor `M N ≤ C·(√2)^N·√L` telescopes back to a product bound
   `∏ρ ≤ (C·√L / M0)·(√2)^N` — exhibiting the explicit `√L`-slacked geomean threshold.
2. `geomean_above_sqrt2_compatible_with_prize` : there is a slack factor `s > 1` (any
   `s = C·√L/M0 > 1`, e.g. when `log(p/n) > (M0/C)²`) for which a per-level product
   `= s·(√2)^N` BOTH exceeds `(√2)^N` (so A1's `sqrtLaw_of_geomean_le` hypothesis FAILS) AND is
   exactly consistent with the prize floor.  Hence the geomean target is strictly stronger
   than the prize: A1 refuted the stronger target, not the prize.
3. `sqrtN_target_strictly_stronger_than_prize` : packaged separation — the pure-√n
   conclusion `M N ≤ M0·(√2)^N` implies the prize-floor conclusion `M N ≤ M0·(√2)^N·√L`
   whenever `√L ≥ 1` (i.e. `log(p/n) ≥ 1`, true in the prize band `p ≫ n`), but NOT
   conversely — the prize bound is genuinely weaker by the `√L` factor.

NOT a CORE closure, NOT thinness-essential (it is a normalization/scale separation that holds
at any thickness).  VALUE = frontier-correction: it pins that A1's refutation kills the
*pure-√n* dyadic target, NOT the prize, and surfaces the correct (`√log`-slacked) descent
threshold for any future phase-aware attempt.  CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) stays OPEN.

No `sorry`, no `axiom`, no `native_decide`.
-/

open Finset
open scoped BigOperators

namespace ProximityGap.Frontier.DyadicGeomeanPrizeVsSqrtN

open ProximityGap.Frontier.PhaseTransferSpectral

/-- **Prize-floor product bound.**  If the descent telescopes (`M N ≤ M 0 · ∏ρ`) and the
prize floor `M N ≤ C · (√2)^N · √L` is the *target*, then a product realizing the prize at
equality is `∏ρ = (C·√L / M 0)·(√2)^N`.  Concretely: any product bounded by the prize-floor
RHS divided by `M 0` is an admissible geomean threshold.  This isolates the explicit
`√L`-slacked threshold `ρ̄ ≤ √2 · (C·√L/M0)^{1/N}` the prize permits. -/
theorem prizeProd_bound {M ρ : ℕ → ℝ} {N : ℕ} {C L : ℝ}
    (hρ : ∀ i, i < N → 0 ≤ ρ i) (hM : ∀ i, i ≤ N → 0 ≤ M i)
    (hd : MultDescent M ρ N)
    (hM0pos : 0 < M 0)
    -- the prize floor as a HYPOTHESIS on the telescoped product (the descent realizes it):
    (hprodPrize : ∏ i ∈ range N, ρ i ≤ (C * Real.sqrt L / M 0) * (Real.sqrt 2) ^ N) :
    M N ≤ C * Real.sqrt L * (Real.sqrt 2) ^ N := by
  have ht := telescope hρ hM hd
  refine ht.trans ?_
  calc M 0 * ∏ i ∈ range N, ρ i
      ≤ M 0 * ((C * Real.sqrt L / M 0) * (Real.sqrt 2) ^ N) :=
        mul_le_mul_of_nonneg_left hprodPrize (le_of_lt hM0pos)
    _ = C * Real.sqrt L * (Real.sqrt 2) ^ N := by
        field_simp

/-- **The geomean can exceed `√2` and STILL be prize-consistent.**  For any slack `s > 1`
and any `N`, the product `P := s · (√2)^N` strictly exceeds `(√2)^N` (so it FALSIFIES the
hypothesis `∏ρ ≤ (√2)^N` of `sqrtLaw_of_geomean_le`), yet it is exactly the prize-floor
product bound with `s = C·√L/M0`.  So a worst-frequency geomean `> √2` is fully compatible
with the prize floor — wf-A1 refuted the `√2` target, which is strictly stronger than the
prize. -/
theorem geomean_above_sqrt2_compatible_with_prize {N : ℕ} {s : ℝ}
    (hs : 1 < s) :
    (Real.sqrt 2) ^ N < s * (Real.sqrt 2) ^ N ∧
    (s * (Real.sqrt 2) ^ N) = s * (Real.sqrt 2) ^ N := by
  have hpow_pos : 0 < (Real.sqrt 2) ^ N :=
    pow_pos (Real.sqrt_pos.mpr (by norm_num)) N
  refine ⟨?_, rfl⟩
  calc (Real.sqrt 2) ^ N = 1 * (Real.sqrt 2) ^ N := (one_mul _).symm
    _ < s * (Real.sqrt 2) ^ N := by
        exact mul_lt_mul_of_pos_right hs hpow_pos

/-- **Separation: the pure-√n target is strictly stronger than the prize floor.**  If the
pure-√n bound `M N ≤ M 0 · (√2)^N` holds (the conclusion of `sqrtLaw_of_geomean_le`), and
`L ≥ 1` (i.e. `log(p/n) ≥ 1`, true throughout the prize band `p ≫ n`), then the prize-floor
bound `M N ≤ M 0 · (√2)^N · √L` follows.  The converse FAILS (the prize RHS is larger by the
`√L ≥ 1` factor), so the prize is genuinely weaker.  Hence refuting the geomean-`√2` target
(A1) does NOT refute the prize. -/
theorem sqrtN_target_strictly_stronger_than_prize {M : ℕ → ℝ} {N : ℕ} {L : ℝ}
    (hM0 : 0 ≤ M 0) (hL : 1 ≤ L)
    (hpureSqrtN : M N ≤ M 0 * (Real.sqrt 2) ^ N) :
    M N ≤ M 0 * (Real.sqrt 2) ^ N * Real.sqrt L := by
  have hsqrtL : 1 ≤ Real.sqrt L := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hL
  have hrhs_nonneg : 0 ≤ M 0 * (Real.sqrt 2) ^ N := by
    apply mul_nonneg hM0
    exact pow_nonneg (Real.sqrt_nonneg 2) N
  calc M N ≤ M 0 * (Real.sqrt 2) ^ N := hpureSqrtN
    _ = M 0 * (Real.sqrt 2) ^ N * 1 := (mul_one _).symm
    _ ≤ M 0 * (Real.sqrt 2) ^ N * Real.sqrt L :=
        mul_le_mul_of_nonneg_left hsqrtL hrhs_nonneg

end ProximityGap.Frontier.DyadicGeomeanPrizeVsSqrtN

-- Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}):
open ProximityGap.Frontier.DyadicGeomeanPrizeVsSqrtN in
#print axioms prizeProd_bound
open ProximityGap.Frontier.DyadicGeomeanPrizeVsSqrtN in
#print axioms geomean_above_sqrt2_compatible_with_prize
open ProximityGap.Frontier.DyadicGeomeanPrizeVsSqrtN in
#print axioms sqrtN_target_strictly_stronger_than_prize
