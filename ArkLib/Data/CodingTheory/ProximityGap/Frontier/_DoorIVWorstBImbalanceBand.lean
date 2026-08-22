/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWorstBCoherentImbalance
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Real.Basic

/-!
# Door-(iv) constraint: the worst-`b` half-split is a STATIONARY `O(1)` band — dead from BOTH ends (#444)

This file builds on `_DoorIVWorstBCoherentImbalance` (worst-`b` halves are coherent
`‖A + B‖ = ‖A‖ + ‖B‖` but strictly imbalanced) and pins the *quantitative shape* of the imbalance,
correcting an earlier **probe-only** misreading.

## Probe finding it grounds (refutation-with-mechanism)

`scripts/probes/probe_dooriv_worstb_imbalance_growth_law.py` (FULL coset scan `F_p^*/μ_n ≅ ℤ_m`,
proper `μ_n`, `p ≫ n³`, `β = 4`, **median over 4–12 structured primes per `n`**, never `n = q-1`):

- The MEDIAN worst-`b` balance ratio `r(b*) = min(‖A‖,‖B‖)/max(‖A‖,‖B‖)` is **FLAT** across the thin
  regime: `r*(med) = 0.832, 0.810, 0.830` at `n = 16, 32, 64` (12 primes/n) — essentially **constant
  ≈ 0.83**.  All three decay-law fits give `R² < 0.015`: polynomial `d ~ c·n^{-s}` (`R²=0.0095`),
  logarithmic `d ~ c/log n` (`R²=0.0107`), `√log` on the magnitude gap (`R²=0.0144`).  There is **no
  growth law**: `r(b*)` does **not** decay to `0`.
- This CORRECTS the prior probe-only entry `[doorIV-worstb-coherent-imbalance]` ("min_p `r(b*)`
  monotone-down `0.704 → 0.527 → 0.478`, halves DIVERGE as `μ_n` thins"): the **min** over a handful of
  primes is noisy (picks the single worst prime) and was a 3-point sampling artifact; the **median**
  (robust statistic) is stationary.  The worst-`b` imbalance is **thickness-band-bounded**, sitting in a
  fixed band `r(b*) ∈ [r_lo, r_hi] ⊂ (0,1)` (empirically `≈ [0.72, 0.90]`, median `≈ 0.83`), **not**
  asymptotically degenerating.

## What this file proves (axiom-clean, NO growth-law theorem — HARD RULE 1)

We do **not** assert any `n`-asymptotic from a trend.  We formalize the *conditional* structural
consequence of a stationary band: at the coherent worst frequency, write `H = max(‖A‖,‖B‖)` (the heavier
half-norm) and assume the band `r_lo ≤ min/max ≤ r_hi` with `0 < r_lo` and `r_hi < 1`.  Then:

1. **No degeneration to one half** (lower band): `(1 + r_lo) · H ≤ ‖A + B‖`, with strict slack
   `‖A + B‖ − H ≥ r_lo · H > 0` whenever `H > 0`.  The lighter half carries a **persistent positive
   share** `≥ r_lo · H`; the split does **not** collapse to a single heavier half (so the greedy
   single-chain reframe `905cd5577` is inapplicable for a *structural* reason: there genuinely is a
   second non-negligible term).
2. **No `√`-thinning over the heavier half** (upper band): `‖A + B‖ ≤ (1 + r_hi) · H < 2 · H`.  The
   2-term coherent split contributes only a **bounded `O(1)` factor** `(1 + r_hi) ≤ 2` over the single
   heavier half — it supplies **no asymptotic thinning** of `M(n)` relative to `H`.

So the worst-`b` half-split is a **dead `√`-thinning lever from BOTH ends**: neither degenerate (a real
second term persists) nor thinning (the second term is an `O(1)` reshuffle, never sub-leading).  This is
a precisely-mapped non-tightness, **not** a CORE / cancellation / completion / moment / capacity claim:
it does not bound `M(n)`; it certifies that the *coherent imbalanced half-split structure*, by itself,
cannot move the `√`-frontier in either direction.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVWorstBImbalanceBand

open ArkLib.ProximityGap.Frontier.DoorIVWorstBCoherentImbalance

variable {E : Type*} [SeminormedAddCommGroup E]

/-- **Coherent peak as heavier-half scaling.**  At full coherence the period norm is the heavier
half-norm `H = max(‖A‖,‖B‖)` scaled by `1 + r`, where `r = min/max` is the balance ratio.  Stated
multiplicatively to avoid division: `‖A + B‖ = max + min = (1 + r)·max` once `min = r·max`. -/
theorem coherent_norm_eq_one_add_ratio_mul_max {A B : E} {r : ℝ}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) (hr : min ‖A‖ ‖B‖ = r * max ‖A‖ ‖B‖) :
    ‖A + B‖ = (1 + r) * max ‖A‖ ‖B‖ := by
  rw [coherent_norm_eq_max_add_min hcoh, hr]; ring

/-- **Lower band ⇒ persistent second term (no degeneration to one half).**  If the lighter half is at
least an `r_lo`-fraction of the heavier (`r_lo · max ≤ min`), then at coherence the period norm is at
least `(1 + r_lo)·max`.  With `0 < r_lo` and a nonzero heavier half this gives strict positive slack
over the single heavier half. -/
theorem one_add_rlo_mul_max_le_norm {A B : E} {rlo : ℝ}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) (hlo : rlo * max ‖A‖ ‖B‖ ≤ min ‖A‖ ‖B‖) :
    (1 + rlo) * max ‖A‖ ‖B‖ ≤ ‖A + B‖ := by
  rw [coherent_norm_eq_max_add_min hcoh]; nlinarith [hlo]

/-- **Strict positive slack over the heavier half.**  Under the lower band with `0 < rlo` and a
nonzero heavier half (`0 < max ‖A‖ ‖B‖`), the lighter half contributes a strictly positive share:
`max ‖A‖ ‖B‖ < ‖A + B‖`.  The split does NOT collapse to a single heavier term. -/
theorem max_lt_norm_of_lower_band {A B : E} {rlo : ℝ}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) (hrlo : 0 < rlo)
    (hH : 0 < max ‖A‖ ‖B‖) (hlo : rlo * max ‖A‖ ‖B‖ ≤ min ‖A‖ ‖B‖) :
    max ‖A‖ ‖B‖ < ‖A + B‖ := by
  have h := one_add_rlo_mul_max_le_norm hcoh hlo
  nlinarith [mul_pos hrlo hH]

/-- **Upper band ⇒ no `√`-thinning (bounded `O(1)` factor over the heavier half).**  If the lighter
half is at most an `r_hi`-fraction of the heavier (`min ≤ r_hi · max`) with `r_hi < 1`, then at
coherence the period norm is at most `(1 + r_hi)·max < 2·max`.  The 2-term split inflates the heavier
half by only a bounded constant. -/
theorem norm_le_one_add_rhi_mul_max {A B : E} {rhi : ℝ}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) (hhi : min ‖A‖ ‖B‖ ≤ rhi * max ‖A‖ ‖B‖) :
    ‖A + B‖ ≤ (1 + rhi) * max ‖A‖ ‖B‖ := by
  rw [coherent_norm_eq_max_add_min hcoh]; nlinarith [hhi]

/-- **Strictly below the symmetric ceiling under the upper band.**  With `rhi < 1` and a nonzero
heavier half, `‖A + B‖ ≤ (1 + rhi)·max < 2·max`: the coherent imbalanced split never reaches the
balanced ceiling, so it supplies no thinning of the heavier-half scale. -/
theorem norm_lt_two_mul_max_of_upper_band {A B : E} {rhi : ℝ}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) (hrhi : rhi < 1)
    (hH : 0 < max ‖A‖ ‖B‖) (hhi : min ‖A‖ ‖B‖ ≤ rhi * max ‖A‖ ‖B‖) :
    ‖A + B‖ < 2 * max ‖A‖ ‖B‖ := by
  have h := norm_le_one_add_rhi_mul_max hcoh hhi
  nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - rhi) hH]

/-- **The stationary-band sandwich (capstone).**  At the coherent worst frequency, if the balance ratio
sits in a fixed band `r_lo ≤ min/max ≤ r_hi` with `0 < r_lo` and `r_hi < 1`, then the period norm is
sandwiched
    `(1 + r_lo) · H ≤ ‖A + B‖ ≤ (1 + r_hi) · H`,  `H = max(‖A‖,‖B‖)`.
The lower bound `(1 + r_lo)·H > H` forbids degeneration to a single heavier half; the upper bound
`(1 + r_hi)·H < 2·H` forbids `√`-thinning over the heavier half.  A stationary `O(1)` imbalance band ⟹
the half-split moves the frontier in NEITHER direction. -/
theorem stationary_band_sandwich {A B : E} {rlo rhi : ℝ}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖)
    (hlo : rlo * max ‖A‖ ‖B‖ ≤ min ‖A‖ ‖B‖)
    (hhi : min ‖A‖ ‖B‖ ≤ rhi * max ‖A‖ ‖B‖) :
    (1 + rlo) * max ‖A‖ ‖B‖ ≤ ‖A + B‖ ∧ ‖A + B‖ ≤ (1 + rhi) * max ‖A‖ ‖B‖ :=
  ⟨one_add_rlo_mul_max_le_norm hcoh hlo, norm_le_one_add_rhi_mul_max hcoh hhi⟩

/-- **Endpoint-gap lower bound, lower-band side.**  In the stationary-band regime the amount by which
the coherent sum exceeds the single heavier half is at least `rlo · H`.  This is the quantitative
version of "no degeneration to one half": the slack over the one-half model is not merely positive, it
pays the lower-band fraction of the heavier-half scale. -/
theorem lower_band_slack_over_single_ge {A B : E} {rlo : ℝ}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖)
    (hlo : rlo * max ‖A‖ ‖B‖ ≤ min ‖A‖ ‖B‖) :
    rlo * max ‖A‖ ‖B‖ ≤ ‖A + B‖ - max ‖A‖ ‖B‖ := by
  rw [coherent_norm_eq_max_add_min hcoh]
  nlinarith [hlo]

/-- **Endpoint-gap lower bound, upper-band side.**  In the stationary-band regime the amount by which
the symmetric `2H` ceiling over-counts the coherent sum is at least `(1-rhi)·H`.  Thus an upper band
bounded away from `1` gives a proportional, not infinitesimal, gap from the balanced ceiling. -/
theorem upper_band_gap_to_symmetric_ceiling_ge {A B : E} {rhi : ℝ}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖)
    (hhi : min ‖A‖ ‖B‖ ≤ rhi * max ‖A‖ ‖B‖) :
    (1 - rhi) * max ‖A‖ ‖B‖ ≤ 2 * max ‖A‖ ‖B‖ - ‖A + B‖ := by
  rw [coherent_norm_eq_max_add_min hcoh]
  nlinarith [hhi]

/-- **Stationary band gives proportional gaps from BOTH endpoints.**  Under a band
`rlo·H ≤ min ≤ rhi·H`, the coherent half split is separated from the one-half endpoint by at least
`rlo·H` and from the symmetric `2H` endpoint by at least `(1-rhi)·H`.  This is the exact endpoint-gap
form of the "dead from both ends" verdict. -/
theorem stationary_band_endpoint_gap_bounds {A B : E} {rlo rhi : ℝ}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖)
    (hlo : rlo * max ‖A‖ ‖B‖ ≤ min ‖A‖ ‖B‖)
    (hhi : min ‖A‖ ‖B‖ ≤ rhi * max ‖A‖ ‖B‖) :
    rlo * max ‖A‖ ‖B‖ ≤ ‖A + B‖ - max ‖A‖ ‖B‖ ∧
      (1 - rhi) * max ‖A‖ ‖B‖ ≤ 2 * max ‖A‖ ‖B‖ - ‖A + B‖ :=
  ⟨lower_band_slack_over_single_ge hcoh hlo,
   upper_band_gap_to_symmetric_ceiling_ge hcoh hhi⟩

/-- **Both-ends-dead, packaged.**  Under the stationary band with `0 < r_lo`, `r_hi < 1`, and a nonzero
heavier half, the period norm is strictly between the single-heavier-half value and the balanced
ceiling: `max(‖A‖,‖B‖) < ‖A + B‖ < 2·max(‖A‖,‖B‖)`.  Neither endpoint is reached: the coherent
imbalanced split is a bounded `O(1)` reshuffle, dead as a `√`-thinning lever from both ends. -/
theorem strictly_between_single_and_ceiling {A B : E} {rlo rhi : ℝ}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) (hrlo : 0 < rlo) (hrhi : rhi < 1)
    (hH : 0 < max ‖A‖ ‖B‖)
    (hlo : rlo * max ‖A‖ ‖B‖ ≤ min ‖A‖ ‖B‖)
    (hhi : min ‖A‖ ‖B‖ ≤ rhi * max ‖A‖ ‖B‖) :
    max ‖A‖ ‖B‖ < ‖A + B‖ ∧ ‖A + B‖ < 2 * max ‖A‖ ‖B‖ :=
  ⟨max_lt_norm_of_lower_band hcoh hrlo hH hlo,
   norm_lt_two_mul_max_of_upper_band hcoh hrhi hH hhi⟩

end ArkLib.ProximityGap.Frontier.DoorIVWorstBImbalanceBand

-- Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}).
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBImbalanceBand.stationary_band_sandwich
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBImbalanceBand.strictly_between_single_and_ceiling
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBImbalanceBand.max_lt_norm_of_lower_band
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBImbalanceBand.norm_lt_two_mul_max_of_upper_band
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBImbalanceBand.coherent_norm_eq_one_add_ratio_mul_max
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBImbalanceBand.stationary_band_endpoint_gap_bounds
