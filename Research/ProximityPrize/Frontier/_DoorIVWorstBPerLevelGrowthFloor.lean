/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Research.ProximityPrize.Frontier._DoorIVWorstBCoherentImbalance
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

/-!
# Door-(iv) constraint: a CONDITIONAL `(1+r_lo)(1−ε)` floor on per-level wall growth (#444)

Ties the worst-`b` coherent-imbalance band (`_DoorIVWorstBCoherentImbalance`,
`_DoorIVWorstBImbalanceBand`) to the cross-depth tower via the measured sub-period transfer, yielding
a clean LOWER bound on the per-level growth of `M`.

## Probe finding it grounds

`scripts/probes/probe_dooriv_worstb_crossdepth_argmax.py` (FULL coset scan, proper `μ_n`, `p ≫ n³`,
`β = 4`, median over 6 structured primes, never `n=q-1`):

- **Per-level wall growth** `M(μ_n) / M(μ_{n/2}) = 1.75, 1.57, 1.47` at `n = 16, 32, 64` — above
  `√2 ≈ 1.414` in these three finite samples. These are finite probe measurements, not a uniform or
  infinite-tower statement.
- **Cross-depth rank position**: the full-group worst frequency `b*` sits at the **99.9th rank
  percentile** (`0.9988, 0.9987, 0.9975`) of the sub-group `μ_{n/2}`'s `|η|` distribution (by
  `_DoorIVWorstBNonNested`, **not** exactly the sub-argmax).

*Correction (audit 2026-10-28, R-220).* An earlier version inferred from those percentiles the
amplitude transfer `‖A_{b*}‖ ≥ (1−ε)·M(μ_{n/2})` with `ε ≈ 10⁻³`. A rank percentile gives no such
amplitude ratio: a family with `999` entries equal to `1` and one entry `H` has cumulative
percentile `0.999` at value `1`, while its amplitude ratio to the maximum is `1/H`, arbitrarily
small. The value of `ε` that `htransfer` needs must come from the actual ratio
`‖A_{b*}‖ / M(μ_{n/2})` at each cell, which these probe outputs (as recorded here) do not supply.

## What this file proves (axiom-clean — a real LOWER bound, NO growth-law trend)

At the coherent worst frequency `b*`, `M(μ_n) = ‖A_{b*}‖ + ‖B_{b*}‖`, where `A_{b*}` is itself a
`μ_{n/2}`-period (the subgroup half) and `B_{b*}` the coset half. Combine:
1. **coherent imbalance band** (`_DoorIVWorstBImbalanceBand`): `‖A+B‖ = (1+r)·H ≥ (1+r_lo)·‖A‖` once
   `A` is the heavier (or `≥ (1+r_lo)·‖A‖` directly from the lower band with `H ≥ ‖A‖`); concretely we
   use `M(μ_n) ≥ ‖A_{b*}‖` (a single summand of a coherent nonneg sum) and the band multiplier;
2. **sub-transfer hypothesis**: `‖A_{b*}‖ ≥ (1−ε)·M₂`, `M₂ = M(μ_{n/2})` (an amplitude ratio, to be
   supplied per cell; not implied by the percentile data above).

Then `M(μ_n) ≥ (1+r_lo)·(1−ε)·M(μ_{n/2})` (`perLevel_growth_floor`). Parameter check (R-220): the
earlier pairing `r_lo ≈ 0.5`, `ε ≈ 10⁻³` gives the floor `1.5·0.999 = 1.4985`, which is **larger**
than the observed ratio `1.47` at `n = 64`; since the theorem would force
`M(μ_n)/M(μ_{n/2}) ≥ 1.4985`, those parameter values cannot all hold simultaneously in that cell. Valid per-cell parameters
`(r_lo, ε)` must be chosen from actual amplitude ratios and checked against each observed growth
ratio; this file does not do that.

So the theorem is: **under** the coherent-band and amplitude-transfer hypotheses (with whatever
`r_lo, ε` actually hold), the per-level growth is at least `(1+r_lo)(1−ε)`, and if that exceeds
`√2` a `√2` per-level descent is excluded (`no_sqrt_two_perLevel_thinning`). It does not establish
that the hypotheses hold with `(1+r_lo)(1−ε) > √2` at any cell, nor anything uniform along the
tower. This is a CONDITIONAL lower bound — **not** a CORE upper bound, cancellation, completion,
moment, or capacity claim. CORE remains OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVWorstBPerLevelGrowthFloor

variable {E : Type*} [SeminormedAddCommGroup E]

/-- **A single coherent nonneg summand is a lower bound on the coherent peak.**  At full coherence
`‖A + B‖ = ‖A‖ + ‖B‖`, the period norm is at least the subgroup-half norm `‖A‖` (since `‖B‖ ≥ 0`). -/
theorem subHalf_norm_le_coherent_peak {A B : E} (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) :
    ‖A‖ ≤ ‖A + B‖ := by
  rw [hcoh]; linarith [norm_nonneg B]

/-- **Band-amplified lower bound on the coherent peak.**  If additionally the coset half carries at
least an `r_lo`-share of the subgroup half (`r_lo · ‖A‖ ≤ ‖B‖`, the lower imbalance band oriented with
`A` heavier-or-equal), then `M = ‖A + B‖ ≥ (1 + r_lo)·‖A‖`. -/
theorem one_add_rlo_mul_subHalf_le_coherent_peak {A B : E} {rlo : ℝ}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) (hlb : rlo * ‖A‖ ≤ ‖B‖) :
    (1 + rlo) * ‖A‖ ≤ ‖A + B‖ := by
  rw [hcoh]; nlinarith [hlb]

/-- **Per-level growth floor (the capstone).**  Let `M₁ = ‖A + B‖ = M(μ_n)` at the coherent worst
frequency, `M₂ = M(μ_{n/2})` the sub-group's own worst-period magnitude, with:
- coherence + lower band: `r_lo · ‖A‖ ≤ ‖B‖` (`0 ≤ r_lo`),
- amplitude transfer: `(1 − ε) · M₂ ≤ ‖A‖` (an actual amplitude ratio; a rank percentile of `b*`
  in the `μ_{n/2}` distribution does not supply it, R-220),
- nonneg slack: `0 ≤ 1 − ε`.
Then `M₁ ≥ (1 + r_lo)·(1 − ε)·M₂`.  Whether the hypotheses hold with `(1 + r_lo)(1 − ε) > √2` at a
given cell must be checked from actual amplitude ratios (the earlier quoted `r_lo ≈ 0.5`,
`ε ≈ 10⁻³` give `1.4985`, inconsistent with the observed ratio `1.47` at `n = 64`). -/
theorem perLevel_growth_floor {A B : E} {rlo ε M₂ : ℝ}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖)
    (hlb : rlo * ‖A‖ ≤ ‖B‖)
    (hrlo : 0 ≤ rlo)
    (htransfer : (1 - ε) * M₂ ≤ ‖A‖)
    (_hε : 0 ≤ 1 - ε) :
    (1 + rlo) * ((1 - ε) * M₂) ≤ ‖A + B‖ := by
  have hpeak : (1 + rlo) * ‖A‖ ≤ ‖A + B‖ := one_add_rlo_mul_subHalf_le_coherent_peak hcoh hlb
  have hmono : (1 + rlo) * ((1 - ε) * M₂) ≤ (1 + rlo) * ‖A‖ := by
    apply mul_le_mul_of_nonneg_left htransfer
    linarith
  linarith

/-- **No per-level thinning below the floor.**  Contrapositive packaging: under the same hypotheses,
if a claimed per-level growth bound `M₁ ≤ K·M₂` has `K < (1 + r_lo)·(1 − ε)` with `0 < M₂`, it is
refuted.  A descent assuming a per-level factor below the floor is impossible. -/
theorem no_perLevel_growth_below_floor {A B : E} {rlo ε M₂ K : ℝ}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖)
    (hlb : rlo * ‖A‖ ≤ ‖B‖) (hrlo : 0 ≤ rlo)
    (htransfer : (1 - ε) * M₂ ≤ ‖A‖) (hε : 0 ≤ 1 - ε)
    (hM₂ : 0 < M₂) (hK : K < (1 + rlo) * (1 - ε)) :
    ¬ ‖A + B‖ ≤ K * M₂ := by
  intro hle
  have hfloor : (1 + rlo) * ((1 - ε) * M₂) ≤ ‖A + B‖ :=
    perLevel_growth_floor hcoh hlb hrlo htransfer hε
  have hKlt : K * M₂ < (1 + rlo) * (1 - ε) * M₂ :=
    mul_lt_mul_of_pos_right hK hM₂
  nlinarith [hfloor, hle, hKlt]

/-- **No `√2` per-level thinning under a super-`√2` floor.**  This is the probe-facing specialization
of `no_perLevel_growth_below_floor`: if the coherent-band/transfer hypotheses hold with
`√2 < (1+r_lo)(1−ε)` (to be verified from actual amplitude ratios, not percentiles), then the dyadic
wall cannot obey the square-root descent step
`M(μ_n) ≤ √2 · M(μ_{n/2})` on those hypotheses.  This is a lower-bound obstruction to that descent,
not a CORE upper bound. -/
theorem no_sqrt_two_perLevel_thinning {A B : E} {rlo ε M₂ : ℝ}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖)
    (hlb : rlo * ‖A‖ ≤ ‖B‖) (hrlo : 0 ≤ rlo)
    (htransfer : (1 - ε) * M₂ ≤ ‖A‖) (hε : 0 ≤ 1 - ε)
    (hM₂ : 0 < M₂) (hsqrt : Real.sqrt 2 < (1 + rlo) * (1 - ε)) :
    ¬ ‖A + B‖ ≤ Real.sqrt 2 * M₂ :=
  no_perLevel_growth_below_floor hcoh hlb hrlo htransfer hε hM₂ hsqrt

end ArkLib.ProximityGap.Frontier.DoorIVWorstBPerLevelGrowthFloor

-- Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}).
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBPerLevelGrowthFloor.perLevel_growth_floor
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBPerLevelGrowthFloor.no_perLevel_growth_below_floor
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBPerLevelGrowthFloor.no_sqrt_two_perLevel_thinning
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBPerLevelGrowthFloor.one_add_rlo_mul_subHalf_le_coherent_peak
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBPerLevelGrowthFloor.subHalf_norm_le_coherent_peak
