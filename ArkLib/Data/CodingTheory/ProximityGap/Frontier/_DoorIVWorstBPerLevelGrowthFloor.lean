/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWorstBCoherentImbalance
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

/-!
# Door-(iv) constraint: per-level wall growth has a `(1+r_lo)(1−ε)` FLOOR — the √-wall cannot thin down the tower (#444)

Ties the worst-`b` coherent-imbalance band (`_DoorIVWorstBCoherentImbalance`,
`_DoorIVWorstBImbalanceBand`) to the cross-depth tower via the measured sub-period transfer, yielding
a clean LOWER bound on the per-level growth of `M`.

## Probe finding it grounds

`scripts/probes/probe_dooriv_worstb_crossdepth_argmax.py` (FULL coset scan, proper `μ_n`, `p ≫ n³`,
`β = 4`, median over 6 structured primes, never `n=q-1`):

- **Per-level wall growth** `M(μ_n) / M(μ_{n/2}) = 1.75, 1.57, 1.47` at `n = 16, 32, 64` — strictly
  above `√2 ≈ 1.414` (the floor on the `√(n·log)` law). The `√`-wall does **not** thin per level.
- **Cross-depth near-alignment**: the full-group worst frequency `b*` sits at the **99.9th
  percentile** (`0.9988, 0.9987, 0.9975`) of the sub-group `μ_{n/2}`'s `|η|` distribution. So `b*` is
  *near-worst* (but, by `_DoorIVWorstBNonNested`, **not** exactly the sub-argmax) for the half-subgroup:
  the sub-period transfer is `‖A_{b*}‖ ≥ (1−ε)·M(μ_{n/2})` with a *small* `ε ≈ 10⁻³`.

## What this file proves (axiom-clean — a real LOWER bound, NO growth-law trend)

At the coherent worst frequency `b*`, `M(μ_n) = ‖A_{b*}‖ + ‖B_{b*}‖`, where `A_{b*}` is itself a
`μ_{n/2}`-period (the subgroup half) and `B_{b*}` the coset half. Combine:
1. **coherent imbalance band** (`_DoorIVWorstBImbalanceBand`): `‖A+B‖ = (1+r)·H ≥ (1+r_lo)·‖A‖` once
   `A` is the heavier (or `≥ (1+r_lo)·‖A‖` directly from the lower band with `H ≥ ‖A‖`); concretely we
   use `M(μ_n) ≥ ‖A_{b*}‖` (a single summand of a coherent nonneg sum) and the band multiplier;
2. **near-worst sub-transfer**: `‖A_{b*}‖ ≥ (1−ε)·M₂`, `M₂ = M(μ_{n/2})`.

Then `M(μ_n) ≥ (1+r_lo)·(1−ε)·M(μ_{n/2})`. With the measured `r_lo ≈ 0.5`, `ε ≈ 10⁻³` this floor is
`≈ 1.498·M₂ > √2·M₂`, matching the observed `1.47–1.75`. So **under the (measured) coherent-band +
near-worst-transfer hypotheses, the per-level wall growth is bounded below by `(1+r_lo)(1−ε) > √2`,
i.e. the wall provably does NOT thin per level** — a recursive descent that hoped for a per-level
factor `< √2` is excluded on these hypotheses.

This is a CONDITIONAL lower bound (hypotheses are the measured band + transfer), a precisely-mapped
constraint — **not** a CORE upper bound, cancellation, completion, moment, or capacity claim. It does
not bound `M(n)` from above; it certifies the wall's per-level growth floor under the observed
structure. CORE remains OPEN.
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
- near-worst transfer: `(1 − ε) · M₂ ≤ ‖A‖` (`b*` is a near-top frequency for `μ_{n/2}`),
- nonneg slack: `0 ≤ 1 − ε`.
Then `M₁ ≥ (1 + r_lo)·(1 − ε)·M₂`.  With measured `r_lo ≈ 0.5`, `ε ≈ 10⁻³` this is `> √2 · M₂`: the
`√`-wall does not thin per level. -/
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
of `no_perLevel_growth_below_floor`: if the measured coherent-band/transfer floor satisfies
`√2 < (1+r_lo)(1−ε)`, then the dyadic wall cannot obey the square-root descent step
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
