/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ShawValueCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NoFifthDoorTetrachotomy

/-!
# Bridging the two synthesis scales: `shawScale = bgkScale ∘ log`, and the gap factor is `√(log(q/n))` (#444)

The grand synthesis (`_ShawGrandSynthesis`) conjoins two standing results that are *intentionally
stated against different scales*:

* the **reduction half** (`_ShawValueCapstone`) normalizes by
  `shawScale q n = √(n · log(q/n))` — the BGK-shaped target;
* the **no-fifth-door half** (`_NoFifthDoorTetrachotomy`) separates
  `prizeScale n = √n` (the genuine prize floor) from `bgkScale n L = √(n·L)` (the door-(i)/(ii)/(iii)
  ceiling), with the closed ratio `bgkScale n L / prizeScale n = √L` (`bgkScale_div_prizeScale`).

`_ShawGrandSynthesis` explicitly leaves the *relationship between these two scales* unformalized:
> "the two halves use intentionally distinct scales … this synthesis does NOT identify them.
>  Identifying the two scales is exactly the open `√L`-gap that door (iv) must close, and which this
>  file makes no claim about."

This file supplies the **bookkeeping bridge** that was left as prose: it identifies the reduction-half
scale with the door-half BGK scale at the concrete thinness index `L = log(q/n)`, and therefore pins
the synthesis's "open `√L`-gap" to a single kernel-checked closed form — the factor by which the
reduction's normalization target `shawScale` exceeds the genuine prize floor `prizeScale` is *exactly*
`√(log(q/n))`.

## Honesty
This is PURE DEFINITIONAL/ALGEBRAIC BOOKKEEPING.  `shawScale q n` and `bgkScale n (log(q/n))` are the
SAME real number by definition (`√(n · log(q/n))`); the gap-factor corollary is an immediate instance
of the already-proven `bgkScale_div_prizeScale`.  It introduces **NO new mathematical content**: no
CORE / cancellation / completion / moment / anti-concentration / capacity / asymptotic claim, and it
makes **no claim that the gap factor is bounded** (i.e. it does NOT identify the two scales — closing
the `√(log(q/n))` gap is exactly the open door-(iv) problem).  It only renders the synthesis's prose
"`√L`-gap" as a kernel-checked identity so a referee can cite the gap as a precise quantity rather
than narrative.  CORE `M(μ_n) ≤ C·√(n·log(p/n))` stays **OPEN**.
-/

namespace ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge

open ProximityGap.Frontier.ShawValueCapstone
open ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy

/-- **Scale identification (definitional).**  The reduction-half normalization scale
`shawScale q n = √(n · log(q/n))` is, by definition, the door-half BGK scale `bgkScale n L = √(n·L)`
evaluated at the concrete logarithmic thinness index `L = log(q/n)`.  This is the missing rung that
connects the two synthesis halves: they live over the *same* scale once the thinness index is named. -/
theorem shawScale_eq_bgkScale (q n : ℝ) :
    shawScale q n = bgkScale n (Real.log (q / n)) := rfl

/-- **The synthesis gap factor is `√(log(q/n))` (closed form).**  In the prize regime `q > n > 0`
(so the thinness index `log(q/n) ≥ 0`), the reduction-half normalization target `shawScale q n`
exceeds the genuine prize floor `prizeScale n = √n` by *exactly* the factor `√(log(q/n))`:
`shawScale q n / prizeScale n = √(log(q/n))`.

This pins `_ShawGrandSynthesis`'s prose "open `√L`-gap" (`L = log(q/n)`) to a single kernel-checked
quantity.  It is an immediate instance of the door-half ratio `bgkScale_div_prizeScale` under the
definitional identification `shawScale_eq_bgkScale`.  It asserts NOTHING about whether this factor is
bounded — that the `√(log(q/n))` factor can be absorbed (i.e. the two scales identified) is exactly
the open door-(iv) problem this file makes NO claim about. -/
theorem shawScale_div_prizeScale (q n : ℝ) (hn : 0 < n) (hqn : 0 ≤ Real.log (q / n)) :
    shawScale q n / prizeScale n = Real.sqrt (Real.log (q / n)) := by
  rw [shawScale_eq_bgkScale]
  exact bgkScale_div_prizeScale hn hqn

/-- **Prize-regime scale guard.**  In the genuine prize regime `q > n > 0`, the thinness index
`log(q/n)` is automatically nonnegative, so the gap-factor identity holds with only the regime
hypothesis: `shawScale q n / prizeScale n = √(log(q/n))`. -/
theorem shawScale_div_prizeScale_of_pos_lt (q n : ℝ) (hn : 0 < n) (hnq : n < q) :
    shawScale q n / prizeScale n = Real.sqrt (Real.log (q / n)) := by
  apply shawScale_div_prizeScale q n hn
  apply Real.log_nonneg
  have hdiv : n / n ≤ q / n := div_le_div_of_nonneg_right (le_of_lt hnq) hn.le
  simpa [div_self (ne_of_gt hn)] using hdiv

/-- **The gap is genuine in the thin regime `log(q/n) > 1`.**  When the logarithmic thinness index
exceeds `1` (i.e. `q/n > e`, the regime where the BGK normalization is nontrivial), the reduction
target `shawScale q n` strictly exceeds the genuine prize floor `prizeScale n = √n`, so there is a
genuine (strictly positive `√(log(q/n))`) gap to close.  This is the door-half separation
`prizeScale_lt_bgkScale` transported across the scale identification.

(The hypothesis is `1 < log(q/n)`, NOT merely `n < q`: `√n < √(n·L)` requires `L > 1`, so the strict
gap is a property of the *thin* regime `q/n > e`, exactly where the BGK `√L` factor bites.  At
`n < q ≤ e·n` the two scales can coincide or invert — the gap factor `√(log(q/n)) ≤ 1` there.) -/
theorem prizeScale_lt_shawScale_of_one_lt_log (q n : ℝ) (hn : 0 < n)
    (hL : 1 < Real.log (q / n)) :
    prizeScale n < shawScale q n := by
  rw [shawScale_eq_bgkScale]
  exact prizeScale_lt_bgkScale hn hL

/-- **The genuine cancellation ratio is the Shaw value times the gap factor.**  Write the genuine
square-root-cancellation ratio as `M / prizeScale n = M / √n` (how far below the trivial `n` bound the
sup norm cancels, measured against the prize floor `√n`).  In the prize regime `q > n > 0`, this ratio
equals the campaign's Shaw value `shawValue q n M = M / shawScale q n` AMPLIFIED by exactly the gap
factor `√(log(q/n))`:
`M / prizeScale n = shawValue q n M · √(log(q/n))`.

This is the *consumer* form of the scale bridge and the precise reason the reduction half and the door
half are not the same statement: bounding the Shaw value by an absolute constant (`Sh = O(1)`, the
reduction) does NOT bound the genuine cancellation ratio `M/√n` unless the `√(log(q/n))` gap factor is
absorbed — which is exactly the open door-(iv) content.  Pure algebra over the definitional bridge; no
claim that either side is bounded. -/
theorem prizeFloorRatio_eq_shawValue_mul_gap (q n M : ℝ) (hn : 0 < n) (hnq : n < q) :
    M / prizeScale n
      = shawValue q n M * Real.sqrt (Real.log (q / n)) := by
  have hsp : 0 < shawScale q n := shawScale_pos_of_pos_lt hn hnq
  have hpp : 0 < prizeScale n := prizeScale_pos hn
  have hgap : shawScale q n / prizeScale n = Real.sqrt (Real.log (q / n)) :=
    shawScale_div_prizeScale_of_pos_lt q n hn hnq
  unfold shawValue
  rw [← hgap]
  field_simp

/-- **A Shaw-value bound only gives a logarithm-amplified prize-floor bound.**  This is the
one-sided operational form of `prizeFloorRatio_eq_shawValue_mul_gap`: if a single instance satisfies
`shawValue q n M ≤ C`, then its genuine square-root-cancellation ratio is bounded only by
`C · √(log(q/n))` against the prize floor.  Thus a constant Shaw bound transports to the prize-floor
normalization with the exact `√log` loss displayed, not silently as an `O(1)` prize-floor bound. -/
theorem prizeFloorRatio_le_shawBound_mul_gap (q n M C : ℝ) (hn : 0 < n) (hnq : n < q)
    (hSh : shawValue q n M ≤ C) :
    M / prizeScale n ≤ C * Real.sqrt (Real.log (q / n)) := by
  rw [prizeFloorRatio_eq_shawValue_mul_gap q n M hn hnq]
  exact mul_le_mul_of_nonneg_right hSh (Real.sqrt_nonneg _)

/-- **Family form: `Sh(n)=O(1)` consumers pay the displayed `√log` factor pointwise.**  A uniform
Shaw-value bound `UniformShawBound q n M C` over a prize-regime family implies the genuine
prize-floor ratios obey the pointwise envelope
`Mᵢ/√nᵢ ≤ C · √(log(qᵢ/nᵢ))`.  This is deliberately NOT an `O(1)` prize-floor statement unless an
additional door-(iv) input controls the gap factor; it records exactly what the reduction alone buys. -/
theorem prizeFloorRatio_family_le_of_uniformShawBound {ι : Type*} {q n M : ι → ℝ} {C : ℝ}
    (hn : ∀ i, 0 < n i) (hnq : ∀ i, n i < q i)
    (hSh : UniformShawBound q n M C) :
    ∀ i, M i / prizeScale (n i) ≤ C * Real.sqrt (Real.log (q i / n i)) := by
  intro i
  exact prizeFloorRatio_le_shawBound_mul_gap (q i) (n i) (M i) C (hn i) (hnq i) (hSh i)


/-- **A prize-floor bound plus a positive Shaw floor forces the gap itself to be bounded.**  If
`c ≤ shawValue q n M` with `c > 0`, and the genuine prize-floor ratio is bounded by `B`, then the
synthesis gap factor must obey `√(log(q/n)) ≤ B/c`.  This is the inverse no-go form of the bridge:
a genuine `O(1)` prize-floor bound cannot coexist with a positive Shaw floor unless the open door-(iv)
`√log` gap has been absorbed. -/
theorem gap_le_prizeFloorBound_div_shawFloor (q n M B c : ℝ) (hn : 0 < n) (hnq : n < q)
    (hc : 0 < c) (hfloor : c ≤ shawValue q n M) (hPrize : M / prizeScale n ≤ B) :
    Real.sqrt (Real.log (q / n)) ≤ B / c := by
  have hgap_nonneg : 0 ≤ Real.sqrt (Real.log (q / n)) := Real.sqrt_nonneg _
  have hcg_le : c * Real.sqrt (Real.log (q / n))
      ≤ shawValue q n M * Real.sqrt (Real.log (q / n)) :=
    mul_le_mul_of_nonneg_right hfloor hgap_nonneg
  have hbridge := prizeFloorRatio_eq_shawValue_mul_gap q n M hn hnq
  have hcg_le_B : c * Real.sqrt (Real.log (q / n)) ≤ B := by
    exact le_trans hcg_le (by simpa [hbridge.symm] using hPrize)
  have hdiv := div_le_div_of_nonneg_right hcg_le_B hc.le
  simpa [mul_div_cancel_left₀ (Real.sqrt (Real.log (q / n))) (ne_of_gt hc)] using hdiv


end ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge

#print axioms ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge.gap_le_prizeFloorBound_div_shawFloor
#print axioms ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge.prizeFloorRatio_le_shawBound_mul_gap
#print axioms ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge.prizeFloorRatio_family_le_of_uniformShawBound
