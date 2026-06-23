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

end ArkLib.ProximityGap.Frontier.ShawScaleDoorScaleBridge
