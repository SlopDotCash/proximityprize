/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVDeficitBudgetSublinearFloor

/-!
# Door-(iv) Lane-3: the SCATTERED-deficit sum floor — measured `S` directly walls the route (#444)

`_DoorIVDeficitBudgetSublinearFloor` proved the exp-relaxed dilation budget stays at/above the
`√(2^a)·M 0` Plancherel/prize scale whenever the **average** per-level deficit is sub-`(log 2)/2`,
phrased through an auxiliary witness `ε` with `S ≤ ε·a` and `ε < (log 2)/2`.

`_DoorIVLeadingZeroDeficitFloor` specialised that to a *leading zero block*: a top run of `T`
exactly-zero-deficit levels with the bottom `a − T` levels carrying `δ ≤ 1`, walled when
`a − T ≤ ((log 2)/2)·a`.

The measured worst-`b` descent does **not** in general have its deficit confined to a leading block.
At `a = 6,7,8` (newly measured, structured primes `p ≈ n^{3.2}`, FULL `F_p^*` coset-deduped worst-`b`
argmax, proper thin `μ_n ⊊ F_p^*`, NEVER `n = q−1`) the nonzero deficits are **scattered** through
the descent (e.g. `a = 8`: deficits at levels 4, 5, 7 with zeros interspersed — NOT a leading block),
so the leading-zero-block hypothesis `δ_k = 0` on a top run is **violated**. The invariant that *does*
survive is the **raw deficit sum** `S = ∑_{k<a} δ_k`:

    a = 5 : S = 0.0000   a = 6 : S = 0.8836   a = 7 : S = 1.6232   a = 8 : S = 1.0307

against the linear-in-`a` budget threshold `(log 2 / 2)·a = 1.733, 2.079, 2.426, 2.773` respectively —
so `S < (log 2 / 2)·a` holds at every measured `a` with comfortable slack, *regardless of where the
deficits sit*. The realized prize ratio `M/√n` stays FLAT (`≈ 4.0–4.9`) across `a = 5..8`, NOT growing
like `√log(p/n)`, consistent with the route being walled.

This module records the **structure-free** form of the converse: the budget bound depends only on the
total `S`, so a directly-measured `S < (log 2 / 2)·a` certificate walls the route with no assumption on
*how* the deficit is distributed across levels (no leading block, no contiguity). It is a strict-form
corollary of `deficit_budget_ge_sqrt_scale_of_sublinear`, eliminating the auxiliary `ε` witness by
taking `ε = S / a`.

This is a Lane-3 **constraint lemma**: it does NOT discharge CORE. It states only that *this particular
bound* (the exp-relaxed dilation budget) stays at/above the `√`-scale whenever the realized total
coherence deficit is sub-`(log 2)/2`-per-level on average — which the measurement confirms at
`a = 5..8`. CORE `M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVDeficitSumScatteredFloor

open ArkLib.ProximityGap.Frontier.DoorIVDeficitBudgetSublinearFloor

/-- **Scattered-deficit sum floor (structure-free, strict measured form).**

If the *raw* total coherence deficit `S = ∑_{k<a} δ_k` over the `a`-level 2-dilation descent is strictly
below the linear-in-`a` budget threshold, `S < (log 2 / 2) · a` (with `a ≥ 1`), then for `M 0 ≥ 0` the
exp-relaxed deficit-budget bound stays at/above the `√(2^a)·M 0` Plancherel/prize scale:

    (√2)^a · M 0 ≤ 2^a · exp(−S) · M 0.

No assumption is made on **how** the deficit is distributed across the levels — there is no leading-zero
block, contiguity, or per-level cap hypothesis. The bound depends on the total `S` alone, which is the
invariant that survives in the measured worst-`b` descent (deficits scattered, not blocked). The
measurement gives `S < (log 2 / 2)·a` with slack at `a = 5..8`, so the *exp-relaxed* dilation budget
cannot witness a `√n`-scale bound there. Lane-3 constraint lemma; CORE not discharged. -/
theorem deficit_budget_ge_sqrt_scale_of_measured_sum {S M0 : ℝ} (a : ℕ)
    (ha : 1 ≤ a) (hS : S < Real.log 2 / 2 * a) (hM0 : 0 ≤ M0) :
    (Real.sqrt 2) ^ a * M0 ≤ 2 ^ a * Real.exp (-S) * M0 := by
  have hapos : (0 : ℝ) < (a : ℝ) := by
    have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  -- take ε = S / a
  refine deficit_budget_ge_sqrt_scale_of_sublinear a (ε := S / (a : ℝ)) ?_ ?_ hM0
  · -- S / a < log 2 / 2, from S < (log 2 / 2) * a
    rw [div_lt_iff₀ hapos]
    linarith [hS]
  · -- S ≤ (S / a) * a, in fact equality
    rw [div_mul_cancel₀ S (ne_of_gt hapos)]

end ArkLib.ProximityGap.Frontier.DoorIVDeficitSumScatteredFloor

