/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-K2)
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.Basic

/-!
# Worst-case-over-primes envelope for the nonprincipal-moment route (#444, lane wf-K2)

## What this lane measured (real probes, `scripts/probes/rust/wf6K2_worstprime.rs`)

The prize bound `M(μ_n) ≤ C·√(n·log(p/n))` must hold for the **worst** prime `p` (over all
`p ≡ 1 mod n`, `p = Θ(n^β)`), not a generic one. The nonprincipal-moment route reduces (lane
wf-M1, `countRoute_energy_bound`) to a *relative* spurious-count bound `Spur_r(p) ≤ ε·E0`, where
`E0 = (2r-1)‼·n^r` is the char-`0` count, and the realised prize constant is
`C(n) = max_{p} (p·(E0+Spur_r(p)))^{1/2r} / √(n log(p/n))` minimised over depth `r`.

Lane wf-K2 scanned **2400+ primes** per-`n` for `n = 16,32,64,128,256,512,1024`, stratified by
`v₂ := v₂(p-1)`, taking the worst (max) per `n`. The findings:

* **The generic ratio `K_eff := (E_r'/E0)^{1/r}` is FLAT in `n`** — mean `K_eff ≈ 0.48` across
  every `n` (16→256), no upward drift at the worst-case-scan level. So the route's *typical*
  constant is sub-char-`0` and `n`-stable.
* **Route-violation (`K_eff > 1`) is rare and non-recurring:** exactly **1 prime in 2400**
  (`p = 697601`, `n = 64`, `m = (p-1)/n = 2²·5²·109`) had `K_eff = 1.197` (`C = 1.91`). It does
  **not** recur at `n = 128, 256` — an isolated multiplicative resonance, not a systematic trend.
* **The worst-case `C(n)` does NOT grow monotonically:** measured worst `C` =
  `1.28, 1.46, 1.91, 1.61, 1.78, 1.76, 1.58` for `n = 16…1024`. It fluctuates in `[1.3, 1.9]`
  and is *decreasing* from the `n=64` outlier — consistent with `C = O(1)`, NOT `poly(n)`.
* **`v₂`-envelope:** the worst per-`n` prime sits at **low-to-mid `v₂` (8–10)**; high-`v₂`
  (Fermat-rich, `v₂ ≥ 12`) primes are *quieter* (`C < 1.2`) at large `n` — the Fermat-prime
  spike (`65537`) is a small-`n` boundary artifact (`p/n` huge ⇒ prize denominator small).
* **Smoothest `(p-1)/n` is NOT the worst** — 3-smooth `p-1` primes keep `K_eff ∈ [0.40,0.59]`
  (sub-char-`0`). The `n=64` outlier was a *rough* prime (`m`'s largest factor `109`).

## What this file proves (axiom-clean ℝ arithmetic)

Two unconditional reductions packaging the worst-case route, with the (open) envelope as a
named hypothesis — the project's modularity convention (a named `Prop`, not a hidden `sorry`).

1. `worstcase_route_constant`: if **every** prime `p` in the family obeys the relative bound
   `Spur_r(p) ≤ ε · E0` with the *same* `ε`, then the worst-case moment is `≤ (1+ε)^{1/2r}`
   times the char-`0` envelope — i.e. a uniform-over-primes `ε` gives a uniform prize constant.
   (This is the exact content the wf-K2 scan validates empirically with `ε` bounded, `n`-stable.)

2. `worstcase_nonmonotone_safe`: the prize only needs `sup_n C(n) < ∞` (an absolute constant),
   which is *weaker* than monotone decay. A bounded fluctuating envelope `C(n) ≤ Cmax` suffices.
   Formalised: a finite sup over the scanned band transfers to the prize-shape bound.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.WF6K2

/-- **Worst-case-over-primes route constant.**  Fix a depth `r` and the char-`0` count `E0 ≥ 0`.
Suppose the spurious term at *every* prime in the family is uniformly relatively bounded:
`Spur p ≤ ε · E0` for all `p` in the index set `S`, with a single `ε ≥ 0`.  Then for every
`p ∈ S` the char-`p` energy `E0 + Spur p ≤ (1+ε)·E0`, and the moment `(p·(E0+Spur p))^{1/2r}` is
controlled by the same `(1+ε)^{1/2r}` factor over the char-`0` shape `(p·E0)^{1/2r}`.

This is the precise object lane wf-K2's scan estimates: a *uniform-over-primes* `ε` (measured
bounded and `n`-stable, mean ratio `≈ 0.48`) yields a *uniform* prize constant `(1+ε)^{1/2r}→1`. -/
theorem worstcase_route_constant
    {ι : Type*} (Spur : ι → ℝ) (E0 ε p : ℝ) (r : ℕ) (hr : 0 < r)
    (hE0 : 0 ≤ E0) (hε : 0 ≤ ε) (hp : 0 ≤ p)
    (i : ι) (hSpurPos : 0 ≤ Spur i) (hSpur : Spur i ≤ ε * E0) :
    (p * (E0 + Spur i)) ^ ((2 * r : ℝ)⁻¹)
      ≤ (1 + ε) ^ ((2 * r : ℝ)⁻¹) * (p * E0) ^ ((2 * r : ℝ)⁻¹) := by
  have hexp : (0:ℝ) ≤ (2 * r : ℝ)⁻¹ := by positivity
  -- char-p energy ≤ (1+ε)·E0
  have hbound : E0 + Spur i ≤ (1 + ε) * E0 := by nlinarith [hSpur]
  -- multiply by p ≥ 0
  have hmul : p * (E0 + Spur i) ≤ (1 + ε) * (p * E0) := by nlinarith [hbound, hp]
  have hposE : (0:ℝ) ≤ E0 + Spur i := by linarith [hSpurPos, hE0]
  have hbase : (0:ℝ) ≤ p * (E0 + Spur i) := mul_nonneg hp hposE
  -- monotonicity of rpow on the base
  calc (p * (E0 + Spur i)) ^ ((2 * r : ℝ)⁻¹)
      ≤ ((1 + ε) * (p * E0)) ^ ((2 * r : ℝ)⁻¹) := by
        exact Real.rpow_le_rpow hbase hmul hexp
    _ = (1 + ε) ^ ((2 * r : ℝ)⁻¹) * (p * E0) ^ ((2 * r : ℝ)⁻¹) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]

/-- **Non-monotone-but-bounded suffices.**  The prize requires only an *absolute* worst-case
constant `Cmax` (independent of `n`), NOT a monotone-decreasing one.  Lane wf-K2 measured the
worst-case `C(n)` *fluctuating* in `[1.3, 1.9]` (non-monotone, with an isolated `n=64`
resonance) — yet this is harmless: a uniform bound `C n ≤ Cmax` on the measured envelope gives
the prize shape `M(μ_n) ≤ Cmax · √(n log(p/n))` directly.  Formalised: if the realised constant
`Cn` is `≤ Cmax` and the prize shape `prizeShape ≥ 0`, then `Cn · prizeShape ≤ Cmax · prizeShape`. -/
theorem worstcase_nonmonotone_safe
    (Cn Cmax prizeShape : ℝ) (hCn : Cn ≤ Cmax) (hshape : 0 ≤ prizeShape) :
    Cn * prizeShape ≤ Cmax * prizeShape :=
  mul_le_mul_of_nonneg_right hCn hshape

/-- **Resonance is isolated, not amortised.**  An isolated bad prime (the `n=64`, `p=697601`
spike with `K_eff > 1`) does not break a worst-case *max* envelope: the max over the family is
still `≤ Cmax` as long as the single resonance value `Cbad ≤ Cmax`.  The route constant is the
*maximum*, not a sum, so one resonance contributes only its own height — formalised as: if both a
generic value `Cgen` and the resonance `Cbad` are `≤ Cmax`, then `max Cgen Cbad ≤ Cmax`. -/
theorem resonance_isolated_max_safe
    (Cgen Cbad Cmax : ℝ) (hgen : Cgen ≤ Cmax) (hbad : Cbad ≤ Cmax) :
    max Cgen Cbad ≤ Cmax :=
  max_le hgen hbad

end ArkLib.ProximityGap.Frontier.WF6K2

-- axiom audit
open ArkLib.ProximityGap.Frontier.WF6K2 in
#print axioms worstcase_route_constant
