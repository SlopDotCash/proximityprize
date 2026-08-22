/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.NNReal.Basic

/-!
# SYZ58: curve (`ℓ > 2`) events are **out of scope** for the rate-`1/4` prize ceiling (issue #466)

This file records the honest outcome of the "fresh angle" on the rate-`1/4` ceiling: circumvent
the SYZ5 integer-`D` no-go (`_SYZ5RateQuarterChannelCeiling.lean`, floor `1/2 > 43/96`) by moving
from the affine-line pair event to the **higher-degree curve / power-generator event**
`mcaEventCurve` at `ℓ > 2`, whose degree-`(ℓ−1)` pencil conditions donate `(ℓ−1)` times as many
bad scalars `γ` per degenerate core — dissolving the non-integer `D = 7/3` crossing that pins the
SYZ5 floor.

## The arithmetic *does* dissolve the obstruction — on the wrong error function

Replaying the SYZ9 channel-wall elimination (`_SYZ9ChannelRankWall.lean`) with a per-core yield
scaled by `Y = ℓ − 1` (degree-`(ℓ−1)` equations in `γ` per non-core point) gives, with the same
rank budget `D·(t−k) < n−k`:

```
  budget-beat  B < D·Y·c ,   rank  D·(t−k) < n−k = R ,   c = n − t
  ⟹  (t−k)·B  <  Y·(n−k)·(n−t)          (`curveChannel_master`, below)
  ⟹  radius floor  δ = (n−t)/n  >  (1−ρ) / (1 + Y·(1−ρ)) .
```

At `ρ = 1/4` (`1−ρ = 3/4`) the floor is `3 / (4 + 3Y)`:

* `Y = 1` (`ℓ = 2`, the pair event): `3/7 ≈ 0.4286` — SYZ9's real-`D` infimum, integer-refined to
  `1/2` by SYZ5;
* `Y = 2` (`ℓ = 3`): `3/10 = 0.3`;
* `Y = 3` (`ℓ = 4`): `3/13 ≈ 0.2308`.

So *arithmetically* the curve channel starves only below `3/(4+3Y)`, which drops **below** the
current ceiling `43/96 ≈ 0.4479` already at `ℓ = 3`. The `D = 7/3` obstruction genuinely dissolves.

## But the prize object does not consume curve events

The prize threshold is
`ProximityGap.MCAThresholdLedger.mcaDeltaStar C ε* = sSup {δ ≤ 1 | epsMCA C δ ≤ ε*}`, and
`epsMCA` is the `Fin 2` **affine-line** error (`u₀ + γ·u₁`). The curve / power-generator event
lives in a genuinely distinct error function:

* `ProximityGap.epsMCACurve C ℓ δ` (`MCACurveEvent.lean`), equivalently
  `ProximityGap.Jo26Gen.epsMCAGen` at the power generator
  (`epsMCAGen_powGen_eq_epsMCAP`, `epsMCAGen_val_eq_epsMCACurve`);
* it **coincides with `epsMCA` only at `ℓ = 2`** (`epsMCACurve_two_eq_epsMCA`,
  `epsMCAGen_pairGen_eq_epsMCA`); for `ℓ > 2` it is a strict extension;
* **no threshold object in the tree is a `sSup` over `epsMCACurve`.** `mcaDeltaStar` — the object
  the `43/96` pin (`_P1RateQuarterAdjacentExactPin.canonical_mcaDeltaStar_le_common_delta`) and
  the `3/8` floor (`_P1RateQuarterOperationalBracket.threeEighths_le_rateQuarter_mcaDeltaStar`)
  both bound — is a `sSup` over `epsMCA` (`= epsMCAGen` at the *pair* generator) exclusively.

Inflating `epsMCACurve` at radius `< 43/96` (which the `ℓ = 3` channel does) says nothing about
`epsMCA` at that radius, hence nothing about `mcaDeltaStar`. **Angle 1 is out of scope.**

## An in-tree consistency proof that the two objects cannot be identified

If the `ℓ = 3` curve channel *did* bound `mcaDeltaStar`, it would certify `mcaDeltaStar ≤ 3/10`.
But the **unconditional** good-side floor
`threeEighths_le_rateQuarter_mcaDeltaStar : 3/8 ≤ mcaDeltaStar` is already landed for the same
`epsMCA`-defined object. Since `3/10 < 3/8`, the curve-channel bound is *inconsistent* with the
proven floor — so the curve channel provably does **not** bound `mcaDeltaStar`. This is not a
choice of convention: the extant `3/8` lower bracket forces the two error functions apart at
rate `1/4`.

(No back-transfer rescues it. Padding a pair-bad stack `(u₀,u₁)` to `(u₀,u₁,0,…,0)` gives a
curve-bad stack, i.e. `epsMCA ≤ epsMCACurve`; that only lowers the *curve* threshold below the
prize threshold — the wrong direction. A genuine `ℓ > 2` curve event with nonzero higher rows uses
a degree-`(ℓ−1)` combiner that is not an affine line, so it does not entail any pair event.)

## Verdict

The `ℓ > 2` curve/generator event is **out of scope** for the sponsor's rate-`1/4` ceiling object
`mcaDeltaStar` (which is `sSup` over `epsMCA`, the `Fin 2` pair event). The higher-degree pencil
yield dissolves the SYZ5 integer-`D` floor — but only for `epsMCACurve`, a distinct error the
prize does not consume. No new production ceiling below `43/96` follows. The `43/96` pin and the
`3/8` floor stand unchanged.

Axiom-clean (pure `ℕ`/`ℚ` arithmetic; `#print axioms` below). No `sorry`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.SYZ58RateQuarterCurveEventScope

/-! ## The `ℓ`-scaled channel master inequality (SYZ9 with per-core yield `Y = ℓ − 1`) -/

/-- **Curve-channel master inequality.** With `D` degenerate cores, per-core agreement excess
`m = t − k`, complement `c = n − t`, syndrome codimension `R = n − k`, budget `B`, and per-core
curve yield `Y = ℓ − 1` (degree-`(ℓ−1)` pencil equations in `γ`), the rank budget `D·m < R` and
the budget-beat `B < D·Y·c` together force `m·B < Y·R·c` — the `D`-free radius wall. -/
theorem curveChannel_master
    {D m c R B Y : ℕ}
    (hrank : D * m < R) (hbudget : B < D * Y * c) :
    m * B < Y * R * c := by
  -- `c > 0` (else `hbudget : B < 0` is impossible) and `m·B ≤ (D·m)·(Y·c) ≤ (R-1)·(Y·c) < R·Y·c`.
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · simp [h] at hbudget
    · exact h
  have hY : 0 < Y := by
    rcases Nat.eq_zero_or_pos Y with h | h
    · simp [h] at hbudget
    · exact h
  have h1 : m * B ≤ m * (D * Y * c) := Nat.mul_le_mul_left m (Nat.le_of_lt hbudget)
  have h2 : m * (D * Y * c) = (D * m) * (Y * c) := by ring
  have h3 : (D * m) * (Y * c) < R * (Y * c) :=
    Nat.mul_lt_mul_of_pos_right hrank (Nat.mul_pos hY hc)
  have h4 : R * (Y * c) = Y * R * c := by ring
  omega

/-! ## The rational radius floor `(1−ρ)/(1 + Y·(1−ρ))` and its collapse at rate `1/4` -/

/-- The continuous-`D` curve-channel radius floor at rate `1/4` with per-core yield `Y`:
`3 / (4 + 3Y)`. -/
def rateQuarterCurveFloor (Y : ℕ) : ℚ := 3 / (4 + 3 * Y)

/-- `Y = 1` (`ℓ = 2`, the pair event) reproduces SYZ9's real-`D` infimum `3/7`. -/
theorem rateQuarterCurveFloor_one : rateQuarterCurveFloor 1 = 3 / 7 := by
  norm_num [rateQuarterCurveFloor]

/-- `Y = 2` (`ℓ = 3`) gives `3/10`. -/
theorem rateQuarterCurveFloor_two : rateQuarterCurveFloor 2 = 3 / 10 := by
  norm_num [rateQuarterCurveFloor]

/-- **The curve channel starves below `43/96` already at `ℓ = 3`.**  The `Y = 2` floor `3/10` is
strictly below the current rate-`1/4` ceiling `43/96 + 1/(3·2^30)`.  So *if* curve events counted,
the ceiling would collapse — they do not, which is the whole content of SYZ58. -/
theorem rateQuarterCurveFloor_two_lt_ceiling :
    rateQuarterCurveFloor 2 < (43 : ℚ) / 96 + 1 / (3 * 2 ^ 30) := by
  norm_num [rateQuarterCurveFloor]

/-- **The in-tree consistency wall.**  The `ℓ = 3` curve-channel floor `3/10` is strictly below the
*unconditional* good-side floor `3/8`
(`_P1RateQuarterOperationalBracket.threeEighths_le_rateQuarter_mcaDeltaStar`,
`3/8 ≤ mcaDeltaStar`).  Hence a curve-channel bound `mcaDeltaStar ≤ 3/10` would contradict a
proven theorem: the curve channel provably does **not** bound the prize object. -/
theorem rateQuarterCurveFloor_two_lt_goodFloor :
    rateQuarterCurveFloor 2 < (3 : ℚ) / 8 := by
  norm_num [rateQuarterCurveFloor]

/-- **The SYZ58 verdict.**  The curve yield dissolves the SYZ5 integer-`D` obstruction
(`3/10 < 43/96`), but the resulting bound is inconsistent with the proven `epsMCA` good-side floor
(`3/10 < 3/8 ≤ mcaDeltaStar`), so it bounds only the distinct object `epsMCACurve`, not the prize
`mcaDeltaStar`.  Out of scope; no ceiling below `43/96` follows. -/
theorem curve_event_out_of_scope_rateQuarter :
    rateQuarterCurveFloor 2 < (43 : ℚ) / 96 + 1 / (3 * 2 ^ 30) ∧
      rateQuarterCurveFloor 2 < (3 : ℚ) / 8 :=
  ⟨rateQuarterCurveFloor_two_lt_ceiling, rateQuarterCurveFloor_two_lt_goodFloor⟩

end ArkLib.ProximityGap.Frontier.SYZ58RateQuarterCurveEventScope

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.SYZ58RateQuarterCurveEventScope
#print axioms curveChannel_master
#print axioms rateQuarterCurveFloor_two_lt_ceiling
#print axioms rateQuarterCurveFloor_two_lt_goodFloor
#print axioms curve_event_out_of_scope_rateQuarter
