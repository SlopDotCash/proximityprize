/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CharZeroEnergyFiveExact

/-!
# AVENUE A continued: the exact char-0 depth-6 additive energy
# `E₆(μ_n) = 10395n⁶ − 155925n⁵ + 1022175n⁴ − 3534300n³ + 6246471n² − 4370520n`

`CharZeroEnergyFiveExact.lean` solved `B 10 m = E₅(μ_n)`. This file extends the SAME machinery the
FINAL rung of the in-tree closed-form ladder (`_AvGER_CharZeroEnergyRecursion` tabulates `E₁…E₆`) to
the depth-6 count `B 12 m = E₆(μ_n)`.

## The recursion (same Lam–Leung balance + add-one-class principle)

  `B 12 (m+1) = Σ_{j=0}^{6} C(12,2j)·C(2j,j)·B (12−2j) m`
            `= B 12 m + 132·B 10 m + 2970·B 8 m + 18480·B 6 m + 34650·B 4 m + 16632·B 2 m + 924`,

since `C(12,2)C(2,1)=132`, `C(12,4)C(4,2)=2970`, `C(12,6)C(6,3)=18480`, `C(12,8)C(8,4)=34650`,
`C(12,10)C(10,5)=16632`, `C(12,12)C(12,6)·(B 0 m=1)=924`. Carried as the new named field `rec12`,
NOT silently discharged. Probe-verified EXACT at m=1,2,4,8
(`B12 = 924, 853776, 357713664, 64941883776 = E₆` at `n = 2,4,8,16`), matching the in-tree closed
form `_AvGER_CharZeroEnergyRecursion.E6`.

## What THIS file proves (axiom-clean; reuses the proven B2/B4/B6/B8/B10 closed forms)

* `B12_closed` : `B 12 m = 665280m⁶ − 4989600m⁵ + 16354800m⁴ − 28274400m³ + 24985884m² − 8741040m`,
* `B12_eq_E6`  : `B 12 m = 10395(2m)⁶ − 155925(2m)⁵ + 1022175(2m)⁴ − 3534300(2m)³ + 6246471(2m)²
                 − 4370520(2m) = 10395n⁶−155925n⁵+1022175n⁴−3534300n³+6246471n²−4370520n` (`n = 2m`).

## Honest status (a REDUCTION of the open `E₆` input, not a CORE closure)

Same scope as the `E₃…E₅` files: replaces the open exact-`E₆` closed-form producer by a proof from the
recursion, relative to the SAME two elementary named inputs (Lam–Leung balance + add-one-class
recursion), now at depth 6. Does NOT touch the deep BGK/Paley wall (depth `r ≈ log m`), makes NO
CORE/cancellation/completion/moment-saving/anti-concentration/capacity claim; prize CORE stays OPEN.
This completes the char-0 energy combinatorial-exactness ladder through the full tabulated range
`E₁…E₆`, all relative to the same two elementary inputs. The `rec12` field is a named `Prop` field.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`. Issue #444 / #389.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.CharZeroEnergySix

open ArkLib.ProximityGap.Frontier.CharZeroEnergyThree (B2_closed B4_closed B6_closed)
open ArkLib.ProximityGap.Frontier.CharZeroEnergyFour (B8_closed)
open ArkLib.ProximityGap.Frontier.CharZeroEnergyFive (BalancedCount10 B10_closed)

/-- **The depth-≤6 balanced-class-count carrier.** Extends `BalancedCount10 B` by the depth-12
add-one-class recursion field, the depth-6 instance of the same elementary counting principle. -/
structure BalancedCount12 (B : ℕ → ℕ → ℤ) : Prop extends BalancedCount10 B where
  /-- The length-12 add-one-class recursion: new class takes `0,2,…,12` positions
      (`+ C(12,2)C(2,1)·B 10 m + C(12,4)C(4,2)·B 8 m + C(12,6)C(6,3)·B 6 m +
        C(12,8)C(8,4)·B 4 m + C(12,10)C(10,5)·B 2 m + C(12,12)C(12,6)`). -/
  rec12 : ∀ m, B 12 (m + 1)
      = B 12 m + 132 * B 10 m + 2970 * B 8 m + 18480 * B 6 m + 34650 * B 4 m + 16632 * B 2 m + 924

variable {B : ℕ → ℕ → ℤ}

/-- **`B 12 m = 665280m⁶ − 4989600m⁵ + 16354800m⁴ − 28274400m³ + 24985884m² − 8741040m`** — the
depth-6 zero-sum count `E₆(μ_{2m})`, solving `rec12` by induction with the proven lower closed
forms `B10/B8/B6/B4/B2`. -/
theorem B12_closed (h : BalancedCount12 B) (m : ℕ) :
    B 12 m = 665280 * (m : ℤ) ^ 6 - 4989600 * (m : ℤ) ^ 5 + 16354800 * (m : ℤ) ^ 4
        - 28274400 * (m : ℤ) ^ 3 + 24985884 * (m : ℤ) ^ 2 - 8741040 * m := by
  induction m with
  | zero => simpa using h.base0 12 (by norm_num)
  | succ k ih =>
      rw [h.rec12 k, ih, B10_closed h.toBalancedCount10 k,
        B8_closed h.toBalancedCount10.toBalancedCount8 k,
        B6_closed h.toBalancedCount10.toBalancedCount8.toBalancedCount k,
        B4_closed h.toBalancedCount10.toBalancedCount8.toBalancedCount k,
        B2_closed h.toBalancedCount10.toBalancedCount8.toBalancedCount k]
      push_cast; ring

/-- **AVENUE A `r = 6` target: `E₆(μ_n) = 10395n⁶−155925n⁵+1022175n⁴−3534300n³+6246471n²−4370520n`**
for `n = 2m`. The depth-6 additive-energy zero-sum count `B 12 m` equals `E₆`. Derived from
`B12_closed` by pure algebra. -/
theorem B12_eq_E6 (h : BalancedCount12 B) (m : ℕ) :
    B 12 m = 10395 * (2 * (m : ℤ)) ^ 6 - 155925 * (2 * (m : ℤ)) ^ 5
        + 1022175 * (2 * (m : ℤ)) ^ 4 - 3534300 * (2 * (m : ℤ)) ^ 3
        + 6246471 * (2 * (m : ℤ)) ^ 2 - 4370520 * (2 * (m : ℤ)) := by
  rw [B12_closed h]; ring

/-- **The exact anchor `E₆(μ_16) = 64941883776`** (`m = 8`), matching the closed form + probe. -/
theorem B12_eq_E6_anchor (h : BalancedCount12 B) : B 12 8 = 64941883776 := by
  rw [B12_closed h]; norm_num

end ArkLib.ProximityGap.Frontier.CharZeroEnergySix

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.CharZeroEnergySix.B12_closed
#print axioms ArkLib.ProximityGap.Frontier.CharZeroEnergySix.B12_eq_E6
#print axioms ArkLib.ProximityGap.Frontier.CharZeroEnergySix.B12_eq_E6_anchor
