/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CharZeroEnergySevenExact
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvL2_E8ClosedForm

/-!
# AVENUE A continued: the exact char-0 depth-8 additive energy `E₈(μ_n)` from the recursion

`CharZeroEnergySevenExact.lean` solved `B 14 m = E₇(μ_n)`. This file extends the SAME machinery to the
depth-8 count `B 16 m = E₈(μ_n)`, proven equal to the in-tree closed form `_AvL2_E8ClosedForm.E8`
(previously only `def`'d + `decide`-anchored). Discharges the open exact-`E₈` producer of
`CrossStepRungSeven` (the `r = 7` cross-step rung).

## The recursion

  `B 16 (m+1) = Σ_{j=0}^{8} C(16,2j)·C(2j,j)·B (16−2j) m`
            `= B 16 m + 240·B 14 m + 10920·B 12 m + 160160·B 10 m + 900900·B 8 m
               + 2018016·B 6 m + 1681680·B 4 m + 411840·B 2 m + 12870`.

Carried as the named field `rec16`. Probe-verified EXACT at m=1,2,3,4,8
(`B16 = 12870, 165636900, 27770358330, 839358285480, 1369263687414480 = E₈` at `n = 2,4,6,8,16`),
matching ALL in-tree `decide`-anchors `_AvL2_E8ClosedForm.E8_two/four/six`.

## What THIS file proves (axiom-clean; reuses the proven B2…B14 closed forms)

* `B16_closed` : `B 16 m = 518918400m⁸ − 7264857600m⁷ + 46616169600m⁶ − 174053880000m⁵
                 + 400894013520m⁴ − 559479800880m³ + 429754447980m² − 136984998150m`,
* `B16_eq_E8`  : `B 16 m = E8 (2m)` (the in-tree closed form), with `n = 2m`.

## Honest status

Same scope as the `E₃…E₇` files: a REDUCTION of the open exact-`E₈` producer to a proof from the SAME
two elementary named inputs (Lam–Leung balance + add-one-class recursion), now at depth 8. Does NOT
touch the deep BGK/Paley wall (depth `r ≈ log m`, not `r = 8`); makes NO CORE/cancellation/completion/
moment-saving/anti-concentration/capacity claim; prize CORE stays OPEN. The `rec16` field is a named
`Prop` field, NOT discharged.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`. Issue #444 / #389.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.CharZeroEnergyEight

open ArkLib.ProximityGap.Frontier.CharZeroEnergyThree (B2_closed B4_closed B6_closed)
open ArkLib.ProximityGap.Frontier.CharZeroEnergyFour (B8_closed)
open ArkLib.ProximityGap.Frontier.CharZeroEnergyFive (B10_closed)
open ArkLib.ProximityGap.Frontier.CharZeroEnergySix (B12_closed)
open ArkLib.ProximityGap.Frontier.CharZeroEnergySeven (BalancedCount14 B14_closed)
open ProximityGap.Frontier.E8ClosedForm (E8)

/-- **The depth-≤8 balanced-class-count carrier.** Extends `BalancedCount14 B` by the depth-16
add-one-class recursion field, the depth-8 instance of the same elementary counting principle. -/
structure BalancedCount16 (B : ℕ → ℕ → ℤ) : Prop extends BalancedCount14 B where
  /-- The length-16 add-one-class recursion: new class takes `0,2,…,16` positions. -/
  rec16 : ∀ m, B 16 (m + 1)
      = B 16 m + 240 * B 14 m + 10920 * B 12 m + 160160 * B 10 m + 900900 * B 8 m
          + 2018016 * B 6 m + 1681680 * B 4 m + 411840 * B 2 m + 12870

variable {B : ℕ → ℕ → ℤ}

/-- **`B 16 m = 518918400m⁸ − 7264857600m⁷ + 46616169600m⁶ − 174053880000m⁵ + 400894013520m⁴
− 559479800880m³ + 429754447980m² − 136984998150m`** — the depth-8 zero-sum count `E₈(μ_{2m})`,
solving `rec16` by induction. -/
theorem B16_closed (h : BalancedCount16 B) (m : ℕ) :
    B 16 m = 518918400 * (m : ℤ) ^ 8 - 7264857600 * (m : ℤ) ^ 7 + 46616169600 * (m : ℤ) ^ 6
        - 174053880000 * (m : ℤ) ^ 5 + 400894013520 * (m : ℤ) ^ 4 - 559479800880 * (m : ℤ) ^ 3
        + 429754447980 * (m : ℤ) ^ 2 - 136984998150 * m := by
  induction m with
  | zero => simpa using h.base0 16 (by norm_num)
  | succ k ih =>
      rw [h.rec16 k, ih, B14_closed h.toBalancedCount14 k,
        B12_closed h.toBalancedCount14.toBalancedCount12 k,
        B10_closed h.toBalancedCount14.toBalancedCount12.toBalancedCount10 k,
        B8_closed h.toBalancedCount14.toBalancedCount12.toBalancedCount10.toBalancedCount8 k,
        B6_closed
          h.toBalancedCount14.toBalancedCount12.toBalancedCount10.toBalancedCount8.toBalancedCount k,
        B4_closed
          h.toBalancedCount14.toBalancedCount12.toBalancedCount10.toBalancedCount8.toBalancedCount k,
        B2_closed
          h.toBalancedCount14.toBalancedCount12.toBalancedCount10.toBalancedCount8.toBalancedCount k]
      push_cast; ring

/-- **AVENUE A `r = 8` target: `B 16 m = E8 (2m)`** — the depth-8 additive-energy zero-sum count equals
the in-tree closed form `_AvL2_E8ClosedForm.E8` at `n = 2m`. Derived from `B16_closed` by pure algebra.
Discharges the open exact-`E₈` producer of `CrossStepRungSeven`. -/
theorem B16_eq_E8 (h : BalancedCount16 B) (m : ℕ) :
    B 16 m = E8 (2 * (m : ℤ)) := by
  rw [B16_closed h]; simp only [E8]; ring

/-- **The exact anchor `E₈(μ_16) = 1369263687414480`** (`m = 8`, `n = 16`), matching the recursion and
`E8 16` of the in-tree closed form (which also `decide`-anchors `E8_two/four/six` at `n = 2,4,6`). -/
theorem B16_anchor (h : BalancedCount16 B) : B 16 8 = 1369263687414480 := by
  rw [B16_closed h]; norm_num

end ArkLib.ProximityGap.Frontier.CharZeroEnergyEight

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.CharZeroEnergyEight.B16_closed
#print axioms ArkLib.ProximityGap.Frontier.CharZeroEnergyEight.B16_eq_E8
#print axioms ArkLib.ProximityGap.Frontier.CharZeroEnergyEight.B16_anchor
