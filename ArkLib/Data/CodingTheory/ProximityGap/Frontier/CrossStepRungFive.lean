/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CrossStepRungFour

/-!
# The `r = 5` rung of the open per-step crux `M3CrossStepBound` from the exact `E_5`, `E_6` closed forms (Issue #444)

`CrossStepRungOne/Two/Three/Four` discharged the rungs `r = 0, 1, 2, 3, 4` of the open `Prop`

    `M3CrossStepBound G : ∀ r, crossMass G r ≤ 2r·(2r−1)‼·n^{r+1}`,   `crossMass G r = E_{r+1} − n·E_r`

(`n = |G|`) by wiring the recursion's `crossMass` object to the proven exact char-`0` energy closed
forms. This file extends the ladder to **`r = 5`**, using the two in-tree closed forms that nobody
had connected to the rung machinery:

* `E_5 = 945n⁵ − 9450n⁴ + 39375n³ − 77175n² + 57456n`     (carried in `CrossStepRungFour`),
* `E_6 = 10395n⁶ − 155925n⁵ + 1022175n⁴ − 3534300n³ + 6246471n² − 4370520n`
  (`_CharZeroEnergyClosedForm`, leading `(2·6−1)‼ = 11‼ = 10395`).

## The exact value of the `r = 5` cross mass

By the proven substrate recursion `rEnergy_succ_crossMass` at `r = 5`,
`E_6 = n·E_5 + crossMass G 5`, so

> **`crossMass G 5 = E_6 − n·E_5 = 9450n⁶ − 146475n⁵ + 982800n⁴ − 3457125n³ + 6189015n² − 4370520n`.**

The step target at `r = 5` is `2·5·(2·5−1)‼·n⁶ = 10·945·n⁶ = 9450n⁶`. Consistent with the uniform
cross-step law (`CrossStepRungFour`):

* **Leading coefficient `9450` is EXACTLY the step target** — the rung is leading-order tight.
* **Second coefficient `−146475` is strictly negative**, with the law `−(r²+r+1)/2·2r·(2r−1)‼`
  at `r = 5`: `−(31/2)·9450 = −146475`. The rung holds because the first correction is a negative
  `O(n⁵)` deficit. (Ratio `crossMass G 5 / 9450n⁶ = .358, .607, .782, .885, .941` at
  `n = 16, 32, 64, 128, 256`; monotone↑, `→ 1` from below.)

The slack `target − crossMass G 5 = 146475n⁵ − 982800n⁴ + 3457125n³ − 6189015n² + 4370520n` is
`≥ 0` for all `n ≥ 1` (exact bigint check `n ≤ 10⁵`; the binding ℕ-truncated dominations
`982800/146475 ≈ 6.7`, `6189015/3457125 ≈ 1.8` all hold at `n ≥ 16`, the prize regime `n = 2^a ≥ 16`).

## Results (axiom-clean, ℕ-arithmetic on the proven recursion)

* `rEnergy_six_eq`                 : `E_6 = n·E_5 + crossMass G 5` (the exact recursion at `r = 5`).
* `crossStepBound_five_iff`        : `crossMass G 5 ≤ 9450n⁶  ↔  E_6 ≤ 9450n⁶ + n·E_5` (both ways).
* `crossStepBound_five_of_sharpE6` : `E_6 ≤ 9450n⁶ + n·E_5 ⟹ crossMass G 5 ≤ 9450n⁶`.
* `crossStepBound_five_of_exact_moments` : exact `E_5` + exact `E_6 ⟹` the `r = 5` rung,
    UNCONDITIONALLY (for `n ≥ 16` so the displayed ℕ-truncated closed forms are faithful).

## Honest scope (rules 1, 3, 4, 6)

This adds the `r = 5` rung of `M3CrossStepBound`, *conditional on the two exact char-`0`-faithful
moment closed forms as hypotheses* (the same shape as `CrossStepRungFour`). It does NOT prove
`M3CrossStepBound` for the `∀ r` form (the deep rungs `r ≥ 6` stay the open char-`p` wall, each
needing its own exact `E_{r+1}` closed form), and does NOT supply the char-`p` transfer at the prize
depth `r ≈ ln q` — the closed forms are char-`0`-faithful only above the root-norm threshold
`p > (2r)^{n/2}`, false at prize scale. CORE (`M(μ_n) ≤ C√(n·log(p/n))`) stays OPEN. No capacity /
beyond-Johnson / growth-law claim. This is a frontier-EXTENSION of a proven theorem onto in-tree
closed forms, not a new lever.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issue #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.CrossStepCeiling (crossMass rEnergy_succ_crossMass)

namespace ArkLib.ProximityGap.CrossStepRungFive

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `n ≥ 16` power-step helper: `a ≤ b·n ⟹ a·n^k ≤ b·n^{k+1}` (via `n^{k+1} = n^k·n`). -/
private lemma pow_step_le {a b n k : ℕ} (h : a ≤ b * n) : a * n ^ k ≤ b * n ^ (k + 1) := by
  calc a * n ^ k ≤ (b * n) * n ^ k := Nat.mul_le_mul_right _ h
    _ = b * n ^ (k + 1) := by ring

/-- **The exact `r = 5` recursion: `E_6 = n·E_5 + crossMass G 5`.** Direct instance of the proven
substrate recursion `rEnergy_succ_crossMass G 5`. -/
theorem rEnergy_six_eq (G : Finset F) :
    rEnergy G 6 = G.card * rEnergy G 5 + crossMass G 5 := by
  have hrec := rEnergy_succ_crossMass G 5
  simpa using hrec

/-- **The `r = 5` rung is EXACTLY a sixth-moment ceiling.** `crossMass G 5 ≤ 9450·n⁶` (the step
target, `2·5·(2·5−1)‼·n⁶ = 9450n⁶`) iff `E_6 ≤ 9450·n⁶ + n·E_5`. Pure arithmetic on the exact
recursion. -/
theorem crossStepBound_five_iff (G : Finset F) :
    crossMass G 5 ≤ 9450 * G.card ^ 6 ↔ rEnergy G 6 ≤ 9450 * G.card ^ 6 + G.card * rEnergy G 5 := by
  have hrec := rEnergy_six_eq G
  constructor
  · intro h; omega
  · intro h; omega

/-- **The `r = 5` rung from a sharp `E_6` ceiling.** If `E_6 ≤ 9450n⁶ + n·E_5` then the `r = 5` rung
of `M3CrossStepBound` holds: `crossMass G 5 ≤ 9450n⁶`. (Step coefficient `2·5·(2·5−1)‼ = 10·945 =
9450`.) -/
theorem crossStepBound_five_of_sharpE6 (G : Finset F)
    (h : rEnergy G 6 ≤ 9450 * G.card ^ 6 + G.card * rEnergy G 5) :
    crossMass G 5 ≤ 9450 * G.card ^ 6 :=
  (crossStepBound_five_iff G).mpr h

/-- **THE `r = 5` RUNG, UNCONDITIONAL FROM THE EXACT CLOSED-FORM MOMENTS.** Given the exact fifth
moment `E_5 = 945n⁵ − 9450n⁴ + 39375n³ − 77175n² + 57456n` and the exact sixth moment
`E_6 = 10395n⁶ − 155925n⁵ + 1022175n⁴ − 3534300n³ + 6246471n² − 4370520n` (the two char-`0`-faithful
closed forms on `μ_{2^m}`), the `r = 5` rung of the open crux `M3CrossStepBound` holds:
`crossMass G 5 ≤ 9450n⁶`. (`n ≥ 16` so the displayed ℕ-truncated closed forms are faithful; `μ_n` has
`n = 2^a ≥ 16` in the prize regime.) -/
theorem crossStepBound_five_of_exact_moments (G : Finset F) (hn : 16 ≤ G.card)
    (hE5 : rEnergy G 5 = 945 * G.card ^ 5 - 9450 * G.card ^ 4 + 39375 * G.card ^ 3
                          - 77175 * G.card ^ 2 + 57456 * G.card)
    (hE6 : rEnergy G 6 = 10395 * G.card ^ 6 - 155925 * G.card ^ 5 + 1022175 * G.card ^ 4
                          - 3534300 * G.card ^ 3 + 6246471 * G.card ^ 2 - 4370520 * G.card) :
    crossMass G 5 ≤ 9450 * G.card ^ 6 := by
  apply crossStepBound_five_of_sharpE6
  set n := G.card with hndef
  have hc16 : (16 : ℕ) ≤ n := hn
  -- n·E_5 = 945n⁶ − 9450n⁵ + 39375n⁴ − 77175n³ + 57456n²  (faithful ℕ subtraction at n ≥ 16)
  have hmul : n * rEnergy G 5
      = 945 * n ^ 6 - 9450 * n ^ 5 + 39375 * n ^ 4 - 77175 * n ^ 3 + 57456 * n ^ 2 := by
    rw [hE5]
    -- reorder to additions-then-subtractions so the multiplication distributes cleanly
    have e1 : 945 * n ^ 5 - 9450 * n ^ 4 + 39375 * n ^ 3 - 77175 * n ^ 2 + 57456 * n
            = (945 * n ^ 5 + 39375 * n ^ 3 + 57456 * n) - (9450 * n ^ 4 + 77175 * n ^ 2) := by
      have hb1 : 9450 * n ^ 4 ≤ 945 * n ^ 5 := pow_step_le (by omega)
      have hb2 : 77175 * n ^ 2 ≤ 39375 * n ^ 3 := by
        have := pow_step_le (a := 77175) (b := 39375) (n := n) (k := 2) (by omega); simpa using this
      omega
    rw [e1, Nat.mul_sub, Nat.mul_add, Nat.mul_add, Nat.mul_add]
    have hp1 : n * (945 * n ^ 5) = 945 * n ^ 6 := by ring
    have hp2 : n * (39375 * n ^ 3) = 39375 * n ^ 4 := by ring
    have hp3 : n * (57456 * n) = 57456 * n ^ 2 := by ring
    have hp4 : n * (9450 * n ^ 4) = 9450 * n ^ 5 := by ring
    have hp5 : n * (77175 * n ^ 2) = 77175 * n ^ 3 := by ring
    rw [hp1, hp2, hp3, hp4, hp5]
    -- goal: (945n⁶ + 39375n⁴ + 57456n²) − (9450n⁵ + 77175n³)
    --       = 945n⁶ − 9450n⁵ + 39375n⁴ − 77175n³ + 57456n²
    have hb3 : 9450 * n ^ 5 ≤ 945 * n ^ 6 := pow_step_le (by omega)
    have hb4 : 77175 * n ^ 3 ≤ 39375 * n ^ 4 := by
      have := pow_step_le (a := 77175) (b := 39375) (n := n) (k := 3) (by omega); simpa using this
    omega
  rw [hE6, hmul]
  -- Goal: E_6 ≤ 9450n⁶ + (945n⁶ − 9450n⁵ + 39375n⁴ − 77175n³ + 57456n²)
  --             = 10395n⁶ − 9450n⁵ + 39375n⁴ − 77175n³ + 57456n²
  -- i.e. 10395n⁶−155925n⁵+1022175n⁴−3534300n³+6246471n²−4370520n
  --        ≤ 10395n⁶−9450n⁵+39375n⁴−77175n³+57456n²
  -- slack = 146475n⁵ − 982800n⁴ + 3457125n³ − 6189015n² + 4370520n ≥ 0 for n ≥ 16.
  -- supply omega with the truncation/domination bounds.
  have c1 : 155925 * n ^ 5 ≤ 10395 * n ^ 6 := pow_step_le (by omega)
  have c2 : 3534300 * n ^ 3 ≤ 1022175 * n ^ 4 := by
    have := pow_step_le (a := 3534300) (b := 1022175) (n := n) (k := 3) (by omega); simpa using this
  have c3 : 4370520 * n ≤ 6246471 * n ^ 2 := by
    have := pow_step_le (a := 4370520) (b := 6246471) (n := n) (k := 1) (by omega); simpa using this
  have c4 : 9450 * n ^ 5 ≤ 10395 * n ^ 6 := pow_step_le (by omega)
  have c5 : 77175 * n ^ 3 ≤ 39375 * n ^ 4 := by
    have := pow_step_le (a := 77175) (b := 39375) (n := n) (k := 3) (by omega); simpa using this
  -- slack 146475n⁵ + 3457125n³ + 4370520n ≥ 982800n⁴ + 6189015n²  (each side dominated at n ≥ 16)
  have hslackA : 982800 * n ^ 4 ≤ 146475 * n ^ 5 := by
    have := pow_step_le (a := 982800) (b := 146475) (n := n) (k := 4) (by omega); simpa using this
  have hslackB : 6189015 * n ^ 2 ≤ 3457125 * n ^ 3 := by
    have := pow_step_le (a := 6189015) (b := 3457125) (n := n) (k := 2) (by omega); simpa using this
  omega

end ArkLib.ProximityGap.CrossStepRungFive

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CrossStepRungFive.rEnergy_six_eq
#print axioms ArkLib.ProximityGap.CrossStepRungFive.crossStepBound_five_iff
#print axioms ArkLib.ProximityGap.CrossStepRungFive.crossStepBound_five_of_sharpE6
#print axioms ArkLib.ProximityGap.CrossStepRungFive.crossStepBound_five_of_exact_moments
