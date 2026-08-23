/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CrossStepRungFive
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvL2_E7ClosedForm

/-!
# The `r = 6` cross-step rung from the exact `E_6`, `E_7` closed forms (#444)

This file extends the finite checked prefix of the open per-step crux

`crossMass G r ≤ 2r · (2r−1)‼ · |G|^(r+1)`

by one further concrete rung.  `CrossStepRungFive` wires `r = 5` through `E_5,E_6`; here we wire
`r = 6` through the in-tree exact char-`0` closed form for `E_7`.

The exact subtraction gives

`crossMass G 6 = E_7 − nE_6`

and, under the displayed faithful closed forms,

```
crossMass G 6 = 124740 n^7 − 2681910 n^6 + 25779600 n^5 − 138357450 n^4
                + 427479822 n^3 − 704625768 n^2 + 471556800 n.
```

The target coefficient is `2·6·11‼ = 124740`.  The slack is

```
2681910 n^6 − 25779600 n^5 + 138357450 n^4 − 427479822 n^3
  + 704625768 n^2 − 471556800 n,
```

which is nonnegative by elementary coefficient absorption.  The formal closed-form hypotheses are used
in the faithful sequential-`Nat` subtraction window `n ≥ 32` for `E_7`.  This is a concrete frontier extension only: it does not prove the `∀ r` statement, does
not transfer the char-`0` closed forms to char `p` at prize depth, and does not touch CORE.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.CrossStepCeiling (crossMass rEnergy_succ_crossMass)

namespace ArkLib.ProximityGap.CrossStepRungSix

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `a ≤ b·n ⟹ a·n^k ≤ b·n^(k+1)`. -/
private lemma pow_step_le {a b n k : ℕ} (h : a ≤ b * n) : a * n ^ k ≤ b * n ^ (k + 1) := by
  calc a * n ^ k ≤ (b * n) * n ^ k := Nat.mul_le_mul_right _ h
    _ = b * n ^ (k + 1) := by ring

/-- The exact `r = 6` recursion: `E_7 = n·E_6 + crossMass G 6`. -/
theorem rEnergy_seven_eq (G : Finset F) :
    rEnergy G 7 = G.card * rEnergy G 6 + crossMass G 6 := by
  simpa using rEnergy_succ_crossMass G 6

/-- The `r = 6` rung is exactly the seventh-moment ceiling with the `n·E_6` term moved across. -/
theorem crossStepBound_six_iff (G : Finset F) :
    crossMass G 6 ≤ 124740 * G.card ^ 7 ↔
      rEnergy G 7 ≤ 124740 * G.card ^ 7 + G.card * rEnergy G 6 := by
  have hrec := rEnergy_seven_eq G
  constructor
  · intro h; omega
  · intro h; omega

/-- A sharp seventh-moment ceiling implies the `r = 6` cross-step rung. -/
theorem crossStepBound_six_of_sharpE7 (G : Finset F)
    (h : rEnergy G 7 ≤ 124740 * G.card ^ 7 + G.card * rEnergy G 6) :
    crossMass G 6 ≤ 124740 * G.card ^ 7 :=
  (crossStepBound_six_iff G).mpr h

/-- **The concrete `r = 6` rung from the exact closed-form moments.** Given the exact sixth and
seventh char-`0`-faithful moment polynomials, the open per-step crux holds at `r = 6`:
`crossMass G 6 ≤ 124740 n^7`, for `n ≥ 32`. -/
theorem crossStepBound_six_of_exact_moments (G : Finset F) (hn : 32 ≤ G.card)
    (hE6 : rEnergy G 6 = 10395 * G.card ^ 6 - 155925 * G.card ^ 5 + 1022175 * G.card ^ 4
                          - 3534300 * G.card ^ 3 + 6246471 * G.card ^ 2 - 4370520 * G.card)
    (hE7 : rEnergy G 7 = 135135 * G.card ^ 7 - 2837835 * G.card ^ 6 + 26801775 * G.card ^ 5
                          - 141891750 * G.card ^ 4 + 433726293 * G.card ^ 3
                          - 708996288 * G.card ^ 2 + 471556800 * G.card) :
    crossMass G 6 ≤ 124740 * G.card ^ 7 := by
  apply crossStepBound_six_of_sharpE7
  set n := G.card with hndef
  have hc32 : (32 : ℕ) ≤ n := hn
  have hc16 : (16 : ℕ) ≤ n := by omega
  have hmul : n * rEnergy G 6
      = 10395 * n ^ 7 - 155925 * n ^ 6 + 1022175 * n ^ 5 - 3534300 * n ^ 4
          + 6246471 * n ^ 3 - 4370520 * n ^ 2 := by
    rw [hE6]
    have e1 : 10395 * n ^ 6 - 155925 * n ^ 5 + 1022175 * n ^ 4 - 3534300 * n ^ 3
          + 6246471 * n ^ 2 - 4370520 * n
        = (10395 * n ^ 6 + 1022175 * n ^ 4 + 6246471 * n ^ 2)
            - (155925 * n ^ 5 + 3534300 * n ^ 3 + 4370520 * n) := by
      have hb1 : 155925 * n ^ 5 ≤ 10395 * n ^ 6 := pow_step_le (by omega)
      have hb2 : 3534300 * n ^ 3 ≤ 1022175 * n ^ 4 := by
        have := pow_step_le (a := 3534300) (b := 1022175) (n := n) (k := 3) (by omega); simpa using this
      have hb3 : 4370520 * n ≤ 6246471 * n ^ 2 := by
        have := pow_step_le (a := 4370520) (b := 6246471) (n := n) (k := 1) (by omega); simpa using this
      omega
    rw [e1, Nat.mul_sub, Nat.mul_add, Nat.mul_add, Nat.mul_add]
    have hp1 : n * (10395 * n ^ 6) = 10395 * n ^ 7 := by ring
    have hp2 : n * (1022175 * n ^ 4) = 1022175 * n ^ 5 := by ring
    have hp3 : n * (6246471 * n ^ 2) = 6246471 * n ^ 3 := by ring
    have hp4 : n * (155925 * n ^ 5) = 155925 * n ^ 6 := by ring
    have hp5 : n * (3534300 * n ^ 3) = 3534300 * n ^ 4 := by ring
    have hp6 : n * (4370520 * n) = 4370520 * n ^ 2 := by ring
    have hp45 : n * (155925 * n ^ 5 + 3534300 * n ^ 3) = 155925 * n ^ 6 + 3534300 * n ^ 4 := by
      rw [Nat.mul_add, hp4, hp5]
    simp only [hp1, hp2, hp3, hp6, hp45]
    have hb4 : 155925 * n ^ 6 ≤ 10395 * n ^ 7 := pow_step_le (by omega)
    have hb5 : 3534300 * n ^ 4 ≤ 1022175 * n ^ 5 := by
      have := pow_step_le (a := 3534300) (b := 1022175) (n := n) (k := 4) (by omega); simpa using this
    have hb6 : 4370520 * n ^ 2 ≤ 6246471 * n ^ 3 := by
      have := pow_step_le (a := 4370520) (b := 6246471) (n := n) (k := 2) (by omega); simpa using this
    have hs1 :
        (10395 * n ^ 7 + 1022175 * n ^ 5 + 6246471 * n ^ 3)
            - (155925 * n ^ 6 + 3534300 * n ^ 4 + 4370520 * n ^ 2)
          = (10395 * n ^ 7 - 155925 * n ^ 6)
              + (1022175 * n ^ 5 - 3534300 * n ^ 4)
              + (6246471 * n ^ 3 - 4370520 * n ^ 2) := by
      omega
    have hs2 :
        10395 * n ^ 7 - 155925 * n ^ 6 + 1022175 * n ^ 5 - 3534300 * n ^ 4
            + 6246471 * n ^ 3 - 4370520 * n ^ 2
          = (10395 * n ^ 7 - 155925 * n ^ 6)
              + (1022175 * n ^ 5 - 3534300 * n ^ 4)
              + (6246471 * n ^ 3 - 4370520 * n ^ 2) := by
      omega
    omega
  rw [hE7, hmul]
  -- Remaining slack:
  -- 2681910n⁶ + 138357450n⁴ + 704625768n² ≥ 25779600n⁵ + 427479822n³ + 471556800n.
  have c1 : 2837835 * n ^ 6 ≤ 135135 * n ^ 7 := pow_step_le (by omega)
  have c2 : 141891750 * n ^ 4 ≤ 26801775 * n ^ 5 := by
    have := pow_step_le (a := 141891750) (b := 26801775) (n := n) (k := 4) (by omega); simpa using this
  have c3 : 708996288 * n ^ 2 ≤ 433726293 * n ^ 3 := by
    have := pow_step_le (a := 708996288) (b := 433726293) (n := n) (k := 2) (by omega); simpa using this
  have c4 : 155925 * n ^ 6 ≤ 10395 * n ^ 7 := pow_step_le (by omega)
  have c5 : 3534300 * n ^ 4 ≤ 1022175 * n ^ 5 := by
    have := pow_step_le (a := 3534300) (b := 1022175) (n := n) (k := 4) (by omega); simpa using this
  have c6 : 4370520 * n ^ 2 ≤ 6246471 * n ^ 3 := by
    have := pow_step_le (a := 4370520) (b := 6246471) (n := n) (k := 2) (by omega); simpa using this
  have hslackA : 25779600 * n ^ 5 ≤ 2681910 * n ^ 6 := by
    have := pow_step_le (a := 25779600) (b := 2681910) (n := n) (k := 5) (by omega); simpa using this
  have hslackB : 427479822 * n ^ 3 ≤ 138357450 * n ^ 4 := by
    have := pow_step_le (a := 427479822) (b := 138357450) (n := n) (k := 3) (by omega); simpa using this
  have hslackC : 471556800 * n ≤ 704625768 * n ^ 2 := by
    have := pow_step_le (a := 471556800) (b := 704625768) (n := n) (k := 1) (by omega); simpa using this
  omega

end ArkLib.ProximityGap.CrossStepRungSix

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CrossStepRungSix.rEnergy_seven_eq
#print axioms ArkLib.ProximityGap.CrossStepRungSix.crossStepBound_six_iff
#print axioms ArkLib.ProximityGap.CrossStepRungSix.crossStepBound_six_of_sharpE7
#print axioms ArkLib.ProximityGap.CrossStepRungSix.crossStepBound_six_of_exact_moments
