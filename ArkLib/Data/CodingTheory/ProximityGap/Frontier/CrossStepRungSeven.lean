/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CrossStepRungSix
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvL2_E8ClosedForm

/-!
# The `r = 7` cross-step rung from the exact `E_7`, `E_8` closed forms (#444)

This file extends the finite checked prefix of the open per-step crux

`crossMass G r ≤ 2r · (2r−1)‼ · |G|^(r+1)`

by one further concrete rung. `CrossStepRungSix` wires `r = 6` through `E_6,E_7`; here we wire
`r = 7` through the in-tree exact char-`0` closed form for `E_8`.

The exact subtraction gives

`crossMass G 7 = E_8 − nE_7`

and, under the displayed faithful closed forms,

```
crossMass G 7 = 1891890 n^8 − 53918865 n^7 + 701575875 n^6 − 5297292000 n^5
                + 24622149552 n^4 − 69225978822 n^3 + 106967055195 n^2
                − 68492499075 n.
```

The target coefficient is `2·7·13‼ = 1891890`.  The slack is

```
53918865 n^7 − 701575875 n^6 + 5297292000 n^5 − 24622149552 n^4
  + 69225978822 n^3 − 106967055195 n^2 + 68492499075 n,
```

which is nonnegative by elementary coefficient absorption in the faithful sequential-`Nat`
subtraction window `n ≥ 64`. This is a concrete frontier extension only: it does not prove the
`∀ r` statement, does not transfer char-`0` closed forms to char `p` at prize depth, and does not
touch CORE.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.CrossStepCeiling (crossMass rEnergy_succ_crossMass)

namespace ArkLib.ProximityGap.CrossStepRungSeven

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `a ≤ b·n ⟹ a·n^k ≤ b·n^(k+1)`. -/
private lemma pow_step_le {a b n k : ℕ} (h : a ≤ b * n) : a * n ^ k ≤ b * n ^ (k + 1) := by
  calc a * n ^ k ≤ (b * n) * n ^ k := Nat.mul_le_mul_right _ h
    _ = b * n ^ (k + 1) := by ring

/-- The exact `r = 7` recursion: `E_8 = n·E_7 + crossMass G 7`. -/
theorem rEnergy_eight_eq (G : Finset F) :
    rEnergy G 8 = G.card * rEnergy G 7 + crossMass G 7 := by
  simpa using rEnergy_succ_crossMass G 7

/-- The `r = 7` rung is exactly the eighth-moment ceiling with the `n·E_7` term moved across. -/
theorem crossStepBound_seven_iff (G : Finset F) :
    crossMass G 7 ≤ 1891890 * G.card ^ 8 ↔
      rEnergy G 8 ≤ 1891890 * G.card ^ 8 + G.card * rEnergy G 7 := by
  have hrec := rEnergy_eight_eq G
  constructor
  · intro h; omega
  · intro h; omega

/-- A sharp eighth-moment ceiling implies the `r = 7` cross-step rung. -/
theorem crossStepBound_seven_of_sharpE8 (G : Finset F)
    (h : rEnergy G 8 ≤ 1891890 * G.card ^ 8 + G.card * rEnergy G 7) :
    crossMass G 7 ≤ 1891890 * G.card ^ 8 :=
  (crossStepBound_seven_iff G).mpr h

/-- **The concrete `r = 7` rung from the exact closed-form moments.** Given the exact seventh and
eighth char-`0`-faithful moment polynomials, the open per-step crux holds at `r = 7`:
`crossMass G 7 ≤ 1891890 n^8`, for `n ≥ 64`. -/
theorem crossStepBound_seven_of_exact_moments (G : Finset F) (hn : 64 ≤ G.card)
    (hE7 : rEnergy G 7 = 135135 * G.card ^ 7 - 2837835 * G.card ^ 6 + 26801775 * G.card ^ 5
                          - 141891750 * G.card ^ 4 + 433726293 * G.card ^ 3
                          - 708996288 * G.card ^ 2 + 471556800 * G.card)
    (hE8 : rEnergy G 8 = 2027025 * G.card ^ 8 - 56756700 * G.card ^ 7
                          + 728377650 * G.card ^ 6 - 5439183750 * G.card ^ 5
                          + 25055875845 * G.card ^ 4 - 69934975110 * G.card ^ 3
                          + 107438611995 * G.card ^ 2 - 68492499075 * G.card) :
    crossMass G 7 ≤ 1891890 * G.card ^ 8 := by
  apply crossStepBound_seven_of_sharpE8
  set n := G.card with hndef
  have hc64 : (64 : ℕ) ≤ n := hn
  have hmul : n * rEnergy G 7
      = 135135 * n ^ 8 - 2837835 * n ^ 7 + 26801775 * n ^ 6 - 141891750 * n ^ 5
          + 433726293 * n ^ 4 - 708996288 * n ^ 3 + 471556800 * n ^ 2 := by
    rw [hE7]
    have e1 : 135135 * n ^ 7 - 2837835 * n ^ 6 + 26801775 * n ^ 5 - 141891750 * n ^ 4
          + 433726293 * n ^ 3 - 708996288 * n ^ 2 + 471556800 * n
        = (135135 * n ^ 7 + 26801775 * n ^ 5 + 433726293 * n ^ 3 + 471556800 * n)
            - (2837835 * n ^ 6 + 141891750 * n ^ 4 + 708996288 * n ^ 2) := by
      have hb1 : 2837835 * n ^ 6 ≤ 135135 * n ^ 7 := pow_step_le (by omega)
      have hb2 : 141891750 * n ^ 4 ≤ 26801775 * n ^ 5 := by
        have := pow_step_le (a := 141891750) (b := 26801775) (n := n) (k := 4) (by omega); simpa using this
      have hb3 : 708996288 * n ^ 2 ≤ 433726293 * n ^ 3 := by
        have := pow_step_le (a := 708996288) (b := 433726293) (n := n) (k := 2) (by omega); simpa using this
      omega
    rw [e1, Nat.mul_sub, Nat.mul_add, Nat.mul_add, Nat.mul_add]
    have hp1 : n * (135135 * n ^ 7) = 135135 * n ^ 8 := by ring
    have hp2 : n * (26801775 * n ^ 5) = 26801775 * n ^ 6 := by ring
    have hp3 : n * (433726293 * n ^ 3) = 433726293 * n ^ 4 := by ring
    have hp4 : n * (471556800 * n) = 471556800 * n ^ 2 := by ring
    have hn1 : n * (2837835 * n ^ 6) = 2837835 * n ^ 7 := by ring
    have hn2 : n * (141891750 * n ^ 4) = 141891750 * n ^ 5 := by ring
    have hn3 : n * (708996288 * n ^ 2) = 708996288 * n ^ 3 := by ring
    have hneg : n * (2837835 * n ^ 6 + 141891750 * n ^ 4 + 708996288 * n ^ 2)
        = 2837835 * n ^ 7 + 141891750 * n ^ 5 + 708996288 * n ^ 3 := by
      rw [Nat.mul_add, Nat.mul_add, hn1, hn2, hn3]
    simp only [hp1, hp2, hp3, hp4]
    have hb4 : 2837835 * n ^ 7 ≤ 135135 * n ^ 8 := pow_step_le (by omega)
    have hb5 : 141891750 * n ^ 5 ≤ 26801775 * n ^ 6 := by
      have := pow_step_le (a := 141891750) (b := 26801775) (n := n) (k := 5) (by omega); simpa using this
    have hb6 : 708996288 * n ^ 3 ≤ 433726293 * n ^ 4 := by
      have := pow_step_le (a := 708996288) (b := 433726293) (n := n) (k := 3) (by omega); simpa using this
    have hs1 :
        (135135 * n ^ 8 + 26801775 * n ^ 6 + 433726293 * n ^ 4 + 471556800 * n ^ 2)
            - (2837835 * n ^ 7 + 141891750 * n ^ 5 + 708996288 * n ^ 3)
          = (135135 * n ^ 8 - 2837835 * n ^ 7)
              + (26801775 * n ^ 6 - 141891750 * n ^ 5)
              + (433726293 * n ^ 4 - 708996288 * n ^ 3)
              + 471556800 * n ^ 2 := by
      omega
    have hs2 :
        135135 * n ^ 8 - 2837835 * n ^ 7 + 26801775 * n ^ 6 - 141891750 * n ^ 5
            + 433726293 * n ^ 4 - 708996288 * n ^ 3 + 471556800 * n ^ 2
          = (135135 * n ^ 8 - 2837835 * n ^ 7)
              + (26801775 * n ^ 6 - 141891750 * n ^ 5)
              + (433726293 * n ^ 4 - 708996288 * n ^ 3)
              + 471556800 * n ^ 2 := by
      omega
    rw [hneg, hs1, hs2]
  rw [hE8, hmul]
  -- Remaining slack:
  -- 53918865n⁷ + 5297292000n⁵ + 69225978822n³ + 68492499075n
  --   ≥ 701575875n⁶ + 24622149552n⁴ + 106967055195n².
  have c1 : 56756700 * n ^ 7 ≤ 2027025 * n ^ 8 := pow_step_le (by omega)
  have c2 : 5439183750 * n ^ 5 ≤ 728377650 * n ^ 6 := by
    have := pow_step_le (a := 5439183750) (b := 728377650) (n := n) (k := 5) (by omega); simpa using this
  have c3 : 69934975110 * n ^ 3 ≤ 25055875845 * n ^ 4 := by
    have := pow_step_le (a := 69934975110) (b := 25055875845) (n := n) (k := 3) (by omega); simpa using this
  have c4 : 68492499075 * n ≤ 107438611995 * n ^ 2 := by
    have := pow_step_le (a := 68492499075) (b := 107438611995) (n := n) (k := 1) (by omega); simpa using this
  have c5 : 2837835 * n ^ 7 ≤ 135135 * n ^ 8 := pow_step_le (by omega)
  have c6 : 141891750 * n ^ 5 ≤ 26801775 * n ^ 6 := by
    have := pow_step_le (a := 141891750) (b := 26801775) (n := n) (k := 5) (by omega); simpa using this
  have c7 : 708996288 * n ^ 3 ≤ 433726293 * n ^ 4 := by
    have := pow_step_le (a := 708996288) (b := 433726293) (n := n) (k := 3) (by omega); simpa using this
  have hslackA : 701575875 * n ^ 6 ≤ 53918865 * n ^ 7 := by
    have := pow_step_le (a := 701575875) (b := 53918865) (n := n) (k := 6) (by omega); simpa using this
  have hslackB : 24622149552 * n ^ 4 ≤ 5297292000 * n ^ 5 := by
    have := pow_step_le (a := 24622149552) (b := 5297292000) (n := n) (k := 4) (by omega); simpa using this
  have hslackC : 106967055195 * n ^ 2 ≤ 69225978822 * n ^ 3 := by
    have := pow_step_le (a := 106967055195) (b := 69225978822) (n := n) (k := 2) (by omega); simpa using this
  omega

end ArkLib.ProximityGap.CrossStepRungSeven

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CrossStepRungSeven.rEnergy_eight_eq
#print axioms ArkLib.ProximityGap.CrossStepRungSeven.crossStepBound_seven_iff
#print axioms ArkLib.ProximityGap.CrossStepRungSeven.crossStepBound_seven_of_sharpE8
#print axioms ArkLib.ProximityGap.CrossStepRungSeven.crossStepBound_seven_of_exact_moments
