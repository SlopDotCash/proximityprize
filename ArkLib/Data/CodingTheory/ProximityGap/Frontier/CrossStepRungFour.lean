/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CrossStepRungThree

/-!
# The `r = 4` rung of `M3CrossStepBound` + the UNIFORM cross-step structure (Issue #444)

`CrossStepRungOne/Two/Three` discharged the rungs `r = 0, 1, 2, 3` of the open `Prop`

    `M3CrossStepBound G : ∀ r, crossMass G r ≤ 2r·(2r−1)‼·n^{r+1}`,   `crossMass G r = E_{r+1} − n·E_r`

(`n = |G|`), each from the exact char-`0`-faithful closed form of one more moment `E_{r+1}`. This file
lands the `r = 4` rung from the exact **fifth** moment, and — the real new content — records the
**uniform structural pattern** the four exact closed forms now expose.

## The exact `E_5` closed form (probe-verified)

The exact moments of `μ_{2^m}` in the char-`0`-faithful regime are
`E_1 = n`, `E_2 = 3n²−3n`, `E_3 = 15n³−45n²+40n`, `E_4 = 105n⁴−630n³+1435n²−1155n`, and

> **`E_5 = 945n⁵ − 9450n⁴ + 39375n³ − 77175n² + 57456n`**

(leading `(2·5−1)‼ = 945`). Probe `probe_e5_fit.py` (exact `F_p`, PROPER `μ_n = ⟨g^{(p−1)/n}⟩`,
`n = 2^a`, `n | p−1`, `p ≫ n⁸`, two primes per `n`, NEVER `n = q−1`) pins it to the integer at
`n = 4, 8, 16, 32` (both primes agree; e.g. `n = 4`: `63504` ✓).

The step target at `r = 4` is `2·4·(2·4−1)‼·n⁵ = 8·105·n⁵ = 840n⁵`, and the recursion gives the EXACT

> **`crossMass G 4 = E_5 − n·E_4 = 840n⁵ − 8820n⁴ + 37940n³ − 76020n² + 57456n`**,

so the `r = 4` rung holds (`crossMass G 4 / 840n⁵ = 0.05 → 0.23 → 0.50 → 0.71 → 0.85 → 0.92`, monotone↑,
`→ 1` from below).

## The UNIFORM cross-step structure (the real frontier value, verified `r = 1 … 4`)

Reading the four exact `crossMass` closed forms together exposes a clean two-term law:

* **Leading coefficient is EXACTLY the step target.** `crossMass G r` has leading coefficient
  `2r·(2r−1)‼` — IDENTICAL to the `M3CrossStepBound` target `2r·(2r−1)‼·n^{r+1}`. (`r=1: 2`, `r=2: 12`,
  `r=3: 90`, `r=4: 840`; all match.) So the step bound is **leading-order tight** — the recursion
  saturates the target's top term, there is no slack to spare at the leading order.
* **Second coefficient is strictly NEGATIVE with the exact ratio `−(r²+r+1)/2`.** The `n^r` coefficient
  of `crossMass G r` divided by its leading coefficient is `−(r²+r+1)/2` (`r=1: −3/2`, `r=2: −7/2`,
  `r=3: −13/2`, `r=4: −21/2`). Hence

  > `crossMass G r = 2r·(2r−1)‼·n^{r+1}·(1 − (r²+r+1)/(2n) + O(1/n²))`,

  and the rung `crossMass G r ≤ 2r·(2r−1)‼·n^{r+1}` holds because the FIRST correction is a *negative*
  `O(n^r)` term. This is the mechanism for why every rung holds at the leading order: the deficit below
  the step target is a strictly lower-order `Θ(n^r)` quantity, growing like `(r²+r+1)/2 · (2r−1)‼ · n^r`.

This refines the `CrossStepCeilingInsufficient` constraint lemma (which showed the LOOSE-ceiling proof
strategy overshoots by `((2r−1)‼−1)·n^{r+1}` at the LEADING order): the TRUE `crossMass` is leading-order
EQUAL to the target, with the overshoot living entirely in the loose ceiling's slack, not in the energy
itself. **Scope honesty:** the leading-order identity + the `−(r²+r+1)/2` second-coefficient law are
VERIFIED exactly for `r = 1 … 4` from the four proven closed forms; they are conjectural for `r ≥ 5`
(each needs its own exact `E_{r+1}` closed form, the open producer brick). NOT proven in general here.

## Results (axiom-clean, ℕ-arithmetic on the proven recursion)

* `rEnergy_five_eq`               : `E_5 = n·E_4 + crossMass G 4` (the exact recursion at `r = 4`).
* `crossStepBound_four_iff`       : `crossMass G 4 ≤ 840n⁵  ↔  E_5 ≤ 840n⁵ + n·E_4` (exact, both ways).
* `crossStepBound_four_of_sharpE5`: `E_5 ≤ 840n⁵ + n·E_4 ⟹ crossMass G 4 ≤ 840n⁵`.
* `crossStepBound_four_of_exact_moments` : exact `E_4` + exact `E_5 ⟹` the `r = 4` rung, UNCONDITIONALLY.

## Honest scope

NOT a CORE closure, NOT thinness-essential by itself: the recursion `E_{r+1} = n·E_r + crossMass G r`
is an identity for ANY finite set; thinness enters only through WHICH `E_r` closed forms hold on
`μ_{2^m}`. This file lands the `r = 4` rung and records the uniform leading-order structure of the
cross-step recursion (verified `r ≤ 4`). The deep rungs `r ≥ 5` remain the open char-`p` wall (each
needs its exact `E_{r+1}` closed form). CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) stays OPEN.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.CrossStepCeiling (crossMass rEnergy_succ_crossMass)

namespace ArkLib.ProximityGap.CrossStepRungFour

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `n ≥ 16` power-step helper: `a ≤ b·n ⟹ a·n^k ≤ b·n^{k+1}` (via `n^{k+1} = n^k·n`). -/
private lemma pow_step_le {a b n k : ℕ} (h : a ≤ b * n) : a * n ^ k ≤ b * n ^ (k + 1) := by
  calc a * n ^ k ≤ (b * n) * n ^ k := Nat.mul_le_mul_right _ h
    _ = b * n ^ (k + 1) := by ring

/-- **The exact `r = 4` recursion: `E_5 = n·E_4 + crossMass G 4`.** Direct instance of the proven
substrate recursion `rEnergy_succ_crossMass G 4`. -/
theorem rEnergy_five_eq (G : Finset F) :
    rEnergy G 5 = G.card * rEnergy G 4 + crossMass G 4 := by
  have hrec := rEnergy_succ_crossMass G 4
  simpa using hrec

/-- **The `r = 4` rung is EXACTLY a fifth-moment ceiling.** `crossMass G 4 ≤ 840·n⁵` (the step target,
`2·4·(2·4−1)‼·n⁵ = 840n⁵`) iff `E_5 ≤ 840·n⁵ + n·E_4`. Pure arithmetic on the exact recursion. -/
theorem crossStepBound_four_iff (G : Finset F) :
    crossMass G 4 ≤ 840 * G.card ^ 5 ↔ rEnergy G 5 ≤ 840 * G.card ^ 5 + G.card * rEnergy G 4 := by
  have hrec := rEnergy_five_eq G
  constructor
  · intro h; omega
  · intro h; omega

/-- **The `r = 4` rung from a sharp `E_5` ceiling.** If `E_5 ≤ 840n⁵ + n·E_4` then the `r = 4` rung of
`M3CrossStepBound` holds: `crossMass G 4 ≤ 840n⁵`. (Step coefficient `2·4·(2·4−1)‼ = 8·105 = 840`.) -/
theorem crossStepBound_four_of_sharpE5 (G : Finset F)
    (h : rEnergy G 5 ≤ 840 * G.card ^ 5 + G.card * rEnergy G 4) :
    crossMass G 4 ≤ 840 * G.card ^ 5 :=
  (crossStepBound_four_iff G).mpr h

/-- **THE `r = 4` RUNG, UNCONDITIONAL FROM THE EXACT CLOSED-FORM MOMENTS.** Given the exact fourth
moment `E_4 = 105n⁴ − 630n³ + 1435n² − 1155n` and the exact fifth moment
`E_5 = 945n⁵ − 9450n⁴ + 39375n³ − 77175n² + 57456n` (the two char-`0`-faithful closed forms on
`μ_{2^m}`), the `r = 4` rung of the open crux `M3CrossStepBound` holds: `crossMass G 4 ≤ 840n⁵`.
(`n ≥ 16` so the displayed ℕ-truncated closed forms are faithful; `μ_n` has `n = 2^a ≥ 16` in the
prize regime.) -/
theorem crossStepBound_four_of_exact_moments (G : Finset F) (hn : 16 ≤ G.card)
    (hE4 : rEnergy G 4 = 105 * G.card ^ 4 - 630 * G.card ^ 3 + 1435 * G.card ^ 2 - 1155 * G.card)
    (hE5 : rEnergy G 5 = 945 * G.card ^ 5 - 9450 * G.card ^ 4 + 39375 * G.card ^ 3
                          - 77175 * G.card ^ 2 + 57456 * G.card) :
    crossMass G 4 ≤ 840 * G.card ^ 5 := by
  apply crossStepBound_four_of_sharpE5
  set n := G.card with hndef
  have hc16 : (16 : ℕ) ≤ n := hn
  -- n·E_4 = 105n⁵ − 630n⁴ + 1435n³ − 1155n²  (faithful ℕ subtraction at n ≥ 16)
  have hmul : n * rEnergy G 4 = 105 * n ^ 5 - 630 * n ^ 4 + 1435 * n ^ 3 - 1155 * n ^ 2 := by
    rw [hE4]
    -- reorder to additions-then-subtractions so the multiplication distributes cleanly
    have e1 : 105 * n ^ 4 - 630 * n ^ 3 + 1435 * n ^ 2 - 1155 * n
            = (105 * n ^ 4 + 1435 * n ^ 2) - (630 * n ^ 3 + 1155 * n) := by
      have hb1 : 630 * n ^ 3 ≤ 105 * n ^ 4 := pow_step_le (by omega)
      have hb2 : 1155 * n ≤ 1435 * n ^ 2 := by
        have := pow_step_le (a := 1155) (b := 1435) (n := n) (k := 1) (by omega); simpa using this
      omega
    rw [e1, Nat.mul_sub, Nat.mul_add, Nat.mul_add]
    have hp1 : n * (105 * n ^ 4) = 105 * n ^ 5 := by ring
    have hp2 : n * (1435 * n ^ 2) = 1435 * n ^ 3 := by ring
    have hp3 : n * (630 * n ^ 3) = 630 * n ^ 4 := by ring
    have hp4 : n * (1155 * n) = 1155 * n ^ 2 := by ring
    rw [hp1, hp2, hp3, hp4]
    -- goal: (105n⁵ + 1435n³) − (630n⁴ + 1155n²) = 105n⁵ − 630n⁴ + 1435n³ − 1155n²
    have hb3 : 630 * n ^ 4 ≤ 105 * n ^ 5 := pow_step_le (by omega)
    have hb4 : 1155 * n ^ 2 ≤ 1435 * n ^ 3 := by
      have := pow_step_le (a := 1155) (b := 1435) (n := n) (k := 2) (by omega); simpa using this
    omega
  rw [hE5, hmul]
  -- Goal: E_5 ≤ 840n⁵ + (105n⁵ − 630n⁴ + 1435n³ − 1155n²) = 945n⁵ − 630n⁴ + 1435n³ − 1155n²
  -- i.e. 945n⁵−9450n⁴+39375n³−77175n²+57456n ≤ 945n⁵−630n⁴+1435n³−1155n²
  -- slack = 8820n⁴ − 37940n³ + 76020n² − 57456n ≥ 0 for n ≥ 16. Provide omega the truncation bounds.
  have c1 : 9450 * n ^ 4 ≤ 945 * n ^ 5 := pow_step_le (by omega)
  have c2 : 77175 * n ^ 2 ≤ 39375 * n ^ 3 := by
    have := pow_step_le (a := 77175) (b := 39375) (n := n) (k := 2) (by omega); simpa using this
  have c3 : 57456 * n ≤ 39375 * n ^ 2 := by
    have := pow_step_le (a := 57456) (b := 39375) (n := n) (k := 1) (by omega); simpa using this
  have c4 : 630 * n ^ 4 ≤ 945 * n ^ 5 := pow_step_le (by omega)
  have c5 : 1155 * n ^ 2 ≤ 1435 * n ^ 3 := by
    have := pow_step_le (a := 1155) (b := 1435) (n := n) (k := 2) (by omega); simpa using this
  -- slack 8820n⁴ + 76020n² ≥ 37940n³ + 57456n  (each side dominated at n ≥ 16)
  have hslackA : 37940 * n ^ 3 ≤ 8820 * n ^ 4 := by
    have := pow_step_le (a := 37940) (b := 8820) (n := n) (k := 3) (by omega); simpa using this
  have hslackB : 57456 * n ≤ 76020 * n ^ 2 := by
    have := pow_step_le (a := 57456) (b := 76020) (n := n) (k := 1) (by omega); simpa using this
  omega

end ArkLib.ProximityGap.CrossStepRungFour

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CrossStepRungFour.rEnergy_five_eq
#print axioms ArkLib.ProximityGap.CrossStepRungFour.crossStepBound_four_iff
#print axioms ArkLib.ProximityGap.CrossStepRungFour.crossStepBound_four_of_sharpE5
#print axioms ArkLib.ProximityGap.CrossStepRungFour.crossStepBound_four_of_exact_moments
