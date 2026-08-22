/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CrossStepRungFour

/-!
# The exact `r = 4` cross-mass closed form + its explicit positive step-DEFICIT (Issue #444)

`CrossStepRungFour.lean` lands the `r = 4` rung of the open per-step crux
`M3CrossStepBound G : ∀ r, crossMass G r ≤ 2r·(2r−1)‼·n^{r+1}` (`crossMass G r = E_{r+1} − n·E_r`,
`n = |G|`) as the one-directional inequality `crossMass G 4 ≤ 840n⁵`, and records the EXACT
closed form `crossMass G 4 = 840n⁵ − 8820n⁴ + 37940n³ − 76020n² + 57456n` plus the uniform
two-term structural law (`−(r²+r+1)/2` second-coefficient) only as **docstring observations**.

`CrossStepRungThree.crossMass_three_exact_of_moments` and `CrossStepRungTwo.crossMass_two_exact_of_moments`
already turn the EXACT crossMass form into a `=` theorem at `r = 2, 3`. This file completes that ladder
at `r = 4` (the missing exact rung) AND, the real new content, lands the explicit **positive step
deficit** as a `=` theorem + a strict positivity — turning the docstring "the rung holds because the
first correction is a negative `Θ(n^r)` term" into a proven mechanism.

## What this file lands (axiom-clean, ℕ-arithmetic on the proven recursion + exact moments)

* `crossMass_four_exact_of_moments` — the EXACT `r = 4` cross-mass closed form (completes the
  `r = 2, 3, 4` exact ladder):
  > `crossMass G 4 = 840n⁵ − 8820n⁴ + 37940n³ − 76020n² + 57456n`   (`n ≥ 16`).
* `stepDeficit_four_eq_of_moments` — the EXACT positive step-DEFICIT below the `840n⁵` target:
  > `840·n⁵ − crossMass G 4 = 8820n⁴ − 37940n³ + 76020n² − 57456n`   (`n ≥ 16`).
  Its leading coefficient `8820 = (r²+r+1)·r·(2r−1)‼ = 21·4·105` is exactly the negated
  second-coefficient law of `crossMass` at `r = 4` (`−(r²+r+1)/2·leading = −21/2·840 = −8820`).
* `stepDeficit_four_pos_of_moments` — the deficit is **strictly positive** for `n ≥ 16`:
  > `crossMass G 4 < 840·n⁵`,
  so the `r = 4` rung holds with EXPLICIT positive `Θ(n⁴)` slack (not just `≤`). This is the
  proven instance of the docstring mechanism "the deficit below the step target is a strictly
  lower-order `Θ(n^r)` quantity".

## Probe (ONE sweep, exact integer)

`scripts/probes/probe_crossmass_deficit_law.py`: from the in-tree exact char-`0`-faithful moments
`E_1…E_5`, computes `crossMass(r) = E_{r+1} − n·E_r`, the step target `T(r) = 2r·(2r−1)‼·n^{r+1}`,
and the deficit `D(r) = T(r) − crossMass(r)` for `r = 1…4`. Verdict (all PASS): leading coeff of
`crossMass(r)` `== 2r·(2r−1)‼` (rung tight at top order); second coeff `== −(r²+r+1)·r·(2r−1)‼`;
`D(r) ≥ 0` on the prize grid `n = 16…2²⁰`; `D(r)` leading coeff `== +(r²+r+1)·r·(2r−1)‼`. The
exact `r = 4` forms it pins are `crossMass G 4 = [840, −8820, 37940, −76020, 57456]` and
`D(4) = [0, 8820, −37940, 76020, −57456]` (high→low `n`-coeffs).

## Honest scope

NOT a CORE closure, NOT thinness-essential by itself: the recursion `E_{r+1} = n·E_r + crossMass G r`
is an identity for ANY finite set; thinness enters only through WHICH exact `E_r` closed forms hold
on `μ_{2^m}` (here taken as hypotheses, exactly as in `CrossStepRungFour`). This file completes the
exact cross-mass ladder at `r = 4` and proves the explicit positive deficit (the docstring
mechanism). The deep rungs `r ≥ 5` and the char-`p` transfer at `r ≈ ln q` remain the open wall;
CORE (`M(μ_n) ≤ C·√(n·log(p/n))`, the BGK/Paley √-cancellation) stays **OPEN**.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.CrossStepCeiling (crossMass rEnergy_succ_crossMass)
open ArkLib.ProximityGap.CrossStepRungFour (rEnergy_five_eq)

namespace ArkLib.ProximityGap.CrossStepRungFourDeficit

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `n ≥ 16` power-step helper: `a ≤ b·n ⟹ a·n^k ≤ b·n^{k+1}` (via `n^{k+1} = n^k·n`). -/
private lemma pow_step_le {a b n k : ℕ} (h : a ≤ b * n) : a * n ^ k ≤ b * n ^ (k + 1) := by
  calc a * n ^ k ≤ (b * n) * n ^ k := Nat.mul_le_mul_right _ h
    _ = b * n ^ (k + 1) := by ring

/-- **The EXACT `r = 4` cross-mass closed form (completes the `r = 2, 3, 4` exact ladder).** Given the
exact fourth and fifth char-`0`-faithful moments on `μ_{2^m}`, `crossMass G 4 = E_5 − n·E_4` equals
> `840n⁵ − 8820n⁴ + 37940n³ − 76020n² + 57456n`.
(`n ≥ 16` so the ℕ-truncated form is faithful; `μ_n` has `n = 2^a ≥ 16` in the prize regime.) -/
theorem crossMass_four_exact_of_moments (G : Finset F) (hn : 16 ≤ G.card)
    (hE4 : rEnergy G 4 = 105 * G.card ^ 4 - 630 * G.card ^ 3 + 1435 * G.card ^ 2 - 1155 * G.card)
    (hE5 : rEnergy G 5 = 945 * G.card ^ 5 - 9450 * G.card ^ 4 + 39375 * G.card ^ 3
                          - 77175 * G.card ^ 2 + 57456 * G.card) :
    crossMass G 4 = 840 * G.card ^ 5 - 8820 * G.card ^ 4 + 37940 * G.card ^ 3
                      - 76020 * G.card ^ 2 + 57456 * G.card := by
  have hrec := rEnergy_five_eq G
  set n := G.card with hndef
  have hc16 : (16 : ℕ) ≤ n := hn
  -- n·E_4 = 105n⁵ − 630n⁴ + 1435n³ − 1155n²  (faithful ℕ subtraction at n ≥ 16)
  have hmul : n * rEnergy G 4 = 105 * n ^ 5 - 630 * n ^ 4 + 1435 * n ^ 3 - 1155 * n ^ 2 := by
    rw [hE4]
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
    have hb3 : 630 * n ^ 4 ≤ 105 * n ^ 5 := pow_step_le (by omega)
    have hb4 : 1155 * n ^ 2 ≤ 1435 * n ^ 3 := by
      have := pow_step_le (a := 1155) (b := 1435) (n := n) (k := 2) (by omega); simpa using this
    omega
  rw [hE5, hmul] at hrec
  -- hrec : E_5(closed) = (105n⁵−630n⁴+1435n³−1155n²) + crossMass G 4
  -- Solve for crossMass via omega with the truncation bounds for both closed forms.
  have c1 : 9450 * n ^ 4 ≤ 945 * n ^ 5 := pow_step_le (by omega)
  have c2 : 77175 * n ^ 2 ≤ 39375 * n ^ 3 := by
    have := pow_step_le (a := 77175) (b := 39375) (n := n) (k := 2) (by omega); simpa using this
  have c3 : 57456 * n ≤ 39375 * n ^ 2 := by
    have := pow_step_le (a := 57456) (b := 39375) (n := n) (k := 1) (by omega); simpa using this
  have c4 : 630 * n ^ 4 ≤ 105 * n ^ 5 := pow_step_le (by omega)
  have c5 : 1155 * n ^ 2 ≤ 1435 * n ^ 3 := by
    have := pow_step_le (a := 1155) (b := 1435) (n := n) (k := 2) (by omega); simpa using this
  -- target form truncation bounds (840n⁵ − 8820n⁴ + 37940n³ − 76020n² + 57456n):
  have d1 : 8820 * n ^ 4 ≤ 840 * n ^ 5 := pow_step_le (by omega)
  have d2 : 76020 * n ^ 2 ≤ 37940 * n ^ 3 := by
    have := pow_step_le (a := 76020) (b := 37940) (n := n) (k := 2) (by omega); simpa using this
  have d3 : 57456 * n ≤ 37940 * n ^ 2 := by
    have := pow_step_le (a := 57456) (b := 37940) (n := n) (k := 1) (by omega); simpa using this
  omega

/-- **The EXACT positive step-DEFICIT below the `r = 4` target `840n⁵`.** From the exact cross-mass
closed form, `840·n⁵ − crossMass G 4 = 8820n⁴ − 37940n³ + 76020n² − 57456n` (`n ≥ 16`). The leading
coefficient `8820 = (r²+r+1)·r·(2r−1)‼ = 21·4·105` is exactly the negated second-coefficient law of
`crossMass` at `r = 4`. -/
theorem stepDeficit_four_eq_of_moments (G : Finset F) (hn : 16 ≤ G.card)
    (hE4 : rEnergy G 4 = 105 * G.card ^ 4 - 630 * G.card ^ 3 + 1435 * G.card ^ 2 - 1155 * G.card)
    (hE5 : rEnergy G 5 = 945 * G.card ^ 5 - 9450 * G.card ^ 4 + 39375 * G.card ^ 3
                          - 77175 * G.card ^ 2 + 57456 * G.card) :
    840 * G.card ^ 5 - crossMass G 4
      = 8820 * G.card ^ 4 - 37940 * G.card ^ 3 + 76020 * G.card ^ 2 - 57456 * G.card := by
  have hcm := crossMass_four_exact_of_moments G hn hE4 hE5
  set n := G.card with hndef
  have hc16 : (16 : ℕ) ≤ n := hn
  rw [hcm]
  -- 840n⁵ − (840n⁵ − 8820n⁴ + 37940n³ − 76020n² + 57456n) = 8820n⁴ − 37940n³ + 76020n² − 57456n
  have d1 : 8820 * n ^ 4 ≤ 840 * n ^ 5 := pow_step_le (by omega)
  have d2 : 76020 * n ^ 2 ≤ 37940 * n ^ 3 := by
    have := pow_step_le (a := 76020) (b := 37940) (n := n) (k := 2) (by omega); simpa using this
  have d3 : 57456 * n ≤ 37940 * n ^ 2 := by
    have := pow_step_le (a := 57456) (b := 37940) (n := n) (k := 1) (by omega); simpa using this
  have e1 : 37940 * n ^ 3 ≤ 8820 * n ^ 4 := by
    have := pow_step_le (a := 37940) (b := 8820) (n := n) (k := 3) (by omega); simpa using this
  have e2 : 57456 * n ≤ 76020 * n ^ 2 := by
    have := pow_step_le (a := 57456) (b := 76020) (n := n) (k := 1) (by omega); simpa using this
  omega

/-- **The `r = 4` rung holds with EXPLICIT positive `Θ(n⁴)` slack.** `crossMass G 4 < 840·n⁵` for
`n ≥ 16` — strict, with the exact deficit `8820n⁴ − 37940n³ + 76020n² − 57456n > 0` (the proven
instance of the docstring mechanism "the first correction below the step target is a strictly
lower-order `Θ(n^r)` quantity"). -/
theorem stepDeficit_four_pos_of_moments (G : Finset F) (hn : 16 ≤ G.card)
    (hE4 : rEnergy G 4 = 105 * G.card ^ 4 - 630 * G.card ^ 3 + 1435 * G.card ^ 2 - 1155 * G.card)
    (hE5 : rEnergy G 5 = 945 * G.card ^ 5 - 9450 * G.card ^ 4 + 39375 * G.card ^ 3
                          - 77175 * G.card ^ 2 + 57456 * G.card) :
    crossMass G 4 < 840 * G.card ^ 5 := by
  -- Use the exact deficit equality: 840n⁵ − crossMass G 4 = (positive Θ(n⁴) form).
  have hdef := stepDeficit_four_eq_of_moments G hn hE4 hE5
  have hcm := crossMass_four_exact_of_moments G hn hE4 hE5
  set n := G.card with hndef
  have hc16 : (16 : ℕ) ≤ n := hn
  -- crossMass G 4 ≤ 840n⁵ (the landed rung) gives crossMass ≤ 840n⁵; we sharpen to strict.
  have hle : crossMass G 4 ≤ 840 * n ^ 5 :=
    ArkLib.ProximityGap.CrossStepRungFour.crossStepBound_four_of_exact_moments G hn hE4 hE5
  -- The deficit 840n⁵ − crossMass G 4 is strictly positive: its closed form is
  -- 8820n⁴ − 37940n³ + 76020n² − 57456n, with 8820n⁴ strictly dominating.
  have hn3pos : 0 < n ^ 3 := by positivity
  have e1strict : 37940 * n ^ 3 < 8820 * n ^ 4 := by
    have hcoef : 37940 < 8820 * n := by omega
    have hlt : 37940 * n ^ 3 < (8820 * n) * n ^ 3 :=
      Nat.mul_lt_mul_of_lt_of_le hcoef (le_refl _) hn3pos
    calc 37940 * n ^ 3 < (8820 * n) * n ^ 3 := hlt
      _ = 8820 * n ^ 4 := by ring
  have e2 : 57456 * n ≤ 76020 * n ^ 2 := by
    have := pow_step_le (a := 57456) (b := 76020) (n := n) (k := 1) (by omega); simpa using this
  have hdefpos : 0 < 840 * n ^ 5 - crossMass G 4 := by
    rw [hdef]; omega
  omega

end ArkLib.ProximityGap.CrossStepRungFourDeficit

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CrossStepRungFourDeficit.crossMass_four_exact_of_moments
#print axioms ArkLib.ProximityGap.CrossStepRungFourDeficit.stepDeficit_four_eq_of_moments
#print axioms ArkLib.ProximityGap.CrossStepRungFourDeficit.stepDeficit_four_pos_of_moments
