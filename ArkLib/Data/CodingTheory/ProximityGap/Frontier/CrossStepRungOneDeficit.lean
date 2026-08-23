/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CrossStepRungOne

/-!
# The exact `r = 1` cross-mass closed form + its explicit positive step-deficit (Issue #444)

`CrossStepRungOne.lean` lands the `r = 0, 1` rungs of the open per-step crux
`M3CrossStepBound G : ∀ r, crossMass G r ≤ 2r·(2r−1)‼·n^{r+1}` (`crossMass G r = E_{r+1} − n·E_r`,
`n = |G|`): it proves `crossMass_one_add` (`E_2 = n² + crossMass G 1`) and the one-directional
ceiling `crossMass G 1 ≤ 2n²` from the `r = 2` Sidon energy ceiling — but it does NOT expose the
EXACT `r = 1` cross-mass form as a `=` theorem.

`CrossStepRungTwo/Three` (`crossMass_two_exact_of_moments`, `crossMass_three_exact_of_moments`) and
`CrossStepRungFourDeficit` (`crossMass_four_exact_of_moments`) land the exact crossMass `=` form at
`r = 2, 3, 4`. This file completes that exact ladder at its base rung `r = 1` AND lands the explicit
positive step-deficit, so the exact crossMass + positive-deficit pair is now a theorem for the WHOLE
in-tree ladder `r = 1, 2, 3, 4`.

## What this file lands (axiom-clean, ℕ-arithmetic on the proven recursion + exact `E_2`)

* `crossMass_one_exact_of_E2` — the EXACT `r = 1` cross-mass closed form (base of the ladder):
  > `crossMass G 1 = 2n² − 3n`   (from the exact Sidon second moment `E_2 = 3n² − 3n`).
* `stepDeficit_one_eq_of_E2` — the EXACT positive step-DEFICIT below the `2n²` target:
  > `2·n² − crossMass G 1 = 3n`   (the cleanest rung; leading `3 = (r²+r+1)·r·(2r−1)‼ = 3·1·1`,
  exactly the negated second-coefficient law `−(r²+r+1)/2·leading = −3/2·2 = −3` at `r = 1`).
* `stepDeficit_one_pos_of_E2` — the deficit is **strictly positive** for `n ≥ 2`:
  > `crossMass G 1 < 2·n²`,
  so the `r = 1` rung holds with EXPLICIT positive `3n` slack (not just `≤`).

The exact `E_2 = 3n² − 3n` input is itself a theorem for `μ_n` (`REnergyTwoExact.mu_n_rEnergy_two_eq`),
so for the thin 2-power subgroup these are unconditional in `E_2`; taken here as a hypothesis to match
the conditional style of the rest of the rung ladder.

## Probe

`scripts/probes/probe_crossmass_deficit_law.py` (the companion of `CrossStepRungFourDeficit`) verifies
the `r = 1` row: `crossMass(1) = [2, −3]` (i.e. `2n² − 3n`), step target `T(1) = 2n²`, deficit
`D(1) = [0, 3]` (`= 3n ≥ 0`), leading-coeff law `2 = 2·1·(2·1−1)‼` and second-coeff law
`−3 = −(1²+1+1)·1·(2·1−1)‼` both PASS.

## Honest scope

NOT a CORE closure, NOT thinness-essential by itself (the recursion is an identity for any finite
set; thinness enters only through `E_2 = 3n² − 3n` on `μ_n`). Completes the exact crossMass ladder at
the base rung `r = 1` + its positive deficit. The deep rungs `r ≥ 5` and the char-`p` transfer at
`r ≈ ln q` remain the open BGK wall; CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) stays **OPEN**.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.CrossStepCeiling (crossMass)
open ArkLib.ProximityGap.CrossStepRungOne (crossMass_one_add)

namespace ArkLib.ProximityGap.CrossStepRungOneDeficit

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The EXACT `r = 1` cross-mass closed form (base of the `r = 1, 2, 3, 4` exact ladder).** From the
recursion `E_2 = n² + crossMass G 1` and the exact Sidon second moment `E_2 = 3n² − 3n`,
`crossMass G 1 = 2n² − 3n` (`n ≥ 2` so the ℕ-truncated form is faithful). -/
theorem crossMass_one_exact_of_E2 (G : Finset F) (hn : 2 ≤ G.card)
    (hE2 : rEnergy G 2 = 3 * G.card ^ 2 - 3 * G.card) :
    crossMass G 1 = 2 * G.card ^ 2 - 3 * G.card := by
  have hrec := crossMass_one_add G
  set n := G.card with hndef
  have hc2 : (2 : ℕ) ≤ n := hn
  rw [hE2] at hrec
  -- hrec : 3n² − 3n = n² + crossMass G 1
  -- 3n ≤ 3n² and 3n ≤ 2n²+n (both hold for n ≥ 2; at n = 1 the ℕ-truncated form is not faithful)
  have hb1 : 3 * n ≤ 3 * n ^ 2 := by nlinarith [hc2, sq_nonneg n]
  have hb2 : 3 * n ≤ 2 * n ^ 2 + n := by nlinarith [hc2, sq_nonneg n]
  omega

/-- **The EXACT positive step-DEFICIT below the `r = 1` target `2n²`.** From the exact cross-mass form,
`2·n² − crossMass G 1 = 3n` (`n ≥ 2`). Leading `3 = (r²+r+1)·r·(2r−1)‼ = 3·1·1` is exactly the
negated second-coefficient law of `crossMass` at `r = 1`. -/
theorem stepDeficit_one_eq_of_E2 (G : Finset F) (hn : 2 ≤ G.card)
    (hE2 : rEnergy G 2 = 3 * G.card ^ 2 - 3 * G.card) :
    2 * G.card ^ 2 - crossMass G 1 = 3 * G.card := by
  have hcm := crossMass_one_exact_of_E2 G hn hE2
  set n := G.card with hndef
  have hc2 : (2 : ℕ) ≤ n := hn
  rw [hcm]
  -- 2n² − (2n² − 3n) = 3n, valid since 3n ≤ 2n² for n ≥ 2; n=1 gives 2−(−1 truncated to 0)… use bound
  have hb : 3 * n ≤ 2 * n ^ 2 := by nlinarith [hc2, sq_nonneg n, hn]
  omega

/-- **The `r = 1` rung holds with EXPLICIT positive `3n` slack.** `crossMass G 1 < 2·n²` for `n ≥ 2`
— strict, with the exact deficit `3n > 0`. The cleanest instance of the docstring mechanism "the
first correction below the step target is a strictly lower-order `Θ(n^r)` quantity". -/
theorem stepDeficit_one_pos_of_E2 (G : Finset F) (hn : 2 ≤ G.card)
    (hE2 : rEnergy G 2 = 3 * G.card ^ 2 - 3 * G.card) :
    crossMass G 1 < 2 * G.card ^ 2 := by
  have hcm := crossMass_one_exact_of_E2 G hn hE2
  set n := G.card with hndef
  have hc2 : (2 : ℕ) ≤ n := hn
  rw [hcm]
  -- 2n² − 3n < 2n²  (strict, since 3n > 0 for n ≥ 2 and 3n ≤ 2n²)
  have hb : 3 * n ≤ 2 * n ^ 2 := by nlinarith [hc2, sq_nonneg n]
  have hpos : 0 < 3 * n := by omega
  omega

end ArkLib.ProximityGap.CrossStepRungOneDeficit

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CrossStepRungOneDeficit.crossMass_one_exact_of_E2
#print axioms ArkLib.ProximityGap.CrossStepRungOneDeficit.stepDeficit_one_eq_of_E2
#print axioms ArkLib.ProximityGap.CrossStepRungOneDeficit.stepDeficit_one_pos_of_E2
