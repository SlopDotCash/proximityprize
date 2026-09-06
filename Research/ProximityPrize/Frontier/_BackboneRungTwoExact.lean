/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The backbone bound `E_{r+1} ≤ (2r+1)·n·E_r` at `r = 2`, from the exact closed forms (#444)

The char-0 backbone chain (`_CharZeroBackboneAntitone`, `_CharZeroBackboneSmallRRegime`,
`_CharZeroOpenCoreSmallR`) rests on the abstract **deficit-antitone** input `d_{r+1} ≤ d_r`, equivalently
the **backbone bound** `E_{r+1}(ℂ) ≤ (2r+1)·n·E_r(ℂ)` (these are the same statement, since
`d_r = E_r/Wick_r` and `Wick_{r+1}/Wick_r = (2r+1)n`). Everywhere upstream this is a *hypothesis*.

**This file: the backbone bound DISCHARGED at `r = 2`, directly from the exact char-0-faithful closed
forms** `E_2 = 3n² − 3n`, `E_3 = 15n³ − 45n² + 40n` (the same closed forms `CrossStepRung*` use; the
crossMass lane proves `E_{r+1} − n·E_r ≤ 2r·(2r−1)‼·n^{r+1}`, a *different* — additively shifted — bound;
here is the *multiplicative* backbone `E_3 ≤ 5n·E_2` the deficit-antitone anchor actually needs).

The certificate is explicit and exact:
```
        5n·E_2 − E_3 = 5n(3n² − 3n) − (15n³ − 45n² + 40n)
                     = (15n³ − 15n²) − (15n³ − 45n² + 40n)
                     = 30n² − 40n  =  10n·(3n − 4)  ≥ 0   for n ≥ 2.
```
So `E_3 ≤ 5n·E_2` (`= (2·2+1)·n·E_2`), the `r = 2` backbone, holds with slack `10n(3n−4)`.

**What this file proves (axiom-clean).**
* `backbone_rung_two_of_closed` — from the exact closed forms `E_2 = 3n²−3n`, `E_3 = 15n³−45n²+40n` and
  `2 ≤ n`, the backbone `E_3 ≤ 5·n·E_2` (i.e. `E_3 ≤ (2·2+1)·n·E_2`). Discharges the deficit-antitone
  hypothesis at `r = 2`.
* `backbone_rung_two_slack` — the exact slack identity `5n·E_2 − E_3 = 10n·(3n − 4)`.

**Honest scope.** This is the `r = 2` rung of the deficit-antitone anchor, char-0 only, from the exact
moments. It grounds the abstract hypothesis of the backbone chain at one concrete depth; the anchor at
the saddle `r ≈ β·log₂n` (the full deficit-antitone) remains the open char-0 input, and the char-p
correction beyond it is the prize. No CORE upper bound, no capacity/growth-law claim. Issue #444.
-/

namespace ProximityGap.Frontier.BackboneRungTwoExact

/-- **Exact slack at `r = 2`.** `5n·E_2 − E_3 = 10n·(3n − 4)`, from the closed forms
`E_2 = 3n² − 3n`, `E_3 = 15n³ − 45n² + 40n`. Pure `ring`. -/
theorem backbone_rung_two_slack (E2 E3 n : ℝ)
    (hE2 : E2 = 3 * n ^ 2 - 3 * n) (hE3 : E3 = 15 * n ^ 3 - 45 * n ^ 2 + 40 * n) :
    5 * n * E2 - E3 = 10 * n * (3 * n - 4) := by
  rw [hE2, hE3]; ring

/-- **The `r = 2` backbone bound from the exact closed forms.** With `E_2 = 3n² − 3n`,
`E_3 = 15n³ − 45n² + 40n` and `2 ≤ n`, the multiplicative backbone `E_3 ≤ 5·n·E_2 = (2·2+1)·n·E_2`
holds (slack `10n(3n−4) ≥ 0`). Discharges the deficit-antitone anchor at depth `r = 2`. -/
theorem backbone_rung_two_of_closed (E2 E3 n : ℝ)
    (hE2 : E2 = 3 * n ^ 2 - 3 * n) (hE3 : E3 = 15 * n ^ 3 - 45 * n ^ 2 + 40 * n)
    (hn : 2 ≤ n) :
    E3 ≤ 5 * n * E2 := by
  have hslack : 5 * n * E2 - E3 = 10 * n * (3 * n - 4) :=
    backbone_rung_two_slack E2 E3 n hE2 hE3
  have hpos : 0 ≤ 10 * n * (3 * n - 4) := by nlinarith [hn]
  linarith [hslack, hpos]

end ProximityGap.Frontier.BackboneRungTwoExact

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.BackboneRungTwoExact.backbone_rung_two_slack
#print axioms ProximityGap.Frontier.BackboneRungTwoExact.backbone_rung_two_of_closed
