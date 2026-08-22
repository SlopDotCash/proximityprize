/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CoshMGFSaddle

/-!
# Assembled closed-form cosh-MGF saddle floor: the open inequality ⟹ `‖η‖ ≤ log(2q²)/y*` (#444 §6.2)

`_CoshMGFSaddle.lean` lands two halves of the saddle consumer but never composes them:
- `period_le_of_mgfBound` : the open inequality `MGF(y) ≤ q·exp(n y²/2)` at a given `y > 0` gives
  `‖η_{b₀}‖ ≤ log(2·q·exp(n y²/2)) / y`;
- `exp_saddle_eq_card` : at the saddle `y*² = 2 log q / n`, `exp(n y*²/2) = q`.

This file performs the composition that turns the consumer into the **explicit closed-form prize
floor at the saddle**: substituting `exp(n y*²/2) = q` into the consumer bound collapses the RHS to
`log(2·q²)/y*` (the docstring of `exp_saddle_eq_card` states this collapse but never builds it as a
theorem).  With `y* = √(2 log q / n)` this is `(log 2 + 2 log q)/√(2 log q / n) = Θ(√(n log q))`,
the prize floor shape `C·√(n log(q/n))` up to the absolute constant `C`.

## What is and is NOT proved here

- **PROVED:** `period_le_saddle_closedForm`, *given* the open inequality `MGF(y*) ≤ q·exp(n y*²/2)`
  at the saddle `y*` (`y*² = 2 log q / n`, `y* > 0`, `n > 0`): `‖η_{b₀}‖ ≤ log(2·q²)/y*`.  Pure
  composition of the two in-tree halves; no new analytic input.
- **NOT proved (honest, the open prize):** the inequality `MGF(y*) ≤ q·exp(n y*²/2)` itself.
  That is the char-`p` Wick bound `A_r ≤ (2r−1)‼·n^r` at depth `r ≈ log q`, the open core of #444.
  This file only makes the saddle-evaluated consumer explicit (the typed object a future Wick bound
  discharges to yield the closed-form floor).

All results axiom-clean (`{propext, Classical.choice, Quot.sound}`).
-/

namespace ProximityGap.Frontier.CoshMGFSaddleAssembled

open ProximityGap.Frontier.CoshMGFSaddle
open ProximityGap.Frontier.CoshMGFIdentity
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The assembled closed-form saddle floor (conditional on the single open inequality).**  At the
saddle `y*` (`y*² = 2 log q / n`, `y* > 0`, with `n = |G| > 0`), if the char-`p` even-moment MGF
obeys the single open inequality `MGF(y*) ≤ q·exp(n y*²/2)`, then the Gauss period satisfies the
**closed-form** bound `‖η_{b₀}‖ ≤ log(2·q²)/y*`.  Composition of `period_le_of_mgfBound`
(at `y = y*`) with `exp_saddle_eq_card` (collapsing `exp(n y*²/2) = q`).  With
`y* = √(2 log q / n)` this is the prize floor `Θ(√(n log q))` up to the absolute constant. -/
theorem period_le_saddle_closedForm {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {y : ℝ} (hy : 0 < y) (b₀ : F)
    (hn : 0 < (G.card : ℝ))
    (hsaddle : y ^ 2 = 2 * Real.log (Fintype.card F : ℝ) / (G.card : ℝ))
    (hMGF : (∑' r : ℕ, ((Fintype.card F : ℝ) * rEnergy G r) * y ^ (2 * r) / ((2 * r).factorial : ℝ))
              ≤ (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2)) :
    ‖eta ψ G b₀‖ ≤ Real.log (2 * (Fintype.card F : ℝ) ^ 2) / y := by
  -- the consumer bound at this `y`
  have hcons := period_le_of_mgfBound (F := F) hψ G hy b₀ hMGF
  -- collapse `exp(n y²/2) = q` at the saddle
  have hexp : Real.exp ((G.card : ℝ) * y ^ 2 / 2) = (Fintype.card F : ℝ) :=
    exp_saddle_eq_card (F := F) hn hsaddle
  rw [hexp] at hcons
  -- `2 * q * q = 2 * q^2`, so the RHS log-argument matches the closed form
  refine hcons.trans_eq ?_
  congr 2
  ring

end ProximityGap.Frontier.CoshMGFSaddleAssembled

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only, NO sorryAx)
open ProximityGap.Frontier.CoshMGFSaddleAssembled in
#print axioms period_le_saddle_closedForm
