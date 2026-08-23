/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sol
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DCCorrectSupNecessity

/-!
# The concrete DC-subtracted moment ceiling the prize forces (#444 / #407)

`_DCCorrectSupNecessity.dcSubtractedMoment_le_of_worstPeriod_le` gives, for any cap `K` on the
worst-`b` sup, the DC-subtracted moment ceiling `S_r ≤ (q−1)·K^{2r}`. The prize itself caps
the sup at
the floor `K = √e·√(2r·|G|)`. This file evaluates the closed form of that ceiling, turning
the abstract
`K^{2r}` into the explicit prize number:

> `prizeFloor_pow_eq` : `(√e·√(2r·|G|))^{2r} = (e·2r·|G|)^r`  (for `0 ≤ 2r·|G|`). The `^{2r}` of the
> floor collapses each √ to its radicand and merges, giving the clean `(e·2r·|G|)^r`.

> `dcSubtractedMoment_le_prizeFloorCeiling` : if the worst-`b` sup is at the prize floor
> `M(G) ≤ √e·√(2r·|G|)`, then `S_r = q·E_r − |G|^{2r} ≤ (q−1)·(e·2r·|G|)^r` — the concrete
> DC-subtracted moment ceiling the prize forces, with no abstract `K`.

**Honest status.** This is an explicit corollary of the elementary necessity counting bound, NOT
progress on CORE. It only names the concrete `(q−1)·(e·2r·|G|)^r` value of the DC-subtracted moment
ceiling implied by the prize sup floor; the converse — that the open `S_r` actually obeys
this ceiling —
remains the char-`p` / BGK / thin-subgroup √-cancellation wall, unproven. No CORE / cancellation /
completion / anti-concentration / moment-saving / capacity claim. Prize CORE stays OPEN.

Issue #444 / #407.
-/

namespace ArkLib.ProximityGap.Frontier.DCCorrectMomentCeilingAtFloor

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.Frontier.DCCorrectSupCapstone
open ArkLib.ProximityGap.Frontier.DCCorrectSupNecessity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Closed form of the `2r`-th power of the prize floor.** `(√e·√(t))^{2r} = (e·t)^r` for `0 ≤ t`.
Each `√` is squared away (`(√x)^{2r} = ((√x)^2)^r = x^r`), and the two `r`-th powers merge. -/
theorem prizeFloor_pow_eq (t : ℝ) (ht : 0 ≤ t) (r : ℕ) :
    (Real.sqrt (Real.exp 1) * Real.sqrt t) ^ (2 * r) = (Real.exp 1 * t) ^ r := by
  rw [mul_pow, pow_mul, pow_mul, Real.sq_sqrt (le_of_lt (Real.exp_pos 1)), Real.sq_sqrt ht,
    ← mul_pow]

/-- **The concrete DC-subtracted moment ceiling forced by the prize sup floor.** If the
worst-`b` sup
is at the prize floor `M(G) ≤ √e·√(2r·|G|)`, then the DC-subtracted moment is forced
`S_r = q·E_r − |G|^{2r} ≤ (q−1)·(e·2r·|G|)^r`. Combines `dcSubtractedMoment_le_of_worstPeriod_le`
(necessity) with `prizeFloor_pow_eq` (the closed-form `K^{2r}` at the floor). -/
theorem dcSubtractedMoment_le_prizeFloorCeiling [Nontrivial F] {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (hsup : worstPeriod ψ G ≤ Real.sqrt (Real.exp 1) * Real.sqrt (2 * r * (G.card : ℝ))) :
    (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
      ≤ ((Fintype.card F : ℝ) - 1) * (Real.exp 1 * (2 * r * (G.card : ℝ))) ^ r := by
  have hnec := dcSubtractedMoment_le_of_worstPeriod_le hψ G r hsup
  rwa [prizeFloor_pow_eq (2 * r * (G.card : ℝ)) (by positivity) r] at hnec

end ArkLib.ProximityGap.Frontier.DCCorrectMomentCeilingAtFloor

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
open ArkLib.ProximityGap.Frontier.DCCorrectMomentCeilingAtFloor in
#print axioms prizeFloor_pow_eq
open ArkLib.ProximityGap.Frontier.DCCorrectMomentCeilingAtFloor in
#print axioms dcSubtractedMoment_le_prizeFloorCeiling
