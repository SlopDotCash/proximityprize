/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._A2OnsetLatticeMinimum
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._WraparoundSaddleCreditForced

/-!
# Onset-pigeonhole ⟹ saddle-credit: the single citable chain (#444, Lane 2/3)

This file wires the two freshest `W_r` bricks into one chain, so the saddle's strictly-positive-credit
consequence is *derived* from the lattice pigeonhole rather than assumed:

* **Onset side** (`_A2OnsetLatticeMinimum`, Shaw `ef3305f3f`): `not_onsetSavesSaddle_of_card_gt` proves
  that once the `ℓ¹`-ball of short relations outgrows `p` below the saddle (`p < S.card`,
  `S` of weight `≤ w ≤ r`), `OnsetSavesSaddle m g r` is **FALSE** — i.e. a nonzero short lattice
  relation of weight `≤ 2r` exists, so the wraparound is nonempty at the saddle.

* **Saddle side** (`_WraparoundSaddleCreditForced`, `5e027e702`): `credit_pos_of_budget_of_wrap_pos`
  proves that a genuinely positive wraparound mass `0 < W` forces the budget credit strictly positive,
  `0 < credit` — the `W = 0` route is excluded past onset.

The missing rung is the **count-positivity bridge** `¬OnsetSavesSaddle ⟹ 0 < W`: the qualitative fact
that the wraparound *count* `W` is real-valued-positive once a wraparound relation exists. We carry it
as an explicit hypothesis `WraparoundCountPositive` (a predicate `¬OnsetSavesSaddle m g r → 0 < W g r`)
rather than larping the exact `W = (lattice point count)` identity, whose definitional bridge lives in
the DC-moment file. With that one rung, the whole chain

  `p < S.card`  ⟹  `¬OnsetSavesSaddle`  ⟹  `0 < W`  ⟹  (budget `p·W ≤ credit`)  ⟹  `0 < credit`

is kernel-checked: at prize scale the saddle is *forced* past onset and the budget *must* spend a
strictly-positive credit.

## Honest scope

Lane-2/3 reduction chain. Real kernel for every rung that is in-tree (pigeonhole → `¬OnsetSavesSaddle`,
and `0 < W` → `0 < credit`); the single arithmetic-content rung (`¬OnsetSavesSaddle → 0 < W`) is an
**explicit hypothesis** (`WraparoundCountPositive`), never asserted as a theorem. No CORE upper bound,
no cancellation, no completion, no anti-concentration, no capacity claim. The open budget inequality
`p·W ≤ credit` (= `W_r ≤ SLACK_r`) at the saddle remains open.
-/

set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.OnsetToSaddleCreditChain

open ProximityGap.Frontier.A2OnsetLatticeMinimum
open ArkLib.ProximityGap.Frontier.WraparoundSaddleCreditForced

/-- The **count-positivity bridge** (carried as a hypothesis, not larped): once `OnsetSavesSaddle`
fails (a short wraparound relation exists at depth `≤ r`), the real-valued wraparound count `W` is
strictly positive. `W : ℕ → ℝ` is the wraparound-count function (`W r = W_r`), `m g r` index the
lattice and depth. -/
def WraparoundCountPositive (m : ℕ) {p : ℕ} (g : ZMod p) (W : ℕ → ℝ) : Prop :=
  ∀ r : ℕ, ¬ OnsetSavesSaddle m g r → 0 < W r

/-- **Onset-pigeonhole ⟹ positive wraparound at the saddle.** If the `ℓ¹`-ball `S` of short relations
(weight `≤ w ≤ r`) outgrows `p` (`p < S.card`) and the count-positivity bridge holds, then the
wraparound count at depth `r` is strictly positive, `0 < W r`. (Combines Shaw's
`not_onsetSavesSaddle_of_card_gt` with the bridge.) -/
theorem wrap_pos_of_pigeonhole
    {m : ℕ} (p : ℕ) [NeZero p] (g : ZMod p) (w r : ℕ) (hwr : w ≤ r)
    (S : Finset (Fin m → ℤ)) (hSw : ∀ a ∈ S, l1 a ≤ w) (hcard : p < S.card)
    (W : ℕ → ℝ) (hbridge : WraparoundCountPositive m g W) :
    0 < W r :=
  hbridge r (not_onsetSavesSaddle_of_card_gt p g w r hwr S hSw hcard)

/-- **The full chain: onset-pigeonhole ⟹ the saddle must spend a strictly-positive credit.** Under
the pigeonhole (`p < S.card`), the count-positivity bridge, the budget inequality
`pp·(W r) ≤ credit`, and `0 < pp`, the credit is strictly positive: `0 < credit`. So at prize scale
the saddle is forced past onset (Shaw) *and* the prize moment bound can never be discharged by a
vanishing credit (this file's saddle side) — one kernel-checked chain. -/
theorem credit_pos_of_pigeonhole_chain
    {m : ℕ} (p : ℕ) [NeZero p] (g : ZMod p) (w r : ℕ) (hwr : w ≤ r)
    (S : Finset (Fin m → ℤ)) (hSw : ∀ a ∈ S, l1 a ≤ w) (hcard : p < S.card)
    (W : ℕ → ℝ) (hbridge : WraparoundCountPositive m g W)
    {pp credit : ℝ} (hpp : 0 < pp) (hbudget : pp * (W r) ≤ credit) :
    0 < credit :=
  credit_pos_of_budget_of_wrap_pos hpp
    (wrap_pos_of_pigeonhole p g w r hwr S hSw hcard W hbridge) hbudget

/-- **Chain capstone (named verdict).** Bundling: at prize scale the onset pigeonhole forces the
saddle past onset, so the wraparound count is positive and the budget — if it holds — must spend a
strictly-positive credit; the `W_r = 0` route is dead and the open content is the budget inequality
on a genuinely positive `W_r`. -/
theorem saddle_forced_past_onset_spends_credit
    {m : ℕ} (p : ℕ) [NeZero p] (g : ZMod p) (w r : ℕ) (hwr : w ≤ r)
    (S : Finset (Fin m → ℤ)) (hSw : ∀ a ∈ S, l1 a ≤ w) (hcard : p < S.card)
    (W : ℕ → ℝ) (hbridge : WraparoundCountPositive m g W)
    {pp credit : ℝ} (hpp : 0 < pp) (hbudget : pp * (W r) ≤ credit) :
    ¬ OnsetSavesSaddle m g r ∧ 0 < W r ∧ 0 < credit :=
  ⟨not_onsetSavesSaddle_of_card_gt p g w r hwr S hSw hcard,
   wrap_pos_of_pigeonhole p g w r hwr S hSw hcard W hbridge,
   credit_pos_of_pigeonhole_chain p g w r hwr S hSw hcard W hbridge hpp hbudget⟩

end ArkLib.ProximityGap.Frontier.OnsetToSaddleCreditChain
