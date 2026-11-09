/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Tactic

/-!
# The saddle forces a strictly-positive credit — `W_{r*}=0` is the wrong target (#444, Lane 3)

This file locks into the kernel the *correction* that Shaw's probe `probe_Wr_onset_vs_saddle.py`
(commit `720f09ac5`) established empirically but left as prose: at the saddle depth `r* ≈ log p`,
the genuine mod-`p` wraparound count `W_{r*}` is **strictly positive** (onset `r_0 = 5 < r* = 11`
at `n = 16`, with `W_8 ≈ 1.4·10¹⁷`), so the previously-hoped *static* target `W_{r*} = 0` is
**false and unprovable**. The correct open target is the budget inequality `W_r ≤ SLACK_r`, which
the saddle satisfies with margin *despite* `W > 0` because the char-0 deficit dwarfs `W`.

## Recalled reduction (proven elsewhere in-tree)

`_WraparoundBudgetIdentity.prize_iff_wraparound_budget` proves, as pure ring rearrangement, that the
DC-subtracted prize moment bound `S_r ≤ (p−1)·Wick_r` is **equivalent** to the single wraparound
budget inequality

  `p·W ≤ creditᵣ`,   where  `creditᵣ := n^(2r) − Wick + p·Delta`

with the two non-negative credits made explicit: the **DC headroom** `n^(2r) − Wick ≥ 0` and the
**char-0 deficit credit** `p·Delta ≥ 0` (`Delta = Wick − E_r(ℂ) ≥ 0`, Lam–Leung/Bessel, char-0
side closed). This file works abstractly over `ℝ` with `credit := n^(2r) − Wick + p·Delta` and
`p > 0`.

## What this file proves (Lane-3 constraint lemmas — abstract, no probe asserted)

* `credit_pos_of_budget_of_wrap_pos` — **the saddle forces a strictly-positive credit.** If the
  wraparound mass is genuinely positive (`0 < W`, the saddle fact `W_{r*} > 0`) and the budget
  inequality `p·W ≤ credit` holds (`0 < p`), then `0 < credit`. So the prize-at-saddle is *never*
  certifiable by a vanishing credit: it must spend the DC-headroom / char-0-deficit credit.

* `wrap_ne_zero_of_onset_lt_saddle` — `W_{r*} = 0` is **false** at any saddle past the onset: from
  the onset witness `0 < W` (it being past onset), `W ≠ 0`.

* `budget_not_via_wrap_zero` — the budget inequality at the saddle is **not** satisfied vacuously
  via `W = 0`: if `0 < W` then `W ≠ 0`, so a proof of `p·W ≤ credit` *cannot* route through the
  zero-wraparound case; it is carried by the credit. (Locks "`W_{r*}=0` is the wrong target".)

* `wrap_zero_budget_iff_credit_nonneg` — in the *off-saddle* `W = 0` regime (`r < r_0`), the budget
  inequality degenerates to the bare credit-nonnegativity `0 ≤ credit`; this is exactly why the
  static target was tempting below onset and why it cannot extend past onset where `W > 0`.

* `credit_strictly_exceeds_wrap_of_margin` — the saddle *margin* form: if the budget holds with a
  strict gap (`p·W < credit`, the probe's `W_r/SLACK_r ≈ 0.0002` tininess), the credit strictly
  dominates the wraparound mass, `p·W < credit`, so the open inequality has genuine slack at the
  saddle and is **not** a knife-edge in `W`.

## Honest scope

This is a Lane-3 *constraint lemma*. It carries the abstract sign logic of the saddle correction:
that the open budget inequality at the saddle must spend a strictly-positive credit and cannot be
discharged by `W = 0`. It uses only the recalled equivalence and elementary `ℝ` inequalities. It
proves **no** CORE upper bound, no cancellation, no completion, no anti-concentration, no capacity
claim, and asserts **no** value of `W` (`0 < W` is taken as the saddle *hypothesis* the probe
supplies, never larped as a theorem). The open problem `p·W ≤ credit` at the saddle remains open.
-/

namespace ArkLib.ProximityGap.Frontier.WraparoundSaddleCreditForced

/-- **The saddle forces a strictly-positive credit.** If the wraparound mass is genuinely positive
(`0 < W` — the saddle fact `W_{r*} > 0`, onset `r_0 < r*`) and the wraparound budget inequality
`p·W ≤ credit` holds with `0 < p`, then the credit is strictly positive: `0 < credit`.

Consequence: at the saddle, the prize moment bound is *never* certifiable by a vanishing credit —
the DC-headroom + char-0-deficit credit must be strictly spent. -/
theorem credit_pos_of_budget_of_wrap_pos
    {p W credit : ℝ} (hp : 0 < p) (hW : 0 < W) (hbudget : p * W ≤ credit) :
    0 < credit :=
  lt_of_lt_of_le (mul_pos hp hW) hbudget

/-- `W_{r*} = 0` is **false** at a saddle past the onset: the onset witness `0 < W` gives `W ≠ 0`.
(The probe `720f09ac5`: onset `r_0 = 5 < r* = 11`, so `W_{r*} > 0`.) -/
theorem wrap_ne_zero_of_onset_lt_saddle {W : ℝ} (hW : 0 < W) : W ≠ 0 :=
  ne_of_gt hW

/-- The saddle budget inequality is **not** satisfied via `W = 0`. Given the saddle fact `0 < W`,
the value `W` is nonzero, so any proof of `p·W ≤ credit` carries the wraparound mass against the
credit rather than collapsing it to the zero-wraparound case. This is the kernel form of
"`W_{r*}=0` is the wrong (false) target; `W_r ≤ SLACK_r` is the open one". -/
theorem budget_not_via_wrap_zero
    {p W credit : ℝ} (hp : 0 < p) (hW : 0 < W) (hbudget : p * W ≤ credit) :
    W ≠ 0 ∧ 0 < credit :=
  ⟨ne_of_gt hW, credit_pos_of_budget_of_wrap_pos hp hW hbudget⟩

/-- In the **off-saddle** `W = 0` regime (`r < r_0`, below onset), the wraparound budget inequality
`p·W ≤ credit` degenerates to the bare credit-nonnegativity `0 ≤ credit`. This is exactly why the
static `W = 0` target was natural below onset — and exactly why it cannot survive past the onset,
where `W > 0` reactivates the genuine `p·W ≤ credit` content. -/
theorem wrap_zero_budget_iff_credit_nonneg {p credit : ℝ} :
    p * (0 : ℝ) ≤ credit ↔ 0 ≤ credit := by
  simp

/-- The saddle **margin** form. If the budget holds with a strict gap `p·W < credit` (the probe's
`W_r/SLACK_r ≈ 0.0002` tininess: the char-0 deficit dwarfs `W`), then the credit strictly dominates
the wraparound mass. So at the saddle the open inequality has genuine slack and is **not** a
knife-edge in `W`; a positive `W` does not threaten it. -/
theorem credit_strictly_exceeds_wrap_of_margin
    {p W credit : ℝ} (hp : 0 < p) (hW : 0 < W) (hgap : p * W < credit) :
    p * W < credit ∧ 0 < credit :=
  ⟨hgap, lt_trans (mul_pos hp hW) hgap⟩

/-- **Saddle correction capstone.** Bundling the corrected target: at any saddle past onset
(`0 < W`) for which the budget inequality holds (`p·W ≤ credit`, `0 < p`), the static target
`W = 0` is false *and* the credit must be strictly positive. The open content is the *budget*
inequality on a genuinely positive `W`, not its vanishing. -/
theorem saddle_target_is_budget_not_vanishing
    {p W credit : ℝ} (hp : 0 < p) (hW : 0 < W) (hbudget : p * W ≤ credit) :
    W ≠ 0 ∧ 0 < credit ∧ p * W ≤ credit :=
  ⟨ne_of_gt hW, credit_pos_of_budget_of_wrap_pos hp hW hbudget, hbudget⟩

end ArkLib.ProximityGap.Frontier.WraparoundSaddleCreditForced
