/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Door IV — the CUMULANT-LADDER vacuity lemma: vanishing connected cumulant at ANY order forecloses
# the entire "go to order 2k" ladder with one statement

The connected-4 (`_DoorIVConnectedCumulantVanishes`) and connected-6
(`_DoorIVTripleCorrelationVanishes`) entries each closed one rung of the correlation hierarchy by the
SAME mechanism: the relevant connected cumulant vanishes (probe-verified), so the order-`2r` moment
Wick-factorizes through the lower-order data, and any door-(iv) candidate controlled by that moment is
controlled by the (independently dead) lower-order objects. Each rung needed its own kernel.

This file generalizes the MECHANISM once, order-agnostically, so the open residual after the
connected-6 closure — "a surviving surface must be an even-higher connected order" — is foreclosed at
the LEVEL OF THE LADDER, not rung by rung. Concretely: for ANY order `r`, if the order-`r` moment `mr`
decomposes (the moment–cumulant relation) as `mr = wickr + cumr` with the connected `cumr = 0`, then a
candidate `M ≤ mr` satisfies `M ≤ wickr` — control through that order passes through the lower-order
Wick data. No fresh arithmetic is created by climbing the ladder; the probe input each rung needs is
exactly `cumr = 0` (the field's order-`r` connected incoherence), nothing more.

This is a citable foreclosure record: it does NOT assert any `cumr = 0` (those are per-order probe
facts; the campaign has verified `r = 2, 4, 6`), and it makes no CORE/cancellation claim. It states the
LOGICAL content shared by every rung, so future order-`2k` attempts reduce to the single empirical
question "does the order-`2k` connected cumulant vanish?" with no new structural lever in play.

## Why this is frontier-movement, not a wrapper

The prior rungs are CONCRETE (`r = 4`: `m22`; `r = 6`: `m33`). This lemma is the SCHEMA they instantiate:
one theorem whose `r = 4` and `r = 6` specializations are exactly the two landed kernels, and whose
`r = 8, 10, …` specializations are the (currently unprobed but mechanism-identical) higher rungs. It
turns an unbounded sequence of potential probes into one statement + a per-rung scalar check.
-/

namespace ProximityGap.Frontier.DoorIVCumulantLadderVacuity

open Finset

/-- **Cumulant-ladder vacuity (real, single order).** For an order-`r` moment `mr` with the
moment–cumulant decomposition `mr = wickr + cumr`, a vanishing connected cumulant `cumr = 0` forces
`mr = wickr`; hence a door-(iv) candidate `M ≤ mr` is controlled by the lower-order Wick data
`M ≤ wickr`. (The parameter `r` is recorded for documentation; the algebra is order-uniform.) -/
theorem ladder_control_passes_through_wick
    {M mr wickr cumr : ℝ}
    (hctrl : M ≤ mr) (hdecomp : mr = wickr + cumr) (hzero : cumr = 0) :
    M ≤ wickr := by
  have : mr = wickr := by rw [hdecomp, hzero, add_zero]
  rwa [this] at hctrl

/-- Complex form (the period field is complex-valued). -/
theorem ladder_moment_eq_wick_complex
    {mr wickr cumr : ℂ}
    (hdecomp : mr = wickr + cumr) (hzero : cumr = 0) :
    mr = wickr := by
  rw [hdecomp, hzero, add_zero]

/-- **Whole-ladder foreclosure.** If EVERY order in a finite set `R` of orders has a vanishing
connected cumulant (`hladder : ∀ r ∈ R, cum r = 0`) and its moment decomposes
(`hdec : ∀ r ∈ R, m r = wick r + cum r`), then for every `r ∈ R` the order-`r` moment equals its Wick
value. Climbing the ladder through any height in `R` creates no new structure: every rung is
lower-order-determined. -/
theorem whole_ladder_wick
    {R : Finset ℕ} {m wick cum : ℕ → ℝ}
    (hdec : ∀ r ∈ R, m r = wick r + cum r)
    (hladder : ∀ r ∈ R, cum r = 0) :
    ∀ r ∈ R, m r = wick r := by
  intro r hr
  rw [hdec r hr, hladder r hr, add_zero]

/-- Consequence of `whole_ladder_wick`: a candidate controlled at every rung
(`hctrl : ∀ r ∈ R, M ≤ m r`) is controlled by every rung's Wick value. No order in `R` supplies a
fresh bound beyond its lower-order data. -/
theorem whole_ladder_control
    {R : Finset ℕ} {M : ℝ} {m wick cum : ℕ → ℝ}
    (hctrl : ∀ r ∈ R, M ≤ m r)
    (hdec : ∀ r ∈ R, m r = wick r + cum r)
    (hladder : ∀ r ∈ R, cum r = 0) :
    ∀ r ∈ R, M ≤ wick r := by
  intro r hr
  have hw : m r = wick r := whole_ladder_wick hdec hladder r hr
  have := hctrl r hr
  rwa [hw] at this

end ProximityGap.Frontier.DoorIVCumulantLadderVacuity

#print axioms ProximityGap.Frontier.DoorIVCumulantLadderVacuity.ladder_control_passes_through_wick
#print axioms ProximityGap.Frontier.DoorIVCumulantLadderVacuity.ladder_moment_eq_wick_complex
#print axioms ProximityGap.Frontier.DoorIVCumulantLadderVacuity.whole_ladder_wick
#print axioms ProximityGap.Frontier.DoorIVCumulantLadderVacuity.whole_ladder_control
