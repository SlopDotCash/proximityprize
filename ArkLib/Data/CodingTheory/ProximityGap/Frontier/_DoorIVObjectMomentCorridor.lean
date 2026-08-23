/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCocycleNoRandomEdge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVExcessIsMoment

/-!
# Door-(iv) object moment-corridor: `realSup` is pinned to `[iidSup, iidSup + Δ]` (#444)

Follow-up to `_DoorIVObjectMomentTrappedCapstone.lean`. That capstone welded the two Lane-1 sides
qualitatively (no edge below; no non-moment lever above). The two Lane-1 kernels
(`_DoorIVCocycleNoRandomEdge`, `_DoorIVExcessIsMoment`) work with an *abstract* advantage `δ`; neither
ties `δ` to the concrete gap `realSup − iidSup`, nor states the resulting **two-sided numeric pin**.

This module does exactly that: it identifies the dispersion advantage with the actual gap
`δ := realSup − iidSup` (the measured `+15..44%` excess of the real Jacobi-cocycle sup over the
iid-unit-phase surrogate), and derives the sharp consequence:

> Under the two measured/identity facts — the no-edge floor (`iidSup ≤ realSup`) and the
> excess-is-moment bound (the gap is bounded by the additive-energy excess `Δ`) — the real
> door-(iv) object's sup is **pinned to a moment-corridor of width `Δ`** above the extreme-value
> floor: `iidSup ≤ realSup ≤ iidSup + Δ`.

This is quantitatively STRONGER than the qualitative trap: it is a numeric sandwich, not just two
sign facts. Any bound a hoped-for door-(iv) certificate could give for `realSup` is squeezed between
`iidSup` (an extreme-value / moment = door i/iii object) below and `iidSup + Δ` (the same floor plus a
door-(i) additive-energy excess) above. There is no room between the two dead-door objects for a
non-moment, non-extreme-value mechanism.

## What is proved (and what is NOT)

Everything is a clean order-theoretic consequence of the two carried hypotheses, stated over arbitrary
reals, so the file proves no unverified arithmetic and introduces no axioms. It does **not** prove the
prize inequality, does **not** give any anti-concentration / cancellation estimate, and does **not**
claim door (iv) is achievable. CORE (`M ≤ C·√(n·log(p/n))`) stays open. The contribution is the
quantitative corridor: the open object's sup is trapped in a width-`Δ` moment-band over the
extreme-value floor.

Probes: `scripts/probes/probe_dooriv_jacobi_cocycle_dispersion_magnitude.py`,
`scripts/probes/probe_dooriv_cocycle_excess_structure.py`. Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVObjectMomentCorridor

open ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge
open ArkLib.ProximityGap.Frontier.DoorIVExcessIsMoment

/-- The dispersion advantage as the **actual gap** between the real sup and the surrogate sup:
`gap iidSup realSup = realSup − iidSup`. The Lane-1 measurement is exactly that this gap is
nonnegative (no edge) and bounded by the additive-energy excess (a moment). -/
def gap (iidSup realSup : ℝ) : ℝ := realSup - iidSup

/-- Under the no-edge floor `iidSup ≤ realSup`, the gap is nonnegative. -/
theorem gap_nonneg {iidSup realSup : ℝ} (hEdge : SurrogateLeReal iidSup realSup) :
    0 ≤ gap iidSup realSup := by
  unfold gap SurrogateLeReal at *
  linarith

/-- **Gap is moment-sourced.** If the gap `realSup − iidSup` is bounded by the additive-energy excess
`Δ` (the excess-is-moment fact) and the no-edge floor holds, then `MomentSourced (gap …) Δ` — i.e. the
concrete gap satisfies the abstract moment-source predicate `0 ≤ gap ∧ gap ≤ Δ`. This is the bridge
that instantiates `_DoorIVExcessIsMoment`'s abstract `δ` with the real geometric gap. -/
theorem gap_momentSourced {iidSup realSup Δ : ℝ}
    (hEdge : SurrogateLeReal iidSup realSup)
    (hExcess : gap iidSup realSup ≤ Δ) :
    MomentSourced (gap iidSup realSup) Δ :=
  ⟨gap_nonneg hEdge, hExcess⟩

/-- **The moment-corridor pin (headline).** Under the no-edge floor (`iidSup ≤ realSup`) and the
excess-is-moment bound (`realSup − iidSup ≤ Δ`), the real door-(iv) object's sup is pinned to a
width-`Δ` corridor above the extreme-value floor:
`iidSup ≤ realSup ∧ realSup ≤ iidSup + Δ`. -/
theorem realSup_in_moment_corridor {iidSup realSup Δ : ℝ}
    (hEdge : SurrogateLeReal iidSup realSup)
    (hExcess : gap iidSup realSup ≤ Δ) :
    iidSup ≤ realSup ∧ realSup ≤ iidSup + Δ := by
  unfold SurrogateLeReal at hEdge
  unfold gap at hExcess
  refine ⟨hEdge, ?_⟩
  linarith

/-- **Corridor upper bound feeds the door-(i) ceiling.** If, in addition, the additive-energy excess
obeys a door-(i) Johnson/BGK ceiling `Δ ≤ Bm`, the real sup is bounded above by the surrogate plus that
moment ceiling: `realSup ≤ iidSup + Bm`. So the entire upper envelope of the real object is
`(extreme-value floor) + (moment cap)` — both dead doors, no non-moment slack. -/
theorem realSup_le_surrogate_plus_moment_ceiling {iidSup realSup Δ Bm : ℝ}
    (hEdge : SurrogateLeReal iidSup realSup)
    (hExcess : gap iidSup realSup ≤ Δ)
    (hCeil : Δ ≤ Bm) :
    realSup ≤ iidSup + Bm := by
  have h := (realSup_in_moment_corridor hEdge hExcess).2
  linarith

/-- **Sharp corridor width.** The width of the corridor containing `realSup` is at most `Δ`: the gap
`realSup − iidSup` lies in `[0, Δ]`. A non-moment lever would need this width to be controllable
*below* the moment excess by a non-moment estimate, which the bound `gap ≤ Δ` (a moment) forecloses. -/
theorem corridor_width_le {iidSup realSup Δ : ℝ}
    (hEdge : SurrogateLeReal iidSup realSup)
    (hExcess : gap iidSup realSup ≤ Δ) :
    0 ≤ gap iidSup realSup ∧ gap iidSup realSup ≤ Δ :=
  ⟨gap_nonneg hEdge, hExcess⟩

/-- Falsifiable iff for the corridor: `realSup` sits in `[iidSup, iidSup + Δ]` exactly when the
no-edge floor and the moment bound hold. A future probe breaking either (`realSup < iidSup`, a genuine
edge; or `realSup − iidSup > Δ`, a genuine non-moment excess) would break the corridor. Neither has
across `n = 16..128` and multiple structured primes. -/
theorem corridor_iff {iidSup realSup Δ : ℝ} :
    (SurrogateLeReal iidSup realSup ∧ gap iidSup realSup ≤ Δ) ↔
      (iidSup ≤ realSup ∧ realSup ≤ iidSup + Δ) := by
  constructor
  · rintro ⟨hEdge, hExcess⟩
    exact realSup_in_moment_corridor hEdge hExcess
  · rintro ⟨hlo, hhi⟩
    refine ⟨hlo, ?_⟩
    unfold gap
    linarith

end ArkLib.ProximityGap.Frontier.DoorIVObjectMomentCorridor

-- Axiom audit: all theorems must be ⊆ {propext, Classical.choice, Quot.sound}
section AxiomAudit
open ArkLib.ProximityGap.Frontier.DoorIVObjectMomentCorridor
#print axioms gap_nonneg
#print axioms gap_momentSourced
#print axioms realSup_in_moment_corridor
#print axioms realSup_le_surrogate_plus_moment_ceiling
#print axioms corridor_width_le
#print axioms corridor_iff
end AxiomAudit
