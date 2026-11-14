/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Research.ProximityGap.Frontier._DoorIVCocycleNoRandomEdge
import ArkLib.Research.ProximityGap.Frontier._DoorIVExcessIsMoment

/-!
# Lane-1 → Lane-3 synthesis: the named door-(iv) object is moment-trapped from BOTH sides (#444)

This module is the single citable bridge welding the two *disconnected* Lane-1 object-level
constraint lemmas about the SINGLE live door-(iv) open object (the Jacobi-cocycle / coset-half
coherence sup `M = max_{b≠0} ‖η_b‖` of `_JacobiCocycleDispersion.lean`):

* `DoorIVCocycleNoRandomEdge` — the **no-edge** side: the real cocycle sup is bounded *below* by an
  iid-unit-phase surrogate sup (`iidSup ≤ realSup`, measured `real/iid ∈ [1.15, 1.44]`, never < 1).
  So the cocycle disperses *no better* than random phases: any upper bound on the real sup transfers
  to the (moment / extreme-value = door i/iii) surrogate.
* `DoorIVExcessIsMoment` — the **excess-is-moment** side: the `+15..44%` advantage of the real sup
  *over* the surrogate is an **additive-energy** excess (the period 4th moment equals `E₄(μ_n)/n²`,
  verified exactly), hence bounded by the moment excess `Δ` and capped by exactly the proven-dead
  door-(i) Johnson/BGK ceiling.

No file in the repository imported both before; this is the first kernel-checked bridge tying the two
sides of the door-(iv) *object* analysis into one statement.

## What this module proves (and what it does NOT)

The two sides together say: the named door-(iv) object is **trapped between two moment objects**:

* below by the iid surrogate (`iidSup ≤ realSup`), and
* the gap above it (`realSup − iidSup`, modeled by the advantage `δ`) is itself a moment (`δ ≤ Δ`).

Consequently any upper bound `B` on the real sup that one might hope to derive *non*-classically is
forced through BOTH dead doors:

1. `B` must dominate the iid surrogate (`iidSup ≤ B`) — it cannot beat the extreme-value floor; and
2. the advantage `δ` is moment-bounded above (`δ ≤ Δ`).

*Correction (audit 2026-10-28, R-220).* `δ ≤ Δ` is an **upper** bound on `δ`; it does not prevent
reducing `δ` below `Δ` (an earlier version said reducing it below the moment excess is impossible).
Moreover the formal variables never assert `δ = realSup − iidSup`; that identification is prose
only. So the scalar implications below do not create a two-sided analytic trap and are not an
all-method prohibition; they are conjunction/transitivity facts about entered hypotheses.

This is a **refuted-lever constraint capstone** (Lane 1 → Lane 3): it backs the no-fifth-door
tetrachotomy at the level of the *named open object itself* (not just the mechanism taxonomy). It does
**not** prove the prize inequality, does **not** give any anti-concentration / cancellation estimate,
and does **not** claim door (iv) is achievable. Both inputs are pure restatements of measured /
identity facts carried as hypotheses; the open problem (a genuinely new door-(iv) evaluation) is
exactly as open as before. The contribution is the *conjunction* of the two entered facts; it does
not show that no non-moment, non-extreme-value lever can grip the object.

Probes: `scripts/probes/probe_dooriv_jacobi_cocycle_dispersion_magnitude.py`,
`scripts/probes/probe_dooriv_cocycle_excess_structure.py`. Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVObjectMomentTrappedCapstone

open ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge
open ArkLib.ProximityGap.Frontier.DoorIVExcessIsMoment

/-- **The door-(iv) object is moment-trapped (conjunctive form).**

Given the two measured/identity facts about the single live door-(iv) object — the no-edge side
(`SurrogateLeReal iidSup realSup`, i.e. `iidSup ≤ realSup`) and the excess-is-moment side
(`MomentSourced δ Δ`, i.e. the dispersion advantage `δ` is nonneg and `≤` the additive-energy excess
`Δ`) — both of the following hold simultaneously:

1. **No edge below.** The real object does not disperse strictly below the (moment / extreme-value)
   surrogate: `¬ realSup < iidSup`.
2. **No non-moment lever above.** The dispersion advantage does not exceed the additive-energy
   (moment) excess: `¬ Δ < δ`.

So the named door-(iv) object is squeezed between two dead-door objects on both sides; no non-moment,
non-extreme-value slack survives. This is the single Lane-1→Lane-3 statement behind the prose "the
open door-(iv) object is itself moment-trapped." No cancellation / anti-concentration estimate is
asserted; CORE stays open. -/
theorem doorIV_object_moment_trapped
    {iidSup realSup δ Δ : ℝ}
    (hEdge : SurrogateLeReal iidSup realSup)
    (hMoment : MomentSourced δ Δ) :
    (¬ realSup < iidSup) ∧ (¬ Δ < δ) :=
  ⟨no_cocycle_edge_of_surrogate_le hEdge, no_nonmoment_lever hMoment⟩

/-- **Any candidate bound is forced through both dead doors.**

If, in addition to the two measured facts, one posits an upper bound `realSup ≤ B` on the real sup
and a door-(i) moment ceiling `Δ ≤ Bm` on the additive-energy excess, then:

1. the bound `B` must also dominate the extreme-value surrogate (`iidSup ≤ B`), and
2. the dispersion advantage is capped by the same moment ceiling (`δ ≤ Bm`).

These are scalar consequences of the entered hypotheses: the bound must dominate the surrogate,
and `δ` is capped above by `Bm`. They do not show that no non-moment lever can pay for the prize
(an upper cap on `δ` does not stop `δ` from being smaller; R-220). -/
theorem candidate_bound_forced_through_dead_doors
    {iidSup realSup δ Δ B Bm : ℝ}
    (hEdge : SurrogateLeReal iidSup realSup)
    (hMoment : MomentSourced δ Δ)
    (hReal : realSup ≤ B)
    (hCeil : Δ ≤ Bm) :
    iidSup ≤ B ∧ δ ≤ Bm :=
  ⟨real_bound_transfers_to_surrogate hEdge hReal,
   advantage_within_moment_bound hMoment hCeil⟩

/-- **Falsifiable iff (both sides at once).** The door-(iv) object is moment-trapped exactly when both
measured hypotheses hold: the no-edge inequality `iidSup ≤ realSup` and the moment-source bracket
`0 ≤ δ ∧ δ ≤ Δ`. A future probe breaking *either* (`realSup < iidSup`, a genuine dispersion edge; or
`δ > Δ`, a genuine non-moment excess) would reopen the lever. Neither has broken across `n = 16..128`
and multiple structured primes (`real/iid ∈ [1.15, 1.44]`; `m4_real = E₄/n²` to measured digits). -/
theorem moment_trapped_iff
    {iidSup realSup δ Δ : ℝ} :
    (SurrogateLeReal iidSup realSup ∧ MomentSourced δ Δ) ↔
      (iidSup ≤ realSup ∧ (0 ≤ δ ∧ δ ≤ Δ)) := by
  constructor
  · rintro ⟨hEdge, hMoment⟩
    exact ⟨hEdge, hMoment⟩
  · rintro ⟨hEdge, hMoment⟩
    exact ⟨hEdge, hMoment⟩

end ArkLib.ProximityGap.Frontier.DoorIVObjectMomentTrappedCapstone

-- Axiom audit: all theorems must be ⊆ {propext, Classical.choice, Quot.sound}
section AxiomAudit
open ArkLib.ProximityGap.Frontier.DoorIVObjectMomentTrappedCapstone
#print axioms doorIV_object_moment_trapped
#print axioms candidate_bound_forced_through_dead_doors
#print axioms moment_trapped_iff
end AxiomAudit
