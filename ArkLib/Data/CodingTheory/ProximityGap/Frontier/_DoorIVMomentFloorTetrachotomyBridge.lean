/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NoFifthDoorTetrachotomy
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVMomentEnergyFloorOvershoot

/-!
# `_DoorIVMomentFloorTetrachotomyBridge`: wiring the INTERNAL energy floor into the tetrachotomy (#444)

## What this connects

The no-fifth-door tetrachotomy (`_NoFifthDoorTetrachotomy`) discharges the door-(i) (moment /
symmetric-function) overshoot from the **third-party SOTA exponent** `δ < 1/2`: a moment mechanism that
`RespectsProvenScale` certifies at least the literature value `C·n^{1−δ}`, and that value eventually
exceeds the BGK argument scale `√(n·L)` (`momentEVT_scale_eventually_ge_bgkScale`).  That is a
*citation* to the in-tree SOTA number `δ ≈ 0.011`, threaded as a hypothesis.

Meanwhile `_DoorIVMomentEnergyFloorOvershoot` proved, with **NO SOTA exponent**, the structural fact
that a moment mechanism's only accessible sup-certificate — the energy-moment scale
`(E_r / card)^{1/(2r)}` — never drops below the L²/Plancherel rms floor, because every `η_b` is REAL
(via `momentHierarchy_energy_dominated`).  In particular the squared rms `E_1 / card` sits **below**
`(max_c |η_c|)²`: the moment route's scale is `≥ rms`.

These two capstones were not connected.  This file supplies the bridge:

* a moment mechanism whose certified scale is (at least) its accessible energy-moment scale satisfies
  the **floor** `prizeScale n ≤ certScale` — i.e. it can never certify a **strictly sub-prize** bound
  `certScale < √n`.  This is the door-(i) floor *derived from `η` being real*, with **no `δ`**.

## Honest scope of the bridge (read before citing)

The tetrachotomy's `forces_doorIV` consumes `OvershootsBGK`, i.e. `√(n·L) ≤ certScale` — a floor at the
**BGK ceiling** `√(n·L)`, a strict `√L` factor ABOVE the prize floor `√n`.  The internal energy floor
proves only `√n ≤ certScale` (the prize floor itself), which is **strictly weaker** than `OvershootsBGK`
in the regime `L > 1`.  So this bridge does **not** discharge `OvershootsBGK` and does **not** replace
the SOTA hypothesis inside `forces_doorIV`.

What it *does* give is the honest, SOTA-free half of the door-(i) obstruction: the moment door cannot
descend **below** the prize floor `√n`.  The remaining `√L` factor between `√n` and the BGK ceiling
`√(n·L)` is exactly the open door-(iv) gap; the SOTA citation is what currently fills it inside the
tetrachotomy, and replacing that citation with an internal proof is **still open** (it would require an
internal proof that the moment scale reaches `√(n·L)`, not merely `√n`).  We state the bridge at the
floor it actually proves and flag the gap to the ceiling explicitly.

NO CORE bound, NO cancellation / anti-concentration / completion / capacity claim.  CORE
`M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN; door (iv) remains the only live door.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVMomentFloorTetrachotomyBridge

open ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy
open ArkLib.ProximityGap.Frontier.DoorIVMomentEnergyFloorOvershoot

/-- The **accessible energy-moment scale** of a real period field at the rms (`r = 1`) rung:
`rms = √(E_1 / card)`.  This is the smallest scale a moment mechanism can possibly extract from the
energy hierarchy (the `r = 1` / Plancherel rung); higher rungs only overshoot it
(`normSq_energyMoment_one_le_normEnergyMoment_two`). -/
noncomputable def rmsScale {ι : Type*} (f : ι → ℝ) (s : Finset ι) : ℝ :=
  Real.sqrt (energyMoment f s 1 / (s.card : ℝ))

/-- The rms scale is nonnegative. -/
theorem rmsScale_nonneg {ι : Type*} (f : ι → ℝ) (s : Finset ι) :
    0 ≤ rmsScale f s := Real.sqrt_nonneg _

/-- **The rms scale is the prize floor when `E_1 / card = n`.**  In the prize regime the negation-
closed thin subgroup has `E_1 / card = ∑_c (η_c)² / card = n` (the Plancherel identity, proven in tree
as `max_ge_rms`'s hypothesis), so `rmsScale f s = √n = prizeScale n`.  We state the algebraic bridge:
if the normalized first energy moment equals `n`, the rms scale equals the tetrachotomy's prize scale. -/
theorem rmsScale_eq_prizeScale {ι : Type*} (f : ι → ℝ) (s : Finset ι) {n : ℝ}
    (h : energyMoment f s 1 / (s.card : ℝ) = n) :
    rmsScale f s = prizeScale n := by
  unfold rmsScale prizeScale
  rw [h]

/-- **The energy-moment scale never drops below the rms scale (root form).**  Taking square roots of
the `r = 2` power-mean rung `(E_1/card)² ≤ E_2/card`, the L⁴ energy scale `√(E_2/card)` dominates the
squared rms... but the cleaner consumable is: the rms scale itself is a genuine lower scale, and the
max dominates it.  Here we record the **max ≥ rms** form needed for the floor: `rmsScale ≤ max |f|`. -/
theorem rmsScale_le_sup {ι : Type*} (f : ι → ℝ) (s : Finset ι) (hs : s.Nonempty) :
    rmsScale f s ≤ s.sup' hs (fun c => |f c|) := by
  unfold rmsScale
  have hfloor := normEnergyMoment_one_le_sq_max f s hs
  -- hfloor : E_1/card ≤ (sup' |f|)^2
  have hsup_nonneg : 0 ≤ s.sup' hs (fun c => |f c|) := by
    obtain ⟨c, hc⟩ := hs
    exact le_trans (abs_nonneg (f c)) (Finset.le_sup' (fun c => |f c|) hc)
  calc Real.sqrt (energyMoment f s 1 / (s.card : ℝ))
      ≤ Real.sqrt ((s.sup' hs (fun c => |f c|)) ^ 2) := Real.sqrt_le_sqrt hfloor
    _ = s.sup' hs (fun c => |f c|) := by
        rw [Real.sqrt_sq hsup_nonneg]

/-- **Door-(i) prize floor, INTERNAL (no SOTA exponent).**  Model a *real* moment mechanism on the
real period field `f = η` over the index set `s` as one whose certified scale is at least its accessible
rms scale (the `r = 1` / Plancherel rung — the smallest scale the energy hierarchy affords).  If the
normalized first energy moment equals `n` (the Plancherel identity `∑(η_c)²/card = n` of the negation-
closed thin subgroup), then the mechanism's certified scale is **at least the prize floor**
`prizeScale n = √n`.

This is the door-(i) floor derived purely from `η` being real (via the energy-moment domination), with
**NO `δ`, NO SOTA citation**: a moment mechanism cannot certify a *strictly sub-prize* bound. -/
theorem momentMechanism_certScale_ge_prizeScale
    {ι : Type*} (f : ι → ℝ) (s : Finset ι) {n : ℝ} (m : Mechanism)
    (hPlancherel : energyMoment f s 1 / (s.card : ℝ) = n)
    (hreal : rmsScale f s ≤ m.certScale) :
    prizeScale n ≤ m.certScale := by
  rw [← rmsScale_eq_prizeScale f s hPlancherel]
  exact hreal

/-- **No strictly sub-prize moment certificate (INTERNAL).**  Contrapositive packaging of the floor:
a real moment mechanism (certifying at least its accessible rms scale) cannot certify a bound strictly
below the prize floor `√n`.  Derived from `η` real (energy-moment domination), no SOTA exponent. -/
theorem momentMechanism_not_subPrize
    {ι : Type*} (f : ι → ℝ) (s : Finset ι) {n : ℝ} (m : Mechanism)
    (hPlancherel : energyMoment f s 1 / (s.card : ℝ) = n)
    (hreal : rmsScale f s ≤ m.certScale) :
    ¬ (m.certScale < prizeScale n) := by
  intro hlt
  exact absurd (momentMechanism_certScale_ge_prizeScale f s m hPlancherel hreal)
    (not_le.mpr hlt)

/-- **The internal floor is strictly below the BGK ceiling (the honest gap to the tetrachotomy).**
In the prize regime `L > 1`, the prize floor that the internal energy floor delivers, `prizeScale n`,
is STRICTLY below the BGK ceiling `bgkScale n L` that the tetrachotomy's `OvershootsBGK` requires.  This
records, as a kernel statement, exactly *why* the internal floor does not by itself discharge
`OvershootsBGK`: there is a residual `√L` factor between the internal floor `√n` and the BGK ceiling
`√(n·L)`, and closing it is the open door-(iv) content (currently filled by the SOTA citation). -/
theorem internalFloor_strictly_below_bgkCeiling {n L : ℝ} (hn : 0 < n) (hL : 1 < L) :
    prizeScale n < bgkScale n L :=
  prizeScale_lt_bgkScale hn hL

/-- **Bridge summary (citable).**  For a real period field `f = η` with Plancherel normalization
`E_1/card = n`, and a real moment mechanism certifying at least its accessible rms scale, BOTH hold in
the prize regime `L > 1`:

* `prizeScale n ≤ m.certScale` — the moment door cannot descend **below** the prize floor `√n`
  (INTERNAL: from `η` real, no SOTA exponent); and
* `prizeScale n < bgkScale n L` — yet the prize floor is strictly below the BGK ceiling that
  `OvershootsBGK` requires, so this internal floor does **not** discharge `OvershootsBGK`.

The bundle makes precise what the internal energy floor contributes to the tetrachotomy (a SOTA-free
floor at `√n`) and what it leaves open (the `√L` factor up to the BGK ceiling = the door-(iv) gap). -/
theorem momentDoor_internalFloor_bridge
    {ι : Type*} (f : ι → ℝ) (s : Finset ι) {n L : ℝ} (m : Mechanism)
    (hn : 0 < n) (hL : 1 < L)
    (hPlancherel : energyMoment f s 1 / (s.card : ℝ) = n)
    (hreal : rmsScale f s ≤ m.certScale) :
    prizeScale n ≤ m.certScale ∧ prizeScale n < bgkScale n L :=
  ⟨momentMechanism_certScale_ge_prizeScale f s m hPlancherel hreal,
   internalFloor_strictly_below_bgkCeiling hn hL⟩

end ArkLib.ProximityGap.Frontier.DoorIVMomentFloorTetrachotomyBridge

#print axioms ArkLib.ProximityGap.Frontier.DoorIVMomentFloorTetrachotomyBridge.momentMechanism_certScale_ge_prizeScale
#print axioms ArkLib.ProximityGap.Frontier.DoorIVMomentFloorTetrachotomyBridge.rmsScale_le_sup
#print axioms ArkLib.ProximityGap.Frontier.DoorIVMomentFloorTetrachotomyBridge.momentDoor_internalFloor_bridge
