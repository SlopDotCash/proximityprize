/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._EtaCosetOrbitMultiplicity

/-!
# Worst-frequency orbit lower bound for the door-IV object (#444)

This file packages the exact multiplicity consequence of the already-proven door-IV coset invariance:
if one nonzero frequency `b` is above a threshold, then the whole multiplicative `G`-orbit `G*b` is above
that same threshold.  Since right-multiplication by `b ≠ 0` is injective, this gives at least `|G|`
non-principal above-threshold frequencies.

## Why this is useful and limited

Lane 1 asks whether the adversarial/worst `b` set has exploitable structure.  The positive structure that
is kernel-checked so far is purely multiplicative: bad frequencies come in full `μ_n`-cosets.  This file
turns that into the exact counting statement used by quotient probes: counting bad frequencies in `F*`
is counting bad quotient representatives, multiplied by `|G|`.

Honesty: this is quotient/multiplicity bookkeeping only.  It proves no upper bound on any Gauss period,
no anti-concentration, and no CORE/prize closure.  The missing theorem remains a bound on the shared
period value on each quotient orbit.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ProximityGap.Frontier.WorstBOrbitLowerBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- If `b` is above a threshold, then every element of its multiplicative `G`-orbit is above the same
threshold.  This is the set-level form of the door-IV coset invariance. -/
theorem frequency_orbit_subset_threshold {ψ : AddChar F ℂ} (G : Finset F)
    (hGnz : ∀ c ∈ G, c ≠ 0)
    (hmulG : ∀ c ∈ G, ∀ x ∈ G, c * x ∈ G) (thr : ℝ) {b : F}
    (hbthr : thr ≤ ‖eta ψ G b‖) :
    (G.image fun c => c * b) ⊆ Finset.univ.filter (fun y => thr ≤ ‖eta ψ G y‖) := by
  classical
  intro y hy
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ y, ?_⟩
  have hnorm := ProximityGap.Frontier.EtaCosetOrbitMultiplicity.norm_eta_eq_on_frequency_orbit
    (ψ := ψ) G hGnz hmulG b y hy
  simpa [hnorm] using hbthr

/-- Nonzero version: if `b ≠ 0` and `0 ∉ G`, then the whole above-threshold orbit lies in the
non-principal frequency line. -/
theorem frequency_orbit_subset_nonzero_threshold {ψ : AddChar F ℂ} (G : Finset F)
    (hGnz : ∀ c ∈ G, c ≠ 0)
    (hmulG : ∀ c ∈ G, ∀ x ∈ G, c * x ∈ G) (thr : ℝ) {b : F} (hbne : b ≠ 0)
    (hbthr : thr ≤ ‖eta ψ G b‖) :
    (G.image fun c => c * b) ⊆
      Finset.univ.filter (fun y => y ≠ 0 ∧ thr ≤ ‖eta ψ G y‖) := by
  classical
  intro y hy
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ y, ?_⟩
  refine ⟨ProximityGap.Frontier.EtaCosetOrbitMultiplicity.frequency_orbit_nonzero
    G hbne hGnz hy, ?_⟩
  have hnorm := ProximityGap.Frontier.EtaCosetOrbitMultiplicity.norm_eta_eq_on_frequency_orbit
    (ψ := ψ) G hGnz hmulG b y hy
  simpa [hnorm] using hbthr

/-- A single above-threshold nonzero representative forces at least `|G|` non-principal
above-threshold frequencies. -/
theorem card_nonzero_threshold_ge_card_of_mem {ψ : AddChar F ℂ} (G : Finset F)
    (hGnz : ∀ c ∈ G, c ≠ 0)
    (hmulG : ∀ c ∈ G, ∀ x ∈ G, c * x ∈ G) (thr : ℝ) {b : F} (hbne : b ≠ 0)
    (hbthr : thr ≤ ‖eta ψ G b‖) :
    G.card ≤ (Finset.univ.filter (fun y => y ≠ 0 ∧ thr ≤ ‖eta ψ G y‖)).card := by
  classical
  calc
    G.card = (G.image fun c => c * b).card :=
      (ProximityGap.Frontier.EtaCosetOrbitMultiplicity.card_frequency_orbit_eq G hbne).symm
    _ ≤ (Finset.univ.filter (fun y => y ≠ 0 ∧ thr ≤ ‖eta ψ G y‖)).card :=
      Finset.card_le_card (frequency_orbit_subset_nonzero_threshold G hGnz hmulG thr hbne hbthr)

/-- Contrapositive quotient-count certificate: if fewer than `|G|` non-principal frequencies clear a
threshold, then no nonzero frequency clears it.  Thus any nonempty above-threshold event is visible only
at the quotient-orbit scale, never as an isolated `b`. -/
theorem not_exists_nonzero_threshold_of_card_lt {ψ : AddChar F ℂ} (G : Finset F)
    (hGnz : ∀ c ∈ G, c ≠ 0)
    (hmulG : ∀ c ∈ G, ∀ x ∈ G, c * x ∈ G) (thr : ℝ)
    (hcard : (Finset.univ.filter (fun y => y ≠ 0 ∧ thr ≤ ‖eta ψ G y‖)).card < G.card) :
    ¬ ∃ b : F, b ≠ 0 ∧ thr ≤ ‖eta ψ G b‖ := by
  rintro ⟨b, hbne, hbthr⟩
  exact not_lt_of_ge (card_nonzero_threshold_ge_card_of_mem G hGnz hmulG thr hbne hbthr) hcard

end ProximityGap.Frontier.WorstBOrbitLowerBound

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only). -/
#print axioms ProximityGap.Frontier.WorstBOrbitLowerBound.frequency_orbit_subset_threshold
#print axioms ProximityGap.Frontier.WorstBOrbitLowerBound.frequency_orbit_subset_nonzero_threshold
#print axioms ProximityGap.Frontier.WorstBOrbitLowerBound.card_nonzero_threshold_ge_card_of_mem
#print axioms ProximityGap.Frontier.WorstBOrbitLowerBound.not_exists_nonzero_threshold_of_card_lt
