/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._EtaCosetOrbitMultiplicity

/-!
# Frequency-coset orbit partition bookkeeping for door IV (#444)

`_EtaCosetOrbitMultiplicity` records that each nonzero frequency `b` carries a full `G`-orbit of
frequencies with the same Gauss-period norm.  This file adds the quotient bookkeeping: under the usual
finite multiplicative-subgroup closures (multiplication + inverse), two such frequency orbits are equal
as soon as one representative lies in the other orbit.

This is the formal coset-partition substrate for the localized door-IV search over worst frequencies:
probe over quotient representatives, not over all `b ∈ F*`, because changing representatives inside the
same multiplicative `G`-coset changes neither the orbit nor `‖η_b‖`.

## Honesty

Pure finite coset algebra.  It bounds no period, proves no anti-concentration, and does not close CORE.
The missing theorem is still an upper bound for the shared `η` value on each coset.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


open Finset AddChar

namespace ProximityGap.Frontier.EtaCosetOrbitPartition

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Orbit equality from membership of one representative in the other orbit.**

Assume `G` is closed under multiplication and inverse.  If `b = c*a` for some `c ∈ G`, then the two
frequency orbits `{d*b : d ∈ G}` and `{d*a : d ∈ G}` are equal.  This is the exact quotient-representative
bookkeeping behind the statement that the door-IV worst-frequency search lives on `F* / G`. -/
theorem frequency_orbit_eq_of_mem_orbit (G : Finset F)
    (hGnz : ∀ c ∈ G, c ≠ 0)
    (hmulG : ∀ c ∈ G, ∀ d ∈ G, c * d ∈ G)
    (hinvG : ∀ c ∈ G, c⁻¹ ∈ G) {a b : F}
    (hb : b ∈ G.image fun c => c * a) :
    (G.image fun d => d * b) = (G.image fun d => d * a) := by
  classical
  rw [Finset.mem_image] at hb
  obtain ⟨c, hcG, rfl⟩ := hb
  apply Finset.ext
  intro y
  constructor
  · intro hy
    rw [Finset.mem_image] at hy
    obtain ⟨d, hdG, rfl⟩ := hy
    rw [Finset.mem_image]
    refine ⟨d * c, hmulG d hdG c hcG, ?_⟩
    ring
  · intro hy
    rw [Finset.mem_image] at hy
    obtain ⟨d, hdG, rfl⟩ := hy
    rw [Finset.mem_image]
    refine ⟨d * c⁻¹, hmulG d hdG c⁻¹ (hinvG c hcG), ?_⟩
    have hcne : c ≠ 0 := hGnz c hcG
    field_simp [hcne]

/-- **Orbit equality transports the door-IV period norm across representatives.**

This combines orbit equality with `norm_eta_eq_on_frequency_orbit`: if `b` lies in the frequency orbit
of `a`, then every frequency in the orbit of `b` has the same `η`-norm as `a`. -/
theorem norm_eta_eq_on_equivalent_frequency_orbit {ψ : AddChar F ℂ} (G : Finset F)
    (hGnz : ∀ c ∈ G, c ≠ 0)
    (hmulG : ∀ c ∈ G, ∀ d ∈ G, c * d ∈ G)
    (hinvG : ∀ c ∈ G, c⁻¹ ∈ G) (a b y : F)
    (hb : b ∈ G.image fun c => c * a)
    (hy : y ∈ G.image fun d => d * b) :
    ‖ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G y‖
      = ‖ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G a‖ := by
  classical
  have horb : (G.image fun d => d * b) = (G.image fun d => d * a) :=
    frequency_orbit_eq_of_mem_orbit G hGnz hmulG hinvG hb
  exact ProximityGap.Frontier.EtaCosetOrbitMultiplicity.norm_eta_eq_on_frequency_orbit
    G hGnz hmulG a y (by simpa [horb] using hy)

end ProximityGap.Frontier.EtaCosetOrbitPartition

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only). -/
#print axioms ProximityGap.Frontier.EtaCosetOrbitPartition.frequency_orbit_eq_of_mem_orbit
#print axioms ProximityGap.Frontier.EtaCosetOrbitPartition.norm_eta_eq_on_equivalent_frequency_orbit
