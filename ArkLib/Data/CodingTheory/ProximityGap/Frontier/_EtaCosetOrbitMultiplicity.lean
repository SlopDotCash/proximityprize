/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._EtaCosetInvariance

/-!
# Frequency-coset orbit multiplicity for the door-IV Gauss period (#444)

This file packages the exact finite symmetry behind the localized door-IV object
`ρ(b)` / worst-frequency coherence: once the multiplicative connection set `G` is closed under its own
multiplication and contains no zero, every nonzero frequency `b` carries a whole multiplicative
`G`-orbit of frequencies with the **same** Gauss-period norm.

The previous keystone `_EtaCosetInvariance` proves the pointwise identity
`η_{c b} = η_b` for each admissible `c`.  Here we add the orbit bookkeeping needed by probes and
capstone statements:

* `card_frequency_orbit_eq` : the frequency orbit `G * b` has exactly `|G|` points when `b ≠ 0`.
* `norm_eta_eq_on_frequency_orbit` : every point in that orbit has the same `‖η‖` as `b`.
* `frequency_orbit_nonzero` : the whole orbit stays inside non-principal frequencies.

## Honesty

This is a structural door-IV localization brick only.  It bounds no individual period and does not prove
CORE.  It says a worst `b` is never isolated: it comes with a full thin-subgroup coset of equally bad
frequencies.  The missing prize theorem remains the anti-concentration / coherence bound on the value
shared by such a coset.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ProximityGap.Frontier.EtaCosetOrbitMultiplicity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **A nonzero frequency has a full `|G|` multiplicative orbit.**

Right-multiplication by `b ≠ 0` is injective, so the image `{c*b : c ∈ G}` has cardinality `|G|`.
This is the exact multiplicity bookkeeping behind the statement that a worst frequency comes in a full
multiplicative `G`-coset. -/
theorem card_frequency_orbit_eq (G : Finset F) {b : F} (hb : b ≠ 0) :
    (G.image fun c => c * b).card = G.card := by
  classical
  exact Finset.card_image_of_injOn (s := G) (f := fun c => c * b) (by
    intro c _ d _ hcd
    exact mul_right_cancel₀ hb hcd)

/-- **The `G`-orbit of a nonzero frequency stays non-principal** when `0 ∉ G`. -/
theorem frequency_orbit_nonzero (G : Finset F) {b y : F} (hb : b ≠ 0)
    (hGnz : ∀ c ∈ G, c ≠ 0) (hy : y ∈ G.image fun c => c * b) :
    y ≠ 0 := by
  classical
  rw [Finset.mem_image] at hy
  obtain ⟨c, hcG, rfl⟩ := hy
  exact mul_ne_zero (hGnz c hcG) hb

/-- **Every frequency in the multiplicative `G`-orbit has the same period norm.**

Assume the connection set has no zero and is multiplicatively closed.  If `y = c*b` with `c ∈ G`, then
`‖η_y‖ = ‖η_b‖`.  This is `_EtaCosetInvariance.norm_eta_dilate_eq` lifted from one dilation to the
whole finite coset. -/
theorem norm_eta_eq_on_frequency_orbit {ψ : AddChar F ℂ} (G : Finset F)
    (hGnz : ∀ c ∈ G, c ≠ 0)
    (hmulG : ∀ c ∈ G, ∀ x ∈ G, c * x ∈ G) (b y : F)
    (hy : y ∈ G.image fun c => c * b) :
    ‖eta ψ G y‖ = ‖eta ψ G b‖ := by
  classical
  rw [Finset.mem_image] at hy
  obtain ⟨c, hcG, rfl⟩ := hy
  exact ProximityGap.Frontier.EtaCosetInvariance.norm_eta_dilate_eq G (hGnz c hcG)
    (hmulG c hcG) b

end ProximityGap.Frontier.EtaCosetOrbitMultiplicity

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only). -/
#print axioms ProximityGap.Frontier.EtaCosetOrbitMultiplicity.card_frequency_orbit_eq
#print axioms ProximityGap.Frontier.EtaCosetOrbitMultiplicity.frequency_orbit_nonzero
#print axioms ProximityGap.Frontier.EtaCosetOrbitMultiplicity.norm_eta_eq_on_frequency_orbit
