/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card

/-!
# Orbit/value-spectrum counting bricks

The cliff probes for the proximity-gap programme separate two quantities:
the number of certifying configurations and the number of distinct `γ` values
they produce.  The latter is an image-size problem.  If all produced values lie
in one small parameterized orbit, or in a small list of such orbits, then the
value spectrum is small even when the configuration supply is large.

This file records that reusable combinatorial consumer.  It intentionally does
not bake in a particular group action; downstream smooth-domain proofs only
need to provide the finite parameterization of the value orbit(s).
-/

open Finset

namespace ProximityGap

/-- If every value produced by `cert` lies in a target finite set, then the value spectrum
has cardinality at most the target cardinality. -/
theorem valueSpectrum_card_le_of_mem_target {α β : Type} [DecidableEq β]
    (cert : Finset α) (value : α → β) (target : Finset β)
    (hcover : ∀ x ∈ cert, value x ∈ target) :
    (cert.image value).card ≤ target.card := by
  refine Finset.card_le_card ?_
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
  exact hcover x hx

/-- Single-orbit form: if every produced value is one of `orbit i`, then the value
spectrum has size at most the parameter type. -/
theorem valueSpectrum_card_le_of_orbit_param {ι α β : Type} [Fintype ι] [DecidableEq β]
    (cert : Finset α) (value : α → β) (orbit : ι → β)
    (hcover : ∀ x ∈ cert, ∃ i : ι, value x = orbit i) :
    (cert.image value).card ≤ Fintype.card ι := by
  classical
  let target : Finset β := (Finset.univ : Finset ι).image orbit
  have hmem : ∀ x ∈ cert, value x ∈ target := by
    intro x hx
    rcases hcover x hx with ⟨i, hi⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.symm⟩
  have hspec : (cert.image value).card ≤ target.card :=
    valueSpectrum_card_le_of_mem_target cert value target hmem
  have htarget : target.card ≤ Fintype.card ι := by
    simpa [target] using (Finset.card_image_le (s := (Finset.univ : Finset ι)) (f := orbit))
  exact le_trans hspec htarget

/-- Multi-orbit form: if every produced value lies in one of the parameterized orbits
`i ↦ act i seed` for `seed ∈ seeds`, then the value spectrum is bounded by
`seeds.card * Fintype.card ι`.

This is the intended consumer for spectrum-collapse statements of the form
`O(n * poly(j))`: `ι` is the smooth-domain rotation parameter, while `seeds`
is the small list of orbit prototypes left by the census theorem. -/
theorem valueSpectrum_card_le_of_orbit_seed_cover
    {ι α β : Type} [Fintype ι] [DecidableEq β]
    (cert : Finset α) (value : α → β) (seeds : Finset β) (act : ι → β → β)
    (hcover : ∀ x ∈ cert, ∃ seed ∈ seeds, ∃ i : ι, value x = act i seed) :
    (cert.image value).card ≤ seeds.card * Fintype.card ι := by
  classical
  let target : Finset β :=
    (seeds ×ˢ (Finset.univ : Finset ι)).image (fun p : β × ι => act p.2 p.1)
  have hmem : ∀ x ∈ cert, value x ∈ target := by
    intro x hx
    rcases hcover x hx with ⟨seed, hseed, i, hi⟩
    refine Finset.mem_image.mpr ?_
    exact ⟨(seed, i), Finset.mem_product.mpr ⟨hseed, Finset.mem_univ i⟩, hi.symm⟩
  have hspec : (cert.image value).card ≤ target.card :=
    valueSpectrum_card_le_of_mem_target cert value target hmem
  have htarget : target.card ≤ seeds.card * Fintype.card ι := by
    calc
      target.card ≤ (seeds ×ˢ (Finset.univ : Finset ι)).card := by
        simpa [target] using
          (Finset.card_image_le
            (s := seeds ×ˢ (Finset.univ : Finset ι))
            (f := fun p : β × ι => act p.2 p.1))
      _ = seeds.card * Fintype.card ι := by
        simp [Finset.card_product]
  exact le_trans hspec htarget

end ProximityGap

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.valueSpectrum_card_le_of_mem_target
#print axioms ProximityGap.valueSpectrum_card_le_of_orbit_param
#print axioms ProximityGap.valueSpectrum_card_le_of_orbit_seed_cover
