/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountCosetInvariance

/-!
# Coset-concentration of the representation count (#389): a `√n` sharpening

Building on the coset-invariance `repCount_mul_mem_eq` (`r(c·ζ) = r(c)` for `ζ ∈ G`),
this file proves a genuinely sharper pointwise bound on the additive representation
count of a root-of-unity subgroup `G = μ_n`:

> **`repCount_sq_card_le_energy`** — for every `c ≠ 0`, `n · r(c)² ≤ E(G)`.

Equivalently `r(c) ≤ √(E(G)/n)`.  The trivial bound from `E(G) = Σ_t r(t)²` is only
`r(c) ≤ √(E(G))`; coset-invariance improves it by a **factor `√n`**, because the whole
`n`-element coset `c·G` shares the single value `r(c)`, contributing `n·r(c)²` to the
energy at once.

Consequence for the wall: any additive-energy bound `E(G) ≤ B` now yields the
Garcia–Voloch rep bound `r(c) ≤ √(B/n)` — e.g. the (conditional) Heath-Brown–Konyagin
`E(G) ≲ n^{5/2}` gives `r(c) ≲ n^{3/4}`, and the minimal/Sidon energy `E(G) ≈ n²`
gives `r(c) ≲ √n`.  This is the coset-uniform conversion the GV/HBK route needs,
proved unconditionally from the symmetry alone.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- The sumset `G + G` as a finset. -/
def sumset (G : Finset F) : Finset F := (G ×ˢ G).image (fun p => p.1 + p.2)

/-- The fiber `{(a,b) ∈ G×G : a+b=t}` has exactly `repCount G t` elements. -/
theorem fiber_card_eq_repCount (G : Finset F) (t : F) :
    ((G ×ˢ G).filter (fun p => p.1 + p.2 = t)).card = repCount G t := by
  rw [repCount]
  refine Finset.card_nbij' (fun p => p.1) (fun y => (y, t - y)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨ha, hb⟩, hab⟩ := hp
    simp only [Finset.mem_coe, Finset.mem_filter]
    refine ⟨ha, ?_⟩
    have : t - a = b := by rw [← hab]; ring
    rw [this]; exact hb
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy
    obtain ⟨hy, hty⟩ := hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hy, hty⟩, by ring⟩
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨_, hab⟩ := hp
    simp only [Prod.mk.injEq, true_and]
    rw [← hab]; ring
  · intro y hy
    simp

/-- **The additive energy is the sum of squared representation counts** over the
sumset: `E(G) = Σ_{t ∈ G+G} r(t)²`. -/
theorem additiveEnergy_eq_sum_sq (G : Finset F) :
    additiveEnergy G = ∑ t ∈ sumset G, (repCount G t) ^ 2 := by
  rw [additiveEnergy]
  rw [← Finset.sum_product']
  have hmaps : ∀ p ∈ G ×ˢ G, p.1 + p.2 ∈ sumset G := by
    intro p hp; rw [sumset, Finset.mem_image]; exact ⟨p, hp, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hconst : ∀ p ∈ (G ×ˢ G).filter (fun p => p.1 + p.2 = t),
      repCount G (p.1 + p.2) = repCount G t := by
    intro p hp; rw [Finset.mem_filter] at hp; rw [hp.2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul,
    fiber_card_eq_repCount G t, sq]

/-- The coset `c·G` as a finset (`{c·z : z ∈ G}`). -/
theorem card_smul_coset {G : Finset F} {c : F} (hc : c ≠ 0) :
    (G.image (fun z => c * z)).card = G.card :=
  Finset.card_image_of_injective _ (fun _ _ h => by
    field_simp at h; exact h)

/-- **THE COSET-CONCENTRATION BOUND**: for a root-of-unity subgroup `G = μ_n` and any
`c ≠ 0`, `n · r(c)² ≤ E(G)`.  The `n`-element coset `c·G` shares the value `r(c)`
(coset-invariance), contributing `n·r(c)²` to `E(G) = Σ_t r(t)²` at once. -/
theorem repCount_sq_card_le_energy {G : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) {c : F} (hc : c ≠ 0) :
    G.card * (repCount G c) ^ 2 ≤ additiveEnergy G := by
  classical
  rcases Nat.eq_zero_or_pos (repCount G c) with h0 | hpos
  · simp [h0]
  -- the coset c·G
  set cG : Finset F := G.image (fun z => c * z) with hcG
  -- every element of c·G has repCount = r(c) and lies in the sumset
  have hval : ∀ t ∈ cG, repCount G t = repCount G c := by
    intro t ht
    rw [hcG, Finset.mem_image] at ht
    obtain ⟨z, hz, rfl⟩ := ht
    exact repCount_mul_mem_eq hn hGmem c hz
  have hsub : cG ⊆ sumset G := by
    intro t ht
    have hrt : repCount G t = repCount G c := hval t ht
    have htpos : 0 < repCount G t := by rw [hrt]; exact hpos
    have hne : (G.filter (fun y => t - y ∈ G)).Nonempty := Finset.card_pos.mp htpos
    obtain ⟨y, hy⟩ := hne
    obtain ⟨hyG, hyt⟩ := Finset.mem_filter.mp hy
    rw [sumset, Finset.mem_image]
    refine ⟨(y, t - y), ?_, by ring⟩
    rw [Finset.mem_product]; exact ⟨hyG, hyt⟩
  -- n·r(c)² = Σ_{t∈cG} r(t)²  ≤  Σ_{t∈sumset} r(t)² = E(G)
  calc G.card * (repCount G c) ^ 2
      = ∑ _t ∈ cG, (repCount G c) ^ 2 := by
        rw [Finset.sum_const, smul_eq_mul, card_smul_coset hc]
    _ = ∑ t ∈ cG, (repCount G t) ^ 2 := by
        refine Finset.sum_congr rfl fun t ht => ?_; rw [hval t ht]
    _ ≤ ∑ t ∈ sumset G, (repCount G t) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    _ = additiveEnergy G := (additiveEnergy_eq_sum_sq G).symm

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.additiveEnergy_eq_sum_sq
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount_sq_card_le_energy
