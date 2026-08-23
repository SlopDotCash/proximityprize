/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SmoothCubicSupplyBound
import ArkLib.Data.CodingTheory.ProximityGap.RepCountCosetConcentration
import ArkLib.Data.CodingTheory.ProximityGap.RepCountSidonBound

/-!
# The cubic supply has an EXACT coset closed form (#389)

The cubic word's explainable-3-core count equals the zero-sum-triple count
`zeroSumTriples G = ∑_{c ∈ G} r(−c)` (sibling `cubicSupply_eq_sumZeroCard`).  For a
root-of-unity subgroup `G = μ_n`, coset-invariance `repCount_mul_mem_eq` pins `r` to a
single value on `G` itself (`G = 1·G`), so the cubic supply collapses to an **exact
closed form**:

> **`zeroSumTriples_eq_card_mul_repCount_one`** — `zeroSumTriples G = |G| · r(1)`.

This upgrades the Cauchy–Schwarz bound `T(G) ≤ √(n·E)` (sibling) to follow from an exact
identity, and combines with the coset-concentration / Sidon bounds:

* **`zeroSumTriples_sq_le_card_energy_viaCoset`** — `T(G)² ≤ |G| · E(G)` (now via the identity
  `T = |G|·r(1)` and `|G|·r(1)² ≤ E`).
* **`zeroSumTriples_sq_le_of_sidonModNeg`** — under the Sidon hypothesis, `T(G)² ≤ 3n³`,
  i.e. `T(G) ≤ √3 · n^{3/2}` — the minimal cubic supply, conditional on `μ_n` being
  Sidon-modulo-negation (the open energy input, isolated).

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

open ArkLib.ProximityGap.AdditiveEnergySidonModNeg

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The exact coset closed form of the cubic supply.**  For a root-of-unity subgroup,
`r` is constant on `G` (coset-invariance, `G = 1·G`), so the zero-sum-triple count is
`|G| · r(1)`. -/
theorem zeroSumTriples_eq_card_mul_repCount_one {G : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (hneg : ∀ x ∈ G, -x ∈ G) :
    zeroSumTriples G = G.card * repCount G 1 := by
  rw [zeroSumTriples]
  have key : ∀ c ∈ G, repCount G (-c) = repCount G 1 := by
    intro c hc
    have hnc : -c ∈ G := hneg c hc
    have h := repCount_mul_mem_eq hn hGmem 1 hnc
    rwa [one_mul] at h
  rw [Finset.sum_congr rfl key, Finset.sum_const, smul_eq_mul]

/-- **`T(G)² ≤ |G|·E(G)`**, via the exact identity and coset-concentration. -/
theorem zeroSumTriples_sq_le_card_energy_viaCoset {G : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (hneg : ∀ x ∈ G, -x ∈ G) :
    (zeroSumTriples G) ^ 2 ≤ G.card * additiveEnergy G := by
  rw [zeroSumTriples_eq_card_mul_repCount_one hn hGmem hneg]
  have hcc : G.card * (repCount G 1) ^ 2 ≤ additiveEnergy G :=
    repCount_sq_card_le_energy hn hGmem (one_ne_zero)
  calc (G.card * repCount G 1) ^ 2
      = G.card * (G.card * (repCount G 1) ^ 2) := by ring
    _ ≤ G.card * additiveEnergy G := Nat.mul_le_mul_left _ hcc

/-- **The minimal cubic supply under the Sidon hypothesis: `T(G)² ≤ 3n³`.**  Conditional
on `SidonModNeg G` (the open minimal-energy input for `μ_n`), the cubic supply is
`T(G) ≤ √3 · n^{3/2}`. -/
theorem zeroSumTriples_sq_le_of_sidonModNeg {G : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (hcard : G.card = n) (h2 : (2 : F) ≠ 0)
    (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G) (hS : SidonModNeg G) :
    (zeroSumTriples G) ^ 2 ≤ 3 * n ^ 3 := by
  have hE : additiveEnergy G = 3 * G.card ^ 2 - 3 * G.card :=
    additiveEnergy_eq_of_sidonModNeg h2 h0 hneg hS
  have hEle : additiveEnergy G ≤ 3 * G.card ^ 2 := by rw [hE]; exact Nat.sub_le _ _
  have h1 : (zeroSumTriples G) ^ 2 ≤ G.card * additiveEnergy G :=
    zeroSumTriples_sq_le_card_energy_viaCoset hn hGmem hneg
  calc (zeroSumTriples G) ^ 2 ≤ G.card * additiveEnergy G := h1
    _ ≤ G.card * (3 * G.card ^ 2) := Nat.mul_le_mul_left _ hEle
    _ = 3 * G.card ^ 3 := by ring
    _ = 3 * n ^ 3 := by rw [hcard]

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.zeroSumTriples_eq_card_mul_repCount_one
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.zeroSumTriples_sq_le_of_sidonModNeg
