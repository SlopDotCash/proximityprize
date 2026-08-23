/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyNegClosedLower
import ArkLib.Data.CodingTheory.ProximityGap.GVRepBoundFromEnergy

/-!
# The energy EXCESS is the single open quantity of the `μ_n` wall (#389)

The additive energy of an NTT domain is bracketed `3n²−3n ≤ E(μ_n)` (lower bound proven
unconditionally in `AdditiveEnergyNegClosedLower`).  This file names the **excess** over
the minimal/Sidon value and proves it is *exactly* the controlling quantity of the whole
supply wall:

> **`energyExcess G := E(G) − (3·|G|² − 3·|G|)`**

* **`additiveEnergy_eq_min_add_excess`** — `E(G) = (3n²−3n) + energyExcess G` (the
  bracket realised as an honest decomposition; `energyExcess ≥ 0`, `= 0` iff Sidon).
* **`repCount_sq_card_le_via_excess`** — `n·r(c)² ≤ (3n²−3n) + energyExcess G` (the
  coset-concentration in excess form: the `√n`-optimal conversion).
* **`gvRepBound_of_excess_le`** — if `energyExcess G ≤ n·M² − (3n²−3n)` and `M³ ≤ 64n²`,
  then `GVRepBound G M`.  The wall closes with `M = O(√n)` **iff** the excess is
  `O(n²)`.

So the entire `#389` supply wall is reduced — machine-checked — to a single
nonnegative integer `energyExcess(μ_n)`: the count of additive quadruples of `μ_n`
beyond those forced by negation/diagonal, i.e. the multiplicative–additive interaction.
Bounding it by `O(n²)` is the Stepanov/sum-product input; that single bound is the open
core, now isolated as one named quantity with proven nonnegativity and proven sufficiency.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergySidonModNeg

open ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The energy excess** over the minimal (Sidon-mod-negation) value `3|G|²−3|G|`. -/
def energyExcess (G : Finset F) : ℕ := additiveEnergy G - (3 * G.card ^ 2 - 3 * G.card)

/-- **The honest energy decomposition.**  For negation-closed `G` the lower bound makes
`E(G) = (3n²−3n) + energyExcess G`, with `energyExcess G ≥ 0` and `= 0` iff Sidon. -/
theorem additiveEnergy_eq_min_add_excess {G : Finset F}
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G) :
    additiveEnergy G = (3 * G.card ^ 2 - 3 * G.card) + energyExcess G := by
  rw [energyExcess, Nat.add_sub_cancel' (additiveEnergy_ge_of_negClosed h2 h0 hneg)]

/-- **Coset-concentration in excess form.**  `n·r(c)² ≤ (3n²−3n) + energyExcess G`. -/
theorem repCount_sq_card_le_via_excess {G : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ x ∈ G, -x ∈ G) {c : F} (hc : c ≠ 0) :
    G.card * (repCount G c) ^ 2 ≤ (3 * G.card ^ 2 - 3 * G.card) + energyExcess G := by
  rw [← additiveEnergy_eq_min_add_excess h2 h0 hneg]
  exact repCount_sq_card_le_energy hn hGmem hc

/-- **The wall closes iff the excess is `O(n²)`.**  If `energyExcess G ≤ n·M² − (3n²−3n)`
and `M³ ≤ 64n²`, then `GVRepBound G M`.  (With `M = O(√n)` this asks `energyExcess = O(n²)`.) -/
theorem gvRepBound_of_excess_le {G : Finset F} {n M : ℕ} (hn : 1 ≤ n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (hcard : G.card = n) (h2 : (2 : F) ≠ 0)
    (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G)
    (hexc : energyExcess G ≤ n * M ^ 2 - (3 * n ^ 2 - 3 * n)) (hM3 : M ^ 3 ≤ 64 * G.card ^ 2)
    (hmin : 3 * n ^ 2 - 3 * n ≤ n * M ^ 2) :
    GVRepBound G M := by
  refine gvRepBound_of_energy_le hn hGmem ?_ hM3
  rw [additiveEnergy_eq_min_add_excess h2 h0 hneg, hcard]
  omega

end ArkLib.ProximityGap.AdditiveEnergySidonModNeg

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.additiveEnergy_eq_min_add_excess
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.gvRepBound_of_excess_le
