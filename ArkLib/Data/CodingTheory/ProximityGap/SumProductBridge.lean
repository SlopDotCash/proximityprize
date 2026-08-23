/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountCosetConcentration
import Mathlib.Algebra.Order.Chebyshev

/-!
# The sum–product bridge: `|G|⁴ ≤ |G+G|·E(G)` (#389)

The open core of the `μ_n` wall is the additive-energy excess (`EnergyExcessCore`).  This
file proves the classical **Cauchy–Schwarz sum–product inequality** linking the energy to
the sumset size, which recasts that open core as a sum–product dichotomy:

> **`card_pow_four_le_card_sumset_mul_energy`** — `|G|⁴ ≤ |G+G| · E(G)`.

Equivalently `|G+G| ≥ |G|⁴ / E(G)`.  Since `E(G) = (3n²−3n) + energyExcess`, a *small*
excess forces a *large* sumset `|G+G| ≈ n²/3` (near-maximal), and vice versa — the
sum–product dichotomy.  So "is `energyExcess = O(n²)`?" is equivalently "is the sumset of
`μ_n` near-maximal `|G+G| = Ω(n²)`?", the standard sum–product formulation of the open
Stepanov input.

Proof: `Σ_{t ∈ G+G} r(t) = |G|²` (every pair sums into `G+G`), and Cauchy–Schwarz
`(Σ r)² ≤ |G+G| · Σ r²` with `Σ r² = E(G)`.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- `Σ_{t ∈ G+G} r(t) = |G|²` — every ordered pair of `G` sums into the sumset exactly
once. -/
theorem sum_repCount_sumset_eq (G : Finset F) :
    ∑ t ∈ sumset G, repCount G t = G.card ^ 2 := by
  classical
  have hmaps : ∀ p ∈ G ×ˢ G, p.1 + p.2 ∈ sumset G := by
    intro p hp; rw [sumset, Finset.mem_image]; exact ⟨p, hp, rfl⟩
  have key : (G ×ˢ G).card = ∑ t ∈ sumset G, repCount G t := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    exact Finset.sum_congr rfl (fun t _ => fiber_card_eq_repCount G t)
  rw [← key, Finset.card_product]; ring

/-- **The sum–product bridge.**  `|G|⁴ ≤ |G+G| · E(G)`, by Cauchy–Schwarz applied to the
representation function on the sumset. -/
theorem card_pow_four_le_card_sumset_mul_energy (G : Finset F) :
    G.card ^ 4 ≤ (sumset G).card * additiveEnergy G := by
  have hcs : (∑ t ∈ sumset G, repCount G t) ^ 2
      ≤ (sumset G).card * ∑ t ∈ sumset G, (repCount G t) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [sum_repCount_sumset_eq G] at hcs
  rw [← additiveEnergy_eq_sum_sq G] at hcs
  calc G.card ^ 4 = (G.card ^ 2) ^ 2 := by ring
    _ ≤ (sumset G).card * additiveEnergy G := hcs

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.sum_repCount_sumset_eq
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.card_pow_four_le_card_sumset_mul_energy
