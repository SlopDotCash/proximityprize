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
the sumset size — a **one-way** implication from small energy to large sumset:

> **`card_pow_four_le_card_sumset_mul_energy`** — `|G|⁴ ≤ |G+G| · E(G)`.

Equivalently `|G+G| ≥ |G|⁴ / E(G)`.  Since `E(G) = (3n²−3n) + energyExcess`, a *small*
excess forces a *large* sumset (`energyExcess = O(n²)` gives `|G+G| = Ω(n²)`, roughly
`|G+G| ≳ n²/3` when the excess is negligible).  The converse does **not** follow from this
inequality: a product lower bound gives no upper bound on `E(G)` from a lower bound on
`|G+G|`.  For general sets it is false — the disjoint union of an arithmetic progression of size
`m` with `m` well-separated powers of `3` (in a prime field large enough to avoid wraparound) has
`|G| = 2m`, `|G+G| = Ω(m²)` and `E(G) ≥ E(AP) = Θ(m³)`.  So "small energy excess" and
"near-maximal sumset" are **not** shown equivalent here; for multiplicative subgroups `μ_n` any
such converse would need a separate structural (inverse) theorem, and the energy bound remains a
separate open input (the Stepanov-type input).

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
