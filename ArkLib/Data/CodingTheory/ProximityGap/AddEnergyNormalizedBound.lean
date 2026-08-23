/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AddEnergyMulHomogeneous

/-!
# The normalized-count API: `N ≤ |G|²`, and the exact open sum-product gap (#357)

`AddEnergyMulHomogeneous` reduced the additive energy to the normalized count
`E(G) = |G| · N`, `N = #{(z₁,z₂,z₃)∈G³ : z₁+z₂ = z₃+1}`. This file brackets `N` from above by the
trivial bound and records the precise open gap:

* `normalizedEnergyCount_le_sq` : `N ≤ |G|²` (for each `(z₁,z₂)`, `z₃ = z₁+z₂−1` is forced).
* `addEnergy_le_cube_via_homogeneity` : `E(G) ≤ |G|³`, re-derived *through* the homogeneity
  identity `E(G) = |G|·N` and `N ≤ |G|²` — a consistency check matching the direct
  `addEnergy_le_cube`.

**The exact open gap, formally framed:** the elementary bound is `N ≤ |G|²`, giving `E(G) ≤ |G|³`.
The deployed prize needs the **sum-product** improvement `N ≪ |G|^{3/2}` (equivalently
`E(G) ≪ |G|^{5/2}`, Heath-Brown–Konyagin/Shkredov) — a beyond-elementary incidence/Stepanov estimate
for the multiplicative subgroup, which is the hard open input (dossier §24) and is not yet available
in formalizable form. This file makes the gap between "what is elementary" (`|G|²`) and "what the
prize needs" (`|G|^{3/2}`) an explicit, machine-checked boundary.

**Honest scope:** elementary counting; does not bound `N` sub-quadratically, hence does not pin `δ*`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Trivial bound on the normalized count: `N ≤ |G|²`.** For each `(z₁,z₂)` the constraint
`z₁+z₂ = z₃+1` forces `z₃ = z₁+z₂−1` uniquely, so the inner count over `z₃` is `≤ 1`. -/
theorem normalizedEnergyCount_le_sq (G : Finset F) :
    normalizedEnergyCount G ≤ G.card ^ 2 := by
  rw [normalizedEnergyCount]
  have hsq : G.card ^ 2 = ∑ _z₁ ∈ G, ∑ _z₂ ∈ G, (1 : ℕ) := by
    simp [Finset.sum_const, smul_eq_mul]; ring
  rw [hsq]
  refine Finset.sum_le_sum (fun z₁ _ => ?_)
  refine Finset.sum_le_sum (fun z₂ _ => ?_)
  -- `∑_{z₃∈G} [z₁+z₂ = z₃+1] ≤ 1`, since `z₃ = z₁+z₂−1` is forced.
  have heq : (∑ z₃ ∈ G, (if z₁ + z₂ = z₃ + 1 then (1 : ℕ) else 0))
      = ∑ z₃ ∈ G, (if z₁ + z₂ - 1 = z₃ then (1 : ℕ) else 0) := by
    refine Finset.sum_congr rfl (fun z₃ _ => ?_)
    congr 1
    rw [eq_iff_iff, sub_eq_iff_eq_add]
  rw [heq, Finset.sum_ite_eq]
  split_ifs <;> simp

/-- **`E(G) ≤ |G|³` re-derived through the homogeneity reduction.** Composing
`E(G) = |G|·N` (`addEnergy_eq_card_mul_normalizedCount`) with `N ≤ |G|²` recovers the cube ceiling,
confirming consistency with the direct `addEnergy_le_cube`. -/
theorem addEnergy_le_cube_via_homogeneity (G : Finset F)
    (hmul : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ G) (hinv : ∀ a ∈ G, a⁻¹ ∈ G) (h0 : (0 : F) ∉ G) :
    addEnergy G ≤ G.card ^ 3 := by
  rw [addEnergy_eq_card_mul_normalizedCount G hmul hinv h0]
  calc G.card * normalizedEnergyCount G
      ≤ G.card * G.card ^ 2 := Nat.mul_le_mul_left _ (normalizedEnergyCount_le_sq G)
    _ = G.card ^ 3 := by ring

end ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.normalizedEnergyCount_le_sq
#print axioms ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.addEnergy_le_cube_via_homogeneity
