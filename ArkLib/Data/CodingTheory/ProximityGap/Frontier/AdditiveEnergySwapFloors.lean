/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.REnergyTwoEqAdditiveEnergy

/-!
# Universal floors on the representation-count additive energy (#444, #389)

Via the bridge `rEnergy G 2 = additiveEnergy G` (`REnergyTwoEqAdditiveEnergy`), the two universal
hypothesis-free floors on the `r = 2` Gauss-sum moment transfer verbatim to the
representation-count additive energy `AdditiveEnergyRepBound.additiveEnergy` (the object the GV /
list-decoding rep-count bounds consume):

> **`additiveEnergy_ge_card_sq`.**  `|G|² ≤ additiveEnergy G`   (the diagonal floor).
> **`additiveEnergy_ge_swap_floor`.**  `2|G|² − |G| ≤ additiveEnergy G`   (the swap floor).
> **`additiveEnergy_affine_ge_card_sq`.**  The diagonal floor for `u + tG`, written in `|G|`.
> **`additiveEnergy_affine_ge_swap_floor`.**  The swap floor for `u + tG`, written in `|G|`.

Both are char-free and need no hypothesis on `G`.  The swap floor is the **plain Sidon minimum**
(attained iff `IsSidonSet G`, `additiveEnergy_eq_swap_floor_iff_sidon`); the diagonal floor is the
weaker companion beneath it.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  No CORE closure, no char-p transfer, no
capacity / beyond-Johnson / growth-law claim.  Issues #444, #389.
-/

open Finset

namespace ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open ArkLib.ProximityGap.AdditiveEnergyRepBound (additiveEnergy)

/-- **Diagonal floor on the representation-count additive energy.**  `|G|² ≤ additiveEnergy G`.
Transferred from `REnergyDiagonalFloor.rEnergy_ge_card_pow` (`r = 2`) via the bridge. -/
theorem additiveEnergy_ge_card_sq (G : Finset F) :
    G.card ^ 2 ≤ additiveEnergy G := by
  rw [← rEnergy_two_eq_additiveEnergy]
  exact rEnergy_ge_card_pow G 2

/-- **Swap floor on the representation-count additive energy.**  `2|G|² − |G| ≤ additiveEnergy G`.
Transferred from `REnergySwapFloor.rEnergy_ge_swap_floor` (`r = m + 2`, `m = 0`) via the bridge.
This is the **plain Sidon minimum** (`= ` iff `IsSidonSet G`). -/
theorem additiveEnergy_ge_swap_floor (G : Finset F) :
    2 * G.card ^ 2 - G.card ≤ additiveEnergy G := by
  rw [← rEnergy_two_eq_additiveEnergy]
  simpa using rEnergy_ge_swap_floor G 0

/-- **Affine-normalized diagonal floor.**  A nonzero affine image `u + tG` obeys the same
representation-count additive-energy diagonal floor, with the floor expressed using the original
cardinality `|G|` (cardinality is preserved by the embedding). -/
theorem additiveEnergy_affine_ge_card_sq (G : Finset F) (u : F) {t : F} (ht : t ≠ 0) :
    G.card ^ 2 ≤ additiveEnergy (G.map (affineEmbeddingOfNe u t ht)) := by
  have hcard : (G.map (affineEmbeddingOfNe u t ht)).card = G.card := by
    simp
  rw [← hcard]
  exact additiveEnergy_ge_card_sq (G.map (affineEmbeddingOfNe u t ht))

/-- **Affine-normalized swap floor.**  A nonzero affine image `u + tG` obeys the same
representation-count additive-energy swap floor, with the floor expressed using the original
cardinality `|G|` (cardinality is preserved by the embedding). -/
theorem additiveEnergy_affine_ge_swap_floor (G : Finset F) (u : F) {t : F} (ht : t ≠ 0) :
    2 * G.card ^ 2 - G.card ≤ additiveEnergy (G.map (affineEmbeddingOfNe u t ht)) := by
  have hcard : (G.map (affineEmbeddingOfNe u t ht)).card = G.card := by
    simp
  rw [← hcard]
  exact additiveEnergy_ge_swap_floor (G.map (affineEmbeddingOfNe u t ht))

end ArkLib.ProximityGap.SubgroupGaussSumMoment

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only (no sorryAx).
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.additiveEnergy_ge_card_sq
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.additiveEnergy_ge_swap_floor
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.additiveEnergy_affine_ge_card_sq
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.additiveEnergy_affine_ge_swap_floor
