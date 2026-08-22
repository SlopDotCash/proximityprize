/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyRepBound

/-!
# Round 11 (Issue #232, ABF26) — the additive-energy TOWER of `F₁₇`: `E(G)/|G|²` crosses the
# char-0 minimum as the subgroup grows.

`SubgroupAdditiveEnergyF17` computed `E(G) = 264` for the order-8 subgroup. This file computes the
**exact additive energy of every subgroup in the `F₁₇^×` 2-power tower** (orders `2,4,8,16`) and
isolates the **crossover**: the char-0 minimal-energy bound `E(G) ≤ 3|G|²` (true for complex roots of
unity) **holds for the small subgroups and fails for the large ones**, with the crossover between
order 4 and order 8:

| order `|G|` | `E(G)` | `3|G|²` | `E(G)/|G|²` | char-0 bound `E ≤ 3|G|²`? |
|---|---|---|---|---|
| 2  | 6    | 12  | 1.50  | ✓ holds |
| 4  | 36   | 48  | 2.25  | ✓ holds |
| 8  | 264  | 192 | 4.125 | ✗ fails |
| 16 | 3856 | 768 | 15.06 | ✗ fails (`= F₁₇^×`, energy `≈ |G|³/p`) |

The ratio `E(G)/|G|²` is monotone increasing up the tower — concrete evidence that the finite-field
additive energy of a multiplicative subgroup grows (toward concentration) as `|G|` approaches `q`,
exactly the `|G|`-vs-`q` dependence the prize question turns on. All `decide`, `sorry`-free,
axiom-clean.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

open ArkLib.ProximityGap.AdditiveEnergyRepBound

namespace ArkLib.ProximityGap.SubgroupAdditiveEnergyTowerF17

local instance localInstance_SubgroupAdditiveEnergyTowerF17_1 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- Order-2 subgroup `⟨16⟩ = {±1}`. -/
def G2 : Finset (ZMod 17) := {1, 16}
/-- Order-4 subgroup (4-th roots of unity). -/
def G4 : Finset (ZMod 17) := {1, 4, 13, 16}
/-- Order-8 subgroup (8-th roots of unity). -/
def G8 : Finset (ZMod 17) := {1, 2, 4, 8, 9, 13, 15, 16}
/-- Order-16 subgroup `= F₁₇^×` (all nonzero elements). -/
def G16 : Finset (ZMod 17) := {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}

theorem cards : G2.card = 2 ∧ G4.card = 4 ∧ G8.card = 8 ∧ G16.card = 16 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **Exact additive energies up the `F₁₇^×` 2-power tower.** -/
theorem energy_G2 : additiveEnergy G2 = 6 := by decide
theorem energy_G4 : additiveEnergy G4 = 36 := by decide
theorem energy_G8 : additiveEnergy G8 = 264 := by decide
theorem energy_G16 : additiveEnergy G16 = 3856 := by decide

/-- **The char-0 minimal-energy bound `E ≤ 3|G|²` HOLDS for the small subgroups** (orders 2, 4):
`6 ≤ 12` and `36 ≤ 48`. -/
theorem char0_bound_holds_small :
    additiveEnergy G2 ≤ 3 * G2.card ^ 2 ∧ additiveEnergy G4 ≤ 3 * G4.card ^ 2 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **The char-0 minimal-energy bound `E ≤ 3|G|²` FAILS for the large subgroups** (orders 8, 16):
`264 > 192` and `3856 > 768`. The finite-field additive energy strictly exceeds the
roots-of-unity (char-0) minimum once the subgroup is large enough — the loss of anti-concentration. -/
theorem char0_bound_fails_large :
    3 * G8.card ^ 2 < additiveEnergy G8 ∧ 3 * G16.card ^ 2 < additiveEnergy G16 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **The crossover is monotone:** the normalized energy `E(G)·(other |G|²)` comparisons show
`E(G)/|G|²` strictly increasing across the tower `2 < 4 < 8 < 16`. Stated cross-multiplied to stay in
`ℕ`: `E(G_a)·|G_b|² < E(G_b)·|G_a|²` for consecutive `a < b`. -/
theorem energy_ratio_strictly_increasing :
    additiveEnergy G2 * G4.card ^ 2 < additiveEnergy G4 * G2.card ^ 2 ∧
    additiveEnergy G4 * G8.card ^ 2 < additiveEnergy G8 * G4.card ^ 2 ∧
    additiveEnergy G8 * G16.card ^ 2 < additiveEnergy G16 * G8.card ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end ArkLib.ProximityGap.SubgroupAdditiveEnergyTowerF17

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupAdditiveEnergyTowerF17.energy_G16
#print axioms ArkLib.ProximityGap.SubgroupAdditiveEnergyTowerF17.char0_bound_fails_large
#print axioms ArkLib.ProximityGap.SubgroupAdditiveEnergyTowerF17.energy_ratio_strictly_increasing
