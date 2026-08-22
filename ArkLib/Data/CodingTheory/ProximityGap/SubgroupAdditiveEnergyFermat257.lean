/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyRepBound

/-!
# Round 12 (Issue #232, ABF26) — the PRIZE-REGIME additive energy: F₂₅₇ (Fermat smooth field) and
# the located char-0 crossover.

The `SubgroupAdditiveEnergyF17`/`…TowerF17` data lived in the `|G| ~ q` regime (`q = 17`). This file
moves into the **prize regime `|G| ≪ q`** on a genuinely prize-faithful smooth field: `F₂₅₇`, whose
multiplicative group has order `256 = 2⁸` (fully 2-power smooth — `257 = 2^{2^3}+1` is a Fermat
prime). All energies by `decide`, `sorry`-free, axiom-clean.

## The key finding: char-0 anti-concentration PERSISTS into the prize regime, with a located crossover

Exact additive energies of the `F₂₅₇^×` 2-power-subgroup tower:

| order `|G|` | `E(G)` | `3|G|²` (char-0 min) | `E/|G|²` | char-0 bound `E ≤ 3|G|²`? |
|---|---|---|---|---|
| 2  | 6   | 12  | 1.50  | ✓ |
| 4  | 36  | 48  | 2.25  | ✓ |
| 8  | 168 | 192 | 2.625 | ✓ (**below** the char-0 minimum — minimal energy / anti-concentration) |
| 16 | 912 | 768 | 3.562 | ✗ (crossover) |

So on the prize-faithful smooth field the char-0 bound `E ≤ 3|G|²` **holds through order 8 and first
fails at order 16** — the anti-concentration/concentration crossover is *located* at `|G|` between
`8` and `16` for `q = 257`.

## The `|G|`-vs-`q` dependence, made concrete

The **same** order-8 subgroup has additive energy `264` over `F₁₇` (`SubgroupAdditiveEnergyF17`,
`|G| ~ q`) but `168` over `F₂₅₇` (`|G| ≪ q`): as `q` grows into the prize regime the energy **drops
to the char-0 value `168`** (the additive energy of the complex 8-th roots of unity). The `repCount`
counterexample `repCount = 3 > 2` (`SubgroupRepCountFiniteFieldCounterexample`, over the small field
`F₁₇`) is thus a **small-`q` artifact**: in the deployed regime `|G| ≪ q` the small smooth subgroups
are minimally anti-concentrated, exactly as in characteristic 0. The open prize quantity is precisely
*where the crossover sits* as `|G|, q → ∞` — here pinned, for `q = 257`, between orders 8 and 16.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

set_option linter.style.longLine false


open ArkLib.ProximityGap.AdditiveEnergyRepBound

namespace ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat257

local instance localInstance_SubgroupAdditiveEnergyFermat257_1 : Fact (Nat.Prime 257) := ⟨by norm_num⟩

/-- Order-2 subgroup `{±1}` of `F₂₅₇^×`. -/
def H2 : Finset (ZMod 257) := {1, 256}
/-- Order-4 subgroup of `F₂₅₇^×`. -/
def H4 : Finset (ZMod 257) := {1, 16, 241, 256}
/-- Order-8 subgroup of `F₂₅₇^×` (8-th roots of unity), in the prize regime `|G| = 8 ≪ q = 257`. -/
def H8 : Finset (ZMod 257) := {1, 4, 16, 64, 193, 241, 253, 256}
/-- Order-16 subgroup of `F₂₅₇^×`. -/
def H16 : Finset (ZMod 257) :=
  {1, 2, 4, 8, 16, 32, 64, 128, 129, 193, 225, 241, 249, 253, 255, 256}

theorem cards : H2.card = 2 ∧ H4.card = 4 ∧ H8.card = 8 ∧ H16.card = 16 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **Exact additive energies up the F₂₅₇^× tower.** -/
theorem energy_H2 : additiveEnergy H2 = 6 := by decide
theorem energy_H4 : additiveEnergy H4 = 36 := by decide
theorem energy_H8 : additiveEnergy H8 = 168 := by decide
theorem energy_H16 : additiveEnergy H16 = 912 := by decide

/-- **Anti-concentration holds through order 8 in the prize regime `|G| ≪ q`.** `6 ≤ 12`, `36 ≤ 48`,
and crucially `168 ≤ 192` — the order-8 subgroup of the Fermat field `F₂₅₇` has energy **at or below**
the char-0 minimum `3|G|²`, i.e. it is minimally anti-concentrated, matching characteristic 0. -/
theorem char0_bound_holds_through_8 :
    additiveEnergy H2 ≤ 3 * H2.card ^ 2 ∧
    additiveEnergy H4 ≤ 3 * H4.card ^ 2 ∧
    additiveEnergy H8 ≤ 3 * H8.card ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **The crossover: the char-0 bound first FAILS at order 16.** `768 = 3·16² < 912 = E(H16)`. So on
`F₂₅₇` the anti-concentration/concentration crossover is located at `|G|` between 8 and 16. -/
theorem char0_bound_fails_at_16 : 3 * H16.card ^ 2 < additiveEnergy H16 := by decide

end ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat257

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat257.energy_H8
#print axioms ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat257.char0_bound_holds_through_8
#print axioms ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat257.char0_bound_fails_at_16
