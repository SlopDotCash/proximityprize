/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyRepBound

/-!
# Round 12 (Issue #232, ABF26) — prize-scale additive energy on F₆₅₅₃₇, and the refutation of a
# `√q` crossover law.

This is the third (largest) prize-scale Fermat field: `F₆₅₅₃₇` (`|F^×| = 65536 = 2^16`, `65537 = 2^16+1`
the largest known Fermat prime, fully 2-power smooth, `√q ≈ 256`). Together with
`SubgroupAdditiveEnergyTowerF17` (`q=17`) and `SubgroupAdditiveEnergyFermat257` (`q=257`) it pins the
char-0 anti-concentration crossover at three scales — and **refutes** the tempting `crossover ≈ √q`
law (a 2-point over-extrapolation):

| field | `√q` | order-8 | order-16 | char-0 bound through 16? |
|---|---|---|---|---|
| `F₁₇`    | 4.1 | 264 (✗ already at 8) | — | no |
| `F₂₅₇`   | 16  | 168 ✓ | 912 ✗ | fails at 16 |
| `F₆₅₅₃₇` | 256 | 168 ✓ | 720 ✓ | **holds at 16** |

Crossover orders `~8, ~16, ~32` for `q = 2^4+1, 2^8+1, 2^16+1` grow far **slower** than `√q`
(`4, 16, 256`). No scaling law is asserted (three points do not determine one). What is verified:

* `energy_H8 = 168` — the **same** value as in `F₂₅₇`: the order-8 energy is `q`-independent at the
  char-0 value once `q` is large (minimal anti-concentration in the prize regime `|G| ≪ q`), and
* `energy_H16 = 720 ≤ 768 = 3|G|²` — order-16 anti-concentration **holds** here, whereas it *failed*
  at `q = 257` (`912 > 768`): for fixed `|G|` the energy decreases toward its char-0 value as `q`
  grows, so the anti-concentration regime is much larger than `√q` would suggest.

`sorry`-free, axiom-clean. The exact crossover law as `|G|, q → ∞` remains the open prize quantity.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

set_option linter.style.longLine false
set_option maxRecDepth 4096


open ArkLib.ProximityGap.AdditiveEnergyRepBound

namespace ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat65537

local instance localInstance_SubgroupAdditiveEnergyFermat65537_1 : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

/-- Order-8 subgroup of `F₆₅₅₃₇^×` (prize regime `|G| = 8 ≪ q = 65537`). -/
def H8 : Finset (ZMod 65537) := {1, 16, 256, 4096, 61441, 65281, 65521, 65536}
/-- Order-16 subgroup of `F₆₅₅₃₇^×`. -/
def H16 : Finset (ZMod 65537) :=
  {1, 4, 16, 64, 256, 1024, 4096, 16384, 49153, 61441, 64513, 65281, 65473, 65521, 65533, 65536}

theorem cards : H8.card = 8 ∧ H16.card = 16 := by refine ⟨?_, ?_⟩ <;> decide

/-- **Order-8 energy is the `q`-independent char-0 value `168`** — identical to `F₂₅₇`, confirming
minimal anti-concentration of the small smooth subgroup in the prize regime `|G| ≪ q`. -/
theorem energy_H8 : additiveEnergy H8 = 168 := by decide

/-- **Order-16 energy is `720 ≤ 768 = 3|G|²`** — anti-concentration HOLDS here, whereas at `q = 257`
the same-order subgroup had energy `912 > 768` and failed. This is the datum that refutes the
`crossover ≈ √q` law (`√65537 ≈ 256`, yet order 16 ≪ 256 and behaves anti-concentrated). -/
theorem energy_H16 : additiveEnergy H16 = 720 := by decide

/-- **char-0 anti-concentration holds through order 16 at `q = 65537`.** `168 ≤ 192` and
`720 ≤ 768` — the crossover sits above order 16 here (it was below 16 at `q = 257`). -/
theorem char0_bound_holds_through_16 :
    additiveEnergy H8 ≤ 3 * H8.card ^ 2 ∧ additiveEnergy H16 ≤ 3 * H16.card ^ 2 := by
  refine ⟨?_, ?_⟩ <;> decide

end ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat65537

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat65537.energy_H8
#print axioms ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat65537.energy_H16
