/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupAdditiveEnergyFermat257

/-!
# The char-0 energy-bound crossover for 2-power subgroups of `F_257` (#389)

`F_257 = F_{2^8+1}` (the Fermat prime) hosts the full 2-power subgroup tower
`μ_2 ⊂ μ_4 ⊂ μ_8 ⊂ μ_16 ⊂ …`.  The char-0 additive-energy bound `E(G) ≤ 3·|G|²` (the
roots-of-unity Sidon-mod-neg value `3|G|² − 3|G|`, rounded up) holds for `μ_2, μ_4, μ_8` but
**fails** at `μ_16`.  This file names that crossover as a single theorem: `μ_8` is the last 2-power
order on which the char-0 bound survives over `F_257`, and `μ_8` sits exactly at the Sidon-mod-neg
value `E(μ_8) = 168 = 3·8² − 3·8`.  Pure repackaging of the three in-tree facts
`energy_H8`, `char0_bound_holds_through_8`, `char0_bound_fails_at_16`; axiom-clean.
-/

open ArkLib.ProximityGap.AdditiveEnergyRepBound

namespace ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat257

instance primeFact_Fermat257EnergyCrossover_1 : Fact (Nat.Prime 257) := ⟨by norm_num⟩

/-- **The char-0 energy-bound crossover at `μ_8 ⊂ F_257`.**  `μ_8` realizes the Sidon-mod-neg
energy `E = 3·8² − 3·8 = 168` and satisfies the char-0 bound `E ≤ 3·|μ_8|²`, while the next
2-power order `μ_16` violates it (`3·|μ_16|² < E(μ_16)`).  So `μ_8` is the largest 2-power subgroup
of `F_257` on which the char-0 additive-energy bound holds. -/
theorem orderEight_energy_band_F257_boundary :
    additiveEnergy H8 = 3 * 8 ^ 2 - 3 * 8 ∧
    additiveEnergy H8 ≤ 3 * H8.card ^ 2 ∧
    3 * H16.card ^ 2 < additiveEnergy H16 :=
  ⟨energy_H8.trans (by norm_num), char0_bound_holds_through_8.2.2, char0_bound_fails_at_16⟩

end ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat257
