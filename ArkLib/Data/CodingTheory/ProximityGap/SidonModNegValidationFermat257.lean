/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergySidonModNeg
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupAdditiveEnergyFermat257

/-!
# Round 12 (Issue #232, ABF26) — end-to-end validation: `SidonModNeg` on the F₂₅₇ prize instance.

`AdditiveEnergySidonModNeg.additiveEnergy_eq_of_sidonModNeg` proves `E(G) = 3|G|² − 3|G|` for any
Sidon-modulo-negation set. This closes the loop on the prize-faithful Fermat field `F₂₅₇`
(`|F^×| = 256 = 2⁸`), reusing the `decide`-verified energies of `SubgroupAdditiveEnergyFermat257`:

* `sidonModNeg_H4` — the order-4 subgroup **is** Sidon-modulo-negation (decided);
* `energy_H4_via_theorem` — hence `E(H4) = 36` follows **from the general theorem**, not just a direct
  `decide` — end-to-end validation of the structural result on a concrete subgroup;
* `not_sidonModNeg_H16` — the order-16 subgroup is **not** Sidon-modulo-negation, derived from the
  theorem: were it, `E(H16) = 3·16² − 3·16 = 720`, but `E(H16) = 912` (decided), contradiction.

So the `SidonModNeg` threshold on `F₂₅₇` is located strictly between order 4 and order 16 (matching the
energy crossover), and the general sharp-energy theorem is consistent with every concrete computation.
`sorry`-free, axiom-clean.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

set_option linter.style.longLine false
set_option maxRecDepth 10000


open ArkLib.ProximityGap.AdditiveEnergyRepBound ArkLib.ProximityGap.AdditiveEnergySidonModNeg
open ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat257

namespace ArkLib.ProximityGap.SidonModNegValidationFermat257

local instance localInstance_SidonModNegValidationFermat257_1 : Fact (Nat.Prime 257) := ⟨by norm_num⟩

/-- **The order-4 subgroup of `F₂₅₇` is Sidon-modulo-negation** (decided over `4⁴` quadruples). -/
theorem sidonModNeg_H4 : SidonModNeg H4 := by
  intro a ha b hb c hc d hd
  fin_cases ha <;> fin_cases hb <;> fin_cases hc <;> fin_cases hd <;> decide

/-- **`E(H4) = 36` follows from the GENERAL sharp-energy theorem** (via `sidonModNeg_H4`), validating
`additiveEnergy_eq_of_sidonModNeg` end-to-end against the direct `decide` value. -/
theorem energy_H4_via_theorem : additiveEnergy H4 = 36 := by
  rw [additiveEnergy_eq_of_sidonModNeg (by decide) (by decide) (by decide) sidonModNeg_H4]
  norm_num [cards.2.1]

/-- **The order-16 subgroup of `F₂₅₇` is NOT Sidon-modulo-negation.** If it were, the sharp-energy
theorem would force `E(H16) = 3·16² − 3·16 = 720`; but `E(H16) = 912` (decided), a contradiction. -/
theorem not_sidonModNeg_H16 : ¬ SidonModNeg H16 := by
  intro hS
  have h := additiveEnergy_eq_of_sidonModNeg (G := H16) (by decide) (by decide) (by decide) hS
  rw [energy_H16, cards.2.2.2] at h
  norm_num at h

end ArkLib.ProximityGap.SidonModNegValidationFermat257

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SidonModNegValidationFermat257.sidonModNeg_H4
#print axioms ArkLib.ProximityGap.SidonModNegValidationFermat257.energy_H4_via_theorem
#print axioms ArkLib.ProximityGap.SidonModNegValidationFermat257.not_sidonModNeg_H16
