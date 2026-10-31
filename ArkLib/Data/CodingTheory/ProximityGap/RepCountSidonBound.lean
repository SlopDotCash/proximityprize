/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountCosetConcentration
import ArkLib.Data.CodingTheory.ProximityGap.GVRepBoundFromEnergy
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergySidonModNeg

/-!
# Under the Sidon hypothesis: a coarse energy-only GV rep bound `√(3n)` (#389)

Composing the coset-concentration `repCount_sq_card_le_energy` (`n·r(c)² ≤ E(G)`) with
the sibling's *sharp Sidon-modulo-negation energy* `additiveEnergy_eq_of_sidonModNeg`
(`E(G) = 3n²−3n` when `G` is Sidon-mod-negation), the additive representation count of
a root-of-unity subgroup is bounded by `√(3n)`.  This is a **deliberately coarse, energy-only**
estimate, NOT the sharp conditional bound: Sidon modulo negation directly forces every nonzero
sum `c` to have at most one unordered representing pair, hence `r(c) ≤ 2`
(`SidonGVClosure.repCount_le_two_of_sidonModNeg`; conversely `r(c) ≤ 2` for all `c ≠ 0` implies
Sidon modulo negation, `SidonRepCountCharacterization.sidonModNeg_iff_repCount_le_two`).
The energy route only gives:

> **`repCount_sq_lt_of_sidonModNeg`** — under `SidonModNeg G`, every `c ≠ 0` has
> `r(c)² < 3n`, i.e. `r(c) < √(3n)`.
> **`gvRepBound_of_sidonModNeg`** — hence `GVRepBound G M` whenever `3n ≤ M²` and
> `M³ ≤ 64n²` (e.g. `M = ⌈√(3n)⌉`, valid since `(3n)^{3/2} ≤ 64n²` for all `n ≥ 1`).

This is a **conditional** statement: *if* `G` is Sidon-modulo-negation (minimal additive
energy), the Garcia–Voloch obligation `GVRepBound` holds with `M = O(√n)` by this energy
route — and in fact with the constant `M = 2` by the direct Sidon argument above.  Whether
`μ_n ⊆ F_p` is Sidon modulo negation depends on the prime regime: for even `n` and
`p > 4^{φ(n)}` it IS, unconditionally (`SidonLiftDevacuated.sidonModNeg_rootsOfUnity`; for
`n = 2^m` this is `p > 2^n`, `SidonSubgroupClosed.sidonModNeg_mu_n`), giving
`GVRepBound μ_n 2` (`SidonGVClosure.gvRepBound_rootsOfUnity_two`).  For smaller primes, e.g. the
deployed regime with `p` polynomial in `n`, it can fail — e.g. `μ_16 ⊆ F₂₅₇` has energy
`912 > 720 = 3·16² − 3·16` (`SubgroupAdditiveEnergyFermat257.energy_H16`) — and bounding that
excess energy is the open Stepanov/sum-product kernel.  The machine-checked content here is the
coarse reduction "energy `3n²−3n` ↦ `r(c)² < 3n`"; it is not `√n`-optimal (the sharp value is `2`).

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergySidonModNeg

open ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The coarse energy-only Sidon rep bound.**  Under `SidonModNeg G` (sharp energy `3n²−3n`),
the coset-concentration `n·r(c)² ≤ E(G)` forces `r(c)² < 3n` for every `c ≠ 0`.  Weaker than the
direct consequence `r(c) ≤ 2` (`SidonGVClosure.repCount_le_two_of_sidonModNeg`). -/
theorem repCount_sq_lt_of_sidonModNeg {G : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (hcard : G.card = n) (h2 : (2 : F) ≠ 0)
    (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G) (hS : SidonModNeg G)
    {c : F} (hc : c ≠ 0) :
    (repCount G c) ^ 2 < 3 * n := by
  have hnpos : 0 < n := hn
  have hE : additiveEnergy G = 3 * G.card ^ 2 - 3 * G.card :=
    additiveEnergy_eq_of_sidonModNeg h2 h0 hneg hS
  have hsq : G.card * (repCount G c) ^ 2 ≤ additiveEnergy G :=
    repCount_sq_card_le_energy hn hGmem hc
  rw [hE, hcard] at hsq
  -- n · r² ≤ 3n² − 3n < 3n² = n·(3n)
  have hprod : n * (3 * n) = 3 * n ^ 2 := by ring
  have hlt : n * (repCount G c) ^ 2 < n * (3 * n) := by
    rw [hprod]
    exact lt_of_le_of_lt hsq (Nat.sub_lt (by positivity) (by positivity))
  exact Nat.lt_of_mul_lt_mul_left hlt

/-- **Conditional GV closure under the Sidon hypothesis.**  If `G` is Sidon-mod-negation
and `M` satisfies `3n ≤ M²` and `M³ ≤ 64n²`, then `GVRepBound G M` — the rep bound the
whole supply chain consumes, with `M = O(√n)`. -/
theorem gvRepBound_of_sidonModNeg {G : Finset F} {n M : ℕ} (hn : 1 ≤ n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (hcard : G.card = n) (h2 : (2 : F) ≠ 0)
    (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G) (hS : SidonModNeg G)
    (hM : 3 * n ≤ M ^ 2) (hM3 : M ^ 3 ≤ 64 * G.card ^ 2) :
    GVRepBound G M := by
  refine ⟨fun t ht => ?_, hM3⟩
  have hsq : (repCount G t) ^ 2 < 3 * n :=
    repCount_sq_lt_of_sidonModNeg hn hGmem hcard h2 h0 hneg hS ht
  have hsq2 : (repCount G t) ^ 2 < M ^ 2 := lt_of_lt_of_le hsq hM
  by_contra hcon
  push_neg at hcon
  exact absurd hsq2 (not_lt.mpr (Nat.pow_le_pow_left (le_of_lt hcon) 2))

end ArkLib.ProximityGap.AdditiveEnergySidonModNeg

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.repCount_sq_lt_of_sidonModNeg
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.gvRepBound_of_sidonModNeg
