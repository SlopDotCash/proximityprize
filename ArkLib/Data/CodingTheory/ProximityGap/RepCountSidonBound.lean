/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountCosetConcentration
import ArkLib.Data.CodingTheory.ProximityGap.GVRepBoundFromEnergy
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergySidonModNeg

/-!
# Under the Sidon hypothesis the GV rep bound closes at `√(3n)` (#389)

Composing the coset-concentration `repCount_sq_card_le_energy` (`n·r(c)² ≤ E(G)`) with
the sibling's *sharp Sidon-modulo-negation energy* `additiveEnergy_eq_of_sidonModNeg`
(`E(G) = 3n²−3n` when `G` is Sidon-mod-negation), the additive representation count of
a root-of-unity subgroup is pinned to the optimal `√(3n)` scale:

> **`repCount_sq_lt_of_sidonModNeg`** — under `SidonModNeg G`, every `c ≠ 0` has
> `r(c)² < 3n`, i.e. `r(c) < √(3n)`.
> **`gvRepBound_of_sidonModNeg`** — hence `GVRepBound G M` whenever `3n ≤ M²` and
> `M³ ≤ 64n²` (e.g. `M = ⌈√(3n)⌉`, valid since `(3n)^{3/2} ≤ 64n²` for all `n ≥ 1`).

This is a genuine **conditional closure**: *if* `μ_n` were Sidon-modulo-negation
(minimal additive energy), the Garcia–Voloch obligation — and with it the entire supply
wall — would close with `M = O(√n)`, strictly better than the `n^{2/3}` Stepanov target.
It isolates the *sole* obstruction precisely: `μ_n` over `F_p` is **not** Sidon (its
additive energy exceeds `3n²−3n` by the multiplicative–additive interaction), and
bounding that excess is exactly the open Stepanov/sum-product kernel.  The reduction
"excess energy ↦ rep bound" is now machine-checked and `√n`-optimal.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergySidonModNeg

open ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The Sidon rep bound.**  Under `SidonModNeg G` (sharp energy `3n²−3n`), the
coset-concentration `n·r(c)² ≤ E(G)` forces `r(c)² < 3n` for every `c ≠ 0`. -/
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
