/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountCosetConcentration
import ArkLib.Data.CodingTheory.ProximityGap.GVHBKEnergyReduction

/-!
# A quadratic energy bound is the SOLE open input to the GV rep bound (#389)

Combining the coset-concentration `repCount_sq_card_le_energy` (`n·r(c)² ≤ E(G)`) with
the [GV88]/[HBK00] `GVRepBound` interface, this file proves that the Garcia–Voloch
representation bound — the assumed Stepanov input of the whole supply chain — follows
*unconditionally* from a single **quadratic additive-energy bound**:

> **`gvRepBound_of_energy_le`** — if `E(G) ≤ |G|·M²` and `M³ ≤ 64·|G|²`, then
> `GVRepBound G M` (i.e. `∀ c ≠ 0, r(c) ≤ M`).

Proof: `|G|·r(c)² ≤ E(G) ≤ |G|·M² ⟹ r(c)² ≤ M² ⟹ r(c) ≤ M`, pointwise, from the
coset-concentration alone.

This crisply isolates the open core of the entire `μ_n` supply wall to **one energy
estimate**: `E(μ_n) ≤ 16·n^{7/3}` (the integer-clean form of the [GV]/[HBK] bound,
since `M ≤ 4n^{2/3}` makes `n·M² ≤ 16·n^{7/3}`).  Everything else — coset-invariance,
coset-concentration, the `GVRepBound ⟹ E ≲ |G|^{8/3}` reduction, the supply→single-word
collapse, the cyclic symmetry — is machine-checked.  The remaining obligation is the
unconditional sub-`n³` energy bound for the multiplicative subgroup (Stepanov/sum-product),
which has no elementary proof and stays the named open input.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- **A quadratic energy bound yields the Garcia–Voloch rep bound.**  If
`E(G) ≤ |G|·M²` and `M³ ≤ 64·|G|²`, then every nonzero `t` has at most `M` additive
representations — the `GVRepBound` consumed by the supply chain — proved pointwise from
the coset-concentration `n·r(t)² ≤ E(G)`. -/
theorem gvRepBound_of_energy_le {G : Finset F} {n M : ℕ} (hn : 1 ≤ n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1)
    (hE : additiveEnergy G ≤ G.card * M ^ 2) (hM : M ^ 3 ≤ 64 * G.card ^ 2) :
    GVRepBound G M := by
  refine ⟨fun t ht => ?_, hM⟩
  have hcardpos : 0 < G.card :=
    Finset.card_pos.mpr ⟨1, by rw [hGmem]; exact one_pow n⟩
  -- |G|·r(t)² ≤ E(G) ≤ |G|·M²  ⟹  r(t)² ≤ M²  ⟹  r(t) ≤ M
  have h1 : G.card * (repCount G t) ^ 2 ≤ additiveEnergy G :=
    repCount_sq_card_le_energy hn hGmem ht
  have h2 : G.card * (repCount G t) ^ 2 ≤ G.card * M ^ 2 := le_trans h1 hE
  have h3 : (repCount G t) ^ 2 ≤ M ^ 2 := Nat.le_of_mul_le_mul_left h2 hcardpos
  by_contra hlt
  push_neg at hlt
  have : M ^ 2 < (repCount G t) ^ 2 := by nlinarith
  omega

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.gvRepBound_of_energy_le
