/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountFrobeniusBound
import ArkLib.Data.CodingTheory.ProximityGap.GVHBKEnergyReduction

/-!
# UNCONDITIONAL, RESIDUAL-FREE wall closure for the `n ∣ p+1` family (#389)

The supply wall reduces (machine-checked) to `GVRepBound G M`, defined as
`(∀ t ≠ 0, r(t) ≤ M) ∧ M³ ≤ 64·n²`.  In the **Frobenius regime `n ∣ p+1`** the sibling
result `repCount_le_two_of_dvd_succ` proves `r(t) ≤ 2` *unconditionally* (Frobenius acts
as inversion on `μ_n ⊂ F_{p²}`, the finite-field unit-circle bound).  Since `2³ = 8 ≤ 64·n²`
for every `n ≥ 1`, this yields `GVRepBound G 2` directly — no energy bound, no Stepanov,
no residual:

> **`gvRepBound_of_dvd_succ`** — over a field of characteristic `p` containing `μ_n`, if
> `n ∣ p+1` then `GVRepBound (μ_n) 2`.

So for the **entire infinite family `n ∣ p+1` (all primes `p`)** the proximity-gap supply
wall closes with `M = 2` — a complete end-to-end, residual-free closure.  This is the exact
complement of the deployed split regime `n ∣ p−1` (Frobenius trivial on `μ_n ⊂ F_p`), where
the surplus `Θ(n⁴/p)` is the genuine Stepanov wall.  The GV difficulty is thereby pinned to
*precisely* the `n ∣ p−1` case.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F] {p : ℕ} [Fact p.Prime] [CharP F p]

/-- **Residual-free Garcia–Voloch bound for `n ∣ p+1`.**  `r(t) ≤ 2` (Frobenius regime)
upgrades directly to `GVRepBound (μ_n) 2`, since `2³ = 8 ≤ 64·n²` for `n ≥ 1`.  The whole
supply wall closes unconditionally on this infinite family. -/
theorem gvRepBound_of_dvd_succ {G : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (ndvd : n ∣ p + 1) (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) :
    GVRepBound G 2 := by
  have h1 : (1 : F) ∈ G := (hGmem 1).mpr (one_pow n)
  have hcard : 1 ≤ G.card := Finset.card_pos.mpr ⟨1, h1⟩
  refine ⟨fun t ht => repCount_le_two_of_dvd_succ hn ndvd hGmem ht, ?_⟩
  have hsq : 1 ≤ G.card ^ 2 := Nat.one_le_pow _ _ hcard
  calc (2 : ℕ) ^ 3 = 8 := by norm_num
    _ ≤ 64 * 1 := by norm_num
    _ ≤ 64 * G.card ^ 2 := Nat.mul_le_mul_left _ hsq

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.gvRepBound_of_dvd_succ
