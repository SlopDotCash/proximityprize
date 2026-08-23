/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyRepBound

/-!
# THE REPRESENTATION COUNT IS μ_n-COSET-INVARIANT (#389): a new symmetry of the GV object

The additive representation count `r(c) = #{y ∈ G : c − y ∈ G}` of a multiplicative
subgroup `G = μ_n` — the Garcia–Voloch / additive-energy object that the δ* supply wall
reduces to — is **invariant under multiplication of `c` by any `ζ ∈ G`**:

> **`repCount_mul_mem_eq`** — for `ζ ∈ G`, `r(c·ζ) = r(c)`.

Proof: the dilation `y ↦ y·ζ⁻¹` bijects `{y ∈ G : c·ζ − y ∈ G}` onto `{y ∈ G : c − y ∈ G}`,
because `c − y·ζ⁻¹ = (c·ζ − y)·ζ⁻¹ ∈ G` (subgroup closure).  No Stepanov, no analysis — a
pure group-action symmetry.

**Consequence for the wall.** `r` is constant on each multiplicative coset `c·G`, of which
there are `(|F| − 1)/n`.  So the Garcia–Voloch obligation `∀ c ≠ 0, r(c) ≤ M` need only be
checked on **one representative per coset** (an `n`-fold reduction), and the additive energy
decomposes as `E(G) = Σ_{c≠0} r(c)² + r(0)² = n·Σ_{cosets} r(coset)² + |G|²` — concentrating
all of `E(G)`'s `c ≠ 0` content on `(|F|−1)/n` coset values.  This is the natural reduction
for any Stepanov/HBK attack on the bound, and it is field-uniform.

Verified: `scripts/probes/probe_repcount_coset.py` (0 violations + the energy identity at
6 instances `p = 13 … 257`).  Issue #389.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- A root-of-unity subgroup `G = {z : zⁿ = 1}` is closed under multiplication. -/
theorem mem_of_mem_mem {G : Finset F} {n : ℕ}
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) {a b : F} (ha : a ∈ G) (hb : b ∈ G) :
    a * b ∈ G := by
  rw [hGmem] at ha hb ⊢
  rw [mul_pow, ha, hb, mul_one]

/-- A root-of-unity subgroup contains the inverse of each element. -/
theorem inv_mem_of_mem {G : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) {a : F} (ha : a ∈ G) :
    a⁻¹ ∈ G := by
  have ha0 : a ≠ 0 := by
    intro h; rw [hGmem, h, zero_pow (by omega : n ≠ 0)] at ha; exact zero_ne_one ha
  rw [hGmem] at ha ⊢
  rw [inv_pow, ha, inv_one]

/-- **THE COSET-INVARIANCE OF THE REPRESENTATION COUNT**: for a root-of-unity subgroup
`G = μ_n` and any `ζ ∈ G`, the additive representation count satisfies `r(c·ζ) = r(c)`. -/
theorem repCount_mul_mem_eq {G : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (c : F) {ζ : F} (hζ : ζ ∈ G) :
    repCount G (c * ζ) = repCount G c := by
  classical
  have hζ0 : ζ ≠ 0 := by
    intro h; rw [hGmem, h, zero_pow (by omega : n ≠ 0)] at hζ; exact zero_ne_one hζ
  have hζinv : ζ⁻¹ ∈ G := inv_mem_of_mem hn hGmem hζ
  refine Finset.card_nbij' (fun y => y * ζ⁻¹) (fun y => y * ζ) ?_ ?_ ?_ ?_
  · -- forward maps into the target filter
    intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    obtain ⟨hyG, hcy⟩ := hy
    refine ⟨mem_of_mem_mem hGmem hyG hζinv, ?_⟩
    have : c - y * ζ⁻¹ = (c * ζ - y) * ζ⁻¹ := by field_simp
    rw [this]
    exact mem_of_mem_mem hGmem hcy hζinv
  · -- inverse maps into the source filter
    intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    obtain ⟨hyG, hcy⟩ := hy
    refine ⟨mem_of_mem_mem hGmem hyG hζ, ?_⟩
    have : c * ζ - y * ζ = (c - y) * ζ := by ring
    rw [this]
    exact mem_of_mem_mem hGmem hcy hζ
  · -- left inverse
    intro y _
    field_simp
  · -- right inverse
    intro y _
    field_simp

/-- **The Garcia–Voloch obligation reduces to one representative per coset.** If `r(c) ≤ M`
holds for `c` then it holds for every `c·ζ`, `ζ ∈ G` — the whole multiplicative coset. -/
theorem repCount_le_of_coset {G : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) {c : F} {M : ℕ} (hc : repCount G c ≤ M)
    {ζ : F} (hζ : ζ ∈ G) :
    repCount G (c * ζ) ≤ M := by
  rw [repCount_mul_mem_eq hn hGmem c hζ]; exact hc

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount_mul_mem_eq
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount_le_of_coset
