/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountCosetInvariance
import ArkLib.Data.CodingTheory.ProximityGap.ThreeRootsSumZeroCharZero

/-!
# THE DIAGONAL GV COSET VANISHES (#389): char-0 Mann pins one coset of `r` to zero

The Garcia–Voloch object `r(c) = #{y ∈ μ_n : c − y ∈ μ_n}` over `ℂ` vanishes on the entire
**diagonal coset** `c ∈ μ_n`, for `n` even with `3 ∤ n` (the NTT case `n = 2^k`):

> **`repCount_eq_zero_of_mem`** — for `n` even, `3 ∤ n`, and `c ∈ μ_n`, `r(c) = 0`.

This is the first **exact value** of the GV object on a full coset, obtained by composing the
sibling's char-0 Mann rigidity (`no_three_roots_sum_zero`: no three `n`-th roots of unity sum
to zero when `3 ∤ n`) with the elementary observation that a representation `c = y + (c−y)`
with `y, c−y ∈ μ_n` makes `{y, c−y, −c}` a vanishing sum of three `n`-th roots
(`(−c)^n = 1` since `n` even and `c ∈ μ_n`).  By my `repCount_mul_mem_eq` the value is then
zero on the whole multiplicative coset `c·μ_n = μ_n`.

So over `ℂ` the diagonal coset contributes **nothing** to the additive energy, and the GV
hardness is confined to the *off-diagonal* cosets `c^n ≠ 1` and to the characteristic-`p`
surplus — sharpening exactly which cosets carry the open core.  Issue #389.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

open ProximityGap.ThreeRoots

/-- **THE DIAGONAL COSET VANISHES**: over `ℂ`, for `n` even with `3 ∤ n` and `c ∈ μ_n`, the
additive representation count `r(c) = 0` — no element of `μ_n` is a sum of two elements of
`μ_n` on the diagonal coset. -/
theorem repCount_eq_zero_of_mem {G : Finset ℂ} {n : ℕ} (hn : n ≠ 0) (heven : Even n)
    (h3 : ¬ (3 ∣ n)) (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) {c : ℂ} (hc : c ∈ G) :
    repCount G c = 0 := by
  classical
  rw [repCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro y hy hcy
  -- `y, c − y, −c` are three `n`-th roots of unity summing to zero
  have hyn : y ^ n = 1 := (hGmem y).mp hy
  have hcyn : (c - y) ^ n = 1 := (hGmem (c - y)).mp hcy
  have hcn : c ^ n = 1 := (hGmem c).mp hc
  have hnegcn : (-c) ^ n = 1 := by
    rw [heven.neg_pow, hcn]
  exact no_three_roots_sum_zero hn h3 hyn hcyn hnegcn (by ring)

/-- The diagonal vanishing holds on the **whole** multiplicative coset `c·μ_n` (here `= μ_n`),
by coset-invariance — consistent restatement. -/
theorem repCount_eq_zero_of_mem_coset {G : Finset ℂ} {n : ℕ} (hn : n ≠ 0) (hn1 : 1 ≤ n)
    (heven : Even n) (h3 : ¬ (3 ∣ n)) (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1)
    {c ζ : ℂ} (hc : c ∈ G) (hζ : ζ ∈ G) :
    repCount G (c * ζ) = 0 := by
  rw [repCount_mul_mem_eq hn1 hGmem c hζ]
  exact repCount_eq_zero_of_mem hn heven h3 hGmem hc

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount_eq_zero_of_mem
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount_eq_zero_of_mem_coset
