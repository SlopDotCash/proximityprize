/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountCosetInvariance

/-!
# THE SHIFTED-POWER FORM OF THE REPRESENTATION COUNT (#389)

The additive representation count `r(c) = #{y ∈ G : c − y ∈ G}` of a root-of-unity
subgroup `G = μ_n` equals the **shifted-power count**:

> **`repCount_eq_shiftedPower`** — for `c ≠ 0`,
> `r(c) = #{w ∈ G : (1 + w)^n = c^n}`.

Proof: the Möbius-type bijection `y ↦ (c − y)·y⁻¹` sends `{y ∈ G : c − y ∈ G}` onto
`{w ∈ G : (1 + w)^n = c^n}` (inverse `w ↦ c·(1 + w)⁻¹`), since `1 + (c−y)y⁻¹ = c·y⁻¹`
whose `n`-th power is `c^n`.

This is the symmetric **"two pure `n`-th-power conditions"** normalization Stepanov/HBK
treatments use: `w ∈ μ_n` and `1 + w ∈ c·μ_n` (the right side depends only on `c^n`,
re-deriving the coset-invariance `repCount_mul_mem_eq` from the other direction).  As a
polynomial identity it reads `deg gcd(Xⁿ−1, (c−X)ⁿ−1) = deg gcd(Xⁿ−1, (1+X)ⁿ − cⁿ)` — a
free change of the Garcia–Voloch resultant into translate-of-a-pure-power form.  Issue #389.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- An element of a root-of-unity subgroup is nonzero. -/
theorem ne_zero_of_mem {G : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) {a : F} (ha : a ∈ G) : a ≠ 0 := by
  intro h; rw [hGmem, h, zero_pow (by omega : n ≠ 0)] at ha; exact zero_ne_one ha

/-- **THE SHIFTED-POWER FORM**: `r(c) = #{w ∈ G : (1+w)^n = c^n}` for `c ≠ 0`. -/
theorem repCount_eq_shiftedPower {G : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) {c : F} (hc : c ≠ 0) :
    repCount G c = (G.filter (fun w => (1 + w) ^ n = c ^ n)).card := by
  classical
  refine Finset.card_nbij' (fun y => (c - y) * y⁻¹) (fun w => c * (1 + w)⁻¹) ?_ ?_ ?_ ?_
  · -- forward maps into the shifted-power filter
    intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    obtain ⟨hyG, hcy⟩ := hy
    have hy0 : y ≠ 0 := ne_zero_of_mem hn hGmem hyG
    refine ⟨mem_of_mem_mem hGmem hcy (inv_mem_of_mem hn hGmem hyG), ?_⟩
    have h1w : 1 + (c - y) * y⁻¹ = c * y⁻¹ := by field_simp; ring
    rw [h1w, mul_pow, inv_pow, (hGmem y).mp hyG, inv_one, mul_one]
  · -- inverse maps into the additive filter
    intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter] at hw ⊢
    obtain ⟨hwG, hwc⟩ := hw
    have h1w0 : (1 : F) + w ≠ 0 := by
      intro h; rw [h, zero_pow (by omega : n ≠ 0)] at hwc
      exact hc ((pow_eq_zero_iff (show n ≠ 0 by omega)).mp hwc.symm)
    have hjG : c * (1 + w)⁻¹ ∈ G := by
      rw [hGmem, mul_pow, inv_pow, hwc, mul_inv_cancel₀ (pow_ne_zero n hc)]
    refine ⟨hjG, ?_⟩
    have hcj : c - c * (1 + w)⁻¹ = w * (c * (1 + w)⁻¹) := by field_simp; ring
    rw [hcj]
    exact mem_of_mem_mem hGmem hwG hjG
  · -- left inverse
    intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy
    have hy0 : y ≠ 0 := ne_zero_of_mem hn hGmem hy.1
    have h1w : 1 + (c - y) * y⁻¹ = c * y⁻¹ := by field_simp; ring
    simp only []
    rw [h1w]; field_simp
  · -- right inverse
    intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter] at hw
    have h1w0 : (1 : F) + w ≠ 0 := by
      intro h; rw [h, zero_pow (by omega : n ≠ 0)] at hw
      exact hc ((pow_eq_zero_iff (show n ≠ 0 by omega)).mp hw.2.symm)
    have hcj : c - c * (1 + w)⁻¹ = w * (c * (1 + w)⁻¹) := by field_simp; ring
    simp only []
    rw [hcj]; field_simp

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount_eq_shiftedPower
