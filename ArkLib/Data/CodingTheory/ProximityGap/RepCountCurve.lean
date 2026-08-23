/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyRepBound

/-!
# The rep-count curve reformulation (#389)

The Garcia–Voloch / sum-product representation count `r(c) = |{y ∈ μ_n : c − y ∈ μ_n}|` — the
quantity the whole additive-energy chain (`GVRepBound`, the split-case `n ∣ p−1` wall) is built
on — is reformulated here as the number of `n`-th roots of unity lying on **one explicit curve**:

  `r(c) = |{w ∈ μ_n : (w + 1)^n = c^n}|`.

The bijection is `y ↦ y / (c − y)` (with inverse `w ↦ w·c / (w + 1)`).  Writing `r(c)` as
`μ_n ∩ {(w+1)^n = c^n}` — a single polynomial condition on the subgroup — is the natural shape
for a Stepanov/Weil-style bound: it replaces "two membership conditions `y, c−y ∈ μ_n`" by
"one membership `w ∈ μ_n` plus one curve equation", i.e. the common-root count of `X^n − 1` and
`(X+1)^n − c^n`, which is exactly what a resultant / Stepanov auxiliary acts on.

This is an exact identity (no characteristic hypothesis beyond `1 ≤ n`, `c ≠ 0`), axiom-clean.
-/

open Polynomial Finset

namespace ArkLib.ProximityGap

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The `n`-th roots of unity in `F`, as a `Finset`. -/
noncomputable def muN (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) : Finset F :=
  Finset.univ.filter (fun x => x ^ n = 1)

/-- **The rep-count curve reformulation**: the representation count `r(c)` of `c` by the `n`-th
roots of unity equals the number of `n`-th roots of unity `w` on the explicit curve
`(w + 1)^n = c^n`.  Bijection `y ↦ y / (c − y)`. -/
theorem repCount_eq_curve {n : ℕ} (hn : 1 ≤ n) {c : F} (hc : c ≠ 0) :
    AdditiveEnergyRepBound.repCount (muN F n) c
      = ((muN F n).filter (fun w => (w + 1) ^ n = c ^ n)).card := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hne : ∀ u : F, u ^ n = 1 → u ≠ 0 := by
    intro u hu h0; subst h0; rw [zero_pow hn0] at hu; exact zero_ne_one hu
  rw [AdditiveEnergyRepBound.repCount]
  apply Finset.card_nbij' (fun y => y * (c - y)⁻¹) (fun w => w * c * (w + 1)⁻¹)
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    obtain ⟨hyG, hzG⟩ := hy
    rw [muN, Finset.mem_filter] at hyG hzG
    have hyn : y ^ n = 1 := hyG.2
    have hzn : (c - y) ^ n = 1 := hzG.2
    have hz0 : c - y ≠ 0 := hne _ hzn
    refine ⟨?_, ?_⟩
    · rw [muN, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [mul_pow, inv_pow, hyn, hzn, inv_one, mul_one]⟩
    · have hw1 : y * (c - y)⁻¹ + 1 = c * (c - y)⁻¹ := by field_simp; ring
      rw [hw1, mul_pow, inv_pow, hzn, inv_one, mul_one]
  · intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter] at hw ⊢
    obtain ⟨hwG, hwc⟩ := hw
    rw [muN, Finset.mem_filter] at hwG
    have hwn : w ^ n = 1 := hwG.2
    have hw10 : w + 1 ≠ 0 := fun h =>
      pow_ne_zero n hc (by rw [← hwc, h, zero_pow hn0])
    refine ⟨?_, ?_⟩
    · rw [muN, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by
        rw [mul_pow, mul_pow, inv_pow, hwn, one_mul, hwc, mul_inv_cancel₀ (pow_ne_zero _ hc)]⟩
    · have hceq : c - w * c * (w + 1)⁻¹ = c * (w + 1)⁻¹ := by field_simp; ring
      rw [muN, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by
        rw [hceq, mul_pow, inv_pow, hwc, mul_inv_cancel₀ (pow_ne_zero _ hc)]⟩
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy
    obtain ⟨hyG, hzG⟩ := hy
    rw [muN, Finset.mem_filter] at hzG
    have hz0 : c - y ≠ 0 := hne _ hzG.2
    have hw1 : y * (c - y)⁻¹ + 1 = c * (c - y)⁻¹ := by field_simp; ring
    show y * (c - y)⁻¹ * c * (y * (c - y)⁻¹ + 1)⁻¹ = y
    rw [hw1]; field_simp
  · intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter] at hw
    obtain ⟨hwG, hwc⟩ := hw
    rw [muN, Finset.mem_filter] at hwG
    have hw10 : w + 1 ≠ 0 := fun h =>
      pow_ne_zero n hc (by rw [← hwc, h, zero_pow hn0])
    have hc2 : c - w * c * (w + 1)⁻¹ = c * (w + 1)⁻¹ := by field_simp; ring
    show w * c * (w + 1)⁻¹ * (c - w * c * (w + 1)⁻¹)⁻¹ = w
    rw [hc2]; field_simp

end ArkLib.ProximityGap
