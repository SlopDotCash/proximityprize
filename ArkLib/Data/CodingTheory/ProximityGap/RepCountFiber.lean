/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyRepBound

/-!
# The GV rep-count as a shifted-Fermat fibre (#389)

The Garcia–Voloch object `r(c) = repCount μ_n c = #{a ∈ μ_n : c − a ∈ μ_n}` is the count whose
boundedness pins δ* in the deployed split regime.  This file records a **novel exact
reformulation**: `r(c)` is the fibre over `c^n` of the single map `ζ ↦ (1+ζ)^n`,

> **`repCount_eq_fiber_card`** — for `μ_n = {x : x ≠ 0 ∧ x^n = 1}` and `c ≠ 0`,
> `r(c) = #{ζ ∈ μ_n : (1 + ζ)^n = c^n}`.

The bijection is `a ↦ a/(c−a)` with inverse `ζ ↦ ζc/(1+ζ)`: writing `ζ = a/(c−a)` gives
`1+ζ = c/(c−a)`, so `(1+ζ)^n = c^n/(c−a)^n = c^n` exactly when `c−a ∈ μ_n`.  This recasts the
`gcd(X^n−1, (c−X)^n−1)` object as the roots of the *single* shifted-Fermat polynomial
`(1+X)^n − c^n` lying in `μ_n` — a cleaner Stepanov target (one curve, not an intersection).
No Weil, no Stepanov; a clean structural identity.  Issue #389.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- **The rep-count is a shifted-Fermat fibre.**  For `G = μ_n` (nonzero `n`-th roots of unity in
a field, `n ≠ 0`) and `c ≠ 0`, `repCount G c = #{ζ ∈ G : (1 + ζ)^n = c^n}`. -/
theorem repCount_eq_fiber_card {F : Type*} [Field F] [DecidableEq F] {n : ℕ} (hn : n ≠ 0)
    {G : Finset F} (hG : ∀ x : F, x ∈ G ↔ x ≠ 0 ∧ x ^ n = 1) {c : F} (hc : c ≠ 0) :
    repCount G c = (G.filter (fun ζ => (1 + ζ) ^ n = c ^ n)).card := by
  have hcn : c ^ n ≠ 0 := pow_ne_zero n hc
  unfold repCount
  refine Finset.card_nbij' (fun y => y / (c - y)) (fun ζ => ζ * c / (1 + ζ)) ?_ ?_ ?_ ?_
  · -- maps `{y : c−y ∈ G}` into `{ζ : (1+ζ)^n = c^n}`
    intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    obtain ⟨hyG, hcyG⟩ := hy
    obtain ⟨hy0, hyn⟩ := (hG y).mp hyG
    obtain ⟨hcy0, hcyn⟩ := (hG (c - y)).mp hcyG
    have hmem : y / (c - y) ∈ G := by
      rw [hG]; exact ⟨div_ne_zero hy0 hcy0, by rw [div_pow, hyn, hcyn, div_one]⟩
    refine ⟨hmem, ?_⟩
    have h1 : 1 + y / (c - y) = c / (c - y) := by field_simp; ring
    rw [h1, div_pow, hcyn, div_one]
  · -- maps `{ζ : (1+ζ)^n = c^n}` into `{y : c−y ∈ G}`
    intro ζ hζ
    simp only [Finset.mem_coe, Finset.mem_filter] at hζ ⊢
    obtain ⟨hζG, hζn⟩ := hζ
    obtain ⟨hζ0, hζpow⟩ := (hG ζ).mp hζG
    have hz0 : (1 : F) + ζ ≠ 0 := (pow_ne_zero_iff hn).mp (hζn ▸ hcn)
    have hmem : ζ * c / (1 + ζ) ∈ G := by
      rw [hG]
      exact ⟨div_ne_zero (mul_ne_zero hζ0 hc) hz0, by
        rw [div_pow, mul_pow, hζpow, hζn, one_mul, div_self hcn]⟩
    refine ⟨hmem, ?_⟩
    have hsub : c - ζ * c / (1 + ζ) = c / (1 + ζ) := by field_simp; ring
    rw [hG, hsub]
    exact ⟨div_ne_zero hc hz0, by rw [div_pow, hζn, div_self hcn]⟩
  · -- left inverse
    intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy
    obtain ⟨hyG, hcyG⟩ := hy
    obtain ⟨hy0, _⟩ := (hG y).mp hyG
    obtain ⟨hcy0, _⟩ := (hG (c - y)).mp hcyG
    have h1 : 1 + y / (c - y) = c / (c - y) := by field_simp; ring
    dsimp only; rw [h1]; field_simp
  · -- right inverse
    intro ζ hζ
    simp only [Finset.mem_coe, Finset.mem_filter] at hζ
    obtain ⟨hζG, hζn⟩ := hζ
    obtain ⟨hζ0, _⟩ := (hG ζ).mp hζG
    have hz0 : (1 : F) + ζ ≠ 0 := (pow_ne_zero_iff hn).mp (hζn ▸ hcn)
    have hsub : c - ζ * c / (1 + ζ) = c / (1 + ζ) := by field_simp; ring
    dsimp only; rw [hsub]; field_simp

end ArkLib.ProximityGap.AdditiveEnergyRepBound

#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount_eq_fiber_card
