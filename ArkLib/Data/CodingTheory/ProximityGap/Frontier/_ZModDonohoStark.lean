/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ZModDFTParseval
import Mathlib.Algebra.Order.Chebyshev

/-!
# The Donoho–Stark discrete uncertainty principle on `ZMod N` (#407)

The #407 reframing (c.349/363, mechanism Chebotarev): the smooth-domain prize hardness *is* the
weakness of the discrete uncertainty principle on `Z_{2^μ}`. This file lands the support form of
that principle on `ZMod N`:

> `Φ ≠ 0  ⟹  |supp Φ| · |supp 𝓕Φ| ≥ N`.

Proof (Donoho–Stark), inverse-free, on the unnormalized DFT, building on `dft_parseval`:
`N·‖Φ k‖ ≤ ‖𝓕Φ‖₁` (inversion + `‖stdAddChar‖=1`), so `N²·‖Φ‖₂² ≤ |supp Φ|·‖𝓕Φ‖₁²`; Cauchy–Schwarz
gives `‖𝓕Φ‖₁² ≤ |supp 𝓕Φ|·‖𝓕Φ‖₂²`, Parseval `‖𝓕Φ‖₂² = N·‖Φ‖₂²`. Chaining:
`N²·‖Φ‖₂² ≤ |supp Φ|·|supp 𝓕Φ|·N·‖Φ‖₂²`, and cancelling `N·‖Φ‖₂² > 0` gives the bound.

Why it matters for #407: equality holds for subgroup indicators, and `μ_{2^μ}` is a subgroup — so
`2`-power groups saturate the uncertainty principle (the worst constant), the structural reason the
prize floor on `μ_{2^μ}` is hard. Axiom-clean. Issue #407.
-/

open Finset ZMod
open scoped ComplexConjugate

namespace ProximityGap.Frontier.ZModDonohoStark

variable {N : ℕ} [NeZero N]

/-- `‖stdAddChar a‖ = 1`: the standard additive character of `ZMod N` is unit-modulus. -/
theorem norm_stdAddChar (a : ZMod N) : ‖(stdAddChar a : ℂ)‖ = 1 := by
  have hpow : (stdAddChar a : ℂ) ^ N = 1 := by
    rw [← AddChar.map_nsmul_eq_pow]
    have hz : (N : ℕ) • a = 0 := by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [hz, AddChar.map_zero_eq_one]
  exact Complex.norm_eq_one_of_pow_eq_one hpow (NeZero.ne N)

/-- The `support` of `Φ` as a `Finset`. -/
noncomputable def supp (Φ : ZMod N → ℂ) : Finset (ZMod N) := univ.filter (fun j => Φ j ≠ 0)

/-- A function's `ℓ²` mass is carried by its support. -/
theorem sum_sq_eq_supp (Φ : ZMod N → ℂ) :
    ∑ j : ZMod N, ‖Φ j‖ ^ 2 = ∑ j ∈ supp Φ, ‖Φ j‖ ^ 2 := by
  refine (Finset.sum_subset (Finset.filter_subset _ _) (fun j _ hj => ?_)).symm
  simp only [mem_filter, mem_univ, true_and, not_not] at hj
  rw [hj, norm_zero]; ring

/-- **Inversion bound (inverse-free):** `N·‖Φ k‖ ≤ ‖𝓕Φ‖₁`. -/
theorem N_mul_norm_le_l1 (Φ : ZMod N → ℂ) (k : ZMod N) :
    (N : ℝ) * ‖Φ k‖ ≤ ∑ j : ZMod N, ‖(𝓕 Φ) j‖ := by
  have hNcne : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hNΦ : (N : ℂ) • Φ k = ∑ j : ZMod N, stdAddChar (j * k) * (𝓕 Φ) j := by
    have h1 : (𝓕⁻ (𝓕 Φ)) k = (N : ℂ)⁻¹ • ∑ j : ZMod N, stdAddChar (j * k) * (𝓕 Φ) j := by
      rw [invDFT_apply]; simp [smul_eq_mul]
    rw [dft.symm_apply_apply] at h1
    rw [h1, smul_smul, mul_inv_cancel₀ hNcne, one_smul]
  have hnorm : (N : ℝ) * ‖Φ k‖ = ‖(N : ℂ) • Φ k‖ := by
    rw [norm_smul, Complex.norm_natCast]
  rw [hnorm, hNΦ]
  calc ‖∑ j : ZMod N, stdAddChar (j * k) * (𝓕 Φ) j‖
      ≤ ∑ j : ZMod N, ‖stdAddChar (j * k) * (𝓕 Φ) j‖ := norm_sum_le _ _
    _ = ∑ j : ZMod N, ‖(𝓕 Φ) j‖ := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [norm_mul, norm_stdAddChar, one_mul]

/-- **The Donoho–Stark uncertainty principle on `ZMod N`:**
`Φ ≠ 0 ⟹ N ≤ |supp Φ| · |supp 𝓕Φ|`. -/
theorem donoho_stark (Φ : ZMod N → ℂ) (hΦ : Φ ≠ 0) :
    (N : ℝ) ≤ (supp Φ).card * (supp (𝓕 Φ)).card := by
  set A : ℝ := ((supp Φ).card : ℝ) with hA
  set B : ℝ := ((supp (𝓕 Φ)).card : ℝ) with hB
  set L1 : ℝ := ∑ k : ZMod N, ‖(𝓕 Φ) k‖ with hL1
  set S2 : ℝ := ∑ j : ZMod N, ‖Φ j‖ ^ 2 with hS2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hAnn : 0 ≤ A := by positivity
  have hS2pos : 0 < S2 := by
    obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hΦ
    refine Finset.sum_pos' (fun j _ => by positivity) ⟨j0, Finset.mem_univ _, ?_⟩
    have : Φ j0 ≠ 0 := by simpa using hj0
    positivity
  have hpars : (∑ k : ZMod N, ‖(𝓕 Φ) k‖ ^ 2) = (N : ℝ) * S2 :=
    ZModDFTParseval.dft_parseval Φ
  -- (a)  N²·S2 ≤ A·L1²
  have ha : (N : ℝ) ^ 2 * S2 ≤ A * L1 ^ 2 := by
    have hexp : (N : ℝ) ^ 2 * S2 = ∑ j ∈ supp Φ, ((N : ℝ) * ‖Φ j‖) ^ 2 := by
      rw [hS2, sum_sq_eq_supp, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hexp]
    calc ∑ j ∈ supp Φ, ((N : ℝ) * ‖Φ j‖) ^ 2
        ≤ ∑ _j ∈ supp Φ, L1 ^ 2 := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          have h := N_mul_norm_le_l1 Φ j
          have hnn : 0 ≤ (N : ℝ) * ‖Φ j‖ := mul_nonneg hNpos.le (norm_nonneg _)
          nlinarith [h, hnn]
      _ = A * L1 ^ 2 := by rw [Finset.sum_const, hA, nsmul_eq_mul]
  -- (b)  L1² ≤ B·(N·S2)
  have hb : L1 ^ 2 ≤ B * ((N : ℝ) * S2) := by
    have hL1supp : L1 = ∑ k ∈ supp (𝓕 Φ), ‖(𝓕 Φ) k‖ := by
      rw [hL1]
      refine (Finset.sum_subset (Finset.filter_subset _ _) (fun k _ hk => ?_)).symm
      simp only [mem_filter, mem_univ, true_and, not_not] at hk
      rw [hk, norm_zero]
    have hsq2 : (∑ k ∈ supp (𝓕 Φ), ‖(𝓕 Φ) k‖ ^ 2) = (N : ℝ) * S2 := by
      rw [← sum_sq_eq_supp]; exact hpars
    have hcs : (∑ k ∈ supp (𝓕 Φ), ‖(𝓕 Φ) k‖) ^ 2 ≤ B * ((N : ℝ) * S2) := by
      have h := sq_sum_le_card_mul_sum_sq (s := supp (𝓕 Φ)) (f := fun k => ‖(𝓕 Φ) k‖)
      rw [hsq2] at h
      exact h
    rw [hL1supp]; exact hcs
  -- combine and cancel  N·S2 > 0
  have hcomb : (N : ℝ) ^ 2 * S2 ≤ A * B * (N : ℝ) * S2 :=
    calc (N : ℝ) ^ 2 * S2 ≤ A * L1 ^ 2 := ha
      _ ≤ A * (B * ((N : ℝ) * S2)) := mul_le_mul_of_nonneg_left hb hAnn
      _ = A * B * (N : ℝ) * S2 := by ring
  have hNS2 : 0 < (N : ℝ) * S2 := mul_pos hNpos hS2pos
  have hfin : (N : ℝ) * ((N : ℝ) * S2) ≤ (A * B) * ((N : ℝ) * S2) := by nlinarith [hcomb]
  exact le_of_mul_le_mul_right hfin hNS2

end ProximityGap.Frontier.ZModDonohoStark

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ZModDonohoStark.norm_stdAddChar
#print axioms ProximityGap.Frontier.ZModDonohoStark.donoho_stark
