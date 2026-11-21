/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeDegreeSevenDimension

/-! # The terminal cubic quotient dimension on the actual received-line kernel -/

open Polynomial
namespace ArkLib.ProximityGap.Frontier.SecondPrimeTerminalKernel

open SecondPrimeQuarticInterpolation SecondPrimeDegreeSevenDimension
variable {K ι : Type} [Field K] [Fintype ι]

/-- The terminal interpolants of scalar/value total degree at most 2^25. -/
abbrev Large := Monomials 33554432 5 67108863 357913943

/-- The possible quotients by a value-cubic of weight at least 290805099. -/
abbrev Small := Monomials 33554429 2 67108863 67108844

/-- The concrete constraint on the two given rows. -/
noncomputable abbrev system (dom : ι ↪ K) (u₀ u₁ : ι → K) :=
  constraints (s := 33554432) (v := 5) (d := 67108863) (t := 357913943) dom u₀ u₁

private theorem large_card : Fintype.card Large = 38280597134639049 := by
  simp only [Large, Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]

private theorem small_card : Fintype.card Small = 2251799008378920 := by
  simp only [Small, Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]

/-- This lower bound is for the actual interpolation constraints of every received pair. -/
theorem kernel_dimension (dom : ι ↪ K) (u₀ u₁ : ι → K) (hn : Fintype.card ι = 1073741824) :
    2251799041933257 ≤ Module.finrank K (LinearMap.ker (system dom u₀ u₁)) := by
  have h := (system dom u₀ u₁).finrank_range_add_finrank_ker
  have hle := Submodule.finrank_le (LinearMap.range (system dom u₀ u₁))
  rw [Module.finrank_fintype_fun_eq_card, large_card] at h
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, hn] at hle
  omega

/-- A fixed cubic cannot represent every genuine kernel interpolant using quotients in the
terminal smaller triangle. The dimension excess is 33,554,337. -/
theorem escapes_quotient_window (dom : ι ↪ K) (u₀ u₁ : ι → K) (hn : Fintype.card ι = 1073741824)
    (f : Polynomial (Polynomial K[X])) :
    ∃ c ∈ LinearMap.ker (system dom u₀ u₁), ∀ h : Small → K, surface c ≠ f * surface h := by
  classical
  by_contra! hall
  let L := LinearMap.ker (system dom u₀ u₁)
  let P : L →ₗ[K] Polynomial (Polynomial K[X]) := surfaceLinear.comp L.subtype
  let T : (Small → K) →ₗ[K] Polynomial (Polynomial K[X]) := (Algebra.lmul K _ f).comp surfaceLinear
  have hinj : Function.Injective P := by
    intro x y h
    apply Subtype.ext
    by_contra hne
    apply surface_ne_zero (sub_ne_zero.mpr hne)
    change surfaceLinear (x.val - y.val) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr h
  have hinc : LinearMap.range P ≤ LinearMap.range T := by
    rintro _ ⟨c, rfl⟩
    obtain ⟨h, hh⟩ := hall c.val c.property
    exact ⟨h, hh.symm⟩
  have hK := kernel_dimension dom u₀ u₁ hn
  have hP := LinearMap.finrank_range_of_inj (f := P) hinj
  have hinc' := Submodule.finrank_mono hinc
  have hT := LinearMap.finrank_range_le T
  rw [Module.finrank_fintype_fun_eq_card, small_card] at hT
  change 2251799041933257 ≤ Module.finrank K L at hK
  omega

#print axioms kernel_dimension
#print axioms escapes_quotient_window
end ArkLib.ProximityGap.Frontier.SecondPrimeTerminalKernel
