/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeDegreeSevenDimension

/-! # An interpolation kernel exceeds a smaller quotient space -/

open Polynomial
namespace ArkLib.ProximityGap.Frontier.SecondPrimeKernelCapacity
open SecondPrimeQuarticInterpolation SecondPrimeDegreeSevenDimension

variable {K ι : Type} [Field K] [Fintype ι]

/-- The constraints on actual received rows cannot put their entire kernel in the products
of one fixed factor with a smaller coefficient window if the source dimension exceeds the
number of constraint coordinates plus the size of that quotient window. -/
theorem escapes {s v d t s' v' t' : ℕ} (dom : ι ↪ K) (u₀ u₁ : ι → K)
    (f : Polynomial (Polynomial K[X]))
    (hsize : Fintype.card ι * (s + 1) + Fintype.card (Monomials s' v' d t') <
      Fintype.card (Monomials s v d t)) :
    ∃ c ∈ LinearMap.ker (constraints (s := s) (v := v) (d := d) (t := t) dom u₀ u₁),
      ∀ h : Monomials s' v' d t' → K, surface c ≠ f * surface h := by
  classical
  by_contra! hall
  let M := constraints (s := s) (v := v) (d := d) (t := t) dom u₀ u₁
  let L := LinearMap.ker M
  let P : L →ₗ[K] Polynomial (Polynomial K[X]) := surfaceLinear.comp L.subtype
  let T : (Monomials s' v' d t' → K) →ₗ[K] Polynomial (Polynomial K[X]) :=
    (Algebra.lmul K _ f).comp surfaceLinear
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
  have hK := M.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at hK
  have hrows := Submodule.finrank_le (LinearMap.range M)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin] at hrows
  have hP := LinearMap.finrank_range_of_inj (f := P) hinj
  have hbranch := Submodule.finrank_mono hinc
  have hT := LinearMap.finrank_range_le T
  rw [Module.finrank_fintype_fun_eq_card] at hT
  change Module.finrank K (LinearMap.range M) + Module.finrank K L = _ at hK
  omega

#print axioms escapes
end ArkLib.ProximityGap.Frontier.SecondPrimeKernelCapacity
