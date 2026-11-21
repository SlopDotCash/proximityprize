/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCADeltaStarLiteralEps
import ArkLib.Data.CodingTheory.ReedSolomon

/-! # Smoothness of the dyadic power embedding -/

set_option autoImplicit false
namespace ProximityGap.DyadicPowerDomain

/-- Successive powers of any unit of dyadic order enumerate its entire subgroup. -/
noncomputable def smooth {p μ : ℕ} [Fact p.Prime] (g : (ZMod p)ˣ)
    (order : orderOf g = 2^μ) : ReedSolomon.Smooth (MCADeltaStarLiteralEps.smoothDom p g order) where
  H := Subgroup.zpowers g
  a := 1
  h_card_pow2 := ⟨μ,Fintype.card_fin _⟩
  h_coset := by
    classical
    ext z
    constructor
    · intro h
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
      exact ⟨g^i.val,Subgroup.npow_mem_zpowers _ _,one_mul _⟩
    · rintro ⟨v,hv,rfl⟩
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hv)
      exact Finset.mem_image.mpr ⟨⟨t,order ▸ Finset.mem_range.mp ht⟩,Finset.mem_univ _,(one_mul _).symm⟩

end ProximityGap.DyadicPowerDomain
