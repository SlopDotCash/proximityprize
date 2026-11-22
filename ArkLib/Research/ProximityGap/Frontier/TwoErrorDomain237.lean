/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicLogWitness237
import ArkLib.Data.CodingTheory.ReedSolomon

/-! # The order-128 subgroup of the 237-bit prime field -/
namespace ProximityGap.TwoErrorSliceThreshold

open ArkLib.ProximityGap.Frontier.DyadicLogWitness237

/-- The eighth power of the certified element of order 1024. -/
abbrev root237 : ZMod P := g^8

theorem primitive237 : IsPrimitiveRoot root237 128 :=
  primitive.pow_of_dvd (show 8 ≠ 0 by decide) (by decide)

/-- The exponent enumeration used in the finite two-error calculation. -/
def domain237 : Fin 128 ↪ ZMod P :=
  ⟨fun i => root237^(i : ℕ), fun i j h => Fin.ext (primitive237.pow_inj i.isLt j.isLt h)⟩

noncomputable abbrev group237 : Subgroup (ZMod P)ˣ := rootsOfUnity 128 (ZMod P)
noncomputable instance : Fintype group237 := Fintype.ofFinite _

theorem group237_card : Fintype.card group237 = 128 :=
  Nat.card_eq_fintype_card.symm.trans primitive237.card_rootsOfUnity

noncomputable def index237 (i : Fin 128) : group237 := primitive237.toRootsOfUnity ^ (i : ℕ)

theorem index237_value (i : Fin 128) : domain237 i = ((index237 i : (ZMod P)ˣ) : ZMod P) := rfl

noncomputable instance : ReedSolomon.Smooth domain237 where
  H := group237
  a := 1
  h_card_pow2 := ⟨7,(Fintype.card_fin 128).trans (by decide : 128 = 2^7)⟩
  h_coset := by
    classical
    have inj : Function.Injective index237 := fun _ _ h => domain237.injective
      (congrArg (fun x : group237 => ((x : (ZMod P)ˣ) : ZMod P)) h)
    have sur := ((Fintype.bijective_iff_injective_and_card index237).mpr
      ⟨inj,by rw [Fintype.card_fin,group237_card]⟩).surjective
    ext x
    constructor
    · intro hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact ⟨(index237 i).val,(index237 i).property,by simp [index237_value]⟩
    · rintro ⟨u,hu,rfl⟩
      obtain ⟨i,hi⟩ := sur ⟨u,hu⟩
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by rw [index237_value,hi]; simp⟩

end ProximityGap.TwoErrorSliceThreshold

#print axioms ProximityGap.TwoErrorSliceThreshold.primitive237
