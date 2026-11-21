/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.LinearFieldProductionThreeHeads
import ArkLib.Research.ProximityGap.Frontier.FourRateList128
import Mathlib.Tactic.ReduceModChar

/-! # A 38-bit smooth example of the three-head probability curve

At security denominator 110, the size-2^30 subgroup of this field has
integer budget 2^31. Its rate-one-sixteenth code has the same three-head
crossing as the previously certified much larger second designated field.
-/

set_option autoImplicit false
namespace ProximityGap.ThreeHeadPrime38
open ArkLib.ProximityGap.Frontier Code MCAThresholdLedger
open scoped NNReal ENNReal
abbrev p : ℕ := 236223201281

/-- A Lucas certificate using all three prime factors of the group order. -/
theorem prime : Nat.Prime p := by
  refine lucas_primality p 3 (by reduce_mod_char) ?_
  intro l hl divides
  rw [show p-1 = 2^32 * (5 * 11) by decide] at divides
  rcases hl.dvd_mul.mp divides with two|odd
  · have he := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow two)
    subst l
    reduce_mod_char
    decide
  · rcases hl.dvd_mul.mp odd with h|h
    · have he := (Nat.prime_dvd_prime_iff_eq hl (by decide : Nat.Prime 5)).mp h
      subst l
      reduce_mod_char
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hl (by decide : Nat.Prime 11)).mp h
      subst l
      reduce_mod_char
      decide

instance : Fact p.Prime := ⟨prime⟩
abbrev K := ZMod p

private theorem primitive : IsPrimitiveRoot (62201816290:K) (2^30) := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  apply orderOf_eq_prime_pow (p:=2) (n:=29)
  · change (62201816290:ZMod p)^(2^29:ℕ)≠1
    reduce_mod_char
    decide
  · change (62201816290:ZMod p)^(2^30:ℕ)=1
    reduce_mod_char

noncomputable abbrev H : Subgroup Kˣ := rootsOfUnity (2^30) K
noncomputable instance : Fintype H := Fintype.ofFinite H
theorem card_H : Fintype.card H=2^30 := Nat.card_eq_fintype_card.symm.trans primitive.card_rootsOfUnity
noncomputable abbrev domain : H ↪ K := FourRateList128.domain H

noncomputable instance smooth : ReedSolomon.Smooth domain where
  H := H
  a := 1
  h_card_pow2 := ⟨30,card_H⟩
  h_coset := by
    classical
    ext x
    constructor
    · intro hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact ⟨i.val,i.property,one_mul _⟩
    · rintro ⟨i,hi,rfl⟩
      exact Finset.mem_image.mpr ⟨⟨i,hi⟩,Finset.mem_univ _,(one_mul _).symm⟩

/-- On this concrete smooth code, every positive interleaving width has a
safe predecessor and first failure at 715827882 errors for tolerance 1/110. -/
theorem classification (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code domain 67108864 : Set (H → K)) ^⋈ (Fin width)
    let b := (715827882:ℝ≥0)/1073741824
    mcaDeltaStar (F:=K) C (1/110) = b ∧ ∀ δ, epsMCA (F:=K) C δ≤1/110 ↔ δ<b :=
  LinearFieldProductionThreeHeads.classification (p:=p) domain card_H (Q:=110) (j:=715827882)
    (by decide) (by decide) (by decide) (by decide) (by decide) width

end ProximityGap.ThreeHeadPrime38
#print axioms ProximityGap.ThreeHeadPrime38.classification
