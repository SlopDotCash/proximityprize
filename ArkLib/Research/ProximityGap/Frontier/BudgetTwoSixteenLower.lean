/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterBudgetTwoThreshold
import ArkLib.Research.ProximityGap.Frontier.SixteenCosetListLower

/-!
# Three-word lists at all four rates on sixteen coordinates

The modulus has list budget two at 128-bit security. Its explicit generator
specializes the four-rate list construction for arbitrary smooth cosets.
-/

namespace ProximityGap.BudgetTwoSixteen

open Polynomial Finset Code

/-- Prime field whose 128-bit integer budget is two. -/
abbrev K := ZMod QuarterBudgetTwoThreshold.p

/-- Sixteenth root obtained by raising seven to the index of the subgroup. -/
abbrev g : K := 236023637409912314118267886612795304038

/-- Unit generator for the smoothness witness. -/
def generator : Kˣ := Units.mk0 g (by decide)

theorem generator_order : orderOf generator = 16 := by
  rw [← orderOf_units]
  exact orderOf_eq_prime_pow (p := 2) (n := 3) (by decide) (by decide)

/-- The sixteen successive powers of the generator. -/
def domain : Fin 16 ↪ K where
  toFun i := g ^ i.val
  inj' := by
    intro i j h
    apply Fin.ext
    apply pow_injOn_Iio_orderOf (x := generator) _ _ (Units.ext h)
    · change _ < orderOf generator
      simp [generator_order]
    · change _ < orderOf generator
      simp [generator_order]

noncomputable instance smoothDomain : ReedSolomon.Smooth domain where
  H := Subgroup.zpowers generator
  a := 1
  h_card_pow2 := ⟨4, by decide⟩
  h_coset := by
    classical
    ext x
    constructor
    · rintro hx
      obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      exact ⟨generator ^ i.val, Subgroup.npow_mem_zpowers _ _, by
        change 1 * g ^ i.val = g ^ i.val
        rw [one_mul]⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨t, ht, rfl⟩ := mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hv)
      exact mem_image.mpr ⟨⟨t, by simpa [generator_order] using mem_range.mp ht⟩, mem_univ _,
        by change g ^ t = 1 * g ^ t; rw [one_mul]⟩

/-- Dimensions at the four prize rates. -/
def dimension : Fin 4 → ℕ := ![8, 4, 2, 1]

/-- First failing error counts, ordered by decreasing rate. -/
def firstBad : Fin 4 → ℕ := ![5, 8, 10, 11]

/-- The field-independent three-word construction applies to this explicit ordering. -/
theorem scalar_lower (j : Fin 4) :
    3 ≤ Lambda (ReedSolomon.code domain (dimension j) : Set (Fin 16 → K))
      ((firstBad j : ℝ) / 16) :=
  SixteenCosetListLower.smooth_scalar_lower domain (Fintype.card_fin _) j

#print axioms smoothDomain
#print axioms scalar_lower

end ProximityGap.BudgetTwoSixteen
