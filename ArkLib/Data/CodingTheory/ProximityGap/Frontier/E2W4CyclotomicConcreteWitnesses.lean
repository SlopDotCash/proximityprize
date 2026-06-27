/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.E2W4CyclotomicNonCollision

/-!
# Concrete witnesses for the width-four cyclotomic finite-exception row

This frontier support module keeps small finite-field witnesses out of the already-large
`E2W4CyclotomicNonCollision` core while preserving the same public namespace. The witnesses give
closed finite-field refuters beyond the `n = 32` finite-exception threshold and show that the four
exception primes are genuine primitive-root collapse characteristics.
-/

set_option autoImplicit false

open ArkLib.ProximityGap.E2DilationDirectCount

namespace ArkLib.ProximityGap.E2W4CyclotomicNonCollision

section Concrete1217Ratio

local instance fact_prime_1217_ratio : Fact (Nat.Prime 1217) := ⟨by norm_num⟩

/-- A concrete primitive 32-th root in `F_1217`. -/
theorem orderOf_21_ratio_zmod1217 : orderOf (21 : ZMod 1217) = 32 := by
  have h16 : ¬ (21 : ZMod 1217) ^ (2 : ℕ) ^ 4 = 1 := by decide
  have h32 : (21 : ZMod 1217) ^ (2 : ℕ) ^ 5 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (21 : ZMod 1217)) h16 h32
  norm_num at h
  exact h

/-- `21` is a primitive 32-th root in `F_1217`. -/
theorem isPrimitiveRoot_21_32_ratio_zmod1217 :
    IsPrimitiveRoot (21 : ZMod 1217) 32 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_21_ratio_zmod1217

/-- Concrete `n = 32` width-4 refuter in the small `β = 2` Thorner-Zaman row: the prime
`1217 ∈ [32², 2 * 32²]` is already larger than the reduced Bezout threshold. -/
theorem exists_mu32_width4_refuter_zmod1217 :
    ∃ ζ : ZMod 1217, IsPrimitiveRoot ζ 32 ∧
      ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 32 (1 : ZMod 1217)) 4).card ≤ 32 := by
  exact ⟨21, isPrimitiveRoot_21_32_ratio_zmod1217,
    not_e2BadScalarSet_mu32_card_le_32_zmod_of_prime_gt1153
      (p := 1217) (by norm_num) isPrimitiveRoot_21_32_ratio_zmod1217⟩

end Concrete1217Ratio

section Concrete1048609Ratio

local instance fact_prime_1048609_ratio : Fact (Nat.Prime 1048609) := ⟨by norm_num⟩

/-- A concrete primitive 32-th root in `F_1048609`. -/
theorem orderOf_57211_ratio_zmod1048609 : orderOf (57211 : ZMod 1048609) = 32 := by
  have h16 : ¬ (57211 : ZMod 1048609) ^ (2 : ℕ) ^ 4 = 1 := by decide
  have h32 : (57211 : ZMod 1048609) ^ (2 : ℕ) ^ 5 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (57211 : ZMod 1048609)) h16 h32
  norm_num at h
  exact h

/-- `57211` is a primitive 32-th root in `F_1048609`. -/
theorem isPrimitiveRoot_57211_32_ratio_zmod1048609 :
    IsPrimitiveRoot (57211 : ZMod 1048609) 32 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_57211_ratio_zmod1048609

/-- Concrete large-prime `n = 32` width-4 refuter: the first prime from the concrete
Thorner-Zaman `β = 4` row already lies past the finite-exception threshold. -/
theorem exists_mu32_width4_refuter_zmod1048609 :
    ∃ ζ : ZMod 1048609, IsPrimitiveRoot ζ 32 ∧
      ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 32 (1 : ZMod 1048609)) 4).card ≤ 32 := by
  exact ⟨57211, isPrimitiveRoot_57211_32_ratio_zmod1048609,
    not_e2BadScalarSet_mu32_card_le_32_zmod_of_prime_gt1153
      (p := 1048609) (by norm_num) isPrimitiveRoot_57211_32_ratio_zmod1048609⟩

end Concrete1048609Ratio

/-! ### Sharpness witnesses for the `n = 32` finite bad-prime list -/

section ConcreteN32BadPrimeCollapses

local instance fact_prime_97_bad_ratio : Fact (Nat.Prime 97) := ⟨by norm_num⟩
local instance fact_prime_641_bad_ratio : Fact (Nat.Prime 641) := ⟨by norm_num⟩
local instance fact_prime_673_bad_ratio : Fact (Nat.Prime 673) := ⟨by norm_num⟩
local instance fact_prime_1153_bad_ratio : Fact (Nat.Prime 1153) := ⟨by norm_num⟩

/-- A primitive 32-th root in `F_97` at which the canonical denominator-free obstruction
vanishes. This complements the non-collision witness `19`: the bad-prime behavior depends on the
primitive-root embedding. -/
theorem orderOf_28_bad_ratio_zmod97 : orderOf (28 : ZMod 97) = 32 := by
  have h16 : ¬ (28 : ZMod 97) ^ (2 : ℕ) ^ 4 = 1 := by decide
  have h32 : (28 : ZMod 97) ^ (2 : ℕ) ^ 5 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (28 : ZMod 97)) h16 h32
  norm_num at h
  exact h

/-- `28` is a primitive 32-th root in `F_97`. -/
theorem isPrimitiveRoot_28_32_bad_ratio_zmod97 : IsPrimitiveRoot (28 : ZMod 97) 32 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_28_bad_ratio_zmod97

/-- At the finite-exception prime `97`, the canonical denominator-free obstruction vanishes for
the primitive root `28`. -/
theorem polynomial_eq_28_sq_pow32_zmod97 :
    ((28 : ZMod 97) ^ 4 + 1) ^ 32 =
      ((28 : ZMod 97) ^ 2 + 1) ^ 32 := by
  decide

/-- Equivalently, the canonical ratio for `ζ = 28` is itself a 32-th root in `F_97`. -/
theorem invariantRatio_28_sq_pow32_eq_one_zmod97 :
    invariantRatio (28 : ZMod 97) ((28 : ZMod 97) ^ 2) ^ 32 = 1 := by
  decide

/-- A primitive 32-th root in `F_641` at which the canonical denominator-free obstruction
vanishes. -/
theorem orderOf_25_bad_ratio_zmod641 : orderOf (25 : ZMod 641) = 32 := by
  have h16 : ¬ (25 : ZMod 641) ^ (2 : ℕ) ^ 4 = 1 := by decide
  have h32 : (25 : ZMod 641) ^ (2 : ℕ) ^ 5 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (25 : ZMod 641)) h16 h32
  norm_num at h
  exact h

/-- `25` is a primitive 32-th root in `F_641`. -/
theorem isPrimitiveRoot_25_32_bad_ratio_zmod641 : IsPrimitiveRoot (25 : ZMod 641) 32 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_25_bad_ratio_zmod641

/-- At the finite-exception prime `641`, the canonical denominator-free obstruction vanishes for
the primitive root `25`. -/
theorem polynomial_eq_25_sq_pow32_zmod641 :
    ((25 : ZMod 641) ^ 4 + 1) ^ 32 =
      ((25 : ZMod 641) ^ 2 + 1) ^ 32 := by
  decide

/-- Equivalently, the canonical ratio for `ζ = 25` is itself a 32-th root in `F_641`. -/
theorem invariantRatio_25_sq_pow32_eq_one_zmod641 :
    invariantRatio (25 : ZMod 641) ((25 : ZMod 641) ^ 2) ^ 32 = 1 := by
  decide

/-- A primitive 32-th root in `F_673` at which the canonical denominator-free obstruction
vanishes. -/
theorem orderOf_149_bad_ratio_zmod673 : orderOf (149 : ZMod 673) = 32 := by
  have h16 : ¬ (149 : ZMod 673) ^ (2 : ℕ) ^ 4 = 1 := by decide
  have h32 : (149 : ZMod 673) ^ (2 : ℕ) ^ 5 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (149 : ZMod 673)) h16 h32
  norm_num at h
  exact h

/-- `149` is a primitive 32-th root in `F_673`. -/
theorem isPrimitiveRoot_149_32_bad_ratio_zmod673 : IsPrimitiveRoot (149 : ZMod 673) 32 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_149_bad_ratio_zmod673

/-- At the finite-exception prime `673`, the canonical denominator-free obstruction vanishes for
the primitive root `149`. -/
theorem polynomial_eq_149_sq_pow32_zmod673 :
    ((149 : ZMod 673) ^ 4 + 1) ^ 32 =
      ((149 : ZMod 673) ^ 2 + 1) ^ 32 := by
  decide

/-- Equivalently, the canonical ratio for `ζ = 149` is itself a 32-th root in `F_673`. -/
theorem invariantRatio_149_sq_pow32_eq_one_zmod673 :
    invariantRatio (149 : ZMod 673) ((149 : ZMod 673) ^ 2) ^ 32 = 1 := by
  decide

/-- A primitive 32-th root in `F_1153` at which the canonical denominator-free obstruction
vanishes. -/
theorem orderOf_439_bad_ratio_zmod1153 : orderOf (439 : ZMod 1153) = 32 := by
  have h16 : ¬ (439 : ZMod 1153) ^ (2 : ℕ) ^ 4 = 1 := by decide
  have h32 : (439 : ZMod 1153) ^ (2 : ℕ) ^ 5 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (439 : ZMod 1153)) h16 h32
  norm_num at h
  exact h

/-- `439` is a primitive 32-th root in `F_1153`. -/
theorem isPrimitiveRoot_439_32_bad_ratio_zmod1153 :
    IsPrimitiveRoot (439 : ZMod 1153) 32 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_439_bad_ratio_zmod1153

/-- At the finite-exception prime `1153`, the canonical denominator-free obstruction vanishes for
the primitive root `439`. -/
theorem polynomial_eq_439_sq_pow32_zmod1153 :
    ((439 : ZMod 1153) ^ 4 + 1) ^ 32 =
      ((439 : ZMod 1153) ^ 2 + 1) ^ 32 := by
  decide

/-- Equivalently, the canonical ratio for `ζ = 439` is itself a 32-th root in `F_1153`. -/
theorem invariantRatio_439_sq_pow32_eq_one_zmod1153 :
    invariantRatio (439 : ZMod 1153) ((439 : ZMod 1153) ^ 2) ^ 32 = 1 := by
  decide

/-- The four finite exceptions in the `n = 32` canonical obstruction theorem are genuine:
each characteristic supports a primitive 32-th root at which the denominator-free canonical
collision holds. -/
theorem exists_primitive_polynomial_eq_zmod32_badPrimes :
    (∃ ζ : ZMod 97, IsPrimitiveRoot ζ 32 ∧
      (ζ ^ 4 + 1) ^ 32 = (ζ ^ 2 + 1) ^ 32) ∧
    (∃ ζ : ZMod 641, IsPrimitiveRoot ζ 32 ∧
      (ζ ^ 4 + 1) ^ 32 = (ζ ^ 2 + 1) ^ 32) ∧
    (∃ ζ : ZMod 673, IsPrimitiveRoot ζ 32 ∧
      (ζ ^ 4 + 1) ^ 32 = (ζ ^ 2 + 1) ^ 32) ∧
    (∃ ζ : ZMod 1153, IsPrimitiveRoot ζ 32 ∧
      (ζ ^ 4 + 1) ^ 32 = (ζ ^ 2 + 1) ^ 32) :=
  ⟨⟨28, isPrimitiveRoot_28_32_bad_ratio_zmod97, polynomial_eq_28_sq_pow32_zmod97⟩,
    ⟨25, isPrimitiveRoot_25_32_bad_ratio_zmod641, polynomial_eq_25_sq_pow32_zmod641⟩,
    ⟨149, isPrimitiveRoot_149_32_bad_ratio_zmod673, polynomial_eq_149_sq_pow32_zmod673⟩,
    ⟨439, isPrimitiveRoot_439_32_bad_ratio_zmod1153, polynomial_eq_439_sq_pow32_zmod1153⟩⟩

end ConcreteN32BadPrimeCollapses

end ArkLib.ProximityGap.E2W4CyclotomicNonCollision

namespace ArkLib.ProximityGap.E2W4CyclotomicNonCollision

#print axioms orderOf_21_ratio_zmod1217
#print axioms isPrimitiveRoot_21_32_ratio_zmod1217
#print axioms exists_mu32_width4_refuter_zmod1217
#print axioms orderOf_57211_ratio_zmod1048609
#print axioms isPrimitiveRoot_57211_32_ratio_zmod1048609
#print axioms exists_mu32_width4_refuter_zmod1048609
#print axioms orderOf_28_bad_ratio_zmod97
#print axioms isPrimitiveRoot_28_32_bad_ratio_zmod97
#print axioms polynomial_eq_28_sq_pow32_zmod97
#print axioms invariantRatio_28_sq_pow32_eq_one_zmod97
#print axioms orderOf_25_bad_ratio_zmod641
#print axioms isPrimitiveRoot_25_32_bad_ratio_zmod641
#print axioms polynomial_eq_25_sq_pow32_zmod641
#print axioms invariantRatio_25_sq_pow32_eq_one_zmod641
#print axioms orderOf_149_bad_ratio_zmod673
#print axioms isPrimitiveRoot_149_32_bad_ratio_zmod673
#print axioms polynomial_eq_149_sq_pow32_zmod673
#print axioms invariantRatio_149_sq_pow32_eq_one_zmod673
#print axioms orderOf_439_bad_ratio_zmod1153
#print axioms isPrimitiveRoot_439_32_bad_ratio_zmod1153
#print axioms polynomial_eq_439_sq_pow32_zmod1153
#print axioms invariantRatio_439_sq_pow32_eq_one_zmod1153
#print axioms exists_primitive_polynomial_eq_zmod32_badPrimes

end ArkLib.ProximityGap.E2W4CyclotomicNonCollision
