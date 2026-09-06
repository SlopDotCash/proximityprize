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

section Concrete4289Ratio

local instance fact_prime_4289_ratio : Fact (Nat.Prime 4289) := ⟨by norm_num⟩

/-- A concrete primitive 64-th root in `F_4289`. -/
theorem orderOf_56_ratio_zmod4289 : orderOf (56 : ZMod 4289) = 64 := by
  have h32 : ¬ (56 : ZMod 4289) ^ (2 : ℕ) ^ 5 = 1 := by decide
  have h64 : (56 : ZMod 4289) ^ (2 : ℕ) ^ 6 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (56 : ZMod 4289)) h32 h64
  norm_num at h
  exact h

/-- `56` is a primitive 64-th root in `F_4289`. -/
theorem isPrimitiveRoot_56_64_ratio_zmod4289 :
    IsPrimitiveRoot (56 : ZMod 4289) 64 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_56_ratio_zmod4289

/-- The denominator-free canonical width-four obstruction is nonzero for the concrete
`n = 64` Thorner-Zaman β=2 witness. -/
theorem polynomial_56_sq_pow64_ne_zmod4289 :
    ((56 : ZMod 4289) ^ 4 + 1) ^ 64 ≠
      ((56 : ZMod 4289) ^ 2 + 1) ^ 64 := by
  decide

/-- Concrete `n = 64` width-4 refuter in the small `β = 2` Thorner-Zaman row. -/
theorem exists_mu64_width4_refuter_zmod4289 :
    ∃ ζ : ZMod 4289, IsPrimitiveRoot ζ 64 ∧
      ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 64 (1 : ZMod 4289)) 4).card ≤ 64 := by
  exact ⟨56, isPrimitiveRoot_56_64_ratio_zmod4289,
    not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_polynomialNe
      (F := ZMod 4289) (n := 64) (ζ := (56 : ZMod 4289))
      (by norm_num) (by norm_num) (by norm_num)
      isPrimitiveRoot_56_64_ratio_zmod4289
      polynomial_56_sq_pow64_ne_zmod4289⟩

end Concrete4289Ratio

section Concrete17921Ratio

local instance fact_prime_17921_ratio : Fact (Nat.Prime 17921) := ⟨by norm_num⟩

/-- A concrete primitive 128-th root in `F_17921`. -/
theorem orderOf_244_ratio_zmod17921 : orderOf (244 : ZMod 17921) = 128 := by
  have h64 : ¬ (244 : ZMod 17921) ^ (2 : ℕ) ^ 6 = 1 := by decide
  have h128 : (244 : ZMod 17921) ^ (2 : ℕ) ^ 7 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (244 : ZMod 17921)) h64 h128
  norm_num at h
  exact h

/-- `244` is a primitive 128-th root in `F_17921`. -/
theorem isPrimitiveRoot_244_128_ratio_zmod17921 :
    IsPrimitiveRoot (244 : ZMod 17921) 128 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_244_ratio_zmod17921

set_option maxRecDepth 4096

/-- The denominator-free canonical width-four obstruction is nonzero for the concrete
`n = 128` Thorner-Zaman β=2 witness. -/
theorem polynomial_244_sq_pow128_ne_zmod17921 :
    ((244 : ZMod 17921) ^ 4 + 1) ^ 128 ≠
      ((244 : ZMod 17921) ^ 2 + 1) ^ 128 := by
  decide

set_option maxRecDepth 1000

/-- Concrete `n = 128` width-4 refuter in the small `β = 2` Thorner-Zaman row. -/
theorem exists_mu128_width4_refuter_zmod17921 :
    ∃ ζ : ZMod 17921, IsPrimitiveRoot ζ 128 ∧
      ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 128 (1 : ZMod 17921)) 4).card ≤ 128 := by
  exact ⟨244, isPrimitiveRoot_244_128_ratio_zmod17921,
    not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_polynomialNe
      (F := ZMod 17921) (n := 128) (ζ := (244 : ZMod 17921))
      (by norm_num) (by norm_num) (by norm_num)
      isPrimitiveRoot_244_128_ratio_zmod17921
      polynomial_244_sq_pow128_ne_zmod17921⟩

end Concrete17921Ratio

set_option maxRecDepth 8192

section Concrete65537Ratio

local instance fact_prime_65537_ratio : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

/-- A concrete primitive 256-th root in `F_65537`. -/
theorem orderOf_141_ratio_zmod65537 : orderOf (141 : ZMod 65537) = 256 := by
  have h128 : ¬ (141 : ZMod 65537) ^ (2 : ℕ) ^ 7 = 1 := by decide
  have h256 : (141 : ZMod 65537) ^ (2 : ℕ) ^ 8 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (141 : ZMod 65537)) h128 h256
  norm_num at h
  exact h

/-- `141` is a primitive 256-th root in `F_65537`. -/
theorem isPrimitiveRoot_141_256_ratio_zmod65537 :
    IsPrimitiveRoot (141 : ZMod 65537) 256 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_141_ratio_zmod65537

/-- The denominator-free canonical width-four obstruction is nonzero for the concrete
`n = 256` Thorner-Zaman β=2 witness. -/
theorem polynomial_141_sq_pow256_ne_zmod65537 :
    ((141 : ZMod 65537) ^ 4 + 1) ^ 256 ≠
      ((141 : ZMod 65537) ^ 2 + 1) ^ 256 := by
  decide

/-- Concrete `n = 256` width-4 refuter in the small `β = 2` Thorner-Zaman row. -/
theorem exists_mu256_width4_refuter_zmod65537 :
    ∃ ζ : ZMod 65537, IsPrimitiveRoot ζ 256 ∧
      ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 256 (1 : ZMod 65537)) 4).card ≤ 256 := by
  exact ⟨141, isPrimitiveRoot_141_256_ratio_zmod65537,
    not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_polynomialNe
      (F := ZMod 65537) (n := 256) (ζ := (141 : ZMod 65537))
      (by norm_num) (by norm_num) (by norm_num)
      isPrimitiveRoot_141_256_ratio_zmod65537
      polynomial_141_sq_pow256_ne_zmod65537⟩

end Concrete65537Ratio

set_option maxRecDepth 8192

section Concrete262657Ratio

local instance fact_prime_262657_ratio : Fact (Nat.Prime 262657) := ⟨by norm_num⟩

/-- A concrete primitive 512-th root in `F_262657`. -/
theorem orderOf_1055_ratio_zmod262657 : orderOf (1055 : ZMod 262657) = 512 := by
  have h256 : ¬ (1055 : ZMod 262657) ^ (2 : ℕ) ^ 8 = 1 := by decide
  have h512 : (1055 : ZMod 262657) ^ (2 : ℕ) ^ 9 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (1055 : ZMod 262657)) h256 h512
  norm_num at h
  exact h

/-- `1055` is a primitive 512-th root in `F_262657`. -/
theorem isPrimitiveRoot_1055_512_ratio_zmod262657 :
    IsPrimitiveRoot (1055 : ZMod 262657) 512 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_1055_ratio_zmod262657

/-- The denominator-free canonical width-four obstruction is nonzero for the concrete
`n = 512` Thorner-Zaman β=2 witness. -/
theorem polynomial_1055_sq_pow512_ne_zmod262657 :
    ((1055 : ZMod 262657) ^ 4 + 1) ^ 512 ≠
      ((1055 : ZMod 262657) ^ 2 + 1) ^ 512 := by
  decide

/-- Concrete `n = 512` width-4 refuter in the small `β = 2` Thorner-Zaman row. -/
theorem exists_mu512_width4_refuter_zmod262657 :
    ∃ ζ : ZMod 262657, IsPrimitiveRoot ζ 512 ∧
      ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 512 (1 : ZMod 262657)) 4).card ≤ 512 := by
  exact ⟨1055, isPrimitiveRoot_1055_512_ratio_zmod262657,
    not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_polynomialNe
      (F := ZMod 262657) (n := 512) (ζ := (1055 : ZMod 262657))
      (by norm_num) (by norm_num) (by norm_num)
      isPrimitiveRoot_1055_512_ratio_zmod262657
      polynomial_1055_sq_pow512_ne_zmod262657⟩

end Concrete262657Ratio

section Concrete1053697Ratio

local instance fact_prime_1053697_ratio : Fact (Nat.Prime 1053697) := ⟨by norm_num⟩

/-- A concrete primitive 1024-th root in `F_1053697`. -/
theorem orderOf_80_ratio_zmod1053697 : orderOf (80 : ZMod 1053697) = 1024 := by
  have h512 : ¬ (80 : ZMod 1053697) ^ (2 : ℕ) ^ 9 = 1 := by decide
  have h1024 : (80 : ZMod 1053697) ^ (2 : ℕ) ^ 10 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (80 : ZMod 1053697)) h512 h1024
  norm_num at h
  exact h

/-- `80` is a primitive 1024-th root in `F_1053697`. -/
theorem isPrimitiveRoot_80_1024_ratio_zmod1053697 :
    IsPrimitiveRoot (80 : ZMod 1053697) 1024 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_80_ratio_zmod1053697

/-- The denominator-free canonical width-four obstruction is nonzero for the concrete
`n = 1024` Thorner-Zaman β=2 witness. -/
theorem polynomial_80_sq_pow1024_ne_zmod1053697 :
    ((80 : ZMod 1053697) ^ 4 + 1) ^ 1024 ≠
      ((80 : ZMod 1053697) ^ 2 + 1) ^ 1024 := by
  decide

/-- Concrete `n = 1024` width-4 refuter in the small β=2 Thorner-Zaman row. -/
theorem exists_mu1024_width4_refuter_zmod1053697 :
    ∃ ζ : ZMod 1053697, IsPrimitiveRoot ζ 1024 ∧
      ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 1024 (1 : ZMod 1053697)) 4).card ≤ 1024 := by
  exact ⟨80, isPrimitiveRoot_80_1024_ratio_zmod1053697,
    not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_polynomialNe
      (F := ZMod 1053697) (n := 1024) (ζ := (80 : ZMod 1053697))
      (by norm_num) (by norm_num) (by norm_num)
      isPrimitiveRoot_80_1024_ratio_zmod1053697
      polynomial_80_sq_pow1024_ne_zmod1053697⟩

end Concrete1053697Ratio

set_option maxRecDepth 131072

section Concrete4206593Ratio

local instance fact_prime_4206593_ratio : Fact (Nat.Prime 4206593) := ⟨by norm_num⟩

/-- A concrete primitive 2048-th root in `F_4206593`. -/
theorem orderOf_207446_ratio_zmod4206593 : orderOf (207446 : ZMod 4206593) = 2048 := by
  have h1024 : ¬ (207446 : ZMod 4206593) ^ (2 : ℕ) ^ 10 = 1 := by decide
  have h2048 : (207446 : ZMod 4206593) ^ (2 : ℕ) ^ 11 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (207446 : ZMod 4206593)) h1024 h2048
  norm_num at h
  exact h

/-- `207446` is a primitive 2048-th root in `F_4206593`. -/
theorem isPrimitiveRoot_207446_2048_ratio_zmod4206593 :
    IsPrimitiveRoot (207446 : ZMod 4206593) 2048 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_207446_ratio_zmod4206593

/-- The denominator-free canonical width-four obstruction is nonzero for the concrete
`n = 2048` Thorner-Zaman β=2 witness. -/
theorem polynomial_207446_sq_pow2048_ne_zmod4206593 :
    ((207446 : ZMod 4206593) ^ 4 + 1) ^ 2048 ≠
      ((207446 : ZMod 4206593) ^ 2 + 1) ^ 2048 := by
  decide

/-- Concrete `n = 2048` width-4 refuter in the small β=2 Thorner-Zaman row. -/
theorem exists_mu2048_width4_refuter_zmod4206593 :
    ∃ ζ : ZMod 4206593, IsPrimitiveRoot ζ 2048 ∧
      ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 2048 (1 : ZMod 4206593)) 4).card ≤ 2048 := by
  exact ⟨207446, isPrimitiveRoot_207446_2048_ratio_zmod4206593,
    not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_polynomialNe
      (F := ZMod 4206593) (n := 2048) (ζ := (207446 : ZMod 4206593))
      (by norm_num) (by norm_num) (by norm_num)
      isPrimitiveRoot_207446_2048_ratio_zmod4206593
      polynomial_207446_sq_pow2048_ne_zmod4206593⟩

end Concrete4206593Ratio

section Concrete16957441Ratio

local instance fact_prime_16957441_ratio : Fact (Nat.Prime 16957441) := ⟨by norm_num⟩

/-- A concrete primitive 4096-th root in `F_16957441`. -/
theorem orderOf_233_ratio_zmod16957441 : orderOf (233 : ZMod 16957441) = 4096 := by
  have h2048 : ¬ (233 : ZMod 16957441) ^ (2 : ℕ) ^ 11 = 1 := by decide
  have h4096 : (233 : ZMod 16957441) ^ (2 : ℕ) ^ 12 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (233 : ZMod 16957441)) h2048 h4096
  norm_num at h
  exact h

/-- `233` is a primitive 4096-th root in `F_16957441`. -/
theorem isPrimitiveRoot_233_4096_ratio_zmod16957441 :
    IsPrimitiveRoot (233 : ZMod 16957441) 4096 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_233_ratio_zmod16957441

/-- The denominator-free canonical width-four obstruction is nonzero for the concrete
`n = 4096` Thorner-Zaman β=2 witness. -/
theorem polynomial_233_sq_pow4096_ne_zmod16957441 :
    ((233 : ZMod 16957441) ^ 4 + 1) ^ 4096 ≠
      ((233 : ZMod 16957441) ^ 2 + 1) ^ 4096 := by
  decide

/-- Concrete `n = 4096` width-4 refuter in the small β=2 Thorner-Zaman row. -/
theorem exists_mu4096_width4_refuter_zmod16957441 :
    ∃ ζ : ZMod 16957441, IsPrimitiveRoot ζ 4096 ∧
      ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 4096 (1 : ZMod 16957441)) 4).card ≤ 4096 := by
  exact ⟨233, isPrimitiveRoot_233_4096_ratio_zmod16957441,
    not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_polynomialNe
      (F := ZMod 16957441) (n := 4096) (ζ := (233 : ZMod 16957441))
      (by norm_num) (by norm_num) (by norm_num)
      isPrimitiveRoot_233_4096_ratio_zmod16957441
      polynomial_233_sq_pow4096_ne_zmod16957441⟩

end Concrete16957441Ratio

section Concrete67731457Ratio

local instance fact_prime_67731457_ratio : Fact (Nat.Prime 67731457) := ⟨by norm_num⟩

/-- A concrete primitive 8192-th root in `F_67731457`. -/
theorem orderOf_4859_ratio_zmod67731457 : orderOf (4859 : ZMod 67731457) = 8192 := by
  have h4096 : ¬ (4859 : ZMod 67731457) ^ (2 : ℕ) ^ 12 = 1 := by decide
  have h8192 : (4859 : ZMod 67731457) ^ (2 : ℕ) ^ 13 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (4859 : ZMod 67731457)) h4096 h8192
  norm_num at h
  exact h

/-- `4859` is a primitive 8192-th root in `F_67731457`. -/
theorem isPrimitiveRoot_4859_8192_ratio_zmod67731457 :
    IsPrimitiveRoot (4859 : ZMod 67731457) 8192 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_4859_ratio_zmod67731457

/-- The denominator-free canonical width-four obstruction is nonzero for the concrete
`n = 8192` Thorner-Zaman β=2 witness. -/
theorem polynomial_4859_sq_pow8192_ne_zmod67731457 :
    ((4859 : ZMod 67731457) ^ 4 + 1) ^ 8192 ≠
      ((4859 : ZMod 67731457) ^ 2 + 1) ^ 8192 := by
  decide

/-- Concrete `n = 8192` width-4 refuter in the small β=2 Thorner-Zaman row. -/
theorem exists_mu8192_width4_refuter_zmod67731457 :
    ∃ ζ : ZMod 67731457, IsPrimitiveRoot ζ 8192 ∧
      ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 8192 (1 : ZMod 67731457)) 4).card ≤ 8192 := by
  exact ⟨4859, isPrimitiveRoot_4859_8192_ratio_zmod67731457,
    not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_polynomialNe
      (F := ZMod 67731457) (n := 8192) (ζ := (4859 : ZMod 67731457))
      (by norm_num) (by norm_num) (by norm_num)
      isPrimitiveRoot_4859_8192_ratio_zmod67731457
      polynomial_4859_sq_pow8192_ne_zmod67731457⟩

end Concrete67731457Ratio

section Concrete268730369Ratio

local instance fact_prime_268730369_ratio : Fact (Nat.Prime 268730369) := ⟨by norm_num⟩

/-- A concrete primitive 16384-th root in `F_268730369`. -/
theorem orderOf_1678_ratio_zmod268730369 : orderOf (1678 : ZMod 268730369) = 16384 := by
  have h8192 : ¬ (1678 : ZMod 268730369) ^ (2 : ℕ) ^ 13 = 1 := by decide
  have h16384 : (1678 : ZMod 268730369) ^ (2 : ℕ) ^ 14 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (1678 : ZMod 268730369)) h8192 h16384
  norm_num at h
  exact h

/-- `1678` is a primitive 16384-th root in `F_268730369`. -/
theorem isPrimitiveRoot_1678_16384_ratio_zmod268730369 :
    IsPrimitiveRoot (1678 : ZMod 268730369) 16384 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_1678_ratio_zmod268730369

/-- The denominator-free canonical width-four obstruction is nonzero for the concrete
`n = 16384` Thorner-Zaman β=2 witness. -/
theorem polynomial_1678_sq_pow16384_ne_zmod268730369 :
    ((1678 : ZMod 268730369) ^ 4 + 1) ^ 16384 ≠
      ((1678 : ZMod 268730369) ^ 2 + 1) ^ 16384 := by
  decide

/-- Concrete `n = 16384` width-4 refuter in the small β=2 Thorner-Zaman row. -/
theorem exists_mu16384_width4_refuter_zmod268730369 :
    ∃ ζ : ZMod 268730369, IsPrimitiveRoot ζ 16384 ∧
      ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 16384 (1 : ZMod 268730369)) 4).card ≤
        16384 := by
  exact ⟨1678, isPrimitiveRoot_1678_16384_ratio_zmod268730369,
    not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_polynomialNe
      (F := ZMod 268730369) (n := 16384) (ζ := (1678 : ZMod 268730369))
      (by norm_num) (by norm_num) (by norm_num)
      isPrimitiveRoot_1678_16384_ratio_zmod268730369
      polynomial_1678_sq_pow16384_ne_zmod268730369⟩

end Concrete268730369Ratio

set_option maxRecDepth 262144

section Concrete1073872897Ratio

local instance fact_prime_1073872897_ratio : Fact (Nat.Prime 1073872897) := ⟨by norm_num⟩

/-- A concrete primitive 32768-th root in `F_1073872897`. -/
theorem orderOf_2521228_ratio_zmod1073872897 :
    orderOf (2521228 : ZMod 1073872897) = 32768 := by
  have h16384 : ¬ (2521228 : ZMod 1073872897) ^ (2 : ℕ) ^ 14 = 1 := by decide
  have h32768 : (2521228 : ZMod 1073872897) ^ (2 : ℕ) ^ 15 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (2521228 : ZMod 1073872897)) h16384 h32768
  norm_num at h
  exact h

/-- `2521228` is a primitive 32768-th root in `F_1073872897`. -/
theorem isPrimitiveRoot_2521228_32768_ratio_zmod1073872897 :
    IsPrimitiveRoot (2521228 : ZMod 1073872897) 32768 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_2521228_ratio_zmod1073872897

/-- The denominator-free canonical width-four obstruction is nonzero for the concrete
`n = 32768` Thorner-Zaman β=2 witness. -/
theorem polynomial_2521228_sq_pow32768_ne_zmod1073872897 :
    ((2521228 : ZMod 1073872897) ^ 4 + 1) ^ 32768 ≠
      ((2521228 : ZMod 1073872897) ^ 2 + 1) ^ 32768 := by
  decide

/-- Concrete `n = 32768` width-4 refuter in the small β=2 Thorner-Zaman row. -/
theorem exists_mu32768_width4_refuter_zmod1073872897 :
    ∃ ζ : ZMod 1073872897, IsPrimitiveRoot ζ 32768 ∧
      ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 32768 (1 : ZMod 1073872897)) 4).card ≤
        32768 := by
  exact ⟨2521228, isPrimitiveRoot_2521228_32768_ratio_zmod1073872897,
    not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_polynomialNe
      (F := ZMod 1073872897) (n := 32768) (ζ := (2521228 : ZMod 1073872897))
      (by norm_num) (by norm_num) (by norm_num)
      isPrimitiveRoot_2521228_32768_ratio_zmod1073872897
      polynomial_2521228_sq_pow32768_ne_zmod1073872897⟩

end Concrete1073872897Ratio

set_option maxRecDepth 1000

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
#print axioms orderOf_56_ratio_zmod4289
#print axioms isPrimitiveRoot_56_64_ratio_zmod4289
#print axioms polynomial_56_sq_pow64_ne_zmod4289
#print axioms exists_mu64_width4_refuter_zmod4289
#print axioms orderOf_244_ratio_zmod17921
#print axioms isPrimitiveRoot_244_128_ratio_zmod17921
#print axioms polynomial_244_sq_pow128_ne_zmod17921
#print axioms exists_mu128_width4_refuter_zmod17921
#print axioms orderOf_141_ratio_zmod65537
#print axioms isPrimitiveRoot_141_256_ratio_zmod65537
#print axioms polynomial_141_sq_pow256_ne_zmod65537
#print axioms exists_mu256_width4_refuter_zmod65537
#print axioms orderOf_1055_ratio_zmod262657
#print axioms isPrimitiveRoot_1055_512_ratio_zmod262657
#print axioms polynomial_1055_sq_pow512_ne_zmod262657
#print axioms exists_mu512_width4_refuter_zmod262657
#print axioms orderOf_80_ratio_zmod1053697
#print axioms isPrimitiveRoot_80_1024_ratio_zmod1053697
#print axioms polynomial_80_sq_pow1024_ne_zmod1053697
#print axioms exists_mu1024_width4_refuter_zmod1053697
#print axioms orderOf_207446_ratio_zmod4206593
#print axioms isPrimitiveRoot_207446_2048_ratio_zmod4206593
#print axioms polynomial_207446_sq_pow2048_ne_zmod4206593
#print axioms exists_mu2048_width4_refuter_zmod4206593
#print axioms orderOf_233_ratio_zmod16957441
#print axioms isPrimitiveRoot_233_4096_ratio_zmod16957441
#print axioms polynomial_233_sq_pow4096_ne_zmod16957441
#print axioms exists_mu4096_width4_refuter_zmod16957441
#print axioms orderOf_4859_ratio_zmod67731457
#print axioms isPrimitiveRoot_4859_8192_ratio_zmod67731457
#print axioms polynomial_4859_sq_pow8192_ne_zmod67731457
#print axioms exists_mu8192_width4_refuter_zmod67731457
#print axioms orderOf_1678_ratio_zmod268730369
#print axioms isPrimitiveRoot_1678_16384_ratio_zmod268730369
#print axioms polynomial_1678_sq_pow16384_ne_zmod268730369
#print axioms exists_mu16384_width4_refuter_zmod268730369
#print axioms orderOf_2521228_ratio_zmod1073872897
#print axioms isPrimitiveRoot_2521228_32768_ratio_zmod1073872897
#print axioms polynomial_2521228_sq_pow32768_ne_zmod1073872897
#print axioms exists_mu32768_width4_refuter_zmod1073872897
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
