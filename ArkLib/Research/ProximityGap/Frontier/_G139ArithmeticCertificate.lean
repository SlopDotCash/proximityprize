/-
Copyright (c) 2026 ArkLib Contributors, lucascantship. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors, lucascantship
-/
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
import ArkLib.Research.ProximityGap.Frontier._G139PhiInjectiveSidonBridge
import ArkLib.Research.ProximityGap.Support.BinaryPower

/-!
# G139: kernel-checked production arithmetic

Certifies the exact modulus and generator used by
`scripts/probes/verify_g139_n2e30_arithmetic_contract.py`, not either of the two different
moduli in `_PrizeShapePrimeP30.lean` and `_PrizeShapePrimeP30Second.lean`.

The complete factorizations give five nested Lucas certificates, with witnesses `2`, `11`, `7`,
`7`, and `10`. The shared square-and-multiply implementation lets the Lean kernel check every
modular identity.

The final theorem instantiates the existing G139 zero-accident bridge at these exact constants.
Its sole remaining hypothesis is `PhiWindowInjective g (2 ^ 30)`. This file does not prove that
injectivity, an unconditional energy bound, or the production delta-star claim.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace ArkLib.ProximityGap.Frontier.G139ArithmeticCertificate

/-- The exact modulus in the G139 production certificate. -/
abbrev P : ℕ := 365375409332725729550921208179070755196377235457

open ArkLib.ProximityGap.BinaryPower (binaryPow_eq_pow)

/-! ## The recursive prime-factor certificates -/

/-- The large factor in the next certificate has a short Lucas certificate of its own. -/
private theorem prime_1370701 : Nat.Prime 1370701 := by
  let Q : ℕ := 1370701
  have hmain : (2 : ZMod Q) ^ (Q - 1) = 1 := by
    rw [← binaryPow_eq_pow]
    decide
  refine lucas_primality Q 2 hmain ?_
  intro q hq hdvd
  rw [show Q - 1 = 2 * (2 * (3 * (3 * (5 * (5 * 1523))))) from by norm_num] at hdvd
  simp only [Nat.Prime.dvd_mul hq,
    Nat.prime_dvd_prime_iff_eq hq Nat.prime_two,
    Nat.prime_dvd_prime_iff_eq hq Nat.prime_three,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 1523)] at hdvd
  rcases hdvd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rw [← binaryPow_eq_pow]; decide

private theorem prime_1052698369 : Nat.Prime 1052698369 := by
  let Q : ℕ := 1052698369
  have hmain : (11 : ZMod Q) ^ (Q - 1) = 1 := by
    rw [← binaryPow_eq_pow]
    decide
  refine lucas_primality Q 11 hmain ?_
  intro q hq hdvd
  rw [show Q - 1 = 2 ^ 8 * (3 * 1370701) from by norm_num] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with htwo | hodd
  · have heq : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow htwo)
    subst q
    rw [← binaryPow_eq_pow]
    decide
  · simp only [Nat.Prime.dvd_mul hq,
      Nat.prime_dvd_prime_iff_eq hq Nat.prime_three,
      Nat.prime_dvd_prime_iff_eq hq prime_1370701] at hodd
    rcases hodd with rfl | rfl
    all_goals rw [← binaryPow_eq_pow]; decide

private theorem prime_15132351674065319 : Nat.Prime 15132351674065319 := by
  let Q : ℕ := 15132351674065319
  have hmain : (7 : ZMod Q) ^ (Q - 1) = 1 := by
    rw [← binaryPow_eq_pow]
    decide
  refine lucas_primality Q 7 hmain ?_
  intro q hq hdvd
  rw [show Q - 1 = 2 * (7 * (11 * (269 * (347 * 1052698369)))) from by norm_num] at hdvd
  simp only [Nat.Prime.dvd_mul hq,
    Nat.prime_dvd_prime_iff_eq hq Nat.prime_two,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 269),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 347),
    Nat.prime_dvd_prime_iff_eq hq prime_1052698369] at hdvd
  rcases hdvd with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rw [← binaryPow_eq_pow]; decide

private theorem prime_111774359022899775527551 : Nat.Prime 111774359022899775527551 := by
  let Q : ℕ := 111774359022899775527551
  have hmain : (7 : ZMod Q) ^ (Q - 1) = 1 := by
    rw [← binaryPow_eq_pow]
    decide
  refine lucas_primality Q 7 hmain ?_
  intro q hq hdvd
  rw [show Q - 1 = 2 * (3 * (5 * (5 * (23 * (2141 * 15132351674065319)))))
    from by norm_num] at hdvd
  simp only [Nat.Prime.dvd_mul hq,
    Nat.prime_dvd_prime_iff_eq hq Nat.prime_two,
    Nat.prime_dvd_prime_iff_eq hq Nat.prime_three,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 23),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2141),
    Nat.prime_dvd_prime_iff_eq hq prime_15132351674065319] at hdvd
  rcases hdvd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rw [← binaryPow_eq_pow]; decide

/-- The production modulus is prime, by its complete Lucas certificate with witness `10`. -/
theorem prime_P : Nat.Prime P := by
  have hmain : (10 : ZMod P) ^ (P - 1) = 1 := by
    rw [← binaryPow_eq_pow]
    decide
  refine lucas_primality P 10 hmain ?_
  intro q hq hdvd
  rw [show P - 1 = 2 ^ 30 * (3 * (23 * (37 * (3251 * (11633 *
    (31531 * 111774359022899775527551)))))) from by norm_num] at hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with htwo | hodd
  · have heq : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow htwo)
    subst q
    rw [← binaryPow_eq_pow]
    decide
  · simp only [Nat.Prime.dvd_mul hq,
      Nat.prime_dvd_prime_iff_eq hq Nat.prime_three,
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 23),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 37),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3251),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11633),
      Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 31531),
      Nat.prime_dvd_prime_iff_eq hq prime_111774359022899775527551] at hodd
    rcases hodd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [← binaryPow_eq_pow]; decide

/-- The production certificate's advertised cofactor and smooth subgroup size. -/
theorem P_eq_prize_shape : P = 2 ^ 30 * (2 ^ 128 + 263) + 1 := by norm_num

/-- The certified prime supplies the field structure without an external primality assumption. -/
instance fact_prime_P : Fact (Nat.Prime P) := ⟨prime_P⟩

/-- The exact generator recorded by the G139 production verifier. -/
abbrev g : ZMod P := 26841566604131443990650262696798142924116991820

/-- The published generator satisfies the full smooth-order relation. -/
theorem g_pow_30_eq_one : g ^ (2 : ℕ) ^ 30 = 1 := by
  rw [← binaryPow_eq_pow]
  decide

/-- The half-order power is minus one, excluding every proper divisor of the dyadic order. -/
theorem g_pow_29_eq_neg_one : g ^ (2 : ℕ) ^ 29 = -1 := by
  rw [← binaryPow_eq_pow]
  decide

/-- The published G139 generator has exact order `2^30`. -/
theorem orderOf_g : orderOf g = 2 ^ 30 := by
  have hhalf : g ^ (2 : ℕ) ^ 29 ≠ 1 := by
    rw [g_pow_29_eq_neg_one]
    decide
  have h := orderOf_eq_prime_pow (x := g) hhalf g_pow_30_eq_one
  norm_num at h ⊢
  exact h

/-! ## Discharging the arithmetic inputs of the existing production bridge -/

open ArkLib.ProximityGap.Frontier.G136LawfulCount
open ArkLib.ProximityGap.Frontier.G136ProductionInstantiation
open ArkLib.ProximityGap.Frontier.G139PhiInjectiveSidonBridge

/-- The concrete primitive root required by the production root-set lemmas. -/
theorem isPrimitiveRoot_g : IsPrimitiveRoot g (2 ^ 30) :=
  IsPrimitiveRoot.iff_orderOf.mpr orderOf_g

/-- For the certified arithmetic row, only finite `Phi` injectivity remains for zero accidents. -/
theorem accidents_card_eq_zero_of_phiWindowInjective
    (hPhi : PhiWindowInjective g (2 ^ 30)) :
    (accidents (rootsFinset g (2 ^ 30))).card = 0 :=
  accidents_card_eq_zero_rootsFinset_of_exactOrder_phiWindowInjective
    g_pow_30_eq_one
    (by norm_num) (by norm_num) (hasExactOrder_of_isPrimitiveRoot isPrimitiveRoot_g) hPhi

#print axioms prime_P
#print axioms orderOf_g
#print axioms accidents_card_eq_zero_of_phiWindowInjective

end ArkLib.ProximityGap.Frontier.G139ArithmeticCertificate
