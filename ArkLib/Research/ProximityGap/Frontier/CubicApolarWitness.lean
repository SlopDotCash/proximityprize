/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic
import Mathlib.NumberTheory.LucasPrimality
import ArkLib.Research.ProximityGap.Support.BinaryPower

/-!
# A cubic-locator witness at the rate-half predecessor

The quotient of the evaluation-domain vanisher by a split locator is the
mixed-word discrepancy. The second row has too high a degree for any joint
explanation on the complementary witness set.
-/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.CubicApolarWitness
open Polynomial Finset

variable {F : Type*} [Field F]

/-- Ordinary polynomial division gives a single pair of rows independent of
the scalar t. Here Q is the complementary vanisher. -/
theorem fold_identity (V Q : F[X]) (t : F) (e L : ℕ)
    (hid : V*(X^3-C t) = Q*(X^(e+3)-C (t^L))) :
    (V*X^3) /ₘ X^(e+3) - C t*(V /ₘ X^(e+3)) =
        Q - C (t^L)*(Q /ₘ X^(e+3)) := by
  have h := congrArg (fun P : F[X] => P /ₘ X^(e+3)) hid
  simp only [mul_sub, sub_divByMonic] at h
  rw [mul_comm Q (X^(e+3)), mul_divByMonic_cancel_left _ (monic_X_pow _),
    mul_comm V (C t), mul_comm Q (C (t^L)), ← smul_eq_C_mul, ← smul_eq_C_mul,
    smul_divByMonic, smul_divByMonic, smul_eq_C_mul, smul_eq_C_mul] at h
  exact h

/-- At n=4(e+1), k=2(e+1), the mixed codeword agrees on the complement
of the locator and the second row has no codeword agreeing there. -/
theorem folding_without_joint (V Q : F[X]) (t : F) (e L : ℕ) (he : 2 ≤ e)
    (hV : V.natDegree=4*(e+1)) (hQ : Q.natDegree=4*(e+1)-e)
    (hid : V*(X^3-C t)=Q*(X^(e+3)-C (t^L)))
    (S : Finset F) (hS : S.card=4*(e+1)-e) (hz : ∀ x ∈ S, Q.eval x=0) :
    (∃ P : F[X], P.natDegree < 2*(e+1) ∧ ∀ x ∈ S, P.eval x =
      ((V*X^3) /ₘ X^(e+3)).eval x - t*(V /ₘ X^(e+3)).eval x) ∧
    ¬∃ P : F[X], P.natDegree < 2*(e+1) ∧ ∀ x ∈ S,
      P.eval x = -(V /ₘ X^(e+3)).eval x := by
  have hq : (Q /ₘ X^(e+3)).natDegree = 4*(e+1)-e-(e+3) := by
    rw [natDegree_divByMonic _ (monic_X_pow _), natDegree_X_pow, hQ]
  have hv : (V /ₘ X^(e+3)).natDegree = 4*(e+1)-(e+3) := by
    rw [natDegree_divByMonic _ (monic_X_pow _), natDegree_X_pow, hV]
  constructor
  · refine ⟨-(C (t^L)*(Q /ₘ X^(e+3))), ?_, ?_⟩
    · have h : (C (t^L)*(Q /ₘ X^(e+3))).natDegree ≤
            (C (t^L)).natDegree + (Q /ₘ X^(e+3)).natDegree := natDegree_mul_le
      simp only [natDegree_C, zero_add] at h
      rw [natDegree_neg]
      omega
    · intro x hx
      have h := congrArg (fun R : F[X] => R.eval x) (fold_identity V Q t e L hid)
      simpa [hz x hx] using h.symm
  · rintro ⟨P,hdeg,hagree⟩
    have h := eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (P + V /ₘ X^(e+3)) S (fun x hx => by simp [hagree x hx]) (by
        apply (natDegree_add_le ..).trans_lt
        rw [hS,hv]
        omega)
    have hP : P = -(V /ₘ X^(e+3)) := eq_neg_of_add_eq_zero_left h
    rw [hP,natDegree_neg,hv] at hdeg
    omega

/-- A production-length field with at most h+1 bad scalars allowed. -/
abbrev productionPrime : ℕ := 91343852673653315610116111617434743158930931713

open ArkLib.ProximityGap.BinaryPower (binaryPow_eq_pow)
set_option maxRecDepth 100000 in
private theorem primeFactor : Nat.Prime 5026338851119 := by
  apply lucas_primality 5026338851119 3 (by rw [← binaryPow_eq_pow]; decide)
  intro q hq hd
  rw [show 5026338851119 - 1 = 2*(3*(13*(240437*268013))) by decide] at hd
  simp only [hq.dvd_mul, Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 13),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 240437),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 268013)] at hd
  rcases hd with rfl|rfl|rfl|rfl|rfl <;> rw [← binaryPow_eq_pow] <;> decide

set_option maxRecDepth 100000 in
theorem productionPrime_prime : Nat.Prime productionPrime := by
  apply lucas_primality productionPrime 5 (by rw [← binaryPow_eq_pow]; decide)
  intro q hq hd
  rw [show productionPrime-1=2^84*(3^4*(7*(19*(87211*5026338851119)))) by decide] at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 19),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 87211),
    Nat.prime_dvd_prime_iff_eq hq primeFactor] at hd
  rcases hd with h|h|rfl|rfl|rfl|rfl
  · have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)
    subst q
    rw [← binaryPow_eq_pow]; decide
  · have := (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 3)).mp (hq.dvd_of_dvd_pow h)
    subst q
    rw [← binaryPow_eq_pow]; decide
  · rw [← binaryPow_eq_pow]; decide
  · rw [← binaryPow_eq_pow]; decide
  · rw [← binaryPow_eq_pow]; decide
  · rw [← binaryPow_eq_pow]; decide

/-- The production field has its prescribed budget, smooth subgroup, and the
three full cubic-coset orbits needed for the arbitrary evaluation domain. -/
theorem production_parameters :
    productionPrime / 2^128 = 268435457 ∧
    2^30 ∣ productionPrime-1 ∧ 268435458 ∣ productionPrime-1 ∧
    3*268435458 ≤ productionPrime-1 ∧ 3*268435458 ≤ 2^30 := by decide

/-- Representatives 1, 2 and 4 select three different core cosets. -/
theorem production_cosets :
    (2 : ZMod productionPrime)^268435458 ≠ 1 ∧
    (2 : ZMod productionPrime)^(2*268435458) ≠ 1 := by
  constructor <;> rw [← binaryPow_eq_pow] <;> decide

/-- Cubing the Corvaja–Zannier bound after applying Hölder: the linear
cutoff and the finite-characteristic correction at the named prime scale. -/
theorem small_component_arithmetic {a d : ℕ} (ha : a ≤ 466033) (hd : d ≤ a) :
    128*(36*a^3) ≤ 2^30*(a*(3*a-d)) ∧
    12*(2^30)^2*(a*(3*a-d))^2 < 2^158 := by
  have hdiff : 2*a ≤ 3*a-d := by omega
  have hcut : 2304*a ≤ 2^30 := by omega
  constructor
  · calc
      128*(36*a^3) = (2304*a)*(a*(2*a)) := by ring
      _ ≤ 2^30*(a*(3*a-d)) := Nat.mul_le_mul hcut (Nat.mul_le_mul_left _ hdiff)
  · have htop : 3*a-d ≤ 3*466033 := by omega
    have hD := Nat.mul_le_mul ha htop
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hD 2)).trans_lt (by decide)

/-- At full component degree, the characteristic term is still below
the extra ordered-pair observations from one more accepted parameter. -/
theorem full_component_characteristic {a d : ℕ} (ha : a ≤ 89478485) :
    4*(2^30)^2*(a*(3*a-d)) < 2^156 := by
  have htop : 3*a-d ≤ 3*89478485 := by omega
  exact (Nat.mul_le_mul_left _ (Nat.mul_le_mul ha htop)).trans_lt (by decide)

/-- The total ramification inequality forces a linear genus floor per component. -/
theorem component_genus_floor {a g : ℕ}
    (h : 2*(2^30)*a^2 < 384*a*(10*a+4*g)) : 8388593*a < 6*g := by
  have hh : a*((2*2^30)*a) < a*(384*(10*a+4*g)) := by
    convert h using 1 <;> ring
  have hl := Nat.lt_of_mul_lt_mul_left hh
  omega

#print axioms full_component_characteristic
#print axioms component_genus_floor
#print axioms small_component_arithmetic
#print axioms production_cosets
#print axioms productionPrime_prime
#print axioms production_parameters
#print axioms fold_identity
#print axioms folding_without_joint
end ArkLib.ProximityGap.Frontier.CubicApolarWitness
