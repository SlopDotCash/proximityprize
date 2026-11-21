/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: Proximity Prize contributors
-/
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
import ArkLib.Research.ProximityGap.Support.BinaryPower

/-! # An order-256 domain in the BLS12-381 scalar field

The complete factorization of the scalar modulus minus one and the integer 7
give a Lucas certificate. Raising 7 to the cofactor for 256 gives the
domain generator. Exponentiations are checked by binary powering in ZMod.
-/

namespace ProximityGap.BlsScalarSubgroup

open ArkLib.ProximityGap.BinaryPower (binaryPow binaryPow_eq_pow)

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Scalar modulus of BLS12-381. -/
abbrev P : ℕ := 52435875175126190479447740508185965837690552500527637822603658699938581184513

private def factors : List (ℕ × ℕ) :=
  [(2,32), (3,1), (11,1), (19,1), (10177,1), (125527,1), (859267,1),
   (906349,2), (2508409,1), (2529403,1), (52437899,1), (254760293,2)]

private def productPowers (f : List (ℕ × ℕ)) : ℕ :=
  (f.map fun v => v.1 ^ v.2).prod

private theorem mem_prime_factors {q : ℕ} (hq : q.Prime)
    (f : List (ℕ × ℕ)) (hpr : ∀ v ∈ f, Nat.Prime v.1) (hd : q ∣ productPowers f) :
    ∃ v ∈ f, q = v.1 := by
  induction f with
  | nil =>
    exact (hq.not_dvd_one (by simpa [productPowers] using hd)).elim
  | cons a f ih =>
    rcases hq.dvd_mul.mp (by simpa [productPowers] using hd :
        q ∣ a.1 ^ a.2 * productPowers f) with h | h
    · exact ⟨a, by simp, (Nat.prime_dvd_prime_iff_eq hq (hpr a (by simp))).mp
        (hq.dvd_of_dvd_pow h)⟩
    · obtain ⟨v, hv, he⟩ := ih (fun v hv => hpr v (by simp [hv])) h
      exact ⟨v, by simp [hv], he⟩

private theorem factors_prime : ∀ v ∈ factors, Nat.Prime v.1 := by
  intro v hv
  simp only [factors, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with h|h|h|h|h|h|h|h|h|h|h|h <;> subst v <;> norm_num

/-- The scalar modulus is prime by the Lucas criterion with full-order witness 7. -/
theorem prime_P : P.Prime := by
  have hproduct : P - 1 = productPowers factors := by decide
  have hmain : (7 : ZMod P) ^ (P-1) = 1 := by
    rw [← binaryPow_eq_pow]
    decide
  have htests : factors.all (fun v => decide
      (binaryPow (7 : ZMod P) ((P-1) / v.1) ≠ 1)) = true := by decide
  refine lucas_primality P 7 hmain ?_
  intro q hq hd
  rw [hproduct] at hd
  obtain ⟨v, hv, rfl⟩ := mem_prime_factors hq factors factors_prime hd
  simpa [binaryPow_eq_pow] using of_decide_eq_true (List.all_eq_true.mp htests v hv)

instance fact_prime_P : Fact P.Prime := ⟨prime_P⟩

/-- Cofactor power of 7 giving order 256. -/
abbrev g : ZMod P :=
  36007022166693598376559747923784822035233416720563672082740011604939309541707

theorem g_eq_pow_seven : g = (7 : ZMod P) ^ ((P - 1) / 256) := by
  rw [← binaryPow_eq_pow]
  decide

theorem orderOf_g : orderOf g = 256 := by
  have hhalf : g ^ (2 : ℕ) ^ 7 ≠ 1 := by rw [← binaryPow_eq_pow]; decide
  have hfull : g ^ (2 : ℕ) ^ 8 = 1 := by rw [← binaryPow_eq_pow]; decide
  have h := orderOf_eq_prime_pow (x := g) hhalf hfull
  norm_num at h ⊢
  exact h

/-- Unit form of the generator for the subgroup of evaluation points. -/
def generator : (ZMod P)ˣ := Units.mk0 g (by decide)

theorem generator_order : orderOf generator = 256 := by
  rw [← orderOf_injective (Units.coeHom (ZMod P)) Units.val_injective generator]
  exact orderOf_g

#print axioms prime_P
#print axioms g_eq_pow_seven
#print axioms orderOf_g
#print axioms generator_order

end ProximityGap.BlsScalarSubgroup
