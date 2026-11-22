/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.RatioProductNorm

/-! # Integer norm sieves for admissible products of site ratios -/

namespace ProximityGap.RatioProductNorm
open Polynomial ArkLib.ProximityGap.Frontier.DyadicFrobeniusNorm

/-- A nonzero integer norm precluding the square of the source prime suffices
to transfer a profile comparison to any primitive root of the same order. -/
theorem transfer_of_sieve {p n s : ℕ} [Fact p.Prime] [NeZero n] [NeZero (n : ZMod p)]
    {F : Type*} [Field F] [NeZero (n : F)] (hn : 2<n)
    {z : ZMod p} {w : F} (hz : IsPrimitiveRoot z n) (hw : IsPrimitiveRoot w n)
    (d : ℕ) (a b : Fin s → ℕ)
    (ha : ∀ i,z^(a i) ≠ z^d) (hb : ∀ i,z^(b i) ≠ z^d)
    (ha' : ∀ i,w^(a i) ≠ w^d) (hb' : ∀ i,w^(b i) ≠ w^d)
    (same : profile z d a = profile z d b)
    (sieve : cycloNorm n (difference a b d) ≠ 0 →
      ¬ p^2 ∣ (cycloNorm n (difference a b d)).natAbs) :
    profile w d a = profile w d b := by
  have nz : z≠0 := by
    intro zero
    have impossible := hz.pow_eq_one
    simp [zero,NeZero.ne n] at impossible
  have rev : profile z⁻¹ d a = profile z⁻¹ d b := by rw [profile_inverse nz,profile_inverse nz,same]
  have direct := (difference_zero_iff z d a b ha hb).mpr same
  have reverse := (difference_zero_iff z⁻¹ d a b
    (fun i => by simpa only [inv_pow,ne_eq,inv_inj] using ha i)
    (fun i => by simpa only [inv_pow,ne_eq,inv_inj] using hb i)).mpr rev
  have div := square_dvd_of_reciprocal_roots hn hz _ direct reverse
  apply (difference_zero_iff w d a b ha' hb').mp
  apply eval_zero_of_cyclo_dvd hw
  apply dvd_of_norm_zero
  by_contra nonzero
  apply sieve nonzero
  simpa only [Int.natAbs_pow,Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr div

/-- Remove an explicitly certified power of two before testing the norm
against the square of the split odd prime. -/
theorem sieve_of_odd_bound {p N v m : ℕ} (prime : p.Prime) (odd : p≠2)
    (factor : N=2^v*m) (small : m<p^2) (nonzero : N≠0) : ¬p^2∣N := by
  have cop : Nat.Coprime p 2 := Nat.coprime_primes prime Nat.prime_two |>.mpr odd
  have mm : m≠0 := by intro h; simp [h] at factor; exact nonzero factor
  intro h
  rw [factor] at h
  have divides : p^2 ∣ m := (cop.pow_left 2 |>.pow_right v).dvd_of_dvd_mul_left h
  exact (not_le_of_gt small) (Nat.le_of_dvd (Nat.pos_of_ne_zero mm) divides)

end ProximityGap.RatioProductNorm

#print axioms ProximityGap.RatioProductNorm.transfer_of_sieve
#print axioms ProximityGap.RatioProductNorm.sieve_of_odd_bound
