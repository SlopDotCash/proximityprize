/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicChordEnergy

/-! # Simultaneous lower bounds for nonzero cyclotomic norms -/

namespace ProximityGap.JointMinorNorm
open Finset Polynomial ArkLib.ProximityGap.Frontier.DyadicFrobeniusNorm

/-- If a family of nonzero integral norms is divisible by the square of
the modulus, its cardinality is bounded by the total squared evaluation
energy of all the polynomials, across primitive embeddings. -/
theorem price {A : Type*} [Fintype A] {n p C : ℕ} [NeZero n]
    (P : A → ℤ[X]) (S : Finset A)
    (nz : ∀ i∈S, cycloNorm n (P i)≠0)
    (div : ∀ i∈S, (p:ℤ)^2∣cycloNorm n (P i))
    (total : (∑ w : primitiveRoots n ℂ,∑ i : A,‖valAt (P i) w‖^2)≤(n.totient:ℝ)*C) :
    S.card^n.totient*p^4≤C^n.totient := by
  classical
  have np : 0<n := Nat.pos_of_ne_zero (NeZero.ne n)
  obtain empty|nonempty := S.eq_empty_or_nonempty
  · simp [empty,zero_pow (Nat.totient_pos.mpr np).ne']
  let J := ↥(primitiveRoots n ℂ)
  let _ : Nonempty J := ⟨⟨_,(mem_primitiveRoots np).mpr (Complex.isPrimitiveRoot_exp n np.ne')⟩⟩
  have card : Fintype.card J=n.totient := (Fintype.card_coe _).trans (Complex.card_primitiveRoots n)
  let E (i : A) := ∑ w : J,‖valAt (P i) w‖^2
  obtain ⟨i,mem,least⟩ := S.exists_min_image E nonempty
  have bound : (S.card:ℝ)*E i≤(n.totient:ℝ)*C := calc
    (S.card:ℝ)*E i = ∑ _j∈S,E i := by simp
    _ ≤ ∑ j∈S,E j := sum_le_sum least
    _ ≤ ∑ j,E j := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sum_nonneg fun _ _ => sq_nonneg _)
    _ ≤ (n.totient:ℝ)*C := by dsimp only [E];rw [sum_comm];exact total
  have b : ∑ w : J, (S.card:ℝ)*‖valAt (P i) w‖^2≤(Fintype.card J:ℝ)*C := by
    rw [←mul_sum,card];exact bound
  have g := DyadicChordEnergy.prod_le_of_sum (fun w : J => (S.card:ℝ)*‖valAt (P i) w‖^2)
    (fun w => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) b
  have height : S.card^n.totient*(cycloNorm n (P i)).natAbs^2≤C^n.totient := by
    rw [prod_mul_distrib,prod_const,card_univ,card,prod_pow,←norm_eq_prod_abs,←Int.cast_abs,←Nat.cast_natAbs] at g
    exact_mod_cast g
  have dvd := Int.natAbs_dvd_natAbs.mpr (div i mem)
  rw [Int.natAbs_pow,Int.natAbs_natCast] at dvd
  have cost := Nat.pow_le_pow_left (Nat.le_of_dvd (Int.natAbs_pos.mpr (nz i mem)) dvd) 2
  rw [←pow_mul] at cost
  exact (Nat.mul_le_mul_left _ cost).trans height

end ProximityGap.JointMinorNorm
#print axioms ProximityGap.JointMinorNorm.price
