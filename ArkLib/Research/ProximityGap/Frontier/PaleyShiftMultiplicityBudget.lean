/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PaleyShiftListRecovery
import ArkLib.Research.ProximityGap.Frontier._R16LegendreCosetFace
import Mathlib.Algebra.Polynomial.Roots

/-! # The exact multiplicity budget of quadratic-character shifts

The parity correction in the integer floor of a quarter of the squared shift sum
is supported on the translates meeting zero when the set has even size, and on
their complement when it has odd size.
-/

namespace ProximityGap.PaleyShiftMultiplicityBudget

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- The signed imbalance of the translate `A + b` in the two quadratic classes. -/
def shiftSum (A : Finset (ZMod p)) (b : ZMod p) : ℤ :=
  ∑ u ∈ A, quadraticChar (ZMod p) (u + b)

/-- The integer multiplicity contributed by a shift. -/
def multiplicity (A : Finset (ZMod p)) (b : ZMod p) : ℕ :=
  ((shiftSum A b) ^ 2 / 4).toNat

private theorem four_mul_floor (w : ℤ) : 4 * (w ^ 2 / 4) = w ^ 2 - w % 2 := by
  rcases Int.even_or_odd w with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk, show (k + k)^2 = 4*k^2 by ring]
    omega
  · rw [hk, show (2*k+1)^2 = 4*(k^2+k)+1 by ring]
    omega

private theorem sum_shift_sq (hp : p ≠ 2) (A : Finset (ZMod p)) :
    ∑ b : ZMod p, shiftSum A b ^ 2 = (A.card : ℤ) * p - A.card ^ 2 := by
  have h := ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.sum_sq_shiftedQuadSum
    (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n]) (A.map (Equiv.neg _).toEmbedding)
  simpa only [ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum, shiftSum,
    sum_map, Equiv.coe_toEmbedding, Equiv.neg_apply, sub_neg_eq_add, add_comm,
    card_map, ZMod.card] using h

/-- The zero-symbol parity correction and the full diagonal second moment exactly
exhaust the degree of the central determinant product. -/
theorem sum_multiplicity (hp : p ≠ 2) (A : Finset (ZMod p)) :
    ∑ b : ZMod p, multiplicity A b = (A.card / 2) * ((p - 1) / 2 - A.card / 2) := by
  let z (b : ZMod p) : ℤ := if -b ∈ A then 1 else 0
  have hz : ∑ b : ZMod p, z b = (A.card : ℤ) := by
    change (∑ b : ZMod p, (fun u : ZMod p => if u ∈ A then (1:ℤ) else 0) ((Equiv.neg _) b)) = _
    refine ((Equiv.neg (ZMod p)).bijective.sum_comp (fun u => if u ∈ A then (1 : ℤ) else 0)).trans ?_
    rw [Finset.sum_boole]
    have h : univ.filter (fun i => i ∈ A) = A := by ext; simp
    rw [h]
  have hpar (b : ZMod p) :
      shiftSum A b % 2 = if A.card % 2 = 0 then z b else 1 - z b := by
    have h := PaleyShiftListRecovery.agreement_excess A b (s := 1) (Or.inl rfl)
    change 1 * shiftSum A b = 2 * _ - _ + z b at h
    dsimp only [z] at h ⊢
    split_ifs at * <;> omega
  have hpoint (b : ZMod p) : 4 * (multiplicity A b : ℤ) =
      shiftSum A b ^ 2 - (if A.card % 2 = 0 then z b else 1 - z b) := by
    rw [multiplicity, Int.toNat_of_nonneg (Int.ediv_nonneg (sq_nonneg _) (by decide)),
      four_mul_floor, hpar]
  have hsum := Finset.sum_congr (s₁ := (univ : Finset (ZMod p))) rfl (fun b _ => hpoint b)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_shift_sq hp] at hsum
  have hodd := (Fact.out : p.Prime).odd_of_ne_two hp
  obtain ⟨d, hd⟩ := hodd
  let t := A.card / 2
  have hcard := Finset.card_le_univ A
  rw [ZMod.card] at hcard
  have hpd : (p - 1)/2 = d := by omega
  have ht : t ≤ d := by dsimp [t]; omega
  rw [hpd]
  apply Int.ofNat_inj.mp
  push_cast
  change (∑ b : ZMod p, (multiplicity A b : ℤ)) = (t : ℤ) * ((d - t : ℕ) : ℤ)
  rw [Nat.cast_sub ht]
  have hp' : (p : ℤ) = 2*d+1 := by exact_mod_cast hd
  by_cases ha : A.card % 2 = 0
  · simp only [ha, ite_true, hz] at hsum
    have he : (A.card : ℤ) = 2*t := by exact_mod_cast (show A.card = 2*t by dsimp [t]; omega)
    rw [he, hp'] at hsum
    nlinarith only [hsum]
  · simp only [ha, ite_false, Finset.sum_sub_distrib, hz, sum_const, card_univ,
      ZMod.card, nsmul_eq_mul, mul_one] at hsum
    have he : (A.card : ℤ) = 2*t+1 := by
      exact_mod_cast (show A.card = 2*t+1 by dsimp [t]; omega)
    rw [he, hp'] at hsum
    nlinarith only [hsum]

/-- Once the multiplicities of distinct prescribed roots add up to the full degree,
the polynomial equals its leading coefficient times the product of those factors. -/
theorem eq_leadingCoeff_mul_prod_of_local_dvd {K : Type*} [Field K]
    (P : K[X]) (S : Finset K) (m : K → ℕ)
    (hdegree : P.natDegree = ∑ b ∈ S, m b)
    (hlocal : ∀ b ∈ S, (X - C b) ^ m b ∣ P) :
    P = C P.leadingCoeff * ∏ b ∈ S, (X - C b) ^ m b := by
  classical
  let Q : K[X] := ∏ b ∈ S, (X - C b) ^ m b
  have hm : Q.Monic := monic_prod_of_monic _ _ (fun b _ => (monic_X_sub_C b).pow _)
  have hdeg : Q.natDegree = P.natDegree := by
    rw [hdegree, show Q = _ from rfl, natDegree_prod_of_monic _ _ (fun b _ => (monic_X_sub_C b).pow _)]
    simp
  have hdiv : Q ∣ P := by
    apply Finset.prod_dvd_of_coprime
    · intro x _ y _ hxy
      exact (pairwise_coprime_X_sub_C Function.injective_id hxy).pow
    · exact hlocal
  by_cases hp : P = 0
  · simp [hp]
  obtain ⟨u, hu⟩ := hdiv
  have hn : u ≠ 0 := fun hh => hp (by simp [hu, hh])
  have hudeg : u.natDegree = 0 := by
    rw [hu, natDegree_mul hm.ne_zero hn] at hdeg
    omega
  have hC : u = C u.leadingCoeff := by
    simpa only [leadingCoeff, hudeg] using eq_C_of_natDegree_eq_zero hudeg
  change P = C P.leadingCoeff * Q
  rw [hu, leadingCoeff_mul, hm.leadingCoeff, one_mul, ← hC, mul_comm]

#print axioms sum_multiplicity
#print axioms eq_leadingCoeff_mul_prod_of_local_dvd

end ProximityGap.PaleyShiftMultiplicityBudget
