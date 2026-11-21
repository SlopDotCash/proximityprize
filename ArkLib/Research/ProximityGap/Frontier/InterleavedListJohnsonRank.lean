/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorRateQuarterObtuse
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30Second

/-!
# Interleaved Reed–Solomon lists from constant-weight set families

Every member of a closed list supplies a block of exactly `t` agreement
coordinates. Two blocks share at most `k-1` positions. A constant-weight
bound therefore applies at every radius below the next Hamming step.
-/

namespace ProximityGap.InterleavedListJohnsonRank

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterObtuse
  (card_le_universe_of_equal_card_pair_inter_le)

open Code

/-- A uniform bound on constant-weight families gives the same bound on
interleaved lists over any field, including infinite fields. -/
theorem interleaved_lambda_le_of_block_bound {ι : Type} {F : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] [Field F] (D : ι ↪ F) (k t arity B : ℕ) (δ : ℝ)
    (hδ : δ * (Fintype.card ι : ℝ) < (Fintype.card ι : ℝ) - t + 1)
    (hbound : ∀ (m : ℕ) (S : Fin m → Finset ι), (∀ i, (S i).card = t) →
      (Pairwise fun i j => (S i ∩ S j).card ≤ k - 1) → m ≤ B) :
    Lambda (interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D k : Set (ι → F))) δ ≤
      (B : ℕ∞) := by
  classical
  apply Lambda_le_of_forall_finset_card_le
  intro y T hT
  let e := (Fintype.equivFin ↥T).symm
  let word (i : Fin (Fintype.card ↥T)) := (e i).val
  let support (i : Fin (Fintype.card ↥T)) := Finset.univ.filter fun x => word i x = y x
  have hclose (i) := mem_closeCodewordsRel_iff.mp (hT (word i) (e i).property)
  have hsize (i) : t ≤ (support i).card := by
    have hd := (hclose i).2
    have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    rw [relHammingDist_coe, hammingDist_comm, div_le_iff₀ hn] at hd
    have htotal : (agree (word i) y : ℝ) + (hammingDist (word i) y : ℝ) = Fintype.card ι := by
      exact_mod_cast agree_add_hammingDist
    have hround : t < agree (word i) y + 1 := by
      exact_mod_cast (show (t : ℝ) < (agree (word i) y : ℝ) + 1 by linarith)
    exact Nat.le_of_lt_succ hround
  choose S hsub hcard using fun i => Finset.exists_subset_card_eq (hsize i)
  have hpair : Pairwise fun i j => (S i ∩ S j).card ≤ k - 1 := by
    intro i j hij
    have hne : word i ≠ word j := fun he => hij (e.injective (Subtype.ext he))
    have hd := ReedSolomon.Interleaved.agree_lt_of_mem_interleavedCodeSet
      (hclose i).1 (hclose j).1 hne
    have hle : (S i ∩ S j).card ≤ agree (word i) (word j) := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxi, hxj⟩ := Finset.mem_inter.mp hx
      have hi := (Finset.mem_filter.mp (hsub i hxi)).2
      have hj := (Finset.mem_filter.mp (hsub j hxj)).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hi.trans hj.symm⟩
    omega
  simpa using hbound _ S hcard hpair

/-- In the whole strict Johnson region every interleaved list has size at most
the block length. This bound also covers the lattice points with minimal
positive Johnson denominator. -/
theorem interleaved_lambda_le_length {ι : Type} {F : Type*} [Fintype ι] [Nonempty ι]
    [Field F] (D : ι ↪ F) (k t arity : ℕ) (δ : ℝ)
    (hδ : δ * (Fintype.card ι : ℝ) < (Fintype.card ι : ℝ) - t + 1)
    (hstrict : Fintype.card ι * (k - 1) < t ^ 2) :
    Lambda (interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D k : Set (ι → F))) δ ≤
      (Fintype.card ι : ℕ∞) := by
  classical
  apply interleaved_lambda_le_of_block_bound D k t arity _ δ hδ
  intro m S hcard hpair
  have ht : 1 ≤ t := by by_contra! h; interval_cases t; simp at hstrict
  simpa using card_le_universe_of_equal_card_pair_inter_le
    S (Fintype.card ι) t (k - 1) rfl ht hcard hpair (by omega)

/-- Closed list budget at the radius with exactly `e` errors among the production
block length of `2^30`. -/
abbrev AtErrors {F : Type*} [Field F] (D : Fin 1073741824 ↪ F) (arity k e B : ℕ) : Prop :=
  Lambda (interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D k :
    Set (Fin 1073741824 → F))) ((e : ℝ) / 1073741824) ≤ (B : ℕ∞)

/-- The final strict-Johnson agreement and error counts in the four nominated
rates, using a separate list of up to `B` codewords at each center. -/
def FourRatesAtErrors {F : Type*} [Field F] (D : Fin 1073741824 ↪ F) (arity B : ℕ) : Prop :=
  AtErrors D arity 536870912 314491699 B ∧ AtErrors D arity 268435456 536870913 B ∧
    AtErrors D arity 134217728 694116762 B ∧ AtErrors D arity 67108864 805306370 B

/-- Every field and every choice of distinct evaluation points meets the
length-sized list budget at the four strict-Johnson grid endpoints. -/
theorem four_rates_at_errors {F : Type*} [Field F] (D : Fin 1073741824 ↪ F) (arity B : ℕ)
    (hB : 1073741824 ≤ B) : FourRatesAtErrors D arity B := by
  have row (k t e : ℕ) (he : e + t = 1073741824) (hs : 1073741824 * (k - 1) < t ^ 2) :
      AtErrors D arity k e B := by
    apply le_trans (interleaved_lambda_le_length D k t arity _ ?_ (by simpa using hs))
    · exact_mod_cast (show Fintype.card (Fin 1073741824) ≤ B by simpa using hB)
    · simp only [Fintype.card_fin, Nat.cast_ofNat]
      have hsum : (e : ℝ) + t = 1073741824 := by exact_mod_cast he
      linarith
  exact ⟨row _ 759250125 _ (by decide) (by decide),
    row _ 536870911 _ (by decide) (by decide),
    row _ 379625062 _ (by decide) (by decide),
    row _ 268435454 _ (by decide) (by decide)⟩

/-- Each preceding agreement count fails the strict Johnson inequality. -/
theorem preceding_agreement_counts :
    759250124 ^ 2 ≤ (1073741824 : ℕ) * (536870912 - 1) ∧
    536870910 ^ 2 ≤ (1073741824 : ℕ) * (268435456 - 1) ∧
    379625061 ^ 2 ≤ (1073741824 : ℕ) * (134217728 - 1) ∧
    268435453 ^ 2 ≤ (1073741824 : ℕ) * (67108864 - 1) := by decide

local instance : Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩
local instance : Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- At the first nominated prime its exact security budget is the block length. -/
theorem first_prime_four_rates (D : Fin 1073741824 ↪ ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
    (arity : ℕ) :
    FourRatesAtErrors D arity (ArkLib.ProximityGap.PrizeShapePrimeP30.P / 2 ^ 128) :=
  four_rates_at_errors D arity _ (by decide)

/-- At the second nominated prime its exact security budget is twice the block length. -/
theorem second_prime_four_rates
    (D : Fin 1073741824 ↪ ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) (arity : ℕ) :
    FourRatesAtErrors D arity (ArkLib.ProximityGap.PrizeShapePrimeP30Second.P / 2 ^ 128) :=
  four_rates_at_errors D arity _ (by decide)

end ProximityGap.InterleavedListJohnsonRank

#print axioms ProximityGap.InterleavedListJohnsonRank.interleaved_lambda_le_of_block_bound
#print axioms ProximityGap.InterleavedListJohnsonRank.interleaved_lambda_le_length

#print axioms ProximityGap.InterleavedListJohnsonRank.first_prime_four_rates
#print axioms ProximityGap.InterleavedListJohnsonRank.second_prime_four_rates
