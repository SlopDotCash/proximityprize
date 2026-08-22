/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R389FixedTailMatchingCellBound
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungMultisetAntipodal
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedPairingLifting

/-!
# R390: a nonzero fourfold dyadic representation fiber has size at most `105|G|`

This assembles R387--R389 with the multiset Lam--Leung theorem.  Fix one reference tuple in a
nonzero four-sum fiber. Every other tuple gives an eight-term vanishing relation. In characteristic
zero, Lam--Leung balances it antipodally and pairing lifting assigns one of the `7!! = 105` perfect
matchings. R387 leaves at most one free internal edge and R389 bounds that matching cell by `|G|`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Finset
open ArkLib.ProximityGap.NegationClosedWalk

namespace ArkLib.ProximityGap.Frontier.R390CharZeroNonzeroRepFourBound

open ArkLib.ProximityGap.Frontier.R387NonzeroFourFiberMatchingTopology
open ArkLib.ProximityGap.Frontier.R389FixedTailMatchingCellBound

variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]

/-- Ordered four-tuples from `G` representing `c`. -/
noncomputable def fourFiber (G : Finset L) (c : L) : Finset (Fin 4 → L) :=
  (Fintype.piFinset fun _ : Fin 4 => G).filter (fun a => ∑ i, a i = c)

/-- Sum of the concatenated relation is the difference of the two four-sums. -/
theorem sum_relationTuple (a z : Fin 4 → L) :
    ∑ i, relationTuple a z i = (∑ i, a i) - ∑ i, z i := by
  simp [relationTuple, Fin.sum_univ_succ]
  ring

/-- The left-half sum of the relation tuple is the variable four-sum. -/
theorem sum_leftFour_relationTuple (a z : Fin 4 → L) :
    ∑ i ∈ leftFour, relationTuple a z i = ∑ i, a i := by
  have hleft : leftFour = ({0, 1, 2, 3} : Finset (Fin (2 * 4))) := by decide
  rw [hleft]
  rw [Fin.sum_univ_four]
  simp [relationTuple]
  ring

/-- A nonzero root of unity is not self-antipodal in characteristic zero. -/
theorem root_ne_neg_self {k : ℕ} {x : L} (hx : x ^ (2 ^ k) = 1) : x ≠ -x := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, zero_pow (by positivity)] at hx
    exact zero_ne_one hx
  intro h
  have h2 : (2 : L) * x = 0 := by linear_combination h
  exact hx0 (mul_eq_zero.mp h2 |>.resolve_left two_ne_zero)

/-- Lam--Leung and pairing lifting cover a characteristic-zero fiber by matching cells. -/
theorem fourFiber_subset_matchingCells
    {k : ℕ} (hk : 1 ≤ k) (G : Finset L) (hG : ∀ x ∈ G, x ^ (2 ^ k) = 1)
    {c : L} (z : Fin 4 → L) (hzG : z ∈ Fintype.piFinset (fun _ : Fin 4 => G))
    (hzsum : ∑ i, z i = c) :
    fourFiber G c ⊆
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * 4)) => IsPairing σ)).biUnion
        (fun σ => matchingCell G z σ) := by
  classical
  intro a ha
  rw [fourFiber, Finset.mem_filter] at ha
  let f := relationTuple a z
  have hfroot : ∀ x ∈ Finset.univ.val.map f, x ^ (2 ^ k) = 1 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
    unfold f relationTuple
    split
    · rename_i hlt
      exact hG _ ((Fintype.mem_piFinset.mp ha.1) ⟨i, hlt⟩)
    · rename_i hge
      have hz := hG _ ((Fintype.mem_piFinset.mp hzG)
        ⟨(i : ℕ) - 4, by have := i.isLt; omega⟩)
      have heven : Even (2 ^ k) := Nat.even_pow.mpr ⟨even_two, by omega⟩
      simpa [neg_pow, heven.neg_one_pow] using hz
  have hfsum : (Finset.univ.val.map f).sum = 0 := by
    change ∑ i, relationTuple a z i = 0
    rw [sum_relationTuple, ha.2, hzsum, sub_self]
  have hfbal := LamLeungMultisetAntipodal.count_antipodal_of_sum_eq_zero hfroot hfsum
  have hfself : ∀ i, f i ≠ -f i := by
    intro i
    apply root_ne_neg_self
    apply hfroot
    exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  obtain ⟨σ, hσ, hpair⟩ := exists_isPairing_of_count_balanced f hfbal hfself
  apply Finset.mem_biUnion.mpr
  refine ⟨σ, by simp [hσ], ?_⟩
  rw [matchingCell, Finset.mem_filter]
  exact ⟨ha.1, hpair⟩

/-- **Characteristic-zero nonzero four-fiber bound.** -/
theorem card_fourFiber_le_105_mul_card
    {k : ℕ} (hk : 1 ≤ k) (G : Finset L) (hG : ∀ x ∈ G, x ^ (2 ^ k) = 1)
    {c : L} (hc : c ≠ 0) :
    (fourFiber G c).card ≤ 105 * G.card := by
  classical
  by_cases hne : (fourFiber G c).Nonempty
  · obtain ⟨z, hz⟩ := hne
    rw [fourFiber, Finset.mem_filter] at hz
    let Pairs := Finset.univ.filter
      (fun σ : Equiv.Perm (Fin (2 * 4)) => IsPairing σ)
    have hcover := fourFiber_subset_matchingCells hk G hG z hz.1 hz.2
    calc
      (fourFiber G c).card ≤ (Pairs.biUnion fun σ => matchingCell G z σ).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ σ ∈ Pairs, (matchingCell G z σ).card := Finset.card_biUnion_le
      _ ≤ ∑ _σ ∈ Pairs, G.card := by
        apply Finset.sum_le_sum
        intro σ hσmem
        have hσ : IsPairing σ := (Finset.mem_filter.mp hσmem).2
        by_cases hcell : (matchingCell G z σ).Nonempty
        · obtain ⟨a, ha⟩ := hcell
          rw [matchingCell, Finset.mem_filter] at ha
          have hsum : ∑ i ∈ leftFour, relationTuple a z i ≠ 0 := by
            rw [sum_leftFour_relationTuple]
            have htotal : ∑ i, relationTuple a z i = 0 := by
              have hneg : (∑ i, relationTuple a z i) = -(∑ i, relationTuple a z i) := by
                calc
                  (∑ i, relationTuple a z i) =
                      ∑ i, relationTuple a z (σ i) :=
                    (Equiv.sum_comp σ (relationTuple a z)).symm
                  _ = ∑ i, -relationTuple a z i := by
                    apply Finset.sum_congr rfl
                    intro i _
                    exact ha.2 i
                  _ = -(∑ i, relationTuple a z i) := by simp
              have htwo : (2 : L) * (∑ i, relationTuple a z i) = 0 := by
                linear_combination hneg
              exact (mul_eq_zero.mp htwo).resolve_left two_ne_zero
            have hasum : ∑ i, a i = c := by
              rw [sum_relationTuple, hz.2] at htotal
              linear_combination htotal
            rw [hasum]
            exact hc
          have hint := internalLeftEdges_card_le_one_of_sum_ne_zero
            (relationTuple a z) σ hσ ha.2 hsum
          exact card_matchingCell_le G z σ hσ hint
        · rw [Finset.not_nonempty_iff_eq_empty.mp hcell]
          simp
      _ = Pairs.card * G.card := by simp
      _ = 105 * G.card := by
        change (Finset.univ.filter
          (fun σ : Equiv.Perm (Fin (2 * 4)) => IsPairing σ)).card * G.card = _
        rw [pairings_card_eq_doubleFactorial]
        norm_num
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

end ArkLib.ProximityGap.Frontier.R390CharZeroNonzeroRepFourBound

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R390CharZeroNonzeroRepFourBound.card_fourFiber_le_105_mul_card
