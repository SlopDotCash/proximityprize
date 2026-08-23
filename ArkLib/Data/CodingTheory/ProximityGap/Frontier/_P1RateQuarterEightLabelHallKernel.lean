/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterSmallSubsetRankLocalization

/-!
# P1 divided-difference Hall kernel: eight exceptional labels suffice

The singleton census and the pair-obstruction matching argument were previously recorded as
separate outputs.  This file combines them into one deletion statement.  For exactly `N+1`
threshold-size labels, there is a set of at most eight labels such that **every nonempty subset
of the complement** has its full projected block-Vandermonde Hall budget.

The eight labels are the union of the at-most-two singleton exceptions and an at-most-six vertex
cover of the singleton-safe bad-pair graph.  Subsets of size three through six are handled by the
complement-weighted truncation inequality; subsets of size at least seven use the global P1
localization theorem.

This does not itself prove matrix injectivity: the remaining algebraic step is a block-
Vandermonde/matroid theorem lifting these Hall inequalities, together with control of the eight
deleted labels.  It does reduce the possible non-combinatorial kernel to constant label width.
-/

set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterEightLabelHallKernel

open P1RateQuarterAgreementOverlapGraph
open P1RateQuarterSmallSubsetRankLocalization

/-- The literal P1 label universe has room for two labels outside every set of size at most six. -/
theorem two_le_complement_card_of_card_le_six
    {J : Type} [Fintype J] [DecidableEq J]
    (hcard : Fintype.card J = N + 1) (U : Finset J) (hU : U.card ≤ 6) :
    2 ≤ (Finset.univ \ U).card := by
  simp only [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hcard]
  norm_num [N]
  omega

/-- After deleting at most eight labels, every remaining singleton and pair has its full
projected Hall budget. -/
theorem exists_eight_label_singleton_pairHall_kernel
    {J : Type} [Fintype J] [DecidableEq J]
    (support : Fin N → Finset J) (hcard : Fintype.card J = N + 1)
    (hsize : ∀ j : J, T ≤
      (Finset.univ.filter fun x : Fin N => j ∈ support x).card) :
    ∃ C : Finset J, C.card ≤ 8 ∧
      (∀ j : J, j ∉ C → K ≤ projectedBudget support {j}) ∧
      (∀ u v : J, u ≠ v → u ∉ C → v ∉ C →
        2 * K ≤ projectedBudget support {u, v}) := by
  let E := singletonHallBad support K
  have hE : E.card ≤ 2 := p1_singletonHallBad_card_le_two support hcard hsize
  obtain ⟨P, hP, hpair⟩ := exists_six_label_pairHall_cover support hcard hsize
  refine ⟨E ∪ P, ?_, ?_, ?_⟩
  · calc
      (E ∪ P).card ≤ E.card + P.card := Finset.card_union_le E P
      _ ≤ 2 + 6 := Nat.add_le_add hE hP
      _ = 8 := by norm_num
  · intro j hj
    have hjE : j ∉ E := fun h => hj (Finset.mem_union_left P h)
    simpa only [E, singletonHallBad, Finset.mem_filter, Finset.mem_univ, true_and,
      not_lt] using hjE
  · intro u v huv huC hvC
    have huE : u ∉ E := fun h => huC (Finset.mem_union_left P h)
    have hvE : v ∉ E := fun h => hvC (Finset.mem_union_left P h)
    have huP : u ∉ P := fun h => huC (Finset.mem_union_right E h)
    have hvP : v ∉ P := fun h => hvC (Finset.mem_union_right E h)
    apply hpair u v huv
    · simpa only [E, singletonHallBad, Finset.mem_filter, Finset.mem_univ, true_and,
        not_lt] using huE
    · simpa only [E, singletonHallBad, Finset.mem_filter, Finset.mem_univ, true_and,
        not_lt] using hvE
    · exact huP
    · exact hvP

/-- **Eight-label Hall-kernel capstone.**  Outside one set of at most eight labels, every
nonempty label subset has at least `K` projected rows per label. -/
theorem exists_eight_label_fullHall_kernel
    {J : Type} [Fintype J] [DecidableEq J]
    (support : Fin N → Finset J) (hcard : Fintype.card J = N + 1)
    (hsize : ∀ j : J, T ≤
      (Finset.univ.filter fun x : Fin N => j ∈ support x).card) :
    ∃ C : Finset J, C.card ≤ 8 ∧ ∀ U : Finset J,
      U.Nonempty → Disjoint U C → U.card * K ≤ projectedBudget support U := by
  obtain ⟨C, hC, hsingle, hpair⟩ :=
    exists_eight_label_singleton_pairHall_kernel support hcard hsize
  refine ⟨C, hC, ?_⟩
  intro U hUne hUC
  by_cases h7 : 7 ≤ U.card
  · exact p1_card_mul_K_le_projectedBudget_of_seven_le support U h7
      (fun j _ => hsize j)
  have hU6 : U.card ≤ 6 := by omega
  by_cases h3 : 3 ≤ U.card
  · apply p1_card_mul_K_le_projectedBudget_of_three_le support U h3
      (two_le_complement_card_of_card_le_six hcard U hU6)
    exact hsize
  have hU2 : U.card ≤ 2 := by omega
  rcases hUne with ⟨j, hj⟩
  have hUpos : 0 < U.card := Finset.card_pos.mpr ⟨j, hj⟩
  by_cases hcardOne : U.card = 1
  · obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp hcardOne
    have hju : j = u := by simpa using hj
    subst j
    simpa using hsingle u (fun hu => (Finset.disjoint_left.mp hUC) (by simp) hu)
  have hcardTwo : U.card = 2 := by omega
  obtain ⟨u, v, huv, hUeq⟩ := Finset.card_eq_two.mp hcardTwo
  subst U
  have huC : u ∉ C := fun hu => (Finset.disjoint_left.mp hUC) (by simp) hu
  have hvC : v ∉ C := fun hv => (Finset.disjoint_left.mp hUC) (by simp) hv
  simpa [Finset.card_pair huv] using hpair u v huv huC hvC

end ArkLib.ProximityGap.Frontier.P1RateQuarterEightLabelHallKernel

open ArkLib.ProximityGap.Frontier.P1RateQuarterEightLabelHallKernel

#print axioms two_le_complement_card_of_card_le_six
#print axioms exists_eight_label_singleton_pairHall_kernel
#print axioms exists_eight_label_fullHall_kernel
