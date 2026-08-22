/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterAgreementOverlapGraph

/-!
# P1: deleting eight Hall exceptions still leaves a forced large-overlap pair

The constant-width Hall localization deletes at most eight labels.  Generic Hall-to-rigidity is
false, but the deletion leaves essentially the entire `N+1`-label predecessor family.  This file
uses the sharp five-set integral Johnson theorem to prove that the complement still contains two
distinct witnesses overlapping on at least `K` coordinates.

Thus the correct successor to the eight-label theorem is not generic maximal recoverability:
it is a forced secant/pencil decomposition on the enormous Hall-safe complement.
-/

set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.P1EightLabelComplementForcedSecant

open P1RateQuarterAgreementOverlapGraph

/-- Removing eight labels from the literal `N+1` family leaves at least five. -/
theorem five_le_complement_card
    {J : Type} [Fintype J] [DecidableEq J]
    (hcard : Fintype.card J = N + 1) (C : Finset J) (hC : C.card ≤ 8) :
    5 ≤ (Finset.univ \ C).card := by
  simp only [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hcard]
  norm_num [N]
  omega

/-- **Forced secant outside every eight-label exception set.**  Any `N+1` witness family with
P1 predecessor-size supports contains, outside `C`, two distinct labels whose supports overlap
on at least the interpolation dimension `K`. -/
theorem exists_pair_outside_eight_inter_card_ge_K
    {J : Type} [Fintype J] [DecidableEq J]
    (witness : J → Finset (Fin N))
    (hcard : Fintype.card J = N + 1)
    (hsize : ∀ j : J, T ≤ (witness j).card)
    (C : Finset J) (hC : C.card ≤ 8) :
    ∃ u v : J, u ≠ v ∧ u ∉ C ∧ v ∉ C ∧
      K ≤ (witness u ∩ witness v).card := by
  have hfive := five_le_complement_card hcard C hC
  obtain ⟨L, hLsub, hLcard⟩ :=
    Finset.exists_subset_card_eq hfive
  have e : L ≃ Fin 5 := by
    rw [← hLcard]
    exact L.equivFin
  let S : Fin 5 → Finset (Fin N) := fun i => witness (e.symm i)
  obtain ⟨i, j, hij, hoverlap⟩ :=
    exists_pair_inter_card_ge_K_of_five S (fun r => hsize (e.symm r))
  have hne : (e.symm i : J) ≠ (e.symm j : J) := by
    intro h
    exact hij (e.symm.injective (Subtype.ext h))
  refine ⟨e.symm i, e.symm j, hne, ?_, ?_, ?_⟩
  · have hm := hLsub (e.symm i).2
    simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and] using hm
  · have hm := hLsub (e.symm j).2
    simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and] using hm
  · simpa only [S] using hoverlap

end ArkLib.ProximityGap.Frontier.P1EightLabelComplementForcedSecant

open ArkLib.ProximityGap.Frontier.P1EightLabelComplementForcedSecant

#print axioms five_le_complement_card
#print axioms exists_pair_outside_eight_inter_card_ge_K
