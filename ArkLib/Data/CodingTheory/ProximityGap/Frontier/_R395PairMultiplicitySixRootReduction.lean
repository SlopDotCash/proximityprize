/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R394FiniteFourFiber105Reduction

/-!
# R395: pair multiplicity four is a three-support exclusion

Map an ordered representation `(u₀,u₁)` of `c` to its unordered support `{u₀,u₁}`.  A fixed support
has at most two orderings, so at most two supports imply `rep₂(c) ≤ 4`.  Moreover, two different
supports representing the same sum are disjoint: sharing one endpoint forces the other endpoint.
Thus failure of the support bound produces three disjoint pair supports with one common nonzero sum.
This uses six roots when all supports have size two, and five when one representation is diagonal.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R395PairMultiplicitySixRootReduction

open ArkLib.ProximityGap.Frontier.R392PairFiberNecessaryForFourFiber
open ArkLib.ProximityGap.Frontier.R394FiniteFourFiber105Reduction

variable {F : Type*} [Field F] [DecidableEq F]

/-- Unordered support of an ordered pair. -/
def pairSupport (u : Fin 2 → F) : Finset F := {u 0, u 1}

/-- Supports of all ordered representations of `c`. -/
noncomputable def pairSupports (G : Finset F) (c : F) : Finset (Finset F) :=
  (pairFiber G c).image pairSupport

/-- The three-support exclusion: no nonzero sum has three distinct pair supports. -/
def NoThreePairSupports (G : Finset F) : Prop :=
  ∀ c : F, c ≠ 0 → (pairSupports G c).card ≤ 2

/-- Two ordered pairs with the same first coordinate and the same sum are equal. -/
theorem pair_eq_of_first_eq_of_sum_eq
    {u v : Fin 2 → F} (hfirst : u 0 = v 0) (hsum : ∑ i, u i = ∑ i, v i) : u = v := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at hsum
  funext i
  fin_cases i
  · exact hfirst
  · rw [hfirst] at hsum
    have h : v 0 + u 1 = v 0 + v 1 := hsum
    simpa using add_left_cancel h

/-- Every unordered-support fiber contains at most the two coordinate orderings. -/
theorem pairSupport_fiber_card_le_two
    (S : Finset (Fin 2 → F)) (y : Finset F) :
    (S.filter (fun u => pairSupport u = y)).card ≤ 2 := by
  classical
  by_cases hnonempty : (S.filter (fun u => pairSupport u = y)).Nonempty
  · obtain ⟨w, hw⟩ := hnonempty
    rw [Finset.mem_filter] at hw
    have hy : y.card ≤ 2 := by
      rw [← hw.2]
      change ({w 0, w 1} : Finset F).card ≤ 2
      rcases Finset.card_pair_eq_one_or_two (a := w 0) (b := w 1) with h | h <;> omega
    calc
      (S.filter (fun u => pairSupport u = y)).card ≤ y.card := by
        apply Finset.card_le_card_of_injOn (fun u => u 0)
        · intro u hu
          rw [Finset.mem_coe, Finset.mem_filter] at hu
          rw [← hu.2]
          simp [pairSupport]
        · intro u hu v hv huv
          rw [Finset.mem_coe, Finset.mem_filter] at hu hv
          funext i
          fin_cases i
          · exact huv
          · have huset : pairSupport u = pairSupport v := hu.2.trans hv.2.symm
            have hu1 : u 1 ∈ pairSupport v := by rw [← huset]; simp [pairSupport]
            simp [pairSupport] at hu1
            rcases hu1 with h10 | h11
            · have hv1 : v 1 ∈ pairSupport u := by rw [huset]; simp [pairSupport]
              simp [pairSupport] at hv1
              rcases hv1 with hv10 | hv11
              · exact h10.trans (huv.symm.trans hv10.symm)
              · exact hv11.symm
            · exact h11
      _ ≤ 2 := hy
  · rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty]
    simp

/-- Ordered pair count is at most twice the number of unordered supports. -/
theorem card_pairFiber_le_two_mul_pairSupports (G : Finset F) (c : F) :
    (pairFiber G c).card ≤ 2 * (pairSupports G c).card := by
  classical
  have hpart :
      (pairFiber G c).card = ∑ y ∈ pairSupports G c,
        ((pairFiber G c).filter (fun u => pairSupport u = y)).card := by
    unfold pairSupports
    exact Finset.card_eq_sum_card_fiberwise
      (fun u hu => Finset.mem_image_of_mem pairSupport hu)
  rw [hpart]
  calc
    ∑ y ∈ pairSupports G c,
        ((pairFiber G c).filter (fun u => pairSupport u = y)).card
        ≤ ∑ _y ∈ pairSupports G c, 2 :=
          Finset.sum_le_sum (fun y _ => pairSupport_fiber_card_le_two (pairFiber G c) y)
    _ = 2 * (pairSupports G c).card := by simp [Nat.mul_comm]

/-- Distinct pair supports with the same sum cannot share an endpoint. -/
theorem disjoint_pairSupports_of_ne
    {c : F} {u v : Fin 2 → F} (hu : ∑ i, u i = c) (hv : ∑ i, v i = c)
    (hne : pairSupport u ≠ pairSupport v) :
    Disjoint (pairSupport u) (pairSupport v) := by
  rw [Finset.disjoint_left]
  intro x hxu hxv
  simp [pairSupport] at hxu hxv
  rw [Fin.sum_univ_two] at hu hv
  rcases hxu with (rfl | rfl) <;> rcases hxv with (h | h)
  · apply hne
    rw [h] at hu
    have hother : u 1 = v 1 := by linear_combination hu - hv
    simp [pairSupport, h, hother]
  · apply hne
    rw [h] at hu
    have hother : u 1 = v 0 := by linear_combination hu - hv
    simp [pairSupport, h, hother, Finset.pair_comm]
  · apply hne
    rw [h] at hu
    have hother : u 0 = v 1 := by linear_combination hu - hv
    simp [pairSupport, h, hother, Finset.pair_comm]
  · apply hne
    rw [h] at hu
    have hother : u 0 = v 0 := by linear_combination hu - hv
    simp [pairSupport, h, hother]

/-- **Three-support exclusion implies pair multiplicity four.** -/
theorem pairMultiplicityFour_of_noThreePairSupports
    (G : Finset F) (hthree : NoThreePairSupports G) : PairMultiplicityFour G := by
  intro c hc
  calc
    (pairFiber G c).card ≤ 2 * (pairSupports G c).card :=
      card_pairFiber_le_two_mul_pairSupports G c
    _ ≤ 2 * 2 := Nat.mul_le_mul_left 2 (hthree c hc)
    _ = 4 := by norm_num

end ArkLib.ProximityGap.Frontier.R395PairMultiplicitySixRootReduction

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R395PairMultiplicitySixRootReduction.disjoint_pairSupports_of_ne
#print axioms
  ArkLib.ProximityGap.Frontier.R395PairMultiplicitySixRootReduction.pairMultiplicityFour_of_noThreePairSupports
