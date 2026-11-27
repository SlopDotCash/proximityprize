/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FourHeadWitness
import ArkLib.Research.ProximityGap.Frontier.RateHalfRichHeadCensus

/-! # Four-head reconstruction from an equality-class assignment -/

set_option autoImplicit false
open Finset Polynomial Code
open scoped NNReal ENNReal Polynomial

namespace ProximityGap.FourHeadPartitionAllocation

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
  [Field F] [Fintype F] [DecidableEq F]
variable (dom : I ↪ F) (f : Fin 4 → F[X]) (choice : I → Option (Fin 4))

/-- The ordinary received scalar is the value of the head whose class was selected. -/
def background (x : I) : F := (f ((choice x).getD 0)).eval (dom x)

def occupiedCore (i : Fin 4) : Finset I :=
  univ.filter fun x => (choice x).isSome ∧ (f i).eval (dom x) = background dom f choice x

def ordinary : Finset I := univ.filter fun x =>
  (choice x).isSome ∧ ∃ i, (f i).eval (dom x) ≠ background dom f choice x

def holes : Finset I := univ.filter fun x => choice x = none

/-- The attainable bad labels consist of one per nonunanimous occupied site and
one per distinct head value at each hole. -/
def capacity : ℕ := (ordinary dom f choice).card +
  ∑ x : ↥(holes choice), (univ.image fun i => (f i).eval (dom x.val)).card

/-- An assignment to equality classes reconstructs one received pair with the
computed number of literal bad labels, for every injective domain. -/
theorem realize (k : ℕ) (δ : ℝ≥0)
    (degree : ∀ i, (f i).degree < (k : WithBot ℕ))
    (degreeX : ∀ i, (Polynomial.X * f i).degree < (k : WithBot ℕ))
    (hcore : ∀ i, k ≤ (occupiedCore dom f choice i).card)
    (hsize : ∀ i, (1 - δ) * (Fintype.card I : ℝ≥0) ≤
      (((occupiedCore dom f choice i).card + 1 : ℕ) : ℝ≥0))
    (hfour : 4 < Fintype.card F)
    (hfield : capacity dom f choice * capacity dom f choice < Fintype.card F) :
    ∃ (u : WordStack F (Fin 2) I) (G : Finset F),
      G.card = capacity dom f choice ∧ ∀ γ ∈ G,
        mcaEvent ((ReedSolomon.code dom k : Submodule F (I → F)) : Set (I → F))
          δ (u 0) (u 1) γ := by
  let A : FourHeadWitness.CoreAllocation dom k δ := {
    head := f
    background := background dom f choice
    ordinary := ordinary dom f choice
    special := holes choice
    core := occupiedCore dom f choice
    degree_head := degree
    degree_first := degreeX
    disjoint := disjoint_left.mpr fun _ ho hh => by
      have yes := (mem_filter.mp ho).2.1
      rw [(mem_filter.mp hh).2] at yes
      contradiction
    core_disjoint := fun _ => disjoint_left.mpr fun _ hc hh => by
      have yes := (mem_filter.mp hc).2.1
      rw [(mem_filter.mp hh).2] at yes
      contradiction
    core_agrees := fun _ _ hc => (mem_filter.mp hc).2.2
    core_rank := hcore
    core_size := hsize
    ordinary_mismatch := fun _ ho => (mem_filter.mp ho).2.2 }
  exact FourHeadWitness.exists_bad_scalar_set_of_values A hfour hfield

/-- If deficit units each cost as many incidences as one hole can create above
the ordinary budget, a strict overrun supplies enough distinct holes for repair. -/
theorem repair_room (n labels price deficit vacant : ℕ) (hover : n < labels)
    (budget : labels + price * deficit ≤ n + price * vacant) :
    deficit < vacant := by
  by_contra! h
  have charge := Nat.mul_le_mul_left price h
  omega

/-- Six rich cores contradict the degree bound on all their pair intersections. -/
theorem exclude_six (S : Fin 6 → Finset I) (hn : Fintype.card I = 2 ^ 30)
    (hsize : ∀ i, 787403671 ≤ (S i).card)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 536870911) : False := by
  have h := RateHalfRichHeadCensus.incidence_bound S hsize hinter 4
  rw [hn] at h
  omega

/-- A fifth agreement set cannot be outside the four heads with the indicated
core bounds. The six head-head intersections lose the primitive direction degree. -/
theorem exclude_fifth (S : Fin 5 → Finset I) (hn : Fintype.card I = 2 ^ 30)
    (s : ℕ) (hs : 0 < s)
    (mass : 5 * 787410671 ≤ (∑ i, (S i).card) + 2 + min 2 s + min 6 s)
    (hinter : ∀ i j, i ≠ j →
      (S i ∩ S j).card + s * (if i.val < 4 ∧ j.val < 4 then 1 else 0) ≤ 536870911) :
    False := by
  classical
  let off := ∑ i : Fin 5, ∑ j ∈ univ.erase i, (S i ∩ S j).card
  have tangent (v : ℕ) (hv : v ≤ 5) : 7 * v ≤ v ^ 2 + 12 := by
    interval_cases v <;> decide
  have degree : 7 * (∑ i, (S i).card) ≤
      (∑ i, ∑ j, (S i ∩ S j).card) + 12 * Fintype.card I := by
    rw [ArkLib.Coverage.sum_card_eq_sum_degree,
      ArkLib.ProximityGap.Frontier.FSMBCoreAbsorptionLadder.sum_inter_card_eq_sum_degree_sq,
      mul_sum]
    apply (sum_le_sum (fun x _ => tangent _ ((card_le_univ (univ.filter (fun i => x ∈ S i))).trans
      (by simp)))).trans
    simp [sum_add_distrib, Nat.mul_comm]
  have row (i) : ∑ j, (S i ∩ S j).card =
      (S i).card + ∑ j ∈ univ.erase i, (S i ∩ S j).card := by
    rw [← add_sum_erase univ (fun j => (S i ∩ S j).card) (mem_univ i), inter_self]
  simp only [row, sum_add_distrib, hn] at degree
  have lim := sum_le_sum (s := univ) (fun (i : Fin 5) _ => sum_le_sum
    (s := univ.erase i) (fun j hj => hinter i j (ne_of_mem_erase hj).symm))
  have count : (∑ i : Fin 5, ∑ j ∈ univ.erase i,
      if i.val < 4 ∧ j.val < 4 then (1 : ℕ) else 0) = 12 := by decide
  simp only [sum_add_distrib, ← mul_sum, count, sum_const, card_erase_of_mem (mem_univ _),
    card_univ, Fintype.card_fin, nsmul_eq_mul] at lim
  change off + s * 12 ≤ _ at lim
  change 7 * (∑ i, (S i).card) ≤ (∑ i, (S i).card) + off + _ at degree
  omega

#print axioms exclude_six
#print axioms exclude_fifth
#print axioms realize
#print axioms repair_room
end ProximityGap.FourHeadPartitionAllocation
