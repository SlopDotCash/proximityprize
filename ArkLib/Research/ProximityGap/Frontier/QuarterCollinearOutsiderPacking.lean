/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PencilPairwiseBonferroni

/-! # Packing distinct outsider functions against three collinear quarter-rate heads -/

set_option autoImplicit false

namespace ProximityGap.Frontier.QuarterCollinearOutsiderPacking

open Finset PencilPairwiseBonferroni

variable {I : Type*} [DecidableEq I]

/-- Sum of pair intersections over unordered pairs in an indexed support family. -/
def pairTotal {r : ℕ} (sets : Fin r → Finset I) : ℕ :=
  ∑ p ∈ (univ : Finset (Fin r × Fin r)).filter (fun p => p.1 < p.2),
    (sets p.1 ∩ sets p.2).card

/-- Sum any affine lower bound for the number of colliding pairs at a site. -/
theorem support_tangent {r slope cost : ℕ} (sets : Fin r → Finset I)
    (loc : ∀ v ≤ r, slope * v ≤ v.choose 2 + cost) :
    slope * (∑ i, (sets i).card) ≤ pairTotal sets + cost * (univ.biUnion sets).card := by
  classical
  rw [sum_card_eq_sum_mult, Finset.mul_sum, pairTotal, sum_inter_eq_sum_choose_two]
  calc
    _ ≤ ∑ x ∈ univ.biUnion sets, ((mult r sets x).choose 2 + cost) := by
      apply Finset.sum_le_sum
      intro x _
      apply loc
      exact (Finset.card_filter_le _ _).trans_eq (by simp)
    _ = _ := by simp [Finset.sum_add_distrib, Nat.mul_comm]

/-- Three primary and three distinct outsider supports force this many holes in the core. -/
theorem six_support_holes (sets : Fin 6 → Finset I) {n t h d : ℕ}
    (sites : (univ.biUnion sets).card + h ≤ n)
    (hits : 6*t ≤ (∑ i, (sets i).card) + 3 + 3*h)
    (pairs : pairTotal sets ≤ 15*d) :
    6*t ≤ h + 3 + 2*n + 5*d := by
  have pack := support_tangent (slope := 3) (cost := 6) sets (by intro v hv; interval_cases v <;> decide)
  omega

/-- Two distinct outsiders against three primary heads also cost twice the direction degree. -/
theorem five_support_holes (sets : Fin 5 → Finset I) {n t h d s : ℕ}
    (sites : (univ.biUnion sets).card + h ≤ n)
    (hits : 5*t ≤ (∑ i, (sets i).card) + 3 + 2*h)
    (pairs : pairTotal sets + 2*s ≤ 10*d) :
    10*t + 2*s ≤ h + 6 + 3*n + 10*d := by
  have pack := support_tangent (slope := 2) (cost := 3) sets (by intro v hv; interval_cases v <;> decide)
  omega

/-- In the full first-prime predecessor window, six normalized supports are impossible. -/
theorem first_quarter_no_three_outsiders (sets : Fin 6 → Finset I) {t h : ℕ}
    (agreement : 592794966 ≤ t) (holes : h ≤ 33554772)
    (sites : (univ.biUnion sets).card + h ≤ 1073741824)
    (hits : 6*t ≤ (∑ i, (sets i).card) + 3 + 3*h)
    (pairs : pairTotal sets ≤ 15*268435455) : False := by
  have bound := six_support_holes sets sites hits pairs
  omega

/-- Before 479,930,028 errors the two-outsider packing contradicts the core-hole bound. -/
theorem first_quarter_no_two_outsiders (sets : Fin 5 → Finset I) {t h s : ℕ}
    (agreement : 593811797 ≤ t) (degree_pos : 1 ≤ s)
    (holes : 3*(h+s+t) ≤ 3*268435455+3+1073741824+1023)
    (sites : (univ.biUnion sets).card + h ≤ 1073741824)
    (hits : 5*t ≤ (∑ i, (sets i).card) + 3 + 2*h)
    (pairs : pairTotal sets + 2*s ≤ 10*268435455) : False := by
  have bound := five_support_holes sets sites hits pairs
  omega

/-- A fourth collinear head represented by two labels leaves no room for another
distinct outsider throughout the predecessor window. The last 1023 incidences
allow for uncovered sites whose received value still lies on the common line. -/
theorem first_quarter_repeated_class_excludes_other (sets : Fin 5 → Finset I)
    {t h s : ℕ} (agreement : 592794966 ≤ t) (degree_pos : 1 ≤ s)
    (sites : (univ.biUnion sets).card + h ≤ 1073741824)
    (hits : 10*t ≤ 2*(∑ i, (sets i).card) + 6 + 2*s + 3*h + 1023)
    (pairs : pairTotal sets + 6*s ≤ 10*268435455) : False := by
  have pack := support_tangent (slope := 2) (cost := 3) sets
    (by intro v hv; interval_cases v <;> decide)
  omega

#print axioms first_quarter_no_three_outsiders
#print axioms first_quarter_no_two_outsiders
#print axioms first_quarter_repeated_class_excludes_other

end ProximityGap.Frontier.QuarterCollinearOutsiderPacking
