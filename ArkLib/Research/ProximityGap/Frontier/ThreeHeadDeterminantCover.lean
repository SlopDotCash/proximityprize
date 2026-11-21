/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorRateQuarterDeterminantMultiplicity
import ArkLib.Research.ProximityGap.Frontier._TwoLargeCoreCount

/-! # Coverage by three noncollinear polynomial heads

At a coordinate belonging to several joint cores, the excess incidence contributes
to the root multiplicity of the three-head determinant. An off-line witness can
agree only on a bounded number of sites in each of the three cores.
-/

open Finset Polynomial Code
open _root_.ProximityGap
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthFullWiring
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantMultiplicity
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.ThreeHeadDeterminantCover

variable {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]

/-- Count the actual union, keeping every site that the three cores miss available
for a further witness. -/
theorem core_sum_le_union_add_degree (dom : ι ↪ F) (u v : ι → F)
    (a b c : F[X] × F[X]) (h : threeLineDeterminant a b c ≠ 0) :
    let D := coreSet dom u v
    (D a).card + (D b).card + (D c).card ≤
      (D a ∪ D b ∪ D c).card + (threeLineDeterminant a b c).natDegree := by
  classical
  let D := coreSet dom u v
  let U := D a ∪ D b ∪ D c
  let count := fun i => coreCount (u i) (v i) (dom i) a b c
  have hloc (i : ι) : count i ≤ (if i ∈ U then 1 else 0) + (count i - 1) := by
    by_cases hi : i ∈ U
    · simp only [hi, ite_true]
      omega
    · have hzero : count i = 0 := by
        simp only [U, D, coreSet, mem_union, mem_filter, mem_univ, true_and, not_or] at hi
        simp [count, coreCount, hi.1.1, hi.1.2, hi.2]
      simp [hzero]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hloc i)
  have he : (∑ i : ι, if i ∈ U then 1 else 0) = U.card := by simp
  rw [Finset.sum_add_distrib, he] at hsum
  have hroot := sum_coreCount_sub_one_le_natDegree dom u v a b c univ h
  have htot := sum_coreCount_eq_sum_coreSet_cards dom u v a b c
  change (∑ i : ι, count i) = _ at htot
  change (∑ i : ι, (count i - 1)) ≤ _ at hroot
  rw [htot] at hsum
  exact hsum.trans (Nat.add_le_add_left hroot _)

variable [Fintype F] [DecidableEq F] [Nonempty ι] {dom : ι ↪ F} {k : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) ι}

/-- For three determined secants, the determinant and core sizes alone suffice
to cover the entire selected bad-scalar family under this inequality. -/
theorem cover_of_three_noncollinear (fam : BadScalarRichPointFamily dom k δ u)
    (hk : 1 ≤ k) (a b c : LineParameter F)
    (ha : a ∈ lineParameters fam) (hb : b ∈ lineParameters fam) (hc : c ∈ lineParameters fam)
    (hdet : threeLineDeterminant a b c ≠ 0)
    (hsize : Fintype.card ι + 5*(k-1) <
      ⌈(1-δ) * (Fintype.card ι : ℝ≥0)⌉₊ +
      (jointCore dom (u 0) (u 1) a.1 a.2).card +
      (jointCore dom (u 0) (u 1) b.1 b.2).card +
      (jointCore dom (u 0) (u 1) c.1 c.2).card) :
    fam.G ⊆ pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c := by
  classical
  let D := fun l : LineParameter F => jointCore dom (u 0) (u 1) l.1 l.2
  let U := D a ∪ D b ∪ D c
  have hdeg (l : LineParameter F) (hl : l ∈ lineParameters fam) := lineParameter_degree_lt fam hl
  have hdetdeg := natDegree_threeLineDeterminant_le_two_mul_sub_two
    (hdeg a ha).1 (hdeg a ha).2 (hdeg b hb).1 (hdeg b hb).2 (hdeg c hc).1 (hdeg c hc).2
  have hu := core_sum_le_union_add_degree dom (u 0) (u 1) a b c hdet
  simp only [coreSet_eq_jointCore] at hu
  change (D a).card + (D b).card + (D c).card ≤ U.card + _ at hu
  intro z hz
  by_contra hnot
  simp only [Finset.mem_union, not_or] at hnot
  let A := fullAgreement dom (u 0) (u 1) z (fam.q z)
  have hinter (l : LineParameter F) (hl : l ∈ lineParameters fam) (hn : z ∉ pointsOn fam l) :
      (A ∩ D l).card ≤ k-1 :=
    fullAgreement_inter_jointCore_card_le dom (u 0) (u 1) hk (fam.degree_lt z hz)
      (hdeg l hl).1 (hdeg l hl).2 (fun heq => hn ((mem_pointsOn_iff fam l z).2 ⟨hz, heq⟩))
  have hA : A ⊆ (A ∩ D a ∪ (A ∩ D b) ∪ (A ∩ D c)) ∪ (univ \ U) := by
    intro i hi
    simp only [U, mem_union, mem_inter, mem_sdiff, mem_univ, true_and, hi]
    tauto
  have hcard := Finset.card_le_card hA
  have h1 := Finset.card_union_le (A ∩ D a) (A ∩ D b)
  have h2 := Finset.card_union_le (A ∩ D a ∪ (A ∩ D b)) (A ∩ D c)
  have h3 := Finset.card_union_le (A ∩ D a ∪ (A ∩ D b) ∪ (A ∩ D c)) (univ \ U)
  have hd := Finset.card_sdiff_of_subset (Finset.subset_univ U)
  rw [Finset.card_univ] at hd
  have ht := fam.threshold_le z hz
  change _ ≤ A.card at ht
  change Fintype.card ι + 5*(k-1) < _ + (D a).card + (D b).card + (D c).card at hsize
  have hule := Finset.card_le_univ U
  have ha' := hinter a ha hnot.1.1
  have hb' := hinter b hb hnot.1.2
  have hc' := hinter c hc hnot.2
  omega

#print axioms cover_of_three_noncollinear

end ArkLib.ProximityGap.Frontier.ThreeHeadDeterminantCover
