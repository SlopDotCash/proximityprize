/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterSuccessorCoreGeometry
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorRateQuarterPrimitiveDirection

/-! # A pointwise upper bound at the first-prime quarter-rate successor -/

namespace ArkLib.ProximityGap.Frontier.QuarterSuccessorSiteBudget

open Polynomial Finset Code HalfPredecessorBadEventRichPointBridge HalfPredecessorSecantLines
open HalfPredecessorLineCoreGeometry HalfPredecessorRateQuarterDeterminantCollapse
open HalfPredecessorRateQuarterDeterminantMultiplicity HalfPredecessorRateQuarterPrimitiveDirection
open HalfPredecessorRateQuarterCollapsedClusterInjection
open scoped NNReal ENNReal

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Finite F] [DecidableEq F]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

/-- Across a collapsed cluster the covered sites contribute at most one scalar each.
Uncovered sites contribute at most one scalar per head. -/
theorem cluster_budget {k : ℕ} (fam : BadScalarRichPointFamily dom k δ u)
    (a b : LineParameter F) (hab : a ≠ b) (H : Finset (LineParameter F))
    (valid : ∀ g ∈ H, g ∈ lineParameters fam)
    (col : ∀ g ∈ H, lineDeterminant a b g = 0) (cover : fam.G ⊆ H.biUnion (pointsOn fam)) :
    let U := H.biUnion fun g => jointCore dom (u 0) (u 1) g.1 g.2
    fam.G.card ≤ U.card + H.card * Uᶜ.card := by
  classical
  let _ := Fintype.ofFinite F
  let D (g : LineParameter F) := jointCore dom (u 0) (u 1) g.1 g.2
  let U := H.biUnion D
  let common (i : I) := primitiveScalarAt a b (dom i)
  let key (g : LineParameter F) (i : I) := (u 0 i - g.1.eval (dom i)) / (g.2.eval (dom i) - u 1 i)
  have labels : fam.G ⊆ U.image common ∪ H.biUnion (fun s => Uᶜ.image (key s)) := by
    intro z hz
    obtain ⟨s, hS, hsz⟩ := mem_biUnion.mp (cover hz)
    have deg := lineParameter_degree_lt fam (valid s hS)
    have fresh := not_subset_jointCore_of_not_pairJointAgreesOn dom (u 0) (u 1) _ s.1 s.2
      deg.1 deg.2 (fam.noJoint z hz)
    obtain ⟨i, hit, out⟩ := not_subset.mp fresh
    rw [((mem_pointsOn_iff fam s z).mp hsz).2] at hit
    by_cases hi : i ∈ U
    · obtain ⟨t, ht, inT⟩ := mem_biUnion.mp hi
      have h := gamma_eq_primitiveScalarAt_of_pairEquation a b s t hab (col s hS) (col t ht)
        (transverse_of_mem_fullAgreement_mem_targetCore_not_mem_sourceCore
          dom (u 0) (u 1) s t z hit inT out)
        (pairEquation_of_mem_fullAgreement_of_mem_jointCore dom (u 0) (u 1) s t z hit inT)
      exact mem_union_left _ (mem_image.mpr ⟨i, hi, h.symm⟩)
    · have h := (mem_filter.mp hit).2
      simp only [eval_add, eval_mul, eval_C] at h
      have hd : s.2.eval (dom i) - u 1 i ≠ 0 := by
        intro he
        have he' := sub_eq_zero.mp he
        apply out
        rw [he'] at h
        exact mem_filter.mpr ⟨mem_univ _, add_right_cancel h, he'⟩
      have eq : key s i = z := ((eq_div_iff hd).mpr (by linear_combination h)).symm
      exact mem_union_right _ (mem_biUnion.mpr ⟨s, hS, mem_image.mpr ⟨i, mem_compl.mpr hi, eq⟩⟩)
  have tail : (H.biUnion (fun s => Uᶜ.image (key s))).card ≤ H.card * Uᶜ.card :=
    card_biUnion_le.trans ((sum_le_sum (fun s _ => card_image_le (s := Uᶜ) (f := key s))).trans_eq
      (by simp))
  exact (card_le_card labels).trans ((card_union_le ..).trans (Nat.add_le_add card_image_le tail))

omit [DecidableEq I] in
/-- A genuine received pair can exceed the first named budget at the successor by at
most fourteen scalars. The upper bound holds for every injective domain of this length. -/
theorem family_cap {p : ℕ} [CharP F p] (hp : 132 < p)
    (fam : BadScalarRichPointFamily dom 268435456 δ u) (hn : Fintype.card I = 1073741824)
    (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = 626349396) :
    fam.G.card ≤ 1073741838 := by
  classical
  by_cases hG : 1073741824 < fam.G.card
  · obtain ⟨a,b,c,hab,hac,hbc,valid,det,cover,ha,hb,hc,slack⟩ :=
      QuarterSuccessorCoreGeometry.actual_full_cover hp fam hn ht hG
    let H : Finset (LineParameter F) := {a,b,c}
    have col (g) (hg : g ∈ H) : lineDeterminant a b g = 0 := by
      simp only [H, mem_insert, mem_singleton] at hg
      rcases hg with rfl | rfl | rfl
      · simp [lineDeterminant]
      · simp [lineDeterminant]
      · simpa only [threeLineDeterminant, lineDeterminant, mul_comm] using det
    have eq : H.card = 3 := by simp [H, hab, hac, hbc]
    have cap := cluster_budget fam a b hab H (fun g hg => (valid g hg).1) col (by
      simpa [H, union_assoc] using cover.le)
    let D (g : LineParameter F) := jointCore dom (u 0) (u 1) g.1 g.2
    let U := D a ∪ D b ∪ D c
    have sites : H.biUnion D = U := by simp [U,H,union_assoc]
    change fam.G.card ≤ (H.biUnion D).card + H.card * (H.biUnion D)ᶜ.card at cap
    rw [sites,eq] at cap
    have room : Uᶜ.card ≤ 7 := by
      change Uᶜ.card + _ + _ + _ + _ + _ + _ + _ = 7 at slack
      omega
    have all := card_compl_add_card U
    rw [hn] at all
    omega
  · omega

end ArkLib.ProximityGap.Frontier.QuarterSuccessorSiteBudget
