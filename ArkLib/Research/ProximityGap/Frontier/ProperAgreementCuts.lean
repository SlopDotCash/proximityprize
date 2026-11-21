/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorSecantLines
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Proper received-site cuts for families of polynomial witnesses

A subfamily with at most `d` common agreements has a proper received-site cut
retaining at least the fraction `(t-d)/(n-d)` of its members. A subfamily of bad
scalars with more common agreements has at most `n-t+1` members.
-/
set_option autoImplicit false
open Finset
namespace ArkLib.ProximityGap.Frontier.ProperAgreementCuts

variable {I J : Type*} [Fintype I] [DecidableEq I]

/-- Sites hit by every selected witness. -/
noncomputable def commonSites (M : Finset J) (S : J → Finset I) : Finset I := by
  classical
  exact univ.filter fun i => ∀ z ∈ M, i ∈ S z

theorem mem_commonSites {M : Finset J} {S : J → Finset I} {i : I} :
    i ∈ commonSites M S ↔ ∀ z ∈ M, i ∈ S z := by classical simp [commonSites]

/-- After deleting the common sites, a maximum-incidence remaining site gives
a proper cut. The exact retained fraction uses the message degree. -/
theorem proper_cut (M : Finset J) (S : J → Finset I) {d t : ℕ}
    (hdt : d < t) (htn : t ≤ Fintype.card I)
    (hrich : ∀ z ∈ M, t ≤ (S z).card) (hcommon : (commonSites M S).card ≤ d) :
    ∃ i, (M.filter fun z => i ∈ S z).card < M.card ∧
      M.card * (t-d) ≤ (M.filter fun z => i ∈ S z).card * (Fintype.card I-d) := by
  classical
  let H := commonSites M S
  let U := Hᶜ
  let L := fun i => (M.filter fun z => i ∈ S z).card
  have hc : H.card + U.card = Fintype.card I := card_add_card_compl H
  change H.card ≤ d at hcommon
  obtain ⟨i, hi, hmax⟩ := U.exists_max_image L (card_pos.mp (by omega))
  have hproper : L i < M.card := by
    have hle : L i ≤ M.card := card_filter_le ..
    by_contra! h
    have hall := card_filter_eq_iff.mp (hle.antisymm h)
    exact (mem_compl.mp hi) (mem_commonSites.mpr hall)
  refine ⟨i,hproper,?_⟩
  have htotal : M.card * (t-H.card) ≤ U.card * L i := by
    calc
      _ = ∑ _z ∈ M, (t-H.card) := by simp
      _ ≤ ∑ z ∈ M, (U.filter (fun j => j ∈ S z)).card := by
        apply sum_le_sum
        intro z hz
        have hsub : H ⊆ S z := fun _ hj => mem_commonSites.mp hj z hz
        have heq : U.filter (fun j => j ∈ S z) = S z \ H := by
          ext j
          simp [U, and_comm]
        rw [heq, card_sdiff_of_subset hsub]
        exact Nat.sub_le_sub_right (hrich z hz) _
      _ = ∑ j ∈ U, L j := by simp only [L, card_filter]; rw [sum_comm]
      _ ≤ ∑ _j ∈ U, L i := sum_le_sum hmax
      _ = _ := by simp
  have ht : t-H.card = t-d + (d-H.card) := by omega
  have hn : U.card = (Fintype.card I-d) + (d-H.card) := by omega
  have hdrop := Nat.mul_le_mul_right (d-H.card) hproper.le
  rw [ht,hn,mul_add,add_mul] at htotal
  change M.card * (t-d) ≤ L i * (Fintype.card I-d)
  rw [Nat.mul_comm (Fintype.card I-d), Nat.mul_comm (d-H.card)] at htotal
  omega

open HalfPredecessorBadEventRichPointBridge HalfPredecessorLineCoreGeometry HalfPredecessorSecantLines
open Code
open scoped NNReal
variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [Nonempty ι] [DecidableEq ι] {dom : ι ↪ F} {δ : ℝ≥0}
  {u : WordStack F (Fin 2) ι}

/-- More than `d` common received agreements force all selected polynomials
onto one secant, whose bad-parameter population fits the complement budget. -/
theorem common_head_bound {d t : ℕ} (fam : BadScalarRichPointFamily dom (d+1) δ u)
    (M : Finset F) (hM : M ⊆ fam.G)
    (ht : t ≤ ⌈(1-δ)*(Fintype.card ι : ℝ≥0)⌉₊) (htn : t ≤ Fintype.card ι)
    (hcommon : d < (commonSites M (fun z => fullAgreement dom (u 0) (u 1) z (fam.q z))).card) :
    M.card ≤ Fintype.card ι-t+1 := by
  classical
  by_cases hsize : 1 < M.card
  · obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp hsize
    let l := secantParameter fam a b
    have hl : l ∈ lineParameters fam := secantParameter_mem_lineParameters fam (hM ha) (hM hb) hab
    have hsub : M ⊆ pointsOn fam l := by
      intro c hc
      by_cases he : a=c
      · subst c
        exact first_point_mem_pointsOn_secant fam (hM ha)
      apply (mem_pointsOn_iff ..).mpr
      refine ⟨hM hc,third_point_on_secant_line_of_slope_eq he ?_⟩
      by_contra hn
      have hbound := triple_fullAgreement_card_le_pred_of_slope_ne dom (u 0) (u 1)
        (by omega : 1 ≤ d+1) hab he (fam.degree_lt a (hM ha)) (fam.degree_lt b (hM hb))
        (fam.degree_lt c (hM hc)) (Ne.symm hn)
      have htr : commonSites M (fun z => fullAgreement dom (u 0) (u 1) z (fam.q z)) ⊆
          fullAgreement dom (u 0) (u 1) a (fam.q a) ∩ fullAgreement dom (u 0) (u 1) b (fam.q b)
            ∩ fullAgreement dom (u 0) (u 1) c (fam.q c) := by
        intro j hj
        have hh := mem_commonSites.mp hj
        exact mem_inter.mpr ⟨mem_inter.mpr ⟨hh a ha,hh b hb⟩,hh c hc⟩
      exact hcommon.not_ge ((card_le_card htr).trans (by simpa using hbound))
    have hle := card_le_card hsub
    have hpack := pointsOn_card_mul_max_add_core_le fam hl
    let C := jointCore dom (u 0) (u 1) l.1 l.2
    have hsmall : (pointsOn fam l).card * max 1 (t-C.card) + C.card ≤ Fintype.card ι :=
      le_trans (Nat.add_le_add_right
        (Nat.mul_le_mul_left _ (max_le_max_left _ (Nat.sub_le_sub_right ht _))) _) hpack
    exact hle.trans (line_card_le_complement_threshold_succ htn (card_le_univ C) (by omega) hsmall)
  · omega

/-- A large literal MCA subfamily has a received hyperplane which misses at least
one witness while retaining the stated fraction. This also applies to the
members of any fixed coefficient-space component. -/
theorem large_family_proper_cut {d t : ℕ} (fam : BadScalarRichPointFamily dom (d+1) δ u)
    (M : Finset F) (hM : M ⊆ fam.G) (hdt : d < t)
    (ht : t ≤ ⌈(1-δ)*(Fintype.card ι : ℝ≥0)⌉₊) (htn : t ≤ Fintype.card ι)
    (hlarge : Fintype.card ι-t+1 < M.card) :
    ∃ i, let L := (M.filter fun z => i ∈ fullAgreement dom (u 0) (u 1) z (fam.q z)).card
         L < M.card ∧ M.card*(t-d) ≤ L*(Fintype.card ι-d) := by
  apply proper_cut _ _ hdt htn (fun z hz => ht.trans (fam.threshold_le z (hM hz)))
  by_contra! hcommon
  exact hlarge.not_ge (common_head_bound fam M hM ht htn hcommon)

#print axioms large_family_proper_cut
#print axioms proper_cut
#print axioms common_head_bound
end ArkLib.ProximityGap.Frontier.ProperAgreementCuts
