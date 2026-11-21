/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ProjectiveDirectionIncidence

/-! # Counting bad labels on heavy affine heads of a projective direction -/
set_option autoImplicit false
namespace ProximityGap.AffineHeadBudget
open Finset Polynomial
variable {I F : Type*} [Fintype I] [DecidableEq I] [Field F] [DecidableEq F]

/-- Each polynomial in a finite family accounts for at most its degree many
distinct field roots, including the empty list of roots of the zero polynomial. -/
private theorem root_card (p : F[X]) : p.roots.toFinset.card ≤ p.natDegree :=
  (Multiset.toFinset_card_le _).trans (card_roots' p)

private theorem hbound {α β : Type*} [DecidableEq β] (U : Finset α) (f : α → Finset β) (b : ℕ)
    (hf : ∀ i ∈ U, (f i).card ≤ b) : (U.biUnion f).card ≤ U.card*b := by
  exact card_biUnion_le.trans ((sum_le_sum hf).trans_eq (by simp))

/-- The symbolic class of a polynomial scalar head at a fixed set of row pencils. -/
noncomputable def core (w V : I → F[X]) (h : F[X]) := univ.filter fun i => w i = h*V i

/-- Sites with both polynomials identically zero belong to every symbolic class. -/
noncomputable def common (w V : I → F[X]) := univ.filter fun i => w i = 0 ∧ V i = 0

/-- The genuine bad labels captured by a family of heavy scalar heads have
this budget. The common sites are removed before computing the uncovered
sites. One head admits the stronger separate n−T bound. -/
theorem heavy_budget (w V : I → F[X]) (H : Finset F[X]) (B : Finset F)
    (h : F → F[X]) (S : F → Finset I) (T : ℕ)
    (hsize : ∀ r ∈ H, T < (core w V r).card)
    (hw : ∀ i, (w i).natDegree ≤ 1) (hV : ∀ i, (V i).natDegree ≤ 1)
    (hhead : ∀ r ∈ H, r.natDegree ≤ 1 ∧ ∀ i, (r*V i).natDegree ≤ 1)
    (hh : ∀ z ∈ B, h z ∈ H)
    (hfit : ∀ z ∈ B, ∀ i ∈ S z, (w i).eval z = ((h z)*V i).eval z)
    (hbad : ∀ z ∈ B, ∃ i ∈ S z, w i ≠ (h z)*V i) :
    ∃ K E : ℕ, K+E+(common w V).card = Fintype.card I ∧
      H.card*(T+1-(common w V).card) ≤ K ∧
      B.card ≤ K+E*H.card+H.card^2 ∧
      (H.card = 0 → B.card = 0) ∧
      (H.card = 1 → B.card ≤ Fintype.card I-T-1) := by
  classical
  let J := common w V
  let Tcore (r : F[X]) := core w V r \ J
  let K := H.biUnion Tcore
  let E := univ \ (K ∪ J)
  have hKJ : Disjoint K J := by
    apply disjoint_left.mpr
    intro i hi
    obtain ⟨r,_,hi⟩ := mem_biUnion.mp hi
    exact (mem_sdiff.mp hi).2
  have htot : K.card+E.card+J.card = Fintype.card I := by
    have hc := card_sdiff_add_card_eq_card (subset_univ (K ∪ J))
    rw [card_union_of_disjoint hKJ,card_univ] at hc
    dsimp [E]
    omega
  have hdis : (↑H : Set F[X]).PairwiseDisjoint Tcore := by
    intro r _ p _ hne
    apply disjoint_left.mpr
    intro i hi hj
    obtain ⟨hri,hnJ⟩ := mem_sdiff.mp hi
    obtain ⟨hpi,_⟩ := mem_sdiff.mp hj
    have hr := (mem_filter.mp hri).2
    have hp := (mem_filter.mp hpi).2
    have hz : V i = 0 := (mul_eq_mul_right_iff.mp (hr.symm.trans hp)).resolve_left hne
    exact hnJ (mem_filter.mpr ⟨mem_univ _,by simpa [hz] using hr,hz⟩)
  have hK : H.card*(T+1-J.card) ≤ K.card := by
    dsimp [K]
    rw [card_biUnion hdis]
    calc _ = ∑ _r ∈ H, (T+1-J.card) := by simp
         _ ≤ _ := sum_le_sum fun r hr =>
           (Nat.sub_le_sub_right (hsize r hr) _).trans (le_card_sdiff ..)
  let poles := K.biUnion fun i => (V i).roots.toFinset
  let accidental (r : F[X]) (i : I) := (w i-r*V i).roots.toFinset
  let outside := E.biUnion fun i => H.biUnion fun r => accidental r i
  let collisions := H.biUnion fun r => H.biUnion fun p => (r-p).roots.toFinset
  have hacc (r : F[X]) (hr : r ∈ H) (i : I) : (accidental r i).card ≤ 1 :=
    (root_card _).trans ((natDegree_sub_le ..).trans (max_le (hw i) ((hhead r hr).2 i)))
  have hpoles : poles.card ≤ K.card := by
    simpa only [Nat.mul_one] using hbound K _ 1 (fun i _ => (root_card _).trans (hV i))
  have hout : outside.card ≤ E.card*H.card := by
    apply hbound
    intro i _
    simpa only [Nat.mul_one] using hbound H _ 1 (fun r hr => hacc r hr i)
  have hcol : collisions.card ≤ H.card^2 := by
    rw [sq]
    apply hbound
    intro r hr
    simpa only [Nat.mul_one] using hbound H _ 1 (fun p hp =>
      (root_card _).trans ((natDegree_sub_le ..).trans (max_le (hhead r hr).1 (hhead p hp).1)))
  have hsub : B ⊆ poles ∪ outside ∪ collisions := by
    intro z hz
    obtain ⟨i,hi,hne⟩ := hbad z hz
    have he := hfit z hz i hi
    have hroot : z ∈ accidental (h z) i :=
      Multiset.mem_toFinset.mpr ((mem_roots (sub_ne_zero.mpr hne)).mpr
        (by simpa [IsRoot] using sub_eq_zero.mpr he))
    by_cases hiK : i ∈ K
    · have hin := hiK
      obtain ⟨p,hp,hic⟩ := mem_biUnion.mp hin
      obtain ⟨hc,hnJ⟩ := mem_sdiff.mp hic
      have hwc := (mem_filter.mp hc).2
      have hvi : V i ≠ 0 := fun h =>
        hnJ (mem_filter.mpr ⟨mem_univ _,by simpa [h] using hwc,h⟩)
      have hrp : p ≠ h z := fun h => hne (h ▸ hwc)
      by_cases hv : (V i).eval z = 0
      · exact mem_union_left _ (mem_union_left _ (mem_biUnion.mpr
          ⟨i,hiK,Multiset.mem_toFinset.mpr ((mem_roots hvi).mpr hv)⟩))
      · have heval : p.eval z = (h z).eval z := mul_right_cancel₀ hv
          (by simpa [hwc] using he)
        exact mem_union_right _ (mem_biUnion.mpr ⟨p,hp,mem_biUnion.mpr
          ⟨h z,hh z hz,Multiset.mem_toFinset.mpr ((mem_roots (sub_ne_zero.mpr hrp)).mpr
            (by simpa [IsRoot] using sub_eq_zero.mpr heval))⟩⟩)
    · have hnotJ : i ∉ J := by
        intro hiJ
        obtain ⟨hwi,hvi⟩ := (mem_filter.mp hiJ).2
        exact hne (by simp [hwi,hvi])
      have hiE : i ∈ E := mem_sdiff.mpr ⟨mem_univ _,fun h => (mem_union.mp h).elim hiK hnotJ⟩
      exact mem_union_left _ (mem_union_right _ (mem_biUnion.mpr
        ⟨i,hiE,mem_biUnion.mpr ⟨h z,hh z hz,hroot⟩⟩))
  have hcnt := (card_le_card hsub).trans (card_union_le ..)
  have hcnt' := card_union_le poles outside
  refine ⟨K.card,E.card,htot,hK,by omega,?_,?_⟩
  · intro he
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    simpa [card_eq_zero.mp he] using hh z hz
  · intro hone
    obtain ⟨r,hr⟩ := card_eq_one.mp hone
    have hrH : r ∈ H := by simp [hr]
    let U := univ \ core w V r
    have hcover : B ⊆ U.biUnion (accidental r) := by
      intro z hz
      have he : h z = r := by simpa [hr] using hh z hz
      obtain ⟨i,hi,hne⟩ := hbad z hz
      rw [he] at hne
      have hiU : i ∈ U := mem_sdiff.mpr ⟨mem_univ _,fun h => hne (mem_filter.mp h).2⟩
      have hft := hfit z hz i hi
      rw [he] at hft
      exact mem_biUnion.mpr ⟨i,hiU,Multiset.mem_toFinset.mpr
        ((mem_roots (sub_ne_zero.mpr hne)).mpr (by simpa [IsRoot] using sub_eq_zero.mpr hft))⟩
    have hu := (card_le_card hcover).trans (hbound U _ 1 (fun i _ => hacc r hrH i))
    have hs := hsize r hrH
    simp only [U,card_sdiff_of_subset (subset_univ _),card_univ,Nat.mul_one] at hu
    omega

#print axioms heavy_budget
end ProximityGap.AffineHeadBudget
