/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved

/-! # Agreement bounds for three distinct words

At each site, every agreement after the first requires an agreeing pair of words.
This also applies when the symbols are columns of a positively interleaved code.
-/

namespace ProximityGap.ThreeWordAgreement

open Code Finset

variable {I V : Type*} [Fintype I] [DecidableEq V]

open Classical in
private theorem overlap_le (x z y : I → V) :
    ((univ.filter fun i => x i = y i) ∩ (univ.filter fun i => z i = y i)).card ≤
      agree x z := by
  apply card_le_card
  intro i hi
  obtain ⟨hx, hz⟩ := mem_inter.mp hi
  exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2.trans (mem_filter.mp hz).2.symm⟩

/-- The simultaneous agreement of three words is controlled by two- and three-set counts. -/
theorem agreement_bounds (x z w y : I → V) :
    agree x y + agree z y ≤ Fintype.card I + agree x z ∧
    agree x y + agree z y + agree w y ≤
      Fintype.card I + agree x z + agree x w + agree z w := by
  classical
  let A := univ.filter fun i => x i = y i
  let B := univ.filter fun i => z i = y i
  let C := univ.filter fun i => w i = y i
  have hab : (A ∩ B).card ≤ agree x z := overlap_le x z y
  have hac : (A ∩ C).card ≤ agree x w := overlap_le x w y
  have hbc : (B ∩ C).card ≤ agree z w := overlap_le z w y
  have hu := card_union_add_card_inter A B
  have hv := card_union_add_card_inter (A ∪ B) C
  have hpair := card_le_univ (A ∪ B)
  have htriple := card_le_univ (A ∪ B ∪ C)
  have hcross : ((A ∪ B) ∩ C).card ≤ (A ∩ C).card + (B ∩ C).card := by
    rw [Finset.union_inter_distrib_right]
    exact card_union_le _ _
  change A.card + B.card ≤ _ ∧ A.card + B.card + C.card ≤ _
  omega

/-- If either incidence inequality fails at agreement count t, every closed interleaved
RS list whose radius forces t agreements has at most two members. -/
theorem interleaved_list_le_two {F : Type*} [Field F] [Fintype F] [Nonempty I]
    (D : I ↪ F) (k m t : ℕ) (δ : ℝ)
    (hδ : δ * Fintype.card I < (Fintype.card I : ℝ) - t + 1)
    (hcount : Fintype.card I + (k-1) < 2*t ∨ Fintype.card I + 3*(k-1) < 3*t) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → F))) δ ≤ 2 := by
  classical
  let C := interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → F))
  apply Lambda_le_iff_forall_ncard_le.mpr
  intro y
  refine ⟨Set.toFinite _, ?_⟩
  let S := (closeCodewordsRel C y δ).toFinset
  change (closeCodewordsRel C y δ).ncard ≤ 2
  rw [Set.ncard_eq_toFinset_card']
  change S.card ≤ 2
  by_contra! hfail
  obtain ⟨x, z, w, hx, hz, hw, hxz, hxw, hzw⟩ := Finset.two_lt_card_iff.mp hfail
  have info (v) (hv : v ∈ S) : v ∈ C ∧ t ≤ agree v y := by
    obtain ⟨hc, hd⟩ := mem_closeCodewordsRel_iff.mp (Set.mem_toFinset.mp hv)
    refine ⟨hc, ?_⟩
    have hn : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
    rw [relHammingDist_coe, hammingDist_comm, div_le_iff₀ hn] at hd
    have hsum : (agree v y : ℝ) + (hammingDist v y : ℝ) = Fintype.card I := by
      exact_mod_cast agree_add_hammingDist
    have hround : t < agree v y + 1 := by
      exact_mod_cast (show (t : ℝ) < agree v y + 1 by linarith)
    omega
  obtain ⟨hxc, hxt⟩ := info x hx
  obtain ⟨hzc, hzt⟩ := info z hz
  obtain ⟨hwc, hwt⟩ := info w hw
  have h₁ := ReedSolomon.Interleaved.agree_lt_of_mem_interleavedCodeSet hxc hzc hxz
  have h₂ := ReedSolomon.Interleaved.agree_lt_of_mem_interleavedCodeSet hxc hwc hxw
  have h₃ := ReedSolomon.Interleaved.agree_lt_of_mem_interleavedCodeSet hzc hwc hzw
  have ⟨hpair, htriple⟩ := agreement_bounds x z w y
  omega

#print axioms agreement_bounds
#print axioms interleaved_list_le_two

end ProximityGap.ThreeWordAgreement
