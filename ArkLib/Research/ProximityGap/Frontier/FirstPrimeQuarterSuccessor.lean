/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Johnson.WeightedCertificate
import ArkLib.Research.ProximityGap.Frontier.RateHalfRichHeadCensus
import ArkLib.Research.ProximityGap.Frontier.AgreementSubsetListPacking
import ArkLib.Research.ProximityGap.Frontier.TerminalCollinearHeadCount

/-! # Four polynomial heads near the first-prime quarter-radius successor

Five agreement sets of the stated sizes cannot coexist with the Reed--Solomon
pairwise intersection bound. Four sufficiently large joint cores therefore
cover all selected decoding polynomials. The argument works on every injective
domain at the given half-rate parameters.
-/

set_option autoImplicit false

open Finset Polynomial Code
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.FSMBCoreAbsorptionLadder
open scoped NNReal

namespace ProximityGap.FirstPrimeQuarterSuccessor

open ReedSolomon.HiddenDerivative in
/-- At the first successor, even the refined weighted Johnson exception formula exceeds
the first-prime budget for every valid choice of multiplicity, jet cutoff and height. -/
theorem johnson_exceeds_budget {m b H : ℕ}
    (cert : IsJohnsonWeightedCertificate 1073741824 536870911 805306367 m b H) :
    1073741825 ≤ johnsonWeightedRefinedExceptionCount 1073741824 536870911 805306367 b H := by
  obtain ⟨_, hb, _, _, rfl⟩ := cert
  have hh := hb.trans (johnsonWeightedHeight_ge 1073741824 536870911 805306367 m b)
  calc
    (1073741825 : ℚ) ≤ johnsonWeightedRefinedExceptionCount 1073741824 536870911 805306367 1 1 :=
      by norm_num [johnsonWeightedRefinedExceptionCount]
    _ ≤ _ := by
      unfold johnsonWeightedRefinedExceptionCount
      gcongr

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The integer incidence bound at which five large agreement sets become impossible. -/
theorem five_impossible (hn : Fintype.card I = 1073741824) (cores : Fin 5 → Finset I)
    (hsize : ∀ i, 787410671 ≤ (cores i).card)
    (hinter : ∀ i j, i ≠ j → (cores i ∩ cores j).card ≤ 536870911) : False := by
  have h := RateHalfRichHeadCensus.incidence_bound cores hsize hinter 3
  rw [hn] at h
  norm_num at h

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Nonempty I]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

omit [Fintype F] [DecidableEq F] in
/-- Every closed interleaved list has at most four words through 286331153 errors. -/
theorem four_list (dom : I ↪ F) (hn : Fintype.card I = 1073741824) (m : ℕ) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code dom 536870912 : Set (I → F)))
      (286331153 / 1073741824 : ℝ) ≤ 4 := by
  classical
  apply Lambda_le_of_forall_finset_card_le
  intro y T hT
  by_contra! hlarge
  obtain ⟨V, hV, hcard⟩ := Finset.exists_subset_card_eq (show 5 ≤ T.card by omega)
  let equiv := V.equivFin
  rw [hcard] at equiv
  let w (i : Fin 5) := (equiv.symm i).val
  have hmem (i : Fin 5) := hT (w i) (hV (equiv.symm i).property)
  let A (i : Fin 5) := univ.filter fun x => w i x = y x
  apply five_impossible hn A
  · intro i
    have hd := (mem_closeCodewordsRel_iff.mp (hmem i)).2
    have pos : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
    rw [relHammingDist_coe, hammingDist_comm, div_le_iff₀ pos, hn] at hd
    have hsum : agree (w i) y + hammingDist (w i) y = Fintype.card I := agree_add_hammingDist
    rw [hn] at hsum
    have he : hammingDist (w i) y ≤ 286331153 := by exact_mod_cast (show
      (hammingDist (w i) y : ℝ) ≤ 286331153 by linarith)
    change 787410671 ≤ agree (w i) y
    omega
  · intro i j hij
    have hne : w i ≠ w j := fun h => hij (equiv.symm.injective (Subtype.ext h))
    have bound := ReedSolomon.Interleaved.agree_lt_of_mem_interleavedCodeSet
      (mem_closeCodewordsRel_iff.mp (hmem i)).1 (mem_closeCodewordsRel_iff.mp (hmem j)).1 hne
    have sub : A i ∩ A j ⊆ univ.filter fun x => w i x = w j x := by
      intro x hx
      obtain ⟨hi,hj⟩ := mem_inter.mp hx
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm⟩
    have hs := card_le_card sub
    change (A i ∩ A j).card ≤ agree (w i) (w j) at hs
    omega

/-- If four distinct degree-bounded joint heads each explain at least 787410671 sites,
every selected bad-scalar decoder lies on one of them throughout this agreement range. -/
theorem four_cover (fam : BadScalarRichPointFamily dom 536870912 δ u)
    (hn : Fintype.card I = 1073741824)
    (ht : 787410671 ≤ ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊)
    (v : Fin 4 → LineParameter F) (hv : Function.Injective v)
    (hd : ∀ i, (v i).1.natDegree < 536870912 ∧ (v i).2.natDegree < 536870912)
    (hs : ∀ i, 787410671 ≤ (jointCore dom (u 0) (u 1) (v i).1 (v i).2).card) :
    ∀ z ∈ fam.G, ∃ i, z ∈ pointsOn fam (v i) := by
  intro z hz
  by_contra! hoff
  let W := fullAgreement dom (u 0) (u 1) z (fam.q z)
  let D (i : Fin 4) := jointCore dom (u 0) (u 1) (v i).1 (v i).2
  have hW : 787410671 ≤ W.card := ht.trans (fam.threshold_le z hz)
  have hWD (i : Fin 4) : (W ∩ D i).card ≤ 536870911 := by
    apply fullAgreement_inter_jointCore_card_le dom (u 0) (u 1) (by decide : 1 ≤ 536870912)
      (fam.degree_lt z hz) (hd i).1 (hd i).2
    exact fun he => hoff i ((mem_pointsOn_iff fam _ _).2 ⟨hz, he⟩)
  have hDD (i j : Fin 4) (hne : i ≠ j) : (D i ∩ D j).card ≤ 536870911 := by
    apply jointCore_inter_jointCore_card_le dom (u 0) (u 1) (by decide : 1 ≤ 536870912)
      (hd i).1 (hd i).2 (hd j).1 (hd j).2
    by_contra! he
    exact hne (hv (Prod.ext he.1 he.2))
  apply five_impossible hn (Fin.cons W D)
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hW
    · exact hs j
  · intro i j
    refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
    · exact fun h => (h rfl).elim
    · exact fun _ => hWD b
    · simpa [Finset.inter_comm] using (fun _ : a.succ ≠ 0 => hWD a)
    · intro hab
      exact hDD a b (fun h => hab (congrArg Fin.succ h))

omit [Nonempty I] [Fintype I] in
/-- The second moment on the union controls uncovered sites. -/
theorem core_union_bound (cores : Fin 4 → Finset I) (w b : ℕ)
    (hsize : ∀ i, w ≤ (cores i).card)
    (hpair : ∀ i j, i ≠ j → (cores i ∩ cores j).card ≤ b) :
    16*w ≤ 12*b + 6*(univ.biUnion cores).card := by
  classical
  let U := univ.biUnion cores
  let T (i : Fin 4) := (cores i).subtype (fun x => x ∈ U)
  have hsub (i : Fin 4) : cores i ⊆ U := fun x hx => mem_biUnion.mpr ⟨i, mem_univ i, hx⟩
  have hcard (i : Fin 4) : (T i).card = (cores i).card := by
    rw [Finset.card_subtype]
    simp [Finset.filter_true_of_mem (fun _ hx => hsub i hx)]
  have hint (i j : Fin 4) : T i ∩ T j = (cores i ∩ cores j).subtype (fun x => x ∈ U) := by
    ext x
    simp [T]
  have h := RateHalfRichHeadCensus.incidence_bound T (fun i => (hcard i).symm ▸ hsize i)
    (fun i j hij => by
      rw [hint, Finset.card_subtype]
      exact (card_le_card (filter_subset ..)).trans (hpair i j hij)) 2
  simp only [Fintype.card_coe] at h
  change 16*w ≤ 12*b + 6*U.card
  omega

omit [Nonempty I] in
/-- Nonconstant primitive direction reduces the pairwise overlap by one,
leaving at most one coordinate outside four successor-sized cores. -/
theorem at_most_one_hole (hn : Fintype.card I = 1073741824) (cores : Fin 4 → Finset I)
    (hsize : ∀ i, 805306366 ≤ (cores i).card)
    (hpair : ∀ i j, i ≠ j → (cores i ∩ cores j).card ≤ 536870910) :
    Fintype.card I - (univ.biUnion cores).card ≤ 1 := by
  have h := core_union_bound cores _ _ hsize hpair
  omega

/-- A pair-overlap cap controls the number of labels left beyond the length budget. -/
theorem four_head_count_of_overlap (fam : BadScalarRichPointFamily dom 536870912 δ u)
    (hn : Fintype.card I = 1073741824)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = 805306367)
    (v : Fin 4 → LineParameter F) (hv : Function.Injective v)
    (hline : ∀ i, v i ∈ lineParameters fam)
    (hs : ∀ i, 787410671 ≤ (jointCore dom (u 0) (u 1) (v i).1 (v i).2).card)
    {b holes : ℕ}
    (hpair : ∀ i j, i ≠ j →
      ((jointCore dom (u 0) (u 1) (v i).1 (v i).2) ∩
        (jointCore dom (u 0) (u 1) (v j).1 (v j).2)).card ≤ b)
    (hcost : 12*b + 6*1073741824 < 16*805306366 + 6*(holes+1)) :
    fam.G.card ≤ 1073741824 + 3*holes := by
  classical
  let cores (i : Fin 4) := jointCore dom (u 0) (u 1) (v i).1 (v i).2
  let loc (i : Fin 4) := (pointsOn fam (v i)).card
  have hd (i : Fin 4) := lineParameter_degree_lt fam (hline i)
  have cover := four_cover fam hn (by omega) v hv hd hs
  have hloc (i : Fin 4) : loc i ≤ 268435458 :=
    ArkLib.ProximityGap.Frontier.TwoLargeCoreCount.line_occupancy_le fam
      (by omega : Fintype.card I = 268435457 + 805306367) ht (hline i)
  have sub : fam.G ⊆ univ.biUnion (fun i => pointsOn fam (v i)) := by
    intro z hz
    obtain ⟨i,hi⟩ := cover z hz
    exact mem_biUnion.mpr ⟨i, mem_univ _, hi⟩
  have total : fam.G.card ≤ ∑ i, loc i := (card_le_card sub).trans card_biUnion_le
  by_contra! hlarge
  have strong (i : Fin 4) : 805306366 ≤ (cores i).card := by
    by_contra! hlow
    have hp := pointsOn_card_mul_max_add_core_le fam (hline i)
    rw [ht, hn] at hp
    change loc i * max 1 (805306367 - (cores i).card) + (cores i).card ≤ 1073741824 at hp
    have htwo := Nat.mul_le_mul_left (loc i)
      (show 2 ≤ max 1 (805306367 - (cores i).card) by omega)
    have hother : ∑ j ∈ univ.erase i, loc j ≤ 3*268435458 := by
      calc _ ≤ ∑ _j ∈ univ.erase i, 268435458 := sum_le_sum fun j _ => hloc j
           _ = _ := by simp
    have hsplit := Finset.add_sum_erase univ loc (mem_univ i)
    have hl : 787410671 ≤ (cores i).card := hs i
    omega
  have hunion := core_union_bound cores _ _ strong hpair
  let H := univ.image v
  have hH : H ⊆ lineParameters fam := by
    intro c hc
    obtain ⟨i, _, rfl⟩ := mem_image.mp hc
    exact hline i
  have hdet (i : Fin 4) : RateHalfRichHeadCensus.Rich dom (u 0) (u 1) (v i) :=
    ⟨(hd i).1,(hd i).2, (by decide : 760567125 ≤ 805306366).trans (strong i)⟩
  have hb := TerminalCollinearHeadCount.collinear_card fam H hH (v 0) (v 1)
    (hv.ne (by decide)) (fun c hc => by
      obtain ⟨i, _, rfl⟩ := mem_image.mp hc
      exact RateHalfRichHeadCensus.determinant_zero dom (u 0) (u 1) hn (hdet 0) (hdet 1) (hdet i))
  have hcard : H.card = 4 := by simp [H, card_image_of_injective _ hv]
  rw [hcard,hn] at hb
  simp only [H, image_biUnion] at hb
  change (univ.biUnion (fun i => pointsOn fam (v i))).card ≤
    (univ.biUnion cores).card + (1073741824 - (univ.biUnion cores).card)*4 at hb
  have hcap := Finset.card_le_univ (univ.biUnion cores)
  have hs := (card_le_card sub).trans hb
  omega

/-- Four determined secants with the stated joint agreement sizes cover a total of
at most the length budget plus nine at the successor. -/
theorem four_head_count (fam : BadScalarRichPointFamily dom 536870912 δ u)
    (hn : Fintype.card I = 1073741824)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = 805306367)
    (v : Fin 4 → LineParameter F) (hv : Function.Injective v)
    (hline : ∀ i, v i ∈ lineParameters fam)
    (hs : ∀ i, 787410671 ≤ (jointCore dom (u 0) (u 1) (v i).1 (v i).2).card) :
    fam.G.card ≤ 1073741833 := by
  apply four_head_count_of_overlap fam hn ht v hv hline hs (b := 536870911)
    (holes := 3) _ (by decide)
  intro i j hne
  have hd (a : Fin 4) := lineParameter_degree_lt fam (hline a)
  apply jointCore_inter_jointCore_card_le dom (u 0) (u 1) (by decide : 1 ≤ 536870912)
    (hd i).1 (hd i).2 (hd j).1 (hd j).2
  by_contra! he
  exact hne (hv (Prod.ext he.1 he.2))

#print axioms johnson_exceeds_budget
#print axioms five_impossible
#print axioms four_list
#print axioms four_cover
#print axioms at_most_one_hole
#print axioms four_head_count_of_overlap
#print axioms four_head_count

end ProximityGap.FirstPrimeQuarterSuccessor
