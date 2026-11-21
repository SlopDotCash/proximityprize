/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.FiveEighthCubicFactors

/-! # Three large affine heads on the five-eighth predecessor

A single cubic cannot carry the required population. A quadratic leaves room for
at most one affine component. Thus a larger family uses all three ordinate slots
on large affine components, which give distinct secants over the original field.
-/
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.FiveEighthThreeHeadCover
open SecondPrimeActualPopulations HalfPredecessorBadEventRichPointBridge HalfPredecessorSecantLines
variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I] [DecidableEq I]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : Code.WordStack F (Fin 2) I}

/-- The complete literal family is covered by three distinct large affine
secants outside at most thirteen scalar labels. -/
theorem cover_of_two_head_capacity (fam : Family dom δ u) {p : ℕ} [CharP F p] (hp : 1744830589<p)
    (hn : Fintype.card I=1073741824) (ht : ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊=402653185)
    (hbig : 1342177805 < fam.G.card) :
    ∃ H : Finset (LineParameter F), H⊆lineParameters fam ∧ H.card=3 ∧
      (∀ L∈H, 512<(pointsOn fam L).card) ∧ (fam.G \ H.biUnion (pointsOn fam)).card ≤ 13 := by
  classical
  let K := AlgebraicClosure F
  let φ := algebraMap F K
  let _ : CharP K p := charP_of_injective_ringHom φ.injective p
  obtain ⟨U,E,he,hu,hd,hcov,hcomp⟩ := FiveEighthCubicFactors.components fam φ hp hn ht.ge
  let P := population fam φ
  have mass : fam.G.card ≤ E.card+∑ f∈U, (P f).card :=
    (card_le_card hcov).trans ((card_union_le ..).trans (Nat.add_le_add_left card_biUnion_le _))
  have occupancy (L : LineParameter F) (hL : L∈lineParameters fam) :
      (pointsOn fam L).card≤671088640 := TwoLargeCoreCount.line_occupancy_le fam (e:=671088639) hn ht hL
  have hlin (f : Factor K) (hf : f∈U) (h1 : f.natDegree=1) : (P f).card≤671088640 := by
    by_cases hb : 512<(P f).card
    · obtain ⟨L,hL,hp'⟩ := (hcomp f hf).2.2.2 h1 hb
      exact (card_le_card hp').trans (occupancy L hL)
    · omega
  have linear (f : Factor K) (hf : f∈U) : f.natDegree=1 := by
    have pos := (hcomp f hf).1
    by_contra hn1
    let V := U.erase f
    have drop : (∑ g∈V, g.natDegree)+f.natDegree≤3 := by simpa [V,sum_erase_add _ _ hf] using hd
    have nv : V.card ≤ ∑ g∈V, g.natDegree := by
      simpa using (sum_le_sum (s:=V) fun g hg => (show 1 ≤ g.natDegree from (hcomp g (mem_of_mem_erase hg)).1))
    have other (g : Factor K) (hg : g∈V) : g.natDegree=1 := by
      have pp := (hcomp g (mem_of_mem_erase hg)).1
      have single := single_le_sum (s:=V) (f:=natDegree) (fun _ _ => Nat.zero_le _) hg
      exact le_antisymm (single.trans (show (∑ t∈V,t.natDegree) ≤ 1 by omega)) pp
    have hg : ∑ g∈V, (P g).card ≤ V.card*671088640 := by
      simpa using sum_le_sum (s:=V) fun g hg => hlin g (mem_of_mem_erase hg) (other g hg)
    have hm : fam.G.card ≤ E.card+((∑ g∈V,(P g).card)+(P f).card) := by
      simpa [V,sum_erase_add _ _ hf] using mass
    rcases (show f.natDegree=2 ∨ f.natDegree=3 by omega) with h2 | h3
    · have hh := (hcomp f hf).2.2.1 h2
      change (P f).card≤512 at hh
      omega
    · have hh := (hcomp f hf).2.1 h3
      change (P f).card≤1200005270 at hh
      omega
  have large (f : Factor K) (hf : f∈U) : 512<(P f).card := by
    by_contra! small
    have rest := sum_le_sum (s:=U.erase f) (fun g hg => hlin g (mem_of_mem_erase hg) (linear g (mem_of_mem_erase hg)))
    simp only [sum_const,smul_eq_mul,card_erase_of_mem hf] at rest
    have hm := sum_erase_add U (fun g => (P g).card) hf
    omega
  have existsLine (f : U) := (hcomp f f.property).2.2.2 (linear f f.property) (large f f.property)
  choose line hline hsub using existsLine
  let H := univ.image line
  have memH (f : U) : line f∈H := mem_image_of_mem _ (mem_univ _)
  have hH : H⊆lineParameters fam := by
    rintro L hL
    obtain ⟨f,_,rfl⟩ := mem_image.mp hL
    exact hline f
  have covers : fam.G ⊆ E ∪ H.biUnion (pointsOn fam) := by
    intro z hz
    rcases mem_union.mp (hcov hz) with h | h
    · exact mem_union_left _ h
    obtain ⟨f,hf,hz⟩ := mem_biUnion.mp h
    exact mem_union_right _ (mem_biUnion.mpr ⟨line ⟨f,hf⟩,memH _,hsub ⟨f,hf⟩ hz⟩)
  have hmass := (card_le_card covers).trans (card_union_le ..)
  have hcount : (H.biUnion (pointsOn fam)).card≤H.card*671088640 := card_biUnion_le.trans
    ((sum_le_sum (fun L hL => occupancy L (hH hL))).trans_eq (by simp))
  have hnH : H.card≤3 := (card_image_le.trans (by simp : (univ : Finset U).card=U.card).le).trans hu
  refine ⟨H,hH,by omega,?_,?_⟩
  · intro L hL
    obtain ⟨f,_,rfl⟩ := mem_image.mp hL
    exact (large f f.property).trans_le (card_le_card (hsub f))
  · apply (card_le_card (t:=E) ?_).trans he
    intro z hz
    obtain ⟨hG,hout⟩ := mem_sdiff.mp hz
    exact (mem_union.mp (covers hG)).resolve_right hout

/-- Threshold specialized to the three-head geometric predecessor estimate. -/
theorem cover (fam : Family dom δ u) {p : ℕ} [CharP F p] (hp : 1744830589<p)
    (hn : Fintype.card I=1073741824) (ht : ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊=402653185)
    (hbig : 1565873494 < fam.G.card) :
    ∃ H : Finset (LineParameter F), H⊆lineParameters fam ∧ H.card=3 ∧
      (∀ L∈H, 512<(pointsOn fam L).card) ∧ (fam.G \ H.biUnion (pointsOn fam)).card ≤ 13 :=
  cover_of_two_head_capacity fam hp hn ht (by omega)

#print axioms cover_of_two_head_capacity
#print axioms cover
end ArkLib.ProximityGap.Frontier.FiveEighthThreeHeadCover
