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
secants. -/
theorem primitive_cover (fam : Family dom δ u) {p : ℕ} [CharP F p] (hp : 1744830589<p)
    (hn : Fintype.card I=1073741824) {e : ℕ} (hl : 610000000≤e) (hu : e≤671088639)
    (ht : ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊=1073741824-e)
    {s : ℕ} (hs : 48 ≤ s) (hsu : s ≤ 512) (hbig : 2*(e+1)+s < fam.G.card) :
    ∃ H : Finset (LineParameter F), H⊆lineParameters fam ∧ H.card=3 ∧
      (∀ L∈H, s<(pointsOn fam L).card) ∧ fam.G ⊆ H.biUnion (pointsOn fam) := by
  classical
  let K := AlgebraicClosure F
  let φ := algebraMap F K
  let _ : CharP K p := charP_of_injective_ringHom φ.injective p
  obtain ⟨U,hu,hd,hcov,hcomp⟩ := FiveEighthCubicFactors.primitive_components fam φ hp hn (by omega)
  let P := population fam φ
  have mass : fam.G.card ≤ ∑ f∈U, (P f).card :=
    (card_le_card hcov).trans card_biUnion_le
  have occupancy (L : LineParameter F) (hL : L∈lineParameters fam) :
      (pointsOn fam L).card≤(e+1) := TwoLargeCoreCount.line_occupancy_le fam (e:=e) (by omega) ht hL
  have hlin (f : Factor K) (hf : f∈U) (h1 : f.natDegree=1) : (P f).card≤(e+1) := by
    by_cases hb : s<(P f).card
    · obtain ⟨L,hL,hp'⟩ := (hcomp f hf).2.2.2 h1 (hs.trans_lt hb)
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
    have hg : ∑ g∈V, (P g).card ≤ V.card*(e+1) := by
      simpa using sum_le_sum (s:=V) fun g hg => hlin g (mem_of_mem_erase hg) (other g hg)
    have hm : fam.G.card ≤ (∑ g∈V,(P g).card)+(P f).card := by
      simpa [V,sum_erase_add _ _ hf] using mass
    rcases (show f.natDegree=2 ∨ f.natDegree=3 by omega) with h2 | h3
    · have hh := (hcomp f hf).2.2.1 h2
      change (P f).card≤512 at hh
      have hr := Nat.mul_le_mul_right (e+1) (show V.card≤1 by omega)
      simp only [one_mul] at hr
      omega
    · have hh := (hcomp f hf).2.1 h3
      change (P f).card≤1200005270 at hh
      have hempty : V.card=0 := by omega
      rw [hempty,zero_mul] at hg
      omega
  have large (f : Factor K) (hf : f∈U) : s<(P f).card := by
    by_contra! small
    have rest := sum_le_sum (s:=U.erase f) (fun g hg => hlin g (mem_of_mem_erase hg) (linear g (mem_of_mem_erase hg)))
    simp only [sum_const,smul_eq_mul,card_erase_of_mem hf] at rest
    have hm := sum_erase_add U (fun g => (P g).card) hf
    have hr := Nat.mul_le_mul_right (e+1) (show U.card-1 ≤ 2 by omega)
    omega
  have existsLine (f : U) := (hcomp f f.property).2.2.2 (linear f f.property) (hs.trans_lt (large f f.property))
  choose line hline hsub using existsLine
  let H := univ.image line
  have memH (f : U) : line f∈H := mem_image_of_mem _ (mem_univ _)
  have hH : H⊆lineParameters fam := by
    rintro L hL
    obtain ⟨f,_,rfl⟩ := mem_image.mp hL
    exact hline f
  have covers : fam.G ⊆ H.biUnion (pointsOn fam) := by
    intro z hz
    obtain ⟨f,hf,hz⟩ := mem_biUnion.mp (hcov hz)
    exact mem_biUnion.mpr ⟨line ⟨f,hf⟩,memH _,hsub ⟨f,hf⟩ hz⟩
  have hmass := card_le_card covers
  have hcount : (H.biUnion (pointsOn fam)).card≤H.card*(e+1) := card_biUnion_le.trans
    ((sum_le_sum (fun L hL => occupancy L (hH hL))).trans_eq (by simp))
  have hnH : H.card≤3 := (card_image_le.trans (by simp : (univ : Finset U).card=U.card).le).trans hu
  have hthree : H.card=3 := by
    by_contra! hn3
    have hr := Nat.mul_le_mul_right (e+1) (show H.card≤2 by omega)
    omega
  refine ⟨H,hH,hthree,?_,covers⟩
  · intro L hL
    obtain ⟨f,_,rfl⟩ := mem_image.mp hL
    exact (large f f.property).trans_le (card_le_card (hsub f))

/-- The complete literal family is covered by three distinct large affine
secants outside at most ten scalar labels. -/
theorem degree_ten_cover (fam : Family dom δ u) {p : ℕ} [CharP F p] (hp : 1744830589<p)
    (hn : Fintype.card I=1073741824) {e : ℕ} (hl : 610000000≤e) (hu : e≤671088639)
    (ht : ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊=1073741824-e)
    {s : ℕ} (hs : 48 ≤ s) (hsu : s ≤ 512) (hbig : 2*(e+1)+s+10 < fam.G.card) :
    ∃ H : Finset (LineParameter F), H⊆lineParameters fam ∧ H.card=3 ∧
      (∀ L∈H, s<(pointsOn fam L).card) ∧ (fam.G \ H.biUnion (pointsOn fam)).card ≤ 10 := by
  obtain ⟨H,hH,h3,hlarge,hcov⟩ := primitive_cover fam hp hn hl hu ht hs hsu (by omega)
  exact ⟨H,hH,h3,hlarge,by simp [sdiff_eq_empty_iff_subset.mpr hcov]⟩

/-- The complete literal family is covered by three distinct large affine
secants outside at most thirteen scalar labels. -/
theorem cover_above_budget (fam : Family dom δ u) {p : ℕ} [CharP F p] (hp : 1744830589<p)
    (hn : Fintype.card I=1073741824) {e : ℕ} (hl : 610000000≤e) (hu : e≤671088639)
    (ht : ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊=1073741824-e)
    {s : ℕ} (hs : 184 ≤ s) (hsu : s ≤ 512) (hbig : 2*(e+1)+s+13 < fam.G.card) :
    ∃ H : Finset (LineParameter F), H⊆lineParameters fam ∧ H.card=3 ∧
      (∀ L∈H, s<(pointsOn fam L).card) ∧ (fam.G \ H.biUnion (pointsOn fam)).card ≤ 13 := by
  obtain ⟨H,hH,h3,hlarge,hex⟩ := degree_ten_cover fam hp hn hl hu ht
    (s:=s) (by omega) hsu (by omega)
  exact ⟨H,hH,h3,hlarge,hex.trans (by decide)⟩

/-- Specialization to the last predecessor of the five-eighths plateau. -/
theorem cover_of_two_head_capacity (fam : Family dom δ u) {p : ℕ} [CharP F p] (hp : 1744830589<p)
    (hn : Fintype.card I=1073741824) (ht : ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊=402653185)
    (hbig : 1342177805 < fam.G.card) :
    ∃ H : Finset (LineParameter F), H⊆lineParameters fam ∧ H.card=3 ∧
      (∀ L∈H, 512<(pointsOn fam L).card) ∧ (fam.G \ H.biUnion (pointsOn fam)).card ≤ 13 :=
  cover_above_budget fam hp hn (e:=671088639) (by decide) (by decide) ht (s:=512) (by decide) (by decide) hbig

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
