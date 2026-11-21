/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-! # Selecting two large affine heads from the quarter-rate factor cover

A multiset accounts for multiplicities of irreducible factors. Once a factor
is large enough to put all its selected labels on one head, delete that
occurrence and look only at labels outside the entire first head. The remaining
degree and exceptional labels cannot account for those labels without another
large factor.
-/

namespace ArkLib.ProximityGap.Frontier.QuarterRateFactorSelection

variable {Label Factor Head : Type*} [DecidableEq Label]

private theorem cover_card (fs : Multiset Factor) (pop : Factor → Finset Label)
    (deg : Factor → ℕ) (S E : Finset Label)
    (cover : ∀ x ∈ S, x ∈ E ∨ ∃ f ∈ fs, x ∈ pop f)
    (bound : ∀ f ∈ fs, (S ∩ pop f).card ≤ deg f * 268435490) :
    S.card ≤ E.card + (fs.map deg).sum * 268435490 := by
  induction fs using Multiset.induction_on generalizing S with
  | empty =>
    have hs : S ⊆ E := by
      intro x hx
      simpa using cover x hx
    simpa using Finset.card_le_card hs
  | cons f fs ih =>
    let R := S \ pop f
    have hr : ∀ x ∈ R, x ∈ E ∨ ∃ g ∈ fs, x ∈ pop g := by
      intro x hx
      obtain ⟨hxS, hxF⟩ := Finset.mem_sdiff.mp hx
      rcases cover x hxS with he | ⟨g, hg, hgp⟩
      · exact Or.inl he
      · rcases Multiset.mem_cons.mp hg with rfl | hg
        · exact False.elim (hxF hgp)
        · exact Or.inr ⟨g, hg, hgp⟩
    have hb : ∀ g ∈ fs, (R ∩ pop g).card ≤ deg g * 268435490 := by
      intro g hg
      apply (Finset.card_le_card (Finset.inter_subset_inter_right Finset.sdiff_subset)).trans
      exact bound g (Multiset.mem_cons_of_mem hg)
    have hrest := ih R hr hb
    have hfirst := bound f (Multiset.mem_cons_self ..)
    have hadd := Finset.card_sdiff_add_card_inter S (pop f)
    change (S \ pop f).card ≤ _ at hrest
    simp only [Multiset.map_cons, Multiset.sum_cons, Nat.add_mul]
    omega

private theorem large_factor (fs : Multiset Factor) (pop : Factor → Finset Label)
    (deg : Factor → ℕ) (S E : Finset Label)
    (pos : ∀ f ∈ fs, 0 < deg f) (cover : ∀ x ∈ S, x ∈ E ∨ ∃ f ∈ fs, x ∈ pop f)
    (large : E.card + (fs.map deg).sum * 268435490 < S.card) :
    ∃ f ∈ fs, deg f * 268435458 + 32 < (S ∩ pop f).card := by
  by_contra! h
  apply large.not_ge (cover_card fs pop deg S E cover ?_)
  intro f hf
  apply (h f hf).trans
  rw [show 268435490 = 268435458 + 32 by decide, Nat.mul_add]
  apply Nat.add_le_add_left
  simpa only [Nat.one_mul] using Nat.mul_le_mul_right 32 (pos f hf)

/-- More than `2^30` selected labels force two different rich heads. The
second count uses labels outside the whole first head, so the certified
selected sets are disjoint. Factor multiplicities are included in the degree sum. -/
theorem two_heads (G E : Finset Label) (fs : Multiset Factor)
    (deg : Factor → ℕ) (pop : Factor → Finset Label) (points : Head → Finset Label)
    (hG : 1073741824 < G.card) (hE : E.card ≤ 16) (hsum : (fs.map deg).sum ≤ 3)
    (pos : ∀ f ∈ fs, 0 < deg f)
    (cover : ∀ x ∈ G, x ∈ E ∨ ∃ f ∈ fs, x ∈ pop f)
    (cap : ∀ p, (points p).card ≤ 447392428)
    (capture : ∀ f ∈ fs, ∀ L : Finset Label, L ⊆ G → L ⊆ pop f →
      deg f * 268435458 + 32 < L.card → ∃ p, L ⊆ points p) :
    ∃ p q, p ≠ q ∧ 223696215 ≤ (G ∩ points p).card ∧
      223696215 ≤ ((G \ points p) ∩ points q).card := by
  classical
  obtain ⟨f, hf, hbig⟩ := large_factor fs pop deg G E pos cover (by omega)
  obtain ⟨p, hcarry⟩ := capture f hf _ Finset.inter_subset_left Finset.inter_subset_right hbig
  obtain hfp := pos f hf
  have hmin : 223696215 ≤ (G ∩ pop f).card := by omega
  have hp : G ∩ pop f ⊆ G ∩ points p := Finset.subset_inter Finset.inter_subset_left hcarry
  let R := G \ points p
  let rest := fs.erase f
  have hremove : f ::ₘ rest = fs := Multiset.cons_erase hf
  have hdegree : (rest.map deg).sum ≤ 2 := by
    rw [← hremove, Multiset.map_cons, Multiset.sum_cons] at hsum
    omega
  have hrestpos (g) (hg : g ∈ rest) : 0 < deg g :=
    pos g (Multiset.mem_of_le (Multiset.erase_le f fs) hg)
  have inc : R ⊆ G := Finset.sdiff_subset
  have hrestcover (x) (hx : x ∈ R) : x ∈ E ∨ ∃ g ∈ rest, x ∈ pop g := by
    rcases cover x (inc hx) with h | ⟨g, hg, hgp⟩
    · exact Or.inl h
    · rw [← hremove] at hg
      rcases Multiset.mem_cons.mp hg with rfl | hg
      · exact False.elim ((Finset.mem_sdiff.mp hx).2 (hcarry (Finset.mem_inter.mpr ⟨inc hx, hgp⟩)))
      · exact Or.inr ⟨g, hg, hgp⟩
  have hr : 626349396 < R.card := by
    have := Finset.card_sdiff_add_card_inter G (points p)
    have hi : (G ∩ points p).card ≤ (points p).card := Finset.card_le_card Finset.inter_subset_right
    have := hi.trans (cap p)
    dsimp only [R]
    omega
  obtain ⟨g, hg, hbig'⟩ := large_factor rest pop deg R E hrestpos hrestcover (by omega)
  obtain ⟨q, hcarry'⟩ := capture g (Multiset.mem_of_le (Multiset.erase_le f fs) hg) _
    (Finset.inter_subset_left.trans inc) Finset.inter_subset_right hbig'
  have hgpos := hrestpos g hg
  have hmin' : 223696215 ≤ (R ∩ pop g).card := by omega
  have hq : R ∩ pop g ⊆ R ∩ points q := Finset.subset_inter Finset.inter_subset_left hcarry'
  refine ⟨p, q, ?_, hmin.trans (Finset.card_le_card hp), hmin'.trans (Finset.card_le_card hq)⟩
  intro heq
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < (R ∩ pop g).card)
  have hout := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).1).2
  exact hout (heq ▸ hcarry' hx)

end ArkLib.ProximityGap.Frontier.QuarterRateFactorSelection
