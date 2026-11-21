/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimePrimitiveSurface

/-! # Populations of actual components at the second-prime predecessor

Only the quartic, cubic, nonlinear low-degree, and three- or four-head alternatives require
geometric elimination. The heads here are distinct pairs of polynomials over the original
field. Their carrier sets consist of actual selected labels on their polynomial lines.
-/
set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.SecondPrimeActualPopulations
open Finset Polynomial
open scoped NNReal
open HalfPredecessorBadEventRichPointBridge HalfPredecessorLineCoreGeometry

private theorem population_split {A F H : Type} [DecidableEq F]
    (U : Finset A) (D : A → ℕ) (G E : Finset F) (P : A → Finset F) (head : A → H)
    (line : H → Finset F)
    (pos : ∀ f ∈ U, 0 < D f) (deg : ∑ f ∈ U, D f ≤ 4)
    (exc : E.card ≤ 34) (large : 2147483648 < G.card) (cover : G ⊆ E ∪ U.biUnion P)
    (aff : ∀ f ∈ U, D f = 1 → 184 < (P f).card → P f ⊆ line (head f))
    (cap : ∀ f ∈ U, D f = 1 → 184 < (P f).card → (line (head f)).card ≤ 715827882) :
    (∃ f ∈ U, D f = 4 ∧ 2147483615 ≤ (P f).card) ∨
    (∃ f ∈ U, D f = 3 ∧ 1431655733 ≤ (P f).card) ∨
    (∃ f ∈ U, D f = 2 ∧ 4128 < (P f).card) ∨
    ∃ heads : Finset H, 3 ≤ heads.card ∧ heads.card ≤ 4 ∧
      (∀ h ∈ heads, ∃ f ∈ U, D f = 1 ∧ 512 < (P f).card ∧ h = head f) ∧
      G.card ≤ (heads.biUnion line).card + 4*4128 + 34 := by
  classical
  have sum_one (T : Finset A) (sub : T ⊆ U) : T.card ≤ ∑ g ∈ T, D g := by
    simpa only [sum_const, smul_eq_mul, mul_one] using
      (sum_le_sum (fun g hg => pos g (sub hg)) : ∑ _g ∈ T, 1 ≤ _)
  have nU := (sum_one U (by intro _ h; exact h)).trans deg
  have mass := (card_le_card cover).trans ((card_union_le _ _).trans
    (Nat.add_le_add_left card_biUnion_le E.card))
  have omit_one (f : A) (hf : f ∈ U) :
      (U.erase f).card + D f ≤ 4 ∧
      G.card ≤ E.card + ((∑ g ∈ U.erase f, (P g).card) + (P f).card) := by
    rw [sum_erase_add _ _ hf]
    have hs := sum_one (U.erase f) (erase_subset _ _)
    have h := sum_erase_add U D hf
    omega
  by_cases h4 : ∃ f ∈ U, 4 ≤ D f
  · obtain ⟨f, hf, hd⟩ := h4
    obtain ⟨hh, hm⟩ := omit_one f hf
    have rem : U.erase f = ∅ := card_eq_zero.mp (by omega)
    rw [rem, sum_empty] at hm
    exact Or.inl ⟨f, hf, by omega, by omega⟩
  right
  by_cases h3 : ∃ f ∈ U, 3 ≤ D f
  · obtain ⟨f, hf, hd⟩ := h3
    obtain ⟨hh, hm⟩ := omit_one f hf
    have hlt : D f < 4 := lt_of_not_ge fun hh => h4 ⟨f, hf, hh⟩
    have hsum : ∑ g ∈ U.erase f, D g ≤ 1 := by
      have h := sum_erase_add U D hf
      omega
    have hc (g : A) (hg : g ∈ U.erase f) : (P g).card ≤ 715827882 := by
      have hgU := mem_of_mem_erase hg
      have hpos := pos g hgU
      have hsingle := (single_le_sum (fun _ _ => Nat.zero_le _) hg).trans hsum
      have hg1 : D g = 1 := by omega
      by_cases hp : 184 < (P g).card
      · exact (card_le_card (aff g hgU hg1 hp)).trans (cap g hgU hg1 hp)
      · omega
    have hsmall := sum_le_sum hc
    simp only [sum_const, smul_eq_mul] at hsmall
    exact Or.inl ⟨f,hf,by omega,by omega⟩
  right
  by_cases h2 : ∃ f ∈ U, D f = 2 ∧ 4128 < (P f).card
  · exact Or.inl h2
  right
  let V := U.filter fun f => D f = 1 ∧ 512 < (P f).card
  let heads := V.image head
  have props (h : H) (hh : h ∈ heads) : ∃ f ∈ U, D f = 1 ∧ 512 < (P f).card ∧ h = head f := by
    obtain ⟨f, hf, rfl⟩ := mem_image.mp hh
    obtain ⟨hu, hD, hP⟩ := mem_filter.mp hf
    exact ⟨f,hu,hD,hP,rfl⟩
  have hrest (f : A) (hf : f ∈ U \ V) : (P f).card ≤ 4128 := by
    obtain ⟨hu,hv⟩ := mem_sdiff.mp hf
    have hn := pos f hu
    have hd : D f < 3 := lt_of_not_ge fun hc => h3 ⟨f,hu,hc⟩
    by_contra! hp
    by_cases h1 : D f = 1
    · exact hv (mem_filter.mpr ⟨hu,h1,by omega⟩)
    · exact h2 ⟨f,hu,by omega,hp⟩
  have split_cover : G ⊆ E ∪ ((U \ V).biUnion P ∪ heads.biUnion line) := by
    intro z hz
    rcases mem_union.mp (cover hz) with he | hz
    · exact mem_union_left _ he
    obtain ⟨f,hf,hz⟩ := mem_biUnion.mp hz
    apply mem_union_right
    by_cases hv : f ∈ V
    · obtain ⟨_,hd,hp⟩ := mem_filter.mp hv
      exact mem_union_right _ (mem_biUnion.mpr
        ⟨head f,mem_image_of_mem _ hv,aff f hf hd (by omega) hz⟩)
    · exact mem_union_left _ (mem_biUnion.mpr ⟨f,mem_sdiff.mpr ⟨hf,hv⟩,hz⟩)
  have rest := card_biUnion_le.trans (sum_le_sum hrest)
  simp only [sum_const, smul_eq_mul] at rest
  have hrc := (card_le_card (sdiff_subset (s := U) (t := V))).trans nU
  have hsplit := (card_le_card split_cover).trans ((card_union_le _ _).trans
    (Nat.add_le_add_left (card_union_le _ _) E.card))
  have hH : G.card ≤ (heads.biUnion line).card + 4*4128 + 34 := by omega
  have hcap (h : H) (hh : h ∈ heads) : (line h).card ≤ 715827882 := by
    obtain ⟨f,hu,hd,hp,rfl⟩ := props h hh
    exact cap f hu hd (by omega)
  have hc := card_biUnion_le.trans (sum_le_sum hcap)
  simp only [sum_const, smul_eq_mul] at hc
  exact ⟨heads,by omega,card_image_le.trans ((card_filter_le _ _).trans nU),props,hH⟩

variable {I F K : Type} [Fintype I] [Field F] [DecidableEq F] [Field K]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : Code.WordStack F (Fin 2) I}
abbrev Family (dom : I ↪ F) (δ : ℝ≥0) (u : Code.WordStack F (Fin 2) I) :=
  BadScalarRichPointFamily dom 67108864 δ u
abbrev Factor (K : Type) [Field K] := Polynomial (Polynomial K[X])

/-- Every selected label lying on the specified factor, counted once. -/
noncomputable def population (fam : Family dom δ u) (φ : F →+* K) (f : Factor K) : Finset F := by
  classical
  exact fam.G.filter fun z => f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0

/-- Every selected label whose originally decoded polynomial is on the specified head. -/
noncomputable def carried (fam : Family dom δ u) (p : F[X] × F[X]) : Finset F := by
  classical
  exact fam.G.filter fun z => fam.q z = p.1 + C z * p.2

/-- A head used here has actual coefficients of degree below the code dimension. -/
def valid (p : F[X] × F[X]) : Prop := p.1.natDegree < 67108864 ∧ p.2.natDegree < 67108864

/-- The sharp individual-head bound and the minimum core size of every large head,
from genuine agreement and failure of a joint explanation. -/
theorem head_population [Finite F] (fam : Family dom δ u)
    (hn : Fintype.card I = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (p : F[X] × F[X]) (hp : valid p) :
    (carried fam p).card ≤ 715827882 ∧
    (512 < (carried fam p).card → 356515842 ≤ (jointCore dom (u 0) (u 1) p.1 p.2).card) := by
  classical
  let c := (jointCore dom (u 0) (u 1) p.1 p.2).card
  let L := (carried fam p).card
  let : Fintype F := Fintype.ofFinite F
  have : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  have pack := fam.line_core_packing p.1 p.2 (carried fam p) hp.1 hp.2
    (filter_subset _ _) (fun _ hz => (mem_filter.mp hz).2)
  change L * max 1 (_ - c) + c ≤ _ at pack
  rw [hn] at pack ht
  have h1 : L + c ≤ 1073741824 := by
    have h := Nat.mul_le_mul_left L (le_max_left 1 (⌈(1 - δ) * (1073741824 : ℝ≥0)⌉₊ - c))
    simpa only [Nat.mul_one] using (Nat.add_le_add_right h c).trans pack
  have h2 : L * (357913943 - c) + c ≤ 1073741824 :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left L
      ((Nat.sub_le_sub_right ht c).trans (le_max_right _ _))) c).trans pack
  constructor
  · change L ≤ 715827882
    by_contra! hL
    by_cases hc : c < 357913943
    · have hprod := Nat.mul_le_mul_right (357913943 - c) hL
      omega
    · omega
  · intro hL
    change 512 < L at hL
    change 356515842 ≤ c
    have hprod := Nat.mul_le_mul_right (357913943 - c) hL
    omega

private theorem distinct_degree_le {α : Type} [DecidableEq α] (U : Multiset α) (D : α → ℕ) :
    ∑ f ∈ U.toFinset, D f ≤ (U.map D).sum := by
  change ((U.dedup.map D).sum) ≤ _
  obtain ⟨v,h⟩ := Multiset.le_iff_exists_add.mp (Multiset.dedup_le U)
  calc
    _ ≤ (U.dedup.map D).sum + (v.map D).sum := Nat.le_add_right _ _
    _ = (U.map D).sum := by
      conv_rhs => rw [h, Multiset.map_add, Multiset.sum_add]

/-- At the named predecessor an actual overbudget family forces a populous quartic or cubic,
a quadratic carrying at least 4129 labels, a linear-in-value factor with at least 185 labels
outside the scope of any single head, or three or four different large base-field heads.
These alternatives isolate the ensuing geometric arguments. -/
theorem actual_alternatives [Finite F] (fam : Family dom δ u) (φ : F →+* K)
    (hn : Fintype.card I = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (hbig : 2147483648 < fam.G.card) :
    ∃ Q : Factor K, Q ≠ 0 ∧
      (∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
        j ≤ 4 ∧ i + j ≤ 34 ∧ a + j * 67108863 < 357913943) ∧
      ((∃ f : Factor K, Irreducible f ∧ f ∣ Q ∧
        ((f.natDegree = 4 ∧ 2147483615 ≤ (population fam φ f).card) ∨
         (f.natDegree = 3 ∧ 1431655733 ≤ (population fam φ f).card) ∨
         (f.natDegree = 2 ∧ 4128 < (population fam φ f).card) ∨
         (f.natDegree = 1 ∧ 184 < (population fam φ f).card ∧
           ¬ ∃ p, valid p ∧ population fam φ f ⊆ carried fam p))) ∨
       ∃ heads : Finset (F[X] × F[X]), 3 ≤ heads.card ∧ heads.card ≤ 4 ∧
         (∀ p ∈ heads, valid p ∧ 512 < (carried fam p).card ∧
           (carried fam p).card ≤ 715827882 ∧
           356515842 ≤ (jointCore dom (u 0) (u 1) p.1 p.2).card) ∧
         fam.G.card ≤ (heads.biUnion (carried fam)).card + 4*4128 + 34) := by
  classical
  obtain ⟨Q,U,E,hQ,hshape,hU,hdeg,_,_,hE,hcover⟩ :=
    SecondPrimePrimitiveSurface.actual_components φ dom δ u hn ht fam
  refine ⟨Q,hQ,hshape,?_⟩
  let V := U.toFinset
  let pop := population fam φ
  have hu (f : Factor K) (hf : f ∈ V) := hU f (Multiset.mem_toFinset.mp hf)
  by_cases bad : ∃ f ∈ V, f.natDegree = 1 ∧ 184 < (pop f).card ∧
      ¬ ∃ p, valid p ∧ pop f ⊆ carried fam p
  · obtain ⟨f,hf,hb⟩ := bad
    exact Or.inl ⟨f,(hu f hf).1,(hu f hf).2.2,Or.inr (Or.inr (Or.inr hb))⟩
  have pick (f : Factor K) : ∃ p, f ∈ V → f.natDegree = 1 → 184 < (pop f).card →
      valid p ∧ pop f ⊆ carried fam p := by
    by_cases hb : f ∈ V ∧ f.natDegree = 1 ∧ 184 < (pop f).card
    · have hex : ∃ p, valid p ∧ pop f ⊆ carried fam p :=
        by_contra fun no => bad ⟨f,hb.1,hb.2.1,hb.2.2,no⟩
      exact ⟨hex.choose,fun _ _ _ => hex.choose_spec⟩
    · exact ⟨0,fun hf hd hp => False.elim (hb ⟨hf,hd,hp⟩)⟩
  choose head hhead using pick
  have cov : fam.G ⊆ E ∪ V.biUnion pop := by
    intro z hz
    by_cases he : z ∈ E
    · exact mem_union_left _ he
    obtain ⟨f,hf,hh⟩ := hcover z hz he
    exact mem_union_right _ (mem_biUnion.mpr ⟨f,Multiset.mem_toFinset.mpr hf,
      mem_filter.mpr ⟨hz,hh⟩⟩)
  have alt := population_split V natDegree fam.G E pop head (carried fam)
    (fun f hf => (hu f hf).2.1) ((distinct_degree_le U natDegree).trans hdeg)
    hE hbig cov (fun f hf hd hp => (hhead f hf hd hp).2)
    (fun f hf hd hp => (head_population fam hn ht _ (hhead f hf hd hp).1).1)
  rcases alt with ⟨f,hf,hh⟩ | ⟨f,hf,hh⟩ | ⟨f,hf,hh⟩ | ⟨H,h3,h4,hw,hnum⟩
  · exact Or.inl ⟨f,(hu f hf).1,(hu f hf).2.2,Or.inl hh⟩
  · exact Or.inl ⟨f,(hu f hf).1,(hu f hf).2.2,Or.inr (Or.inl hh)⟩
  · exact Or.inl ⟨f,(hu f hf).1,(hu f hf).2.2,Or.inr (Or.inr (Or.inl hh))⟩
  · refine Or.inr ⟨H,h3,h4,?_,hnum⟩
    intro p hp
    obtain ⟨f,hf,hd,hl,rfl⟩ := hw p hp
    obtain ⟨hv,hsub⟩ := hhead f hf hd (by omega)
    have hl' := hl.trans_le (card_le_card hsub)
    obtain ⟨hcap,hcore⟩ := head_population fam hn ht _ hv
    exact ⟨hv,hl',hcap,hcore hl'⟩

#print axioms actual_alternatives
#print axioms head_population
end ArkLib.ProximityGap.Frontier.SecondPrimeActualPopulations
