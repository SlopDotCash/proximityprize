import Mathlib.Tactic.LinearCombination

set_option linter.style.longLine false
set_option autoImplicit false

/-! Scratch: a negation transversal of a negation-closed `G ⊆ F` that does NOT need `[Fintype F]`.
The only real `Fintype F` use in the E₃ strata chain is `exists_neg_transversal`'s order on `F`
(via `Fintype.equivFin F`). Here we order the finite subtype `↥G` instead (always a `Fintype`),
pick one representative per antipodal pair there, and map back out by `Subtype.val`. Unlocks the
char-0 closed form over `ℂ`. -/

open Finset

namespace NegTransversalCharFree

variable {F : Type*} [Field F] [DecidableEq F]

/-- **A negation transversal exists, with no `[Fintype F]`.** For negation-closed `G` (`0 ∉ G`,
char ≠ 2) there is `T ⊆ G` with one representative per antipodal pair. Same statement as the in-tree
`exists_neg_transversal`, but the order lives on the finite subtype `↥G`. -/
theorem exists_neg_transversal' (G : Finset F) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ x ∈ G, -x ∈ G) :
    ∃ T : Finset F, T ⊆ G ∧ Disjoint T (T.image (fun x => -x))
      ∧ T ∪ T.image (fun x => -x) = G ∧ 2 * T.card = G.card := by
  classical
  -- distinctness of a pair from char ≠ 2 and 0 ∉ G
  have hxne : ∀ x ∈ G, x ≠ -x := by
    intro x hx hcontra
    have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
    have h2a : (2 : F) * x = 0 := by linear_combination hcontra
    rcases mul_eq_zero.mp h2a with h' | h'
    · exact h2 h'
    · exact hx0 h'
  -- order the finite subtype ↥G
  letI : LinearOrder ↥G := LinearOrder.lift' (Fintype.equivFin ↥G) (Equiv.injective _)
  -- negation as an involution on ↥G
  set ι : ↥G → ↥G := fun g => ⟨-(g : F), hneg (g : F) g.2⟩ with hι
  have hιinv : Function.Involutive ι := by
    intro g; apply Subtype.ext; simp [hι]
  have hιfpf : ∀ g : ↥G, ι g ≠ g := by
    intro g hgg
    have : -(g : F) = (g : F) := by simpa [hι, Subtype.ext_iff] using hgg
    exact hxne (g : F) g.2 this.symm
  -- pick the ≤-smaller of each pair on ↥G
  set T' : Finset ↥G := Finset.univ.filter (fun g => g ≤ ι g) with hT'
  have hT'disj : Disjoint T' (T'.image ι) := by
    rw [Finset.disjoint_left]
    intro a haT haI
    rw [hT', Finset.mem_filter] at haT
    rw [Finset.mem_image] at haI
    obtain ⟨b, hbT, hba⟩ := haI
    rw [hT', Finset.mem_filter] at hbT
    -- a ≤ ι a and a = ι b with b ≤ ι b ⟹ a ≤ ι a = b and b ≤ ι b = a ⟹ a = b ⟹ a = ι a, contra fpf
    have hab : a = ι b := hba.symm
    have h1 : a ≤ ι a := haT.2
    have h2' : b ≤ ι b := hbT.2
    have hιa : ι a = b := by rw [hab, hιinv]
    rw [hιa] at h1
    have hba' : b = a := le_antisymm (hab ▸ h2') h1
    exact hιfpf a (hιa.trans hba')
  have hT'cov : T' ∪ T'.image ι = Finset.univ := by
    apply Finset.Subset.antisymm (Finset.subset_univ _)
    intro g _
    rw [Finset.mem_union]
    by_cases hle : g ≤ ι g
    · exact Or.inl (by rw [hT', Finset.mem_filter]; exact ⟨Finset.mem_univ g, hle⟩)
    · refine Or.inr (Finset.mem_image.mpr ⟨ι g, ?_, hιinv g⟩)
      rw [hT', Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hιinv]; exact (not_le.mp hle).le
  -- map T' out to F by Subtype.val
  refine ⟨T'.image (Subtype.val), ?_, ?_, ?_, ?_⟩
  · intro x hx; rw [Finset.mem_image] at hx; obtain ⟨g, _, rfl⟩ := hx; exact g.2
  · -- disjoint T (T.image neg)
    rw [Finset.disjoint_left]
    intro x hxT hxI
    rw [Finset.mem_image] at hxT hxI
    obtain ⟨g, hgT, rfl⟩ := hxT
    obtain ⟨y, hyT, hyx⟩ := hxI
    rw [Finset.mem_image] at hyT
    obtain ⟨b, hbT, rfl⟩ := hyT
    -- (g:F) = -(b:F) = (ι b : F), so g = ι b in ↥G; both g, b ∈ T' ⟹ contra disjoint
    have hgιb : g = ι b := Subtype.ext (by simpa [hι] using hyx.symm)
    have : g ∈ T'.image ι := Finset.mem_image.mpr ⟨b, hbT, hgιb.symm⟩
    exact (Finset.disjoint_left.mp hT'disj hgT) this
  · -- cover
    apply Finset.Subset.antisymm
    · intro x hx
      rw [Finset.mem_union] at hx
      rcases hx with h | h
      · rw [Finset.mem_image] at h; obtain ⟨g, _, rfl⟩ := h; exact g.2
      · rw [Finset.mem_image] at h; obtain ⟨y, hy, rfl⟩ := h
        rw [Finset.mem_image] at hy; obtain ⟨g, _, rfl⟩ := hy
        exact hneg _ g.2
    · intro x hx
      have hgcov : (⟨x, hx⟩ : ↥G) ∈ T' ∪ T'.image ι := hT'cov ▸ Finset.mem_univ _
      rw [Finset.mem_union] at hgcov
      rw [Finset.mem_union]
      rcases hgcov with h | h
      · exact Or.inl (Finset.mem_image.mpr ⟨⟨x, hx⟩, h, rfl⟩)
      · rw [Finset.mem_image] at h; obtain ⟨b, hbT, hbx⟩ := h
        refine Or.inr (Finset.mem_image.mpr ⟨(b : F), Finset.mem_image.mpr ⟨b, hbT, rfl⟩, ?_⟩)
        have : -(b : F) = x := by simpa [hι] using congrArg Subtype.val hbx
        rw [this]
  · -- 2 * |T| = |G|
    have hTcard : (T'.image (Subtype.val)).card = T'.card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    have hITcard : (T'.image ι).card = T'.card :=
      Finset.card_image_of_injective _ hιinv.injective
    have hu := Finset.card_union_of_disjoint hT'disj
    rw [hT'cov, hITcard, Finset.card_univ, Fintype.card_coe] at hu
    rw [hTcard]; omega

end NegTransversalCharFree

#print axioms NegTransversalCharFree.exists_neg_transversal'
