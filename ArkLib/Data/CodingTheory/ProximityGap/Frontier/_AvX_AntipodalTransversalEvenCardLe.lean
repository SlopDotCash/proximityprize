/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Antipodal negation transversal, Fintype-free (#444, AvX)

For a field `F` with `(2:F) ≠ 0` and a `Finset G ⊆ F` closed under negation with `0 ∉ G`, the
map `x ↦ -x` is a **fixed-point-free involution** on `G`. Consequently `|G|` is even, and there
is a **transversal** `T ⊆ G` meeting every antipodal pair `{x, -x}` exactly once, with
`2·|T| = |G|`.

This promotes to a clean reusable namespace the two lemmas that the char-0 No-Excess energy
ladder (`_AvL_T3ClosedForm.lean`'s `exists_neg_transversal` and `negClosed_card_even`) currently
re-derives ad hoc off `[Fintype F]`. The transversal is built purely from a `Finset`-indexing
function (`Fintype.equivFin ↥G`), so it needs **no `Fintype F`** — only the field structure and
`(2:F) ≠ 0`.

The headline `AntipodalTransversalEvenCardLemma` bundles all three facts (fixed-point-freeness,
even cardinality, transversal existence with `|T| = |G|/2`).

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`. This is pure plumbing — it does
not touch the open prize wall.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.AntipodalTransversal

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### Fixed-point-freeness of negation on `G`. -/

/-- For negation-closed `G` avoiding `0` in a field of characteristic `≠ 2`, no element of `G`
is its own negation: `x = -x` forces `2x = 0`, hence `x = 0`, contradicting `0 ∉ G`. -/
theorem neg_fixedPointFree (G : Finset F) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) :
    ∀ x ∈ G, x ≠ -x := by
  intro x hx hcontra
  have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
  have h2a : (2 : F) * x = 0 := by linear_combination hcontra
  rcases mul_eq_zero.mp h2a with h' | h'
  · exact h2 h'
  · exact hx0 h'

/-! ### Fintype-free rank on a finite set `G`. -/

/-- Fintype-free rank on a finite set `G`: injective on `G` (its index in `↥G`). -/
noncomputable def rankG (G : Finset F) (x : F) : ℕ :=
  if h : x ∈ G then (Fintype.equivFin ↥G ⟨x, h⟩).val else 0

theorem rankG_injOn (G : Finset F) {a b : F} (ha : a ∈ G) (hb : b ∈ G)
    (h : rankG G a = rankG G b) : a = b := by
  unfold rankG at h
  rw [dif_pos ha, dif_pos hb] at h
  exact congrArg Subtype.val ((Fintype.equivFin ↥G).injective (Fin.ext h))

/-! ### Even cardinality. -/

/-- **`|G|` is even** for negation-closed `G` avoiding `0` (char ≠ 2): the map `x ↦ −x` is a
fixed-point-free involution on `G`. -/
theorem negClosed_card_even (G : Finset F) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ x ∈ G, -x ∈ G) : Even G.card := by
  classical
  have hsum : ∑ _x ∈ G, (1 : ZMod 2) = 0 := by
    apply Finset.sum_involution (fun x _ => -x)
    · intro a _; decide
    · intro a ha _ hcontra
      have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
      have h2a : (2 : F) * a = 0 := by linear_combination -hcontra
      rcases mul_eq_zero.mp h2a with h' | h'
      · exact h2 h'
      · exact ha0 h'
    · intro a _; exact neg_neg a
    · intro a ha; exact hneg a ha
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  have hdvd : (2 : ℕ) ∣ G.card :=
    (CharP.cast_eq_zero_iff (ZMod 2) 2 G.card).mp (by exact_mod_cast hsum)
  obtain ⟨c, hc⟩ := hdvd
  exact ⟨c, by omega⟩

/-! ### Transversal existence. -/

/-- **A negation transversal exists (no `[Fintype F]`).** For negation-closed `G` (`0∉G`, char≠2)
there is `T ⊆ G` meeting each antipodal pair exactly once: `T` and its negation `-T` are disjoint
and cover `G`, and `2·|T| = |G|`. The transversal is `G.filter (fun x => rankG G x < rankG G (-x))`;
fixed-point-freeness comes from injectivity of `rankG` on `G`. -/
theorem exists_neg_transversal (G : Finset F) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ x ∈ G, -x ∈ G) :
    ∃ T : Finset F, T ⊆ G ∧ Disjoint T (T.image (fun x => -x))
      ∧ T ∪ T.image (fun x => -x) = G ∧ 2 * T.card = G.card := by
  classical
  have hxne : ∀ x ∈ G, x ≠ -x := neg_fixedPointFree G h2 h0
  set T := G.filter (fun x => rankG G x < rankG G (-x)) with hTdef
  have hsub : T ⊆ G := Finset.filter_subset _ _
  have hdisj : Disjoint T (T.image (fun x => -x)) := by
    rw [Finset.disjoint_left]
    intro a haT haI
    rw [hTdef, Finset.mem_filter] at haT
    rw [Finset.mem_image] at haI
    obtain ⟨b, hbT, hba⟩ := haI
    rw [hTdef, Finset.mem_filter] at hbT
    have hab : a = -b := hba.symm
    subst hab
    rw [neg_neg] at haT
    omega
  have hcov : T ∪ T.image (fun x => -x) = G := by
    apply Finset.Subset.antisymm
    · intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact hsub h
      · rw [Finset.mem_image] at h; obtain ⟨y, hy, rfl⟩ := h
        exact hneg y (hsub hy)
    · intro x hx
      rw [Finset.mem_union]
      have hnx : -x ∈ G := hneg x hx
      have hne : rankG G x ≠ rankG G (-x) := by
        intro he; exact hxne x hx (rankG_injOn G hx hnx he)
      by_cases hle : rankG G x < rankG G (-x)
      · exact Or.inl (by rw [hTdef, Finset.mem_filter]; exact ⟨hx, hle⟩)
      · right
        rw [Finset.mem_image]
        refine ⟨-x, ?_, by simp⟩
        rw [hTdef, Finset.mem_filter, neg_neg]
        exact ⟨hnx, by omega⟩
  refine ⟨T, hsub, hdisj, hcov, ?_⟩
  have himg : (T.image (fun x => -x)).card = T.card :=
    Finset.card_image_of_injective _ neg_injective
  have hu := Finset.card_union_of_disjoint hdisj
  rw [hcov, himg] at hu
  omega

/-! ### The bundled headline lemma. -/

/-- **AntipodalTransversalEvenCardLemma.** For a field `F` with `(2:F) ≠ 0` and a finite set
`G ⊆ F` closed under negation with `0 ∉ G`:
* `x ↦ -x` is fixed-point-free on `G` (`∀ x ∈ G, x ≠ -x`);
* `|G|` is even;
* there exists a transversal `T ⊆ G` with `2·|T| = |G|` meeting each antipodal pair `{x,-x}`
  exactly once (`T` and `-T` are disjoint and cover `G`). -/
theorem AntipodalTransversalEvenCardLemma (G : Finset F) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ x ∈ G, -x ∈ G) :
    (∀ x ∈ G, x ≠ -x) ∧ Even G.card ∧
      ∃ T : Finset F, T ⊆ G ∧ Disjoint T (T.image (fun x => -x))
        ∧ T ∪ T.image (fun x => -x) = G ∧ 2 * T.card = G.card :=
  ⟨neg_fixedPointFree G h2 h0, negClosed_card_even G h2 h0 hneg,
    exists_neg_transversal G h2 h0 hneg⟩

end ArkLib.ProximityGap.Frontier.AntipodalTransversal

#print axioms ArkLib.ProximityGap.Frontier.AntipodalTransversal.neg_fixedPointFree
#print axioms ArkLib.ProximityGap.Frontier.AntipodalTransversal.rankG_injOn
#print axioms ArkLib.ProximityGap.Frontier.AntipodalTransversal.negClosed_card_even
#print axioms ArkLib.ProximityGap.Frontier.AntipodalTransversal.exists_neg_transversal
#print axioms ArkLib.ProximityGap.Frontier.AntipodalTransversal.AntipodalTransversalEvenCardLemma
