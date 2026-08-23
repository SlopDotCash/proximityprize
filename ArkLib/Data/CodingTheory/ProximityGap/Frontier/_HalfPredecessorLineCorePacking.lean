/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The abstract line-core packing inequality

This is the set-theoretic content of `(L2)` in the rate-`1/16` half-predecessor proof.  A common
core `D` lies in every agreement set on one selected affine line.  Equality of pairwise
intersections makes the fresh fibers `A_gamma \ D` pairwise disjoint.  If the core is already as
large as the demanded agreement, non-jointness supplies one fresh coordinate per point.

The conclusion is the exact packing inequality

```text
L * max(1, t - |D|) + |D| <= |U|.
```

No field or polynomial structure is used here; those enter only in proving the hypotheses.
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorLineCorePacking

/-! ## Three-set lower bound used by the large-core collapse -/

/-- Three subsets of one finite universe satisfy the elementary Bonferroni lower bound
`|X|+|Y|+|Z| <= 2|V|+|X inter Y inter Z|`. -/
theorem three_set_card_le_two_mul_add_inter
    {U : Type*} [DecidableEq U] (V X Y Z : Finset U)
    (hX : X ⊆ V) (hY : Y ⊆ V) (hZ : Z ⊆ V) :
    X.card + Y.card + Z.card ≤
      2 * V.card + (X ∩ Y ∩ Z).card := by
  let T : Finset U := X ∩ Y ∩ Z
  have hT : T ⊆ V := by
    intro x hx
    exact hX (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1
  have hcover : V \ T ⊆ (V \ X) ∪ (V \ Y) ∪ (V \ Z) := by
    intro x hx
    have hxV : x ∈ V := (Finset.mem_sdiff.mp hx).1
    have hxT : x ∉ T := (Finset.mem_sdiff.mp hx).2
    by_cases hxX : x ∈ X
    · by_cases hxY : x ∈ Y
      · by_cases hxZ : x ∈ Z
        · exact False.elim (hxT (by simp only [T, Finset.mem_inter, hxX, hxY, hxZ, and_self]))
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxV, hxZ⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨hxV, hxY⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨hxV, hxX⟩))
  have hcoverCard : (V \ T).card ≤
      (V \ X).card + (V \ Y).card + (V \ Z).card := by
    refine (Finset.card_le_card hcover).trans ?_
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add (Finset.card_union_le _ _) le_rfl)
  change (V \ (X ∩ Y ∩ Z)).card ≤
    (V \ X).card + (V \ Y).card + (V \ Z).card at hcoverCard
  have hT' : X ∩ Y ∩ Z ⊆ V := by simpa only [T] using hT
  have hsplitT :
      (V \ (X ∩ Y ∩ Z)).card + (X ∩ Y ∩ Z).card = V.card :=
    Finset.card_sdiff_add_card_eq_card hT'
  have hsplitX := Finset.card_sdiff_add_card_eq_card hX
  have hsplitY := Finset.card_sdiff_add_card_eq_card hY
  have hsplitZ := Finset.card_sdiff_add_card_eq_card hZ
  omega

/-- Strict form used in the large-core dichotomy.  If every set has size at least `r` and
`3r > 2|V|+d`, their triple intersection has more than `d` points. -/
theorem three_set_inter_card_gt
    {U : Type*} [DecidableEq U] (V X Y Z : Finset U) (r d : ℕ)
    (hX : X ⊆ V) (hY : Y ⊆ V) (hZ : Z ⊆ V)
    (hXcard : r ≤ X.card) (hYcard : r ≤ Y.card) (hZcard : r ≤ Z.card)
    (hgap : 2 * V.card + d < 3 * r) :
    d < (X ∩ Y ∩ Z).card := by
  have hbonf := three_set_card_le_two_mul_add_inter V X Y Z hX hY hZ
  omega

/-- **Abstract line-core packing (`L2`).**  Pairwise-disjoint fresh fibers plus the common core
fit inside the coordinate universe. -/
theorem lineCore_packing
    {U Gamma : Type*} [Fintype U] [DecidableEq U]
    (G : Finset Gamma) (A : Gamma → Finset U) (D : Finset U) (t : ℕ)
    (hcore : ∀ gamma ∈ G, D ⊆ A gamma)
    (hdisj : ∀ gamma ∈ G, ∀ beta ∈ G, gamma ≠ beta →
      Disjoint (A gamma \ D) (A beta \ D))
    (hsize : ∀ gamma ∈ G, t ≤ (A gamma).card)
    (hfresh : ∀ gamma ∈ G, t ≤ D.card → (A gamma \ D).Nonempty) :
    G.card * max 1 (t - D.card) + D.card ≤ Fintype.card U := by
  let fresh : Gamma → Finset U := fun gamma => A gamma \ D
  have hfresh_disj : ∀ gamma ∈ G, ∀ beta ∈ G, gamma ≠ beta →
      Disjoint (fresh gamma) (fresh beta) := by
    intro gamma hgamma beta hbeta hne
    exact hdisj gamma hgamma beta hbeta hne
  have h_each : ∀ gamma ∈ G, max 1 (t - D.card) ≤ (fresh gamma).card := by
    intro gamma hgamma
    by_cases ht : t ≤ D.card
    · have hsubzero : t - D.card = 0 := Nat.sub_eq_zero_of_le ht
      rw [hsubzero, max_eq_left (by omega)]
      exact Finset.one_le_card.mpr (hfresh gamma hgamma ht)
    · have hDt : D.card ≤ t := Nat.le_of_lt (Nat.lt_of_not_ge ht)
      have hsubpos : 1 ≤ t - D.card := Nat.sub_pos_of_lt (Nat.lt_of_not_ge ht)
      rw [max_eq_right hsubpos]
      change t - D.card ≤ (A gamma \ D).card
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (hcore gamma hgamma)]
      exact Nat.sub_le_sub_right (hsize gamma hgamma) D.card
  have hsum_lower :
      G.card * max 1 (t - D.card) ≤ ∑ gamma ∈ G, (fresh gamma).card := by
    calc
      G.card * max 1 (t - D.card) =
          ∑ _gamma ∈ G, max 1 (t - D.card) := by
            simp
      _ ≤ ∑ gamma ∈ G, (fresh gamma).card := Finset.sum_le_sum h_each
  let Ufresh : Finset U := G.biUnion fresh
  have hsum_eq : ∑ gamma ∈ G, (fresh gamma).card = Ufresh.card := by
    symm
    apply Finset.card_biUnion
    exact hfresh_disj
  have hD_disj : Disjoint D Ufresh := by
    rw [Finset.disjoint_left]
    intro x hxD hxU
    obtain ⟨gamma, hgamma, hxFresh⟩ := Finset.mem_biUnion.mp hxU
    exact (Finset.mem_sdiff.mp hxFresh).2 hxD
  have hfit : Ufresh.card + D.card ≤ Fintype.card U := by
    rw [add_comm, ← Finset.card_union_of_disjoint hD_disj]
    exact Finset.card_le_univ _
  omega

end ArkLib.ProximityGap.Frontier.HalfPredecessorLineCorePacking

#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorLineCorePacking.three_set_card_le_two_mul_add_inter
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorLineCorePacking.three_set_inter_card_gt
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorLineCorePacking.lineCore_packing
