/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Even half-radius third-block obstruction

The odd strict-slack counterexample uses two `(e+1)`-point parent blocks.  Their
facet hyperplanes contribute `2(e+1)=n+1` points when `n=2e+1`.  At the even
half-radius predecessor `n=16`, `e=7`, two eight-point parents contribute only
sixteen facets.  This file proves that a third eight-point parent cannot extend
the standard disjoint packing pencil while retaining global farness.

The proof is domain-independent.  If `A,B` partition sixteen coordinates and
`C` is a third eight-set, one of `A cap C` or `B cap C` has between four and
seven elements.  Its union with `C` has at most twelve elements.  For a parity
frame in which every twelve columns are independent (in particular an
`[16,k]` MDS parity frame with `k <= 4`), the two corresponding column spans
intersect exactly in the span of their common columns.  Therefore any subspace
shared by the packing intersection and `span(C)` is contained in a support
span of size at most seven.  A shared projective line is consequently joint,
not a proper third-block extension.
-/

set_option autoImplicit false

open Finset Submodule

namespace ArkLib.ProximityGap.Frontier.HalfRadiusEvenThirdBlockObstruction

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable {iota : Type*} [Fintype iota] [DecidableEq iota]

/-- The column span indexed by a finite coordinate set. -/
def columnSpan (v : iota -> V) (S : Finset iota) : Submodule F V :=
  Submodule.span F (v '' (S : Set iota))

/-- Local independence makes intersections of two column spans exact: only
the common indexed columns survive. -/
theorem columnSpan_inf_eq_inter
    (v : iota -> V) (S C : Finset iota)
    (hLI : LinearIndepOn F v ((S ∪ C : Finset iota) : Set iota)) :
    columnSpan (F := F) v S ⊓ columnSpan (F := F) v C =
      columnSpan (F := F) v (S ∩ C) := by
  apply le_antisymm
  · intro z hz
    have hzS : z ∈ Submodule.span F (v '' (S : Set iota)) := hz.1
    have hzC : z ∈ Submodule.span F (v '' (C : Set iota)) := hz.2
    rw [Finsupp.mem_span_image_iff_linearCombination] at hzS hzC
    obtain ⟨f, hfS, hfz⟩ := hzS
    obtain ⟨g, hgC, hgz⟩ := hzC
    have hfU : f ∈ Finsupp.supported F F
        ((S ∪ C : Finset iota) : Set iota) := by
      rw [Finsupp.mem_supported] at hfS ⊢
      exact fun x hx => Finset.mem_union_left C (hfS hx)
    have hgU : g ∈ Finsupp.supported F F
        ((S ∪ C : Finset iota) : Set iota) := by
      rw [Finsupp.mem_supported] at hgC ⊢
      exact fun x hx => Finset.mem_union_right S (hgC hx)
    have hfg : f = g :=
      (linearIndepOn_iffₛ.mp hLI) f hfU g hgU (hfz.trans hgz.symm)
    subst g
    have hfI : f ∈ Finsupp.supported F F
        ((S ∩ C : Finset iota) : Set iota) := by
      rw [Finsupp.mem_supported] at hfS hgC ⊢
      exact fun x hx => Finset.mem_inter.mpr ⟨hfS hx, hgC hx⟩
    exact (Finsupp.mem_span_image_iff_linearCombination F).2 ⟨f, hfI, hfz⟩
  · apply le_inf
    · apply Submodule.span_mono
      apply Set.image_mono
      intro x hx
      exact (Finset.mem_inter.mp hx).1
    · apply Submodule.span_mono
      apply Set.image_mono
      intro x hx
      exact (Finset.mem_inter.mp hx).2

/-- A submodule lying in both locally independent column spans lies in the
span of the common columns. -/
theorem sharedSubmodule_le_commonSpan
    (v : iota -> V) (S C : Finset iota) (P : Submodule F V)
    (hLI : LinearIndepOn F v ((S ∪ C : Finset iota) : Set iota))
    (hPS : P ≤ columnSpan (F := F) v S)
    (hPC : P ≤ columnSpan (F := F) v C) :
    P ≤ columnSpan (F := F) v (S ∩ C) := by
  rw [← columnSpan_inf_eq_inter v S C hLI]
  exact le_inf hPS hPC

/-! ## The eight-plus-eight overlap calculation -/

/-- A partition splits every third block into its two parent intersections. -/
theorem inter_card_add_inter_card_eq
    (A B C : Finset iota) (hdisj : Disjoint A B)
    (hcover : A ∪ B = univ) :
    (A ∩ C).card + (B ∩ C).card = C.card := by
  have hsplit : (A ∩ C) ∪ (B ∩ C) = C := by
    ext x
    constructor
    · intro hx
      rcases mem_union.mp hx with hx | hx
      · exact (mem_inter.mp hx).2
      · exact (mem_inter.mp hx).2
    · intro hxC
      have hxAB : x ∈ A ∪ B := by rw [hcover]; exact mem_univ x
      rcases mem_union.mp hxAB with hxA | hxB
      · exact mem_union_left _ (mem_inter.mpr ⟨hxA, hxC⟩)
      · exact mem_union_right _ (mem_inter.mpr ⟨hxB, hxC⟩)
  have hparts : Disjoint (A ∩ C) (B ∩ C) := by
    exact hdisj.mono inter_subset_left inter_subset_left
  have hcard := Finset.card_union_of_disjoint hparts
  rw [hsplit] at hcard
  exact hcard.symm

/-- If both parents and the third block have size eight, some parent overlaps
the third block in at least four coordinates. -/
theorem four_le_max_inter_card
    (A B C : Finset iota) (hdisj : Disjoint A B)
    (hcover : A ∪ B = univ) (hC : C.card = 8) :
    4 ≤ max (A ∩ C).card (B ∩ C).card := by
  have hsum := inter_card_add_inter_card_eq A B C hdisj hcover
  rw [hC] at hsum
  omega

/-- A third eight-block distinct from both parents overlaps its more-populated
parent in at most seven coordinates. -/
theorem max_inter_card_le_seven
    (A B C : Finset iota) (hA : A.card = 8) (hB : B.card = 8)
    (hC : C.card = 8) (hCA : C ≠ A) (hCB : C ≠ B) :
    max (A ∩ C).card (B ∩ C).card ≤ 7 := by
  have hACle : (A ∩ C).card ≤ 8 := by
    rw [← hA]
    exact card_le_card inter_subset_left
  have hBCle : (B ∩ C).card ≤ 8 := by
    rw [← hB]
    exact card_le_card inter_subset_left
  have hACne : (A ∩ C).card ≠ 8 := by
    intro hAC
    have hIA : A ∩ C = A :=
      Finset.eq_of_subset_of_card_le inter_subset_left (by omega)
    have hIC : A ∩ C = C :=
      Finset.eq_of_subset_of_card_le inter_subset_right (by omega)
    exact hCA (hIC.symm.trans hIA)
  have hBCne : (B ∩ C).card ≠ 8 := by
    intro hBC
    have hIB : B ∩ C = B :=
      Finset.eq_of_subset_of_card_le inter_subset_left (by omega)
    have hIC : B ∩ C = C :=
      Finset.eq_of_subset_of_card_le inter_subset_right (by omega)
    exact hCB (hIC.symm.trans hIB)
  exact max_le (by omega) (by omega)

/-- One parent has overlap between four and seven with every genuinely third
eight-block. -/
theorem exists_parent_with_medium_overlap
    (A B C : Finset iota) (hdisj : Disjoint A B)
    (hcover : A ∪ B = univ) (hA : A.card = 8) (hB : B.card = 8)
    (hC : C.card = 8) (hCA : C ≠ A) (hCB : C ≠ B) :
    ∃ S : Finset iota,
      (S = A ∨ S = B) ∧ 4 ≤ (S ∩ C).card ∧ (S ∩ C).card ≤ 7 := by
  have hfour := four_le_max_inter_card A B C hdisj hcover hC
  have hseven := max_inter_card_le_seven A B C hA hB hC hCA hCB
  by_cases hle : (A ∩ C).card ≤ (B ∩ C).card
  · refine ⟨B, Or.inr rfl, ?_, ?_⟩
    · simpa [max_eq_right hle] using hfour
    · exact le_trans (le_max_right _ _) hseven
  · have hBA : (B ∩ C).card ≤ (A ∩ C).card := Nat.le_of_lt (lt_of_not_ge hle)
    refine ⟨A, Or.inl rfl, ?_, ?_⟩
    · simpa [max_eq_left hBA] using hfour
    · exact le_trans (le_max_left _ _) hseven

/-! ## MDS consumer -/

/-- Every collection of at most `d` columns is linearly independent. -/
def IndependentUpTo (v : iota -> V) (d : Nat) : Prop :=
  forall J : Finset iota, J.card ≤ d ->
    LinearIndependent F (fun j : J => v j)

/-- **No proper third half-block extension at `n=16`, `k<=4`.**

For two disjoint eight-point packing parents and a genuinely third eight-set,
any submodule shared by all three parent spans is contained in a support span
of between four and seven columns.  In particular, if `P` is a vector plane,
its projective line is joint/improper at radius `e=7`. -/
theorem thirdBlock_sharedSubmodule_is_supportImproper
    (v : iota -> V) (A B C : Finset iota) (P : Submodule F V)
    (hdisj : Disjoint A B) (hcover : A ∪ B = univ)
    (hA : A.card = 8) (hB : B.card = 8) (hC : C.card = 8)
    (hCA : C ≠ A) (hCB : C ≠ B)
    (hMDS12 : IndependentUpTo (F := F) v 12)
    (hPA : P ≤ columnSpan (F := F) v A)
    (hPB : P ≤ columnSpan (F := F) v B)
    (hPC : P ≤ columnSpan (F := F) v C) :
    ∃ S : Finset iota,
      (S = A ∨ S = B) ∧ 4 ≤ (S ∩ C).card ∧
      (S ∩ C).card ≤ 7 ∧ P ≤ columnSpan (F := F) v (S ∩ C) := by
  obtain ⟨S, hSparent, hfour, hseven⟩ :=
    exists_parent_with_medium_overlap A B C hdisj hcover hA hB hC hCA hCB
  have hS : S.card = 8 := by rcases hSparent with rfl | rfl <;> assumption
  have hunionCard := Finset.card_union_add_card_inter S C
  have hunion : (S ∪ C).card ≤ 12 := by omega
  have hLI' := hMDS12 (S ∪ C) hunion
  have hLI : LinearIndepOn F v ((S ∪ C : Finset iota) : Set iota) := by
    simpa only [LinearIndepOn] using hLI'
  have hPS : P ≤ columnSpan (F := F) v S := by
    rcases hSparent with rfl | rfl
    · exact hPA
    · exact hPB
  have hcommon := sharedSubmodule_le_commonSpan v S C P hLI hPS hPC
  exact ⟨S, hSparent, hfour, hseven, hcommon⟩

end ArkLib.ProximityGap.Frontier.HalfRadiusEvenThirdBlockObstruction

#print axioms
  ArkLib.ProximityGap.Frontier.HalfRadiusEvenThirdBlockObstruction.columnSpan_inf_eq_inter
#print axioms
  ArkLib.ProximityGap.Frontier.HalfRadiusEvenThirdBlockObstruction.exists_parent_with_medium_overlap
#print axioms
  ArkLib.ProximityGap.Frontier.HalfRadiusEvenThirdBlockObstruction.thirdBlock_sharedSubmodule_is_supportImproper
