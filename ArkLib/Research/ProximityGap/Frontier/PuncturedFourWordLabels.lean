/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PuncturedFourWordProfile
import ArkLib.Research.ProximityGap.Frontier.TerminalCollinearHeadCount

/-! # Counting ordinary labels and distinct values at the puncture -/

set_option autoImplicit false
open Finset Polynomial
namespace ProximityGap.PuncturedFourWordLabels
open PuncturedFourWordProfile
variable {F J : Type} [Field F] [DecidableEq F] [Fintype J] [DecidableEq J]

/-- Append the hole value to each of the four punctured error sets. Two augmented
sets have at most one element in common. Thus their union gives at least two labels
more than the original block length. -/
theorem count (D : J ↪ F) (q : Fin 4 → F[X]) (w : J → F) (a : F) (ha : a ∉ Set.range D)
    (h : ℕ) (hn : Fintype.card J + 1 = 4*h) (hinj : Function.Injective q)
    (hq : ∀ i, (q i).natDegree+2 ≤ 2*h)
    (hw : ∀ i, (univ.filter fun x : J => (q i).eval (D x) ≠ w x).card ≤ h+1) :
    let E := fun i => univ.filter (fun x : J => (q i).eval (D x) ≠ w x)
    4*h+2 ≤ (univ.biUnion E).card + (univ.image (fun i => (q i).eval a)).card := by
  classical
  let E (i : Fin 4) := univ.filter (fun x : J => (q i).eval (D x) ≠ w x)
  let v (i : Fin 4) := (q i).eval a
  let A (i : Fin 4) := (E i).disjSum ({v i} : Finset F)
  have hs : ∀ i, (E i).card = h+1 := (polynomial_profile D q w h hn hinj hq hw).1
  have hpair (i j : Fin 4) (hij : i ≠ j) : (A i ∩ A j).card ≤ 1 := by
    have hc := card_union_add_card_inter (E i) (E j)
    rw [hs,hs] at hc
    have hmin : 2*h+1 ≤ (E i ∪ E j).card := error_union D (q i) (q j) w h hn (hinj.ne hij) (hq i) (hq j)
    have hcut : A i ∩ A j = (E i ∩ E j).disjSum (({v i} : Finset F) ∩ {v j}) := by
      ext x
      cases x <;> simp [A]
    rw [hcut,card_disjSum]
    by_cases he : v i = v j
    · suffices hzero : (E i ∩ E j).card = 0 by simp [he,hzero]
      by_contra! hpos
      let G := (univ : Finset J) \ (E i ∪ E j)
      have hg : G.card = Fintype.card J-(E i∪E j).card := by rw [show G = univ \ (E i ∪ E j) from rfl,card_sdiff_of_subset (subset_univ _),card_univ]
      apply separate_outside D (q i) (q j) G a ha (hinj.ne hij) (by have := hq i; omega)
        (by have := hq j; omega) _ he
      intro x hx
      have hout := (mem_sdiff.mp hx).2
      simp [E] at hout
      exact hout.1.trans hout.2.symm
    · have hsing : ({v i} : Finset F) ∩ {v j} = ∅ := by simp [he]
      rw [hsing,card_empty,add_zero]
      omega
  have hrow (i : Fin 4) : h+2 ≤ (A i).card := by simp [A,hs]
  have hbound := TerminalCollinearHeadCount.union_lower (univ : Finset (Fin 4)) A
    (fun i _ => hrow i) (fun i _ j _ => hpair i j)
  have hsub : univ.biUnion A ⊆ (univ.biUnion E).disjSum (univ.image v) := by
    intro x hx
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hx
    cases x with
    | inl x => exact inl_mem_disjSum.mpr (mem_biUnion.mpr ⟨i,mem_univ _,inl_mem_disjSum.mp hi⟩)
    | inr x =>
      have he := mem_singleton.mp (inr_mem_disjSum.mp hi)
      exact inr_mem_disjSum.mpr (he ▸ mem_image_of_mem _ (mem_univ i))
  have hc := card_le_card hsub
  rw [card_disjSum] at hc
  norm_num [Nat.choose] at hbound
  change 4*h+2 ≤ (univ.biUnion E).card + (univ.image v).card
  omega

#print axioms count
end ProximityGap.PuncturedFourWordLabels
