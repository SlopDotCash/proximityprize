/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ProximityGenerator.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Smooth cosets of the same size have the same MCA profile

Normalizing by the coset representative identifies the nodes with the full group
of n-th roots of unity. Scaling the polynomial variable and relabeling coordinates
therefore preserves the canonical error for every generator, degree and radius.
-/

namespace ProximityGap.SmoothDomainMcaEquivalence

open Polynomial Finset CoreDefinitions

variable {F I J : Type} [Field F] [DecidableEq F] [Fintype I] [Fintype J]

/-- Dividing each smooth evaluation site by its coset representative enumerates the subgroup. -/
theorem coset_equiv (D : I ↪ F) [ReedSolomon.Smooth D] :
    ∃ e : I ≃ ReedSolomon.Smooth.H D, ∀ i,
      D i = (ReedSolomon.Smooth.a D : F) * ((e i : Fˣ) : F) := by
  classical
  let H := ReedSolomon.Smooth.H D
  let a := ReedSolomon.Smooth.a D
  have hc : (↑(univ.image D) : Set F) = (fun x : Fˣ => (a : F)*(x : F)) '' (H : Set Fˣ) :=
    ReedSolomon.Smooth.h_coset
  have hx (i : I) : ∃ h : H, D i = (a : F)*((h : Fˣ) : F) := by
    have hi : D i ∈ (↑(univ.image D) : Set F) := mem_image_of_mem D (mem_univ i)
    obtain ⟨x,hx,he⟩ := hc ▸ hi
    exact ⟨⟨x,hx⟩, he.symm⟩
  choose z hz using hx
  have hi : Function.Injective z := fun i j hij => D.injective (by rw [hz i,hz j,hij])
  have hs : Function.Surjective z := by
    intro v
    have hv : (a : F)*((v : Fˣ) : F) ∈ (↑(univ.image D) : Set F) :=
      hc ▸ ⟨v.val,v.property,rfl⟩
    obtain ⟨i,_,he⟩ := mem_image.mp hv
    exact ⟨i,Subtype.ext (Units.ext (mul_left_cancel₀ a.ne_zero ((hz i).symm.trans he)))⟩
  exact ⟨Equiv.ofBijective z ⟨hi,hs⟩, hz⟩

private theorem subgroup_eq_roots (D : I ↪ F) [ReedSolomon.Smooth D] :
    ReedSolomon.Smooth.H D = rootsOfUnity (Fintype.card I) F := by
  obtain ⟨e,_⟩ := coset_equiv D
  let H := ReedSolomon.Smooth.H D
  let : Fintype H := Fintype.ofEquiv I e
  have hcard := Fintype.card_congr e
  have hpos : 0 < Fintype.card I := by
    obtain ⟨a,ha⟩ := ReedSolomon.Smooth.h_card_pow2 (domain := D)
    rw [ha]
    positivity
  have : NeZero (Fintype.card I) := ⟨hpos.ne'⟩
  apply Subgroup.eq_of_le_of_card_ge
  · intro x hx
    apply (mem_rootsOfUnity _ _).mpr
    have h : (⟨x,hx⟩ : H) ^ Fintype.card H = 1 := pow_card_eq_one
    rw [hcard]
    exact congrArg Subtype.val h
  · change Nat.card _ ≤ Nat.card H
    rw [Nat.card_eq_fintype_card (α := H), ← hcard]
    exact card_rootsOfUnity F _

/-- Equal-size smooth domains differ only by a nonzero dilation and reindexing. -/
theorem exists_reindex_scale (D : I ↪ F) (E : J ↪ F)
    [ReedSolomon.Smooth D] [ReedSolomon.Smooth E] (hn : Fintype.card I = Fintype.card J) :
    ∃ (e : I ≃ J) (a : Fˣ), ∀ i, D i = (a : F)*E (e i) := by
  obtain ⟨u,hu⟩ := coset_equiv D
  obtain ⟨v,hv⟩ := coset_equiv E
  have hH : ReedSolomon.Smooth.H D = ReedSolomon.Smooth.H E := by
    rw [subgroup_eq_roots D, subgroup_eq_roots E, hn]
  let c : ReedSolomon.Smooth.H D ≃ ReedSolomon.Smooth.H E :=
    Equiv.subtypeEquivRight (fun _ => by rw [hH])
  let e := u.trans (c.trans v.symm)
  refine ⟨e, ReedSolomon.Smooth.a D * (ReedSolomon.Smooth.a E)⁻¹, fun i => ?_⟩
  rw [hu i,hv (e i)]
  have he : ((v (e i) : Fˣ) : F) = ((u i : Fˣ) : F) := by
    simp [e,c]
  rw [he, Units.val_mul, mul_assoc]
  congr 1
  rw [← mul_assoc, Units.inv_mul, one_mul]

private theorem mem_code_scale {D : I ↪ F} {E : J ↪ F} (e : I ≃ J)
    (a : Fˣ) (he : ∀ i, D i = (a : F)*E (e i)) {k : ℕ} {w : J → F}
    (hw : w ∈ ReedSolomon.code E k) : w ∘ e ∈ ReedSolomon.code D k := by
  obtain ⟨P,hP,h⟩ := ReedSolomon.mem_code_iff_eval.mp hw
  apply ReedSolomon.mem_code_iff_eval.mpr
  have hd : (C (↑a⁻¹ : F) * X).degree = 1 := degree_C_mul_X a⁻¹.ne_zero
  refine ⟨P.comp (C (↑a⁻¹ : F)*X), ?_, ?_⟩
  · rwa [degree_comp (by rw [hd]; decide), hd, mul_one]
  · intro i
    rw [eval_comp,eval_mul,eval_C,eval_X,he i,←mul_assoc,Units.inv_mul,one_mul]
    exact h (e i)

/-- The full canonical MCA error profile is independent of the choice and ordering
of a smooth coset at a given length over a given field. -/
theorem mcaError_eq {S L : Type} [Nonempty S] [Fintype S] [SampleableType S] [Fintype L]
    (G : Generator S L F) (D : I ↪ F) (E : J ↪ F)
    [ReedSolomon.Smooth D] [ReedSolomon.Smooth E] (hn : Fintype.card I = Fintype.card J)
    (k : ℕ) (r : ℝ) : mcaError G (ReedSolomon.code D k) r =
      mcaError G (ReedSolomon.code E k) r := by
  obtain ⟨e,a,he⟩ := exists_reindex_scale D E hn
  apply mcaError_comp_equiv _ _ _ e _ r
  intro w
  refine ⟨fun h => ?_, mem_code_scale e a he⟩
  have hback (j : J) : E j = (↑a⁻¹ : F) * D (e.symm j) := by
    rw [he, Equiv.apply_symm_apply, ←mul_assoc, Units.inv_mul, one_mul]
  simpa [Function.comp_def] using mem_code_scale e.symm a⁻¹ hback h

end ProximityGap.SmoothDomainMcaEquivalence

#print axioms ProximityGap.SmoothDomainMcaEquivalence.exists_reindex_scale
#print axioms ProximityGap.SmoothDomainMcaEquivalence.mcaError_eq
