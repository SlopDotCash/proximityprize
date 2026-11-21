/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.UniversalSignedListNorms
import ArkLib.Research.ProximityGap.Frontier.SmoothDomainMcaEquivalence
import ArkLib.ToMathlib.InformationTheory.Hamming

/-! # Signed half-rate list bounds on every supplied smooth production domain -/

namespace ProximityGap.SmoothSignedListProfile
open Code ReservedFiberList SmoothDomainMcaEquivalence UniversalSignedListNorms

variable {F I J : Type} [Field F] [DecidableEq F] [Fintype I] [Fintype J]

/-- Scaling the evaluation sites and transporting the center along an index equivalence
preserves every attainable interleaved list. -/
theorem list_le_of_scale {D : I ↪ F} {E : J ↪ F} (e : I ≃ J) (a : Fˣ)
    (he : ∀ i, D i=(a:F)*E (e i)) (k width : ℕ) (δ : ℝ) :
    Lambda (interleavedCodeSet (κ:=Fin width) (ReedSolomon.code E k : Set (J → F))) δ ≤
    Lambda (interleavedCodeSet (κ:=Fin width) (ReedSolomon.code D k : Set (I → F))) δ := by
  classical
  let move (w : J → Fin width → F) : I → Fin width → F := w ∘ e
  have hinj : Function.Injective move := fun w v h => funext fun j => by
    simpa [move] using congrFun h (e.symm j)
  apply Lambda_le_iff_forall_encard_le.mpr
  intro center
  apply le_trans _ (encard_closeCodewordsRel_le_Lambda _ _ (move center))
  rw [← hinj.injOn.encard_image]
  apply Set.encard_mono
  rintro _ ⟨w,hw,rfl⟩
  obtain ⟨hwC,hd⟩ := mem_closeCodewordsRel_iff.mp hw
  apply mem_closeCodewordsRel_iff.mpr
  refine ⟨fun j => mem_code_scale e a he (hwC j), ?_⟩
  simpa only [relHammingDist_coe,move,hammingDist_comp_equiv,Fintype.card_congr e] using hd

/-- All fourteen population bounds hold on every smooth coset, with any indexing and every positive width. -/
theorem smooth_list [Finite F] (D : I ↪ F) [ReedSolomon.Smooth D]
    (hn : Fintype.card I=2^30) (i : Fin 14) (B width : ℕ) (hw : 0<width)
    (hB : B<(profile i).population) :
    (B:ℕ∞) < Lambda (interleavedCodeSet (κ:=Fin width) (ReedSolomon.code D (2^29) : Set (I → F)))
      (((profile i).errors:ℝ)/(2^30:ℕ)) := by
  classical
  obtain ⟨sites,hsite⟩ := coset_equiv D
  let H := ReedSolomon.Smooth.H D
  let : Fintype H := Fintype.ofEquiv I sites
  have hc : Nat.card H = 2^30 := by
    rw [Nat.card_eq_fintype_card, ←Fintype.card_congr sites, hn]
  obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α:=H)
  have ho : orderOf g = 2^30 := hg.trans hc
  have hu : orderOf g.val = 2^30 := (orderOf_injective H.subtype Subtype.val_injective g).trans ho
  let A := Fin 64 × Fin 16777216
  let idx : A ≃ Fin (16777216*64) := (Equiv.prodComm _ _).trans finProdFinEquiv
  let point (j : A) : H := g^(idx j).val
  let powers : A ≃ H := Equiv.ofBijective point ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨fun j t he => idx.injective (Fin.ext ((IsPrimitiveRoot.iff_orderOf.mpr ho).pow_inj
      (idx j).isLt (idx t).isLt he)), by rw [←Nat.card_eq_fintype_card (α:=H),hc]
                                         simp only [A,Fintype.card_prod,Fintype.card_fin]; decide⟩)
  let e := sites.trans powers.symm
  have scale (j : I) : D j = (ReedSolomon.Smooth.a D:F)*cyclicDomain (M:=64) (s:=16777216) g.val hu (e j) := by
    rw [hsite]
    apply congrArg (_ * ·)
    have h : sites j = point (e j) := (powers.apply_symm_apply (sites j)).symm
    exact congrArg (fun x : H => ((x:Fˣ):F)) h
  exact (list_bound g.val hu i B width hw hB).trans_le
    (list_le_of_scale e (ReedSolomon.Smooth.a D) scale _ _ _)

#print axioms smooth_list
end ProximityGap.SmoothSignedListProfile
