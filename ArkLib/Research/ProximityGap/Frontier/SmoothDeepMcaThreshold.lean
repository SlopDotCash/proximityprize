/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DeepListMcaTransfer
import ArkLib.Research.ProximityGap.Frontier.PrescribedProductList
import ArkLib.Research.ProximityGap.Frontier.CircuitDensity

/-! # An exact MCA radius on smooth cosets from integer inequalities -/

set_option autoImplicit false
namespace ProximityGap.SmoothDeepMcaThreshold
open Finset Polynomial Code
open scoped NNReal ENNReal
variable {I F : Type} [Fintype I] [Field F] [Fintype F] [DecidableEq F] [DecidableEq I]

omit [DecidableEq I] in
/-- The prescribed-product list argument applies to cosets after scaling the polynomial variable. -/
theorem smooth_list_lower (D : I ↪ F) [ReedSolomon.Smooth D] {k L a : ℕ} (hk : 0 < k)
    (hL : Fintype.card I * Fintype.card F ^ a * L < (Fintype.card I).choose (k+1+a)) :
    (L : ℕ∞) < Lambda (ReedSolomon.code D k : Set (I → F))
      (((Fintype.card I - (k+1+a) : ℕ) : ℝ) / (Fintype.card I : ℝ)) := by
  classical
  let H := ReedSolomon.Smooth.H D
  let c := ReedSolomon.Smooth.a D
  let : Fintype H := Fintype.ofFinite H
  have hcos : (↑(univ.image D) : Set F) = (fun x : Fˣ => (c : F) * (x : F)) '' (H : Set Fˣ) :=
    ReedSolomon.Smooth.h_coset
  have all (i : I) : ∃ z : H, D i = (c : F) * ((z : Fˣ) : F) := by
    have hx : D i ∈ (↑(univ.image D) : Set F) := mem_image_of_mem _ (mem_univ _)
    rw [hcos] at hx
    obtain ⟨z,hz,he⟩ := hx
    exact ⟨⟨z,hz⟩,he.symm⟩
  choose z hz using all
  have hsur : Function.Surjective z := by
    intro v
    have hx : (c : F) * ((v : Fˣ) : F) ∈ (↑(univ.image D) : Set F) :=
      hcos ▸ ⟨v.val,v.property,rfl⟩
    obtain ⟨i,_,he⟩ := mem_image.mp hx
    exact ⟨i,Subtype.ext (Units.ext (mul_left_cancel₀ c.ne_zero ((hz i).symm.trans he)))⟩
  have hcH := Fintype.card_le_of_surjective z hsur
  let D' : I ↪ F := ⟨fun i => ((z i : Fˣ) : F), fun i j h => D.injective
    ((hz i).trans ((congrArg (fun x : F => (c : F) * x) h).trans (hz j).symm))⟩
  have low := PrescribedProductList.exceeds_budget_deeper D' H z (fun _ => rfl) a hk
    ((Nat.mul_le_mul_right L (Nat.mul_le_mul_right _ hcH)).trans_lt hL)
  apply low.trans_le (Lambda_mono_code ?_ _)
  let : NeZero k := ⟨hk.ne'⟩
  intro w hw
  obtain ⟨p,hp,he⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hw
  apply ReedSolomon.mem_code_iff_eval_of_ne_zero.mpr
  refine ⟨p.comp (C (↑c⁻¹ : F) * X), ?_, ?_⟩
  · simpa [natDegree_comp, c⁻¹.ne_zero] using hp
  · intro i
    rw [eval_comp, eval_mul, eval_C, eval_X, hz i, ← mul_assoc, Units.inv_mul, one_mul]
    exact he i

/-- On an arbitrary smooth coset over a finite field, the operational threshold is
exact whenever the circuit upper count, product-fiber lower count and DEEP collision
estimate all straddle the budget at successive agreement counts. -/
theorem epsMCA_le_iff [Nonempty I] (D : I ↪ F) [ReedSolomon.Smooth D]
    {k a t B L : ℕ} (hk : 0 < k) (ht : t = k+2+a) (htn : t ≤ Fintype.card I)
    (hupper : (Fintype.card I).choose (k+1) / t.choose k ≤ B)
    (hlower : Fintype.card I * Fintype.card F ^ a * L < (Fintype.card I).choose t)
    (hroom : k * (L+1).choose 2 < (Fintype.card F - Fintype.card I) * (L+1-B))
    (ε : ℝ≥0∞)
    (hεlo : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ ε)
    (hεhi : ε < ((B+1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
    (δ : ℝ≥0) :
    epsMCA (F := F) (ReedSolomon.code D k : Set (I → F)) δ ≤ ε ↔
    δ < ((Fintype.card I - t : ℕ) : ℝ≥0) / (Fintype.card I : ℝ≥0) := by
  classical
  have hn : (0 : ℝ≥0) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hstep : (1-δ) * (Fintype.card I : ℝ≥0) ≤ t ↔
      ((Fintype.card I - t : ℕ) : ℝ≥0) / Fintype.card I ≤ δ := by
    rw [tsub_mul, one_mul, tsub_le_iff_right, div_le_iff₀ hn, Nat.cast_tsub, tsub_le_iff_right, add_comm]
  constructor
  · intro safe
    by_contra! bad
    have hl := smooth_list_lower D (k := k+1) (a := a) (L := L) (by omega)
      (show _ from by simpa only [ht] using hlower)
    obtain ⟨u₀,u₁,hcount⟩ := DeepListMcaTransfer.exists_bad_count_of_list D δ hk (by omega : k<t)
      htn (hstep.mpr bad) (by simpa only [ht] using hl) hroom
    let G := univ.filter (mcaEvent (F := F) (ReedSolomon.code D k : Set (I → F)) δ u₀ u₁)
    have lo := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
      (ReedSolomon.code D k : Set (I → F)) δ ![u₀,u₁] G (fun γ hγ => (mem_filter.mp hγ).2)
    apply (not_lt_of_ge safe)
    apply hεhi.trans_le (le_trans ?_ lo)
    exact ENNReal.div_le_div_right (by exact_mod_cast (show B+1 ≤ G.card from hcount)) _

  · intro hδ
    apply le_trans ?_ hεlo
    apply epsMCA_le_of_badCount_le
    intro u
    have h := CircuitDensity.mca_count_mul_le D k (t+1) δ (u 0) (u 1) (by omega) (by
      intro S hS
      by_contra! h
      exact (not_le_of_gt hδ) (hstep.mp (hS.trans (by exact_mod_cast (show S.card ≤ t by omega)))))
    exact (Nat.le_div_iff_mul_le (Nat.choose_pos (by omega : k ≤ t))).mpr (by simpa using h) |>.trans hupper

#print axioms smooth_list_lower
#print axioms epsMCA_le_iff
end ProximityGap.SmoothDeepMcaThreshold
