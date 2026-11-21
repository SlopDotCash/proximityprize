/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FullFiberMcaLift
import ArkLib.Research.ProximityGap.Frontier.FourRateSmoothMca128
import ArkLib.Data.CodingTheory.ListDecodability.Bounds.KKH26

/-! # MCA lower bounds at larger smooth domain sizes by power projection -/
set_option autoImplicit false
namespace ProximityGap.SmoothPowerMcaDescent
open Finset Polynomial
open scoped NNReal ENNReal
variable {I F : Type} [Fintype I] [DecidableEq I] [Nonempty I] [Field F] [Fintype F] [DecidableEq F]

/-- Under a factorization of the length m·h with h a power of two, the mth-power
projection produces a smooth coset of size h and preserves every base MCA lower bound. -/
theorem exists_smooth_base (D : I ↪ F) [ReedSolomon.Smooth D] {m h : ℕ} (hm : 0 < m)
    (hn : Fintype.card I = m*h) (hp : ∃ b : ℕ, h = 2^b) :
    ∃ V : Finset F, V.card = h ∧ (∀ i, D i ^ m ∈ V) ∧
      (∀ v ∈ V, (univ.filter (fun i => D i ^ m = v)).card = m) ∧
      Nonempty (ReedSolomon.Smooth (Function.Embedding.subtype (· ∈ V))) ∧
      ∀ (k : ℕ), 0 < k → ∀ δ : ℝ≥0,
      epsMCA (F := F) (ReedSolomon.code (Function.Embedding.subtype (· ∈ V)) k : Set (V → F)) δ ≤
        epsMCA (F := F) (ReedSolomon.code D (k*m) : Set (I → F)) δ := by
  classical
  obtain ⟨V,hcard,hmem,hfib,-⟩ :=
    CodingTheory.AdditiveSetListDecoding.Smooth.exists_pow_projection_structure D hn
  let E := Function.Embedding.subtype (· ∈ V)
  let π (i : I) : V := ⟨D i ^ m,hmem i⟩
  have hf (v : V) : (univ.filter (fun i => π i = v)).card = m := by
    rw [show (univ.filter (fun i => π i = v)) = (univ.filter (fun i => D i ^ m = (v : F))) by
      ext i; simp [π, Subtype.ext_iff]]
    exact hfib v v.property
  have hsur (v : V) : ∃ i, π i = v := by
    obtain ⟨i,hi⟩ := card_pos.mp (hm.trans_eq (hf v).symm)
    exact ⟨i,(mem_filter.mp hi).2⟩
  have ht : 0 < h := by obtain ⟨b,rfl⟩ := hp; positivity
  let : Nonempty V := Fintype.card_pos_iff.mp (by simpa [hcard] using ht)
  refine ⟨V,hcard,hmem,hfib,?_,fun k hk δ => FullFiberMcaLift.epsMCA_le D E π (X^m) hm hk (by simp)
    (fun i => by simp [E,π]) hf δ⟩
  let H := ReedSolomon.Smooth.H D
  let c := ReedSolomon.Smooth.a D
  have hcos : (↑(univ.image D) : Set F) = (fun x : Fˣ => (c : F) * (x : F)) '' (H : Set Fˣ) :=
    ReedSolomon.Smooth.h_coset
  refine ⟨⟨H.map (powMonoidHom m), c^m, ?_, ?_⟩⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨v,_,rfl⟩ := mem_image.mp hx
      obtain ⟨i,hi⟩ := hsur v
      have hx : D i ∈ (↑(univ.image D) : Set F) := mem_image_of_mem _ (mem_univ _)
      rw [hcos] at hx
      obtain ⟨a,ha,he⟩ := hx
      change (c : F) * (a : F) = D i at he
      refine ⟨a^m, ⟨a,ha,rfl⟩, ?_⟩
      change (c^m : Fˣ).val * (a^m : Fˣ).val = (v : F)
      rw [Units.val_pow_eq_pow_val,Units.val_pow_eq_pow_val,← mul_pow,he]
      exact congrArg Subtype.val hi
    · rintro ⟨v,⟨a,ha,rfl⟩,rfl⟩
      have hx : (c : F)*(a : F) ∈ (↑(univ.image D) : Set F) := hcos ▸ ⟨a,ha,rfl⟩
      obtain ⟨i,_,hi⟩ := mem_image.mp hx
      apply mem_image.mpr
      refine ⟨π i,mem_univ _, ?_⟩
      change D i ^ m = (c^m : Fˣ).val * (a^m : Fˣ).val
      rw [Units.val_pow_eq_pow_val,Units.val_pow_eq_pow_val,← mul_pow,hi]
  · obtain ⟨e,he⟩ := hp
    exact ⟨e, by simpa only [Fintype.card_coe] using hcard.trans he⟩

/-- For every smooth length 128m in the certified field-size interval, rate one
half already violates the 128-bit threshold at 31/64 errors, including its endpoint. -/
theorem rate_half_bad (D : I ↪ F) [ReedSolomon.Smooth D] {m : ℕ}
    (hm : 0 < m) (hn : Fintype.card I = m*128)
    (window : FourRateSmoothMca128.BudgetWindow (Fintype.card F)) {δ : ℝ≥0}
    (hδ : 31/64 ≤ δ) :
    ((prizeThreshold : ℝ≥0) : ℝ≥0∞) <
      epsMCA (F := F) (ReedSolomon.code D (64*m) : Set (I → F)) δ := by
  classical
  obtain ⟨V,hV,_,_,⟨sm⟩,hlift⟩ := exists_smooth_base D hm hn ⟨7,rfl⟩
  let := sm
  let : Nonempty V := Fintype.card_pos_iff.mp (by simp [hV])
  let E := Function.Embedding.subtype (· ∈ V)
  have h := FourRateSmoothMca128.half_good_iff (D := E) (by simpa using hV) window δ
  apply lt_of_lt_of_le _ (hlift 64 (by decide) δ)
  exact lt_of_not_ge fun good => (not_lt_of_ge hδ) (by norm_num at h ⊢; exact h.mp good)

/-- A certified 246-bit production-length prime-field family at dimension 2²⁹. -/
theorem prime246_rate_half_bad (D : I ↪ FourRateListPrime246.K) [ReedSolomon.Smooth D]
    (hn : Fintype.card I = 2^30) {δ : ℝ≥0} (hδ : 31/64 ≤ δ) :
    ((prizeThreshold : ℝ≥0) : ℝ≥0∞) <
      epsMCA (F := FourRateListPrime246.K)
        (ReedSolomon.code D (2^29) : Set (I → FourRateListPrime246.K)) δ := by
  have h := rate_half_bad D (m := 8388608) (by decide) (hn.trans (by decide))
    FourRateSmoothMca128.prime246_window hδ
  simpa only [show 64 * 8388608 = 2^29 by decide] using h

#print axioms exists_smooth_base
#print axioms rate_half_bad
#print axioms prime246_rate_half_bad
end ProximityGap.SmoothPowerMcaDescent
