/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.DimensionMultiplierMCA
import ArkLib.Research.ProximityGap.Frontier.UniversalCubicThreshold

/-! # All message dimensions from 2 through 2²⁶ at the production twice-length budget -/

noncomputable section
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.LowDimensionCubicPlateau
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open TerminalDomainSecurity

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

/-- For arbitrary evaluation points, the exact crossing at budget twice the
length extends to every dimension between two and 2²⁶ and every positive width. -/
theorem classification (dom : I ↪ F) (hn : Fintype.card I = n) {p : ℕ} [CharP F p]
    (hp : 1744830589 < p) (hB : Fintype.card F / 2^128 = 2147483648)
    {dim : ℕ} (hl : 2 ≤ dim) (hu : dim ≤ 67108864) (width : ℕ) [NeZero width] :
    mcaDeltaStar (F := F) ((ReedSolomon.code dom dim : Set (I → F)) ^⋈ (Fin width)) tolerance = boundary ∧
    ∀ δ : ℝ≥0, epsMCA (F := F) ((ReedSolomon.code dom dim : Set (I → F)) ^⋈ (Fin width)) δ ≤
      tolerance ↔ δ < boundary := by
  classical
  let e := Fintype.equivFinOfCardEq hn
  let x := e.symm.toEmbedding.trans dom
  have hr := MCAReindexThresholdEquiv.epsMCA_reindex_reedSolomon_eq e.symm x dom (fun _ => rfl) dim
  have hprev : epsMCA (F := F) (ReedSolomon.code dom dim : Set (I → F)) predecessor ≤ tolerance := by
    apply (DimensionMultiplierMCA.epsMCA_mono_dimension dom (by omega) hu predecessor ?_).trans
    · have h := (BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by decide : 0 < 2^128)).2 hB.ge
      exact (UniversalCubicThreshold.predecessor_eps dom hn (.inl hp)).trans
        (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using h)
    · rw [hn]
      norm_num [n, predecessor]
  have hb : tolerance < epsMCA (F := F) (ReedSolomon.code dom dim : Set (I → F)) boundary := by
    rw [hr]
    have hsmall := Nat.lt_mul_div_succ (Fintype.card F) (by decide : 0 < 2^128)
    have hq : Fintype.card F ≤ 2^256 := by omega
    exact ManyHeadLocatorMass.over_budget_128 (h := 0) (d := 2) (r := 357913941) x boundary
      (by decide) hl (by omega) (by
        change (1-(715827882:ℝ≥0)/1073741824)*1073741824 ≤ 357913942
        rw [tsub_mul, one_mul, div_mul_cancel₀ _ (by norm_num)]
        exact tsub_le_iff_right.mpr (by norm_num)) hq (by unfold n; omega)
  have heq : mcaDeltaStar (F := F) (ReedSolomon.code dom dim : Set (I → F)) tolerance = boundary := by
    rw [MCAReindexThresholdEquiv.mcaDeltaStar_reindex_reedSolomon_eq e.symm x dom (fun _ => rfl)]
    exact MCAAdjacentFloorExactPin.mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_bad
      (a := 715827882) (by decide) (by decide) _ _ (by rw [← hr]; exact hprev) (by rw [← hr]; exact hb)
  refine ⟨by rw [mcaDeltaStar_interleaved_eq]; exact heq, ?_⟩
  intro δ
  rw [epsMCA_interleaved_eq]
  constructor
  · intro good
    by_contra! hδ
    exact hb.not_ge ((epsMCA_mono _ hδ).trans good)
  · intro hδ
    by_contra! bad
    exact hδ.not_ge (heq ▸ mcaDeltaStar_le_of_bad _ _ bad)

/-- Every prime in the twice-length budget class has the complete dimension interval. -/
theorem prime_classification {p : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p) (hn : Fintype.card I = n)
    (hB : p / 2^128 = 2147483648) {dim : ℕ} (hl : 2 ≤ dim) (hu : dim ≤ 67108864)
    (width : ℕ) [NeZero width] :
    mcaDeltaStar (F := ZMod p) ((ReedSolomon.code dom dim : Set (I → ZMod p)) ^⋈ (Fin width)) tolerance =
      boundary ∧ ∀ δ : ℝ≥0, epsMCA (F := ZMod p)
        ((ReedSolomon.code dom dim : Set (I → ZMod p)) ^⋈ (Fin width)) δ ≤ tolerance ↔ δ < boundary := by
  exact classification dom hn (p := p) (by omega) (by simpa only [ZMod.card] using hB) hl hu width

#print axioms prime_classification
end ArkLib.ProximityGap.Frontier.LowDimensionCubicPlateau
