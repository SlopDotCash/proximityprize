/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TwoProjectiveExtraFibers
import ArkLib.Research.ProximityGap.Frontier.TwoHeadExtraCoset

/-! # Two extra scalar directions on every production-length smooth coset -/

set_option autoImplicit false
noncomputable section
open Finset Polynomial Code _root_.ProximityGap
open scoped ENNReal NNReal

namespace ArkLib.ProximityGap.Frontier.TwoProjectiveExtraCoset
open TerminalDomainSecurity _root_.ProximityGap.MCAThresholdLedger

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

set_option maxRecDepth 10000 in
/-- The order-32 construction supplies two full heads plus both extra directions
on the same received pair. -/
theorem power_mass (dom : Fin n ↪ F) (c g : F) (hc : c ≠ 0) (hg : orderOf g = n)
    (hdom : ∀ i, dom i = c * g ^ i.val) {e : ℕ} (hl : 659903830 ≤ e) (hu : e ≤ 671088639)
    (hq : (2 * (e + 1) + 1).choose 2 < Fintype.card F) :
    ((2 * (e + 1) + 2 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (Fin n → F)) ((e : ℝ≥0) / n) := by
  classical
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P + e = 939524097 := ⟨939524097 - e, by omega⟩
  obtain ⟨T, hT⟩ : ∃ T : ℕ, T + 2 * P = 872415234 := ⟨872415234 - 2 * P, by omega⟩
  have m : 33554432 * 32 - (33554430 + 3 * 33554432 + P) = e + 1 := by omega
  have base : (1 - (e : ℝ≥0) / n) * (n : ℝ≥0) = ((n - e : ℕ) : ℝ≥0) := by
    rw [tsub_mul, one_mul, div_mul_cancel₀ _ (by norm_num [n]), ← Nat.cast_tsub]
  have room : 2 * (e + 1) + 1 < Fintype.card F := by
    have lower := Nat.choose_le_choose 2 (show 100000 ≤ 2 * (e + 1) + 1 by omega)
    have : 1342177281 < (100000 : ℕ).choose 2 := by norm_num [Nat.choose_two_right]
    omega
  rw [← m]
  apply TwoProjectiveExtraFibers.mass (s := 33554432) (by decide) dom c g hc hg hdom k
    33554430 P T _ (by omega) (by decide) (by dsimp [k]; omega) (by dsimp [k]; omega) _ _
    (by rwa [m]) (by rwa [m])
  · change (1 - (e : ℝ≥0) / n) * (n : ℝ≥0) ≤ _
    rw [base]
    exact_mod_cast (show n - e ≤ 33554430 + 3 * 33554432 + P + 1 by dsimp [n]; omega)
  · change (1 - (e : ℝ≥0) / n) * (n : ℝ≥0) ≤ _
    rw [base]
    exact_mod_cast (show n - e ≤ 33554430 + 2 * 33554432 + T by dsimp [n]; omega)

/-- Every smooth domain admits the same simultaneous mass in each positive width. -/
theorem smooth_mass (dom : I ↪ F) [ReedSolomon.Smooth dom] (hn : Fintype.card I = n)
    {e : ℕ} (hl : 659903830 ≤ e) (hu : e ≤ 671088639)
    (hq : (2 * (e + 1) + 1).choose 2 < Fintype.card F) (width : ℕ) [NeZero width] :
    ((2 * (e + 1) + 2 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width)) ((e : ℝ≥0) / n) := by
  exact TwoHeadExtraCoset.smooth_mass_of_power dom hn _ _ _ (fun base c g hc hg hi =>
    power_mass base c g hc hg hi hl hu hq) width

/-- Each odd budget in this interval fails at least one Hamming step before the
two-full-head attack alone first exceeds that budget. -/
theorem odd_ceiling (dom : I ↪ F) [ReedSolomon.Smooth dom] (hn : Fintype.card I = n) {B : ℕ}
    (hB : Fintype.card F / 2 ^ 128 = B) (odd : B % 2 = 1) (hl : 1319807663 ≤ B) (hu : B ≤ 1342177281)
    (width : ℕ) [NeZero width] :
    let C := ((ReedSolomon.code dom k : Set (I → F)) ^⋈ (Fin width))
    tolerance < epsMCA (F := F) C (((B / 2 - 1 : ℕ) : ℝ≥0) / n) ∧
      mcaDeltaStar (F := F) C tolerance ≤ (((B / 2 - 1 : ℕ) : ℝ≥0) / n) := by
  dsimp only
  let e := B / 2 - 1
  have he : 659903830 ≤ e := by dsimp [e]; omega
  have he' : e ≤ 671088639 := by dsimp [e]; omega
  have cnt : 2 * (e + 1) + 2 = B + 1 := by dsimp [e]; omega
  have hf : (2 * (e + 1) + 1).choose 2 < Fintype.card F := by
    have mono := Nat.choose_le_choose 2 (show 2 * (e + 1) + 1 ≤ 1342177281 by omega)
    have bnd : (1342177281 : ℕ).choose 2 < 2 ^ 128 := by norm_num [Nat.choose_two_right]
    omega
  have above : tolerance < ((2 * (e + 1) + 2 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
    by_contra! below
    have h := (BoundarySecurityBudget.count_ratio_le_iff (Fintype.card_pos (α := F)) (by decide : 0 < 2 ^ 128)).mp
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using below)
    omega
  have bad := above.trans_le (smooth_mass dom hn he he' hf width)
  exact ⟨bad, mcaDeltaStar_le_of_bad _ _ bad⟩

#print axioms power_mass
#print axioms smooth_mass
#print axioms odd_ceiling

end ArkLib.ProximityGap.Frontier.TwoProjectiveExtraCoset
