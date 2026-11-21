/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.CubicApolarExtremum
import ArkLib.Research.ProximityGap.Frontier.LinearFieldBudgetRadius
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger

/-!
# Spike thresholds from the cubic apolar bound

At the predecessor of the integer field budget, a cubic apolar family bound
gives the exact threshold even in some cases where the product criterion
is an equality. This includes the two budgets at and just above a quarter
of the production block length.
-/

set_option autoImplicit false
open ProximityGap ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.CubicSpikeBudgetBoundary

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} [NeZero n]

/-- For the zero code, a bad scalar other than a chosen bad scalar must
cancel a nonzero second-row entry outside the chosen witness. -/
private theorem zero_dimension_upper (x : Fin n ↪ F) {e : ℕ} (he : e ≤ n) :
    epsMCA (F := F) (ReedSolomon.code x 0 : Set (Fin n → F)) ((e : ℝ≥0) / n) ≤
      ((e + 1 : ℕ) : ℝ≥0∞) / Fintype.card F := by
  classical
  rw [ReedSolomon.code_zero]
  apply epsMCA_le_of_badCount_le
  intro W
  let G := Finset.univ.filter (fun a : F => mcaEvent (F := F)
    ((⊥ : Submodule F (Fin n → F)) : Set (Fin n → F)) ((e : ℝ≥0) / n) (W 0) (W 1) a)
  change G.card ≤ e + 1
  rcases G.eq_empty_or_nonempty with hempty | ⟨b, hb⟩
  · simp [hempty]
  have extract (a : F) (ha : a ∈ G) :
      ∃ S : Finset (Fin n), n - e ≤ S.card ∧
        (∀ i ∈ S, W 0 i + a * W 1 i = 0) ∧ ∃ i ∈ S, W 1 i ≠ 0 := by
    obtain ⟨S, hs, ⟨w, hw, hline⟩, hno⟩ := (Finset.mem_filter.mp ha).2
    have hw0 : w = 0 := (Submodule.mem_bot F).mp hw
    subst w
    have hzero (i : Fin n) (hi : i ∈ S) : W 0 i + a * W 1 i = 0 := (hline i hi).symm
    refine ⟨S, ?_, hzero, ?_⟩
    · have hn : (n : ℝ≥0) ≠ 0 := by exact_mod_cast NeZero.ne n
      rw [Fintype.card_fin, tsub_mul, one_mul, div_mul_cancel₀ _ hn, ← Nat.cast_tsub] at hs
      exact_mod_cast hs
    · by_contra! h
      apply hno
      refine ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, fun i hi => ?_⟩
      exact ⟨by simpa [h i hi] using (hzero i hi).symm, (h i hi).symm⟩
  obtain ⟨S, hsize, hbase, _⟩ := extract b hb
  let sites := Finset.univ \ S
  let label (i : Fin n) := -(W 0 i) / W 1 i
  have hsites : sites.card ≤ e := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]
    omega
  have hcover : G ⊆ insert b (sites.image label) := by
    intro a ha
    rcases eq_or_ne a b with rfl | hne
    · exact Finset.mem_insert_self _ _
    obtain ⟨T, _, hline, i, hi, hnonzero⟩ := extract a ha
    have halabel : label i = a := (div_eq_iff hnonzero).mpr (by
      linear_combination -(hline i hi))
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩, halabel⟩
    intro his
    apply hne
    apply mul_right_cancel₀ hnonzero
    linear_combination hline i hi - hbase i his
  exact (Finset.card_le_card hcover).trans ((Finset.card_insert_le ..).trans
    (Nat.add_le_add_right (Finset.card_image_le.trans hsites) 1))

/-- At dimension zero the spike gives the exact MCA probability at every
Hamming step below the full block length. -/
theorem zero_dimension_mass (x : Fin n ↪ F) {e : ℕ} (he : e < n) :
    epsMCA (F := F) (ReedSolomon.code x 0 : Set (Fin n → F)) ((e : ℝ≥0) / n) =
      ((e + 1 : ℕ) : ℝ≥0∞) / Fintype.card F :=
  le_antisymm (zero_dimension_upper x he.le) (LinearFieldBudgetRadius.spike x (by omega))

/-- The cubic apolar cap at the predecessor and the spike construction at the
budget determine the first bad count. The equality case in the distance
condition also works when the integer budget is divisible by three. -/
theorem cubic_spike_radius (x : Fin n ↪ F) {k Q B : ℕ}
    (hQ : 0 < Q) (hB : B = Fintype.card F / Q) (hpos : 6 ≤ B)
    (hroom : k + 2 * B ≤ n) (hcoord : 3 * k + 2 * B < 2 * n + 5)
    (hgap : k + 2 * B < n ∨ 3 ∣ B) :
    mcaDeltaStar (F := F) (ReedSolomon.code x k : Set (Fin n → F)) (1 / (Q : ℝ≥0∞)) =
      (B : ℝ≥0) / n := by
  classical
  let e := B - 1
  let d := n - k - 1
  have he : e + 1 = B := by dsimp [e]; omega
  have hthree : 3 ≤ d + 2 - 2 * e := by dsimp [d, e]; omega
  have hnum : 3 * (e / (d + 2 - 2 * e) + 1) ≤ B := by
    rcases hgap with hlt | hdiv
    · have hf : 4 ≤ d + 2 - 2 * e := by dsimp [d, e]; omega
      have hbound : e / (d + 2 - 2 * e) ≤ e / 4 := Nat.div_le_div_left hf (by decide)
      omega
    · have hbound : e / (d + 2 - 2 * e) ≤ e / 3 := Nat.div_le_div_left hthree (by decide)
      omega
  have hsafe : epsMCA (F := F) (ReedSolomon.code x k : Set (Fin n → F)) ((e : ℝ≥0) / n) ≤
      (1 / (Q : ℝ≥0∞)) := by
    by_cases hk : k = 0
    · subst k
      have hu := zero_dimension_upper x (e := e) (by dsimp [e]; omega)
      rw [he] at hu
      exact hu.trans ((BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos hQ).mpr hB.le)
    have hkpos : 1 ≤ k := by omega
    refine (epsMCA_le_of_badCount_le _ _ B (fun W => ?_)).trans ?_
    · have h := CubicApolarExtremum.count_bound x k e d
        (by dsimp [e, d]; omega) (by dsimp [e, d]; omega) hkpos
        (by rw [Fintype.card_fin]; dsimp [d]; omega)
        (by rw [Fintype.card_fin]; dsimp [d, e]; omega) (W 0) (W 1)
      rw [Fintype.card_fin] at h
      exact h.trans (max_le he.le hnum)
    · exact (BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos hQ).mpr hB.le
  apply le_antisymm
  · apply mcaDeltaStar_le_of_bad _ _
    refine lt_of_lt_of_le ?_ (LinearFieldBudgetRadius.spike x (k := k) (e := B) (by omega))
    apply lt_of_not_ge
    rw [BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos hQ, ← hB]
    omega
  · exact latticeBoundary_le_mcaDeltaStar_of_predecessor_good (by omega)
      (by omega : B ≤ n) _ _ hsafe

/-- At length four times the budget, divisibility by three makes the
half-rate cubic count fit exactly at the predecessor. -/
theorem rate_half_of_three_dvd (x : Fin n ↪ F) {Q B : ℕ} (hQ : 0 < Q)
    (hB : B = Fintype.card F / Q) (hpos : 6 ≤ B) (hn : n = 4 * B) (hdiv : 3 ∣ B) :
    mcaDeltaStar (F := F) (ReedSolomon.code x (2 * B) : Set (Fin n → F)) (1 / (Q : ℝ≥0∞)) =
      (B : ℝ≥0) / n := by
  exact cubic_spike_radius x hQ hB hpos (by omega) (by omega) (Or.inr hdiv)

/-- At the two budgets bordering a quarter of the production length, this
applies through dimension 536870911 and 536870909 respectively on any
prescribed domain, over any finite field of the given budget. -/
theorem production_radius (x : Fin (2 ^ 30) ↪ F) {k B : ℕ}
    (hB : B = Fintype.card F / 2 ^ 128)
    (hcase : (B = 268435456 ∧ k ≤ 536870911) ∨ (B = 268435457 ∧ k ≤ 536870909)) :
    mcaDeltaStar (F := F) (ReedSolomon.code x k : Set (Fin (2 ^ 30) → F))
      (1 / ((2 ^ 128 : ℕ) : ℝ≥0∞)) =
      (B : ℝ≥0) / ((2 ^ 30 : ℕ) : ℝ≥0) := by
  apply cubic_spike_radius x (by decide) hB <;> rcases hcase with ⟨rfl, hb⟩ | ⟨rfl, hb⟩ <;> omega

/-- All positive widths pass the sponsor's MCA budget exactly below the
displayed first failing radius, including real radii between Hamming steps. -/
theorem production_interleaved_good_iff (x : Fin (2 ^ 30) ↪ F) {k B : ℕ}
    (hB : B = Fintype.card F / 2 ^ 128)
    (hcase : (B = 268435456 ∧ k ≤ 536870911) ∨ (B = 268435457 ∧ k ≤ 536870909))
    (width : ℕ) [NeZero width] (δ : ℝ≥0) :
    epsMCA (F := F) (A := Fin width → F)
      ((ReedSolomon.code x k : Set (Fin (2 ^ 30) → F)) ^⋈ (Fin width)) δ ≤ (epsStar : ℝ≥0∞) ↔
      δ < (B : ℝ≥0) / ((2 ^ 30 : ℕ) : ℝ≥0) := by
  rw [epsMCA_interleaved_eq, epsStar_coe_eq_natCast_inv, ← one_div]
  have h := production_radius x hB hcase
  have hlt : mcaDeltaStar (F := F) (ReedSolomon.code x k : Set (Fin (2 ^ 30) → F))
      (1 / ((2 ^ 128 : ℕ) : ℝ≥0∞)) < 1 := by
    rw [h, div_lt_one (by positivity)]
    exact_mod_cast (show B < (2 ^ 30 : ℕ) by omega)
  rw [← h]
  constructor
  · intro good
    by_contra! hb
    exact (MCAStepFunction.lt_epsMCA_mcaDeltaStar_of_lt_one _ _ hlt).not_ge
      ((epsMCA_mono _ hb).trans good)
  · intro l
    by_contra! hb
    exact l.not_ge (mcaDeltaStar_le_of_bad _ _ hb)

end ArkLib.ProximityGap.Frontier.CubicSpikeBudgetBoundary

#print axioms ArkLib.ProximityGap.Frontier.CubicSpikeBudgetBoundary.cubic_spike_radius
#print axioms ArkLib.ProximityGap.Frontier.CubicSpikeBudgetBoundary.production_interleaved_good_iff
