/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonSplitSupply
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._W15SafeBranchLinearCeiling

/-!
# LANE W15 part 3 (#466, thread ll:low-profile-fiber): THE NEAR-CODE JOHNSON BUDGET —
# discharging `LargeZeroSafeLineListBudgeted` by collapsing the line onto its offset

## Position in the lane

`_W15SafeBranchLinearCeiling.lean` reduced the weld's safe large-zero `mcaEvent` branch to
one open input, the near-code line-list budget `LargeZeroSafeLineListBudgeted dom k a L`,
with the two-sided bracket `n − a ≤ B_near ≤ L·(n − a)`.  This file discharges that budget
from the in-tree Johnson substrate in two regimes.

## The mechanism: the offset collapse

On a large-zero line (`z := |Z| ≥ a` zero coordinates of the direction), EVERY line word
`u₀ + γ·u₁` coincides with the single word `u₀` on all of `Z`.  An appearing codeword `c`
(agreement `≥ a` with some line word) therefore agrees with `u₀` on
`≥ a − (n − z) ≥ 2a − n` coordinates: the whole union-over-`γ` line list injects into ONE
per-word agreement list of `u₀` at the reduced threshold `2a − n`.  The in-tree Johnson
bound (`rsCode_agreement_list_card_le`) and the RS pairwise-intersection pigeonhole then
give:

1. `largeZero_lineAppearing_subset_offset_list` / `nearCodeList_of_doubled_johnson_margin`
   — **the general budget**: `L = n² / ((2a − n)² − n(k − 1))` whenever
   `n(k − 1) < (2a − n)²` (the "doubled-Johnson margin": `2a − n` above the per-word
   Johnson agreement line).
2. `nearCodeList_one_of_two_n_add_k_le_three_a` — **`L = 1`** whenever `2n + k ≤ 3a`
   (unique-decoding-plus): two distinct appearing codewords would carry two
   `(a − (n − z))`-sized agreement-with-`u₀` sets inside `Z` overlapping in `≤ k − 1`
   points, and `2(a − (n − z)) − (k − 1) > z` counts them out.
3. `mcaDeltaStar_ge_with_safe_branch_discharged` — **the composed weld corollary**: in the
   `L = 1` regime the safe large-zero branch of
   `mcaDeltaStar_ge_of_farLineList_and_nearCodeList` is DISCHARGED OUTRIGHT (its slot
   becomes the unconditional `n − a`); the remaining named residuals are exactly `hfarL`
   (far-line lists — still open, NOT claimed) and `hunsafe` (unsafe large-zero branch).

Neither theorem needs `ZeroDirectionSafeLine` — large-zero alone suffices; safety is kept
only to match the residual's interface.

## Honesty — the uncovered window

* The campaign rate-quarter shape (`n = 16, k = 4, a = 9`) satisfies NEITHER regime:
  `(2a − n)² = 4 < 48 = n(k − 1)` and `3a = 27 < 36 = 2n + k`
  (`campaign_shape_not_covered`).  There the probe
  (`probe_466_w15_multibase_ladder.py`) certifies `Λ = 1` empirically, but the proof must
  use the SUPPORT-side agreements that the offset collapse discards — the window between
  the Johnson line (`a² > nk`) and the doubled-Johnson margin is the remaining open
  content of `LargeZeroSafeLineListBudgeted`, left as the honest named residual it already
  is.  Nothing open is silently discharged.
* Non-vacuity: at `n = 16, k = 4, a = 12` both regimes hold (`L = 1`, and the general
  form gives `L = 16`); gates below.
* Asymptotically the margin reads `α > (1 + √ρ)/2` (`a = αn`, `k = ρn`) versus Johnson
  `α > √ρ`: the discharge is real but sits above unique decoding at low rates.

NO `sorry`, NO `axiom`, NO `native_decide`; axiom audit must show
`[propext, Classical.choice, Quot.sound]`.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Frontier.W15NearCodeJohnsonBudget

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ProximityGap.LineListMCAWeld ProximityGap.FarCosetExplosion
open ProximityGap.Frontier.W15SafeBranchLinearCeiling

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The offset collapse.**  On a large-zero line (`a ≤ z = |Z|`), every appearing
codeword agrees with the OFFSET `u₀` on at least `2a − n` coordinates: its `≥ a`
line-agreement set loses at most `n − z ≤ n − a` support coordinates, and on `Z` the line
word IS `u₀`. -/
theorem largeZero_appearing_agrees_offset
    (dom : Fin n ↪ F) (k a : ℕ) {u₀ u₁ : Fin n → F}
    (hz : a ≤ (directionZeroSet u₁).card)
    {c : Fin n → F} (hc : c ∈ lineAppearingCodewords dom k a u₀ u₁) :
    2 * a - n ≤ (agreeSet c u₀).card := by
  rw [lineAppearingCodewords, Finset.mem_filter] at hc
  obtain ⟨-, -, γ, hγ⟩ := hc
  set A := agreeSet c (fun i => u₀ i + γ • u₁ i) with hA
  -- A ∩ Z ⊆ agreeSet c u₀
  have hsub : A ∩ directionZeroSet u₁ ⊆ agreeSet c u₀ := by
    intro i hi
    obtain ⟨hiA, hiZ⟩ := Finset.mem_inter.mp hi
    rw [directionZeroSet, Finset.mem_filter] at hiZ
    rw [hA, agreeSet, Finset.mem_filter] at hiA
    rw [agreeSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have := hiA.2
    rw [hiZ.2] at this
    simpa using this
  -- |A ∩ Z| ≥ |A| − (n − z)
  have hsplit : A.card ≤ (A ∩ directionZeroSet u₁).card + (n - (directionZeroSet u₁).card) := by
    have h1 := Finset.card_inter_add_card_sdiff A (directionZeroSet u₁)
    have h2 : (A \ directionZeroSet u₁).card
        ≤ ((Finset.univ : Finset (Fin n)) \ directionZeroSet u₁).card :=
      Finset.card_le_card
        (Finset.sdiff_subset_sdiff (Finset.subset_univ _) Finset.Subset.rfl)
    have h3 : ((Finset.univ : Finset (Fin n)) \ directionZeroSet u₁).card
        = n - (directionZeroSet u₁).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin]
    omega
  have hcap := Finset.card_le_card hsub
  have hzn : (directionZeroSet u₁).card ≤ n := by
    have := Finset.card_le_card (Finset.subset_univ (directionZeroSet u₁))
    simpa [Finset.card_univ, Fintype.card_fin] using this
  omega

open Classical in
/-- The line list of a large-zero line injects into the offset's agreement list at the
reduced threshold `2a − n`. -/
theorem largeZero_lineAppearing_subset_offset_list
    (dom : Fin n ↪ F) (k a : ℕ) {u₀ u₁ : Fin n → F}
    (hz : a ≤ (directionZeroSet u₁).card) :
    lineAppearingCodewords dom k a u₀ u₁ ⊆
      (Finset.univ : Finset (Fin n → F)).filter
        (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
          ∧ 2 * a - n ≤ (agreeSet c u₀).card) := by
  intro c hc
  have hmem : c ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
    rw [lineAppearingCodewords, Finset.mem_filter] at hc
    exact hc.2.1
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hmem, largeZero_appearing_agrees_offset dom k a hz hc⟩

open Classical in
/-- **HEADLINE 1: the near-code list budget above the doubled-Johnson margin.**  Whenever
`n(k − 1) < (2a − n)²`, every zero-direction-safe large-zero line has at most
`n² / ((2a − n)² − n(k − 1))` appearing codewords: `LargeZeroSafeLineListBudgeted` HOLDS
at that explicit budget.  (Safety is not even needed — large-zero suffices.) -/
theorem nearCodeList_of_doubled_johnson_margin
    (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k)
    (hgap : n * (k - 1) < (2 * a - n) ^ 2) :
    LargeZeroSafeLineListBudgeted dom k a
      (n ^ 2 / ((2 * a - n) ^ 2 - n * (k - 1))) := by
  intro u₀ u₁ hne _hsafe
  have hz : a ≤ (directionZeroSet u₁).card := by
    rw [SupportEligibleLineDirection] at hne
    omega
  calc (lineAppearingCodewords dom k a u₀ u₁).card
      ≤ ((Finset.univ : Finset (Fin n → F)).filter
          (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
            ∧ 2 * a - n ≤ (agreeSet c u₀).card)).card :=
        Finset.card_le_card (largeZero_lineAppearing_subset_offset_list dom k a hz)
    _ ≤ n ^ 2 / ((2 * a - n) ^ 2 - n * (k - 1)) :=
        rsCode_agreement_list_card_le dom hk u₀ hgap

open Classical in
/-- **HEADLINE 2: `L = 1` in the unique-decoding-plus regime.**  Whenever `2n + k ≤ 3a`,
a large-zero line carries at most ONE appearing codeword: two distinct ones would place
two `(a − (n − z))`-sized agreement-with-`u₀` sets inside `Z` (`|Z| = z`) overlapping in
at most `k − 1` points, and `2(a − (n − z)) − (k − 1) > z` for every `z ≥ a`. -/
theorem nearCodeList_one_of_two_n_add_k_le_three_a
    (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k)
    (hreg : 2 * n + k ≤ 3 * a) :
    LargeZeroSafeLineListBudgeted dom k a 1 := by
  intro u₀ u₁ hne _hsafe
  have hz : a ≤ (directionZeroSet u₁).card := by
    rw [SupportEligibleLineDirection] at hne
    omega
  rw [LineListBudgeted]
  by_contra hgt
  push_neg at hgt
  obtain ⟨c, hc, c', hc', hcc⟩ := Finset.one_lt_card.mp hgt
  -- both agree with u₀ on ≥ a − (n − z) coordinates INSIDE Z
  have key : ∀ d ∈ lineAppearingCodewords dom k a u₀ u₁,
      a ≤ (agreeSet d u₀ ∩ directionZeroSet u₁).card + (n - (directionZeroSet u₁).card) := by
    intro d hd
    rw [lineAppearingCodewords, Finset.mem_filter] at hd
    obtain ⟨-, -, γ, hγ⟩ := hd
    set A := agreeSet d (fun i => u₀ i + γ • u₁ i) with hA
    have hsub : A ∩ directionZeroSet u₁ ⊆ agreeSet d u₀ ∩ directionZeroSet u₁ := by
      intro i hi
      obtain ⟨hiA, hiZ⟩ := Finset.mem_inter.mp hi
      have hiZ' := hiZ
      rw [directionZeroSet, Finset.mem_filter] at hiZ'
      rw [hA, agreeSet, Finset.mem_filter] at hiA
      refine Finset.mem_inter.mpr ⟨?_, hiZ⟩
      rw [agreeSet, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have := hiA.2
      rw [hiZ'.2] at this
      simpa using this
    have hsplit : A.card ≤ (A ∩ directionZeroSet u₁).card
        + (n - (directionZeroSet u₁).card) := by
      have h1 := Finset.card_inter_add_card_sdiff A (directionZeroSet u₁)
      have h2 : (A \ directionZeroSet u₁).card
          ≤ ((Finset.univ : Finset (Fin n)) \ directionZeroSet u₁).card :=
        Finset.card_le_card
          (Finset.sdiff_subset_sdiff (Finset.subset_univ _) Finset.Subset.rfl)
      have h3 : ((Finset.univ : Finset (Fin n)) \ directionZeroSet u₁).card
          = n - (directionZeroSet u₁).card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
          Fintype.card_fin]
      omega
    have := Finset.card_le_card hsub
    omega
  have hcZ := key c hc
  have hc'Z := key c' hc'
  -- the two Z-agreement sets overlap in ≤ k − 1 points (pairwise RS)
  have hcode : c ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
    rw [lineAppearingCodewords, Finset.mem_filter] at hc; exact hc.2.1
  have hcode' : c' ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
    rw [lineAppearingCodewords, Finset.mem_filter] at hc'; exact hc'.2.1
  have hpair : ((agreeSet c u₀ ∩ directionZeroSet u₁)
      ∩ (agreeSet c' u₀ ∩ directionZeroSet u₁)).card ≤ k - 1 := by
    refine le_trans (Finset.card_le_card ?_)
      (rsCode_pairwise_agreeSet_card_le dom hk hcode hcode' hcc)
    intro i hi
    obtain ⟨hi1, hi2⟩ := Finset.mem_inter.mp hi
    have e1 := (Finset.mem_filter.mp (Finset.mem_inter.mp hi1).1).2
    have e2 := (Finset.mem_filter.mp (Finset.mem_inter.mp hi2).1).2
    rw [agreeSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, e1.trans e2.symm⟩
  -- both sets live inside Z: union ≤ z; inclusion-exclusion closes the count
  have hunion : ((agreeSet c u₀ ∩ directionZeroSet u₁)
      ∪ (agreeSet c' u₀ ∩ directionZeroSet u₁)).card ≤ (directionZeroSet u₁).card := by
    refine Finset.card_le_card ?_
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · exact (Finset.mem_inter.mp h).2
    · exact (Finset.mem_inter.mp h).2
  have hie := Finset.card_union_add_card_inter
    (agreeSet c u₀ ∩ directionZeroSet u₁) (agreeSet c' u₀ ∩ directionZeroSet u₁)
  have hzn : (directionZeroSet u₁).card ≤ n := by
    have := Finset.card_le_card (Finset.subset_univ (directionZeroSet u₁))
    simpa [Finset.card_univ, Fintype.card_fin] using this
  omega

/-! ### The composed weld corollary -/

open Classical in
/-- **The composed consumer: the safe large-zero branch DISCHARGED.**  In the
unique-decoding-plus regime `2n + k ≤ 3a`, the weld holds with the safe branch's slot
filled unconditionally by `n − a` (`L_near = 1`); the ONLY remaining named residuals are
`hfarL` (the far-line list budget — still open, not claimed here) and `hunsafe` (the
unsafe large-zero branch `mcaEvent` budget). -/
theorem mcaDeltaStar_ge_with_safe_branch_discharged
    (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k) (δ : ℝ≥0) (εstar : ℝ≥0∞)
    {L Bfar Bunsafe : ℕ}
    (hreg : 2 * n + k ≤ 3 * a)
    (haC : (1 - δ) * (n : ℝ≥0) ≤ (a : ℝ≥0))
    (haF : ∀ m : ℕ, (1 - δ) * (n : ℝ≥0) ≤ (m : ℝ≥0) → a ≤ m)
    (hfarL : ∀ u₀ u₁ : Fin n → F,
      FarFromCode ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₁ →
        LineListBudgeted dom k a u₀ u₁ L)
    (hfit : ∀ z : ℕ, z < a → L * ((n - z) / (a - z)) ≤ Bfar)
    (hunsafe : ∀ u₀ u₁ : Fin n → F, ¬ ZeroDirectionSafeLine dom k a u₀ u₁ →
      (Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
        ≤ Bunsafe)
    (hBudget : ((max Bfar (max (n - a) Bunsafe) : ℕ) : ℝ≥0∞)
      / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hδ1 : δ ≤ 1) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar := by
  have h1 : (1 : ℕ) * (n - a) = n - a := one_mul _
  refine mcaDeltaStar_ge_of_farLineList_and_nearCodeList dom k a δ εstar
    (Lnear := 1) haC haF hfarL hfit
    (nearCodeList_one_of_two_n_add_k_le_three_a dom hk hreg) hunsafe ?_ hδ1
  rwa [h1]

/-! ### Numeric gates -/

/-- Non-vacuity: at `n = 16, k = 4, a = 12` both discharge regimes hold
(`3a = 36 ≥ 36 = 2n + k`, and `(2a − n)² = 64 > 48 = n(k−1)`, general budget `16`). -/
theorem discharge_regimes_nonvacuous :
    2 * 16 + 4 ≤ 3 * 12 ∧ 16 * (4 - 1) < (2 * 12 - 16) ^ 2 ∧
      (16 : ℕ) ^ 2 / ((2 * 12 - 16) ^ 2 - 16 * (4 - 1)) = 16 := by norm_num

/-- **Honesty: the campaign rate-quarter shape is NOT covered.**  At
`n = 16, k = 4, a = 9` (above Johnson: `a² = 81 > 64 = nk`) BOTH regimes fail:
`3a = 27 < 36 = 2n + k` and `(2a − n)² = 4 < 48 = n(k − 1)`.  There the probe certifies
`Λ = 1` empirically, but the proof must use the support-side agreements that the offset
collapse discards: the window between Johnson and the doubled-Johnson margin is the
remaining open content of `LargeZeroSafeLineListBudgeted`. -/
theorem campaign_shape_not_covered :
    (9 : ℕ) * 9 > 16 * 4 ∧ ¬ (2 * 16 + 4 ≤ 3 * 9) ∧
      ¬ (16 * (4 - 1) < (2 * 9 - 16) ^ 2) := by norm_num

end ProximityGap.Frontier.W15NearCodeJohnsonBudget

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.W15NearCodeJohnsonBudget.largeZero_appearing_agrees_offset
#print axioms ProximityGap.Frontier.W15NearCodeJohnsonBudget.largeZero_lineAppearing_subset_offset_list
#print axioms ProximityGap.Frontier.W15NearCodeJohnsonBudget.nearCodeList_of_doubled_johnson_margin
#print axioms ProximityGap.Frontier.W15NearCodeJohnsonBudget.nearCodeList_one_of_two_n_add_k_le_three_a
#print axioms ProximityGap.Frontier.W15NearCodeJohnsonBudget.mcaDeltaStar_ge_with_safe_branch_discharged
#print axioms ProximityGap.Frontier.W15NearCodeJohnsonBudget.discharge_regimes_nonvacuous
#print axioms ProximityGap.Frontier.W15NearCodeJohnsonBudget.campaign_shape_not_covered
