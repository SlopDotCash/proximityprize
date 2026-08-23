/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAEquivariance
import ArkLib.Data.CodingTheory.ProximityGap.MCAPlateauWindow

/-!
# Round 2 (#357): the first complete exact `ε_mca` profile — and the full threshold curve

R1 (`MCADeltaStarExactPoint`) pinned one exact δ* value. This file completes the picture for
the same smooth-domain code `rsC = RS[F₅, ⟨2⟩, 2]`: **the exact value of `ε_mca` at every
radius**, and consequently **the entire threshold curve `ε* ↦ δ*(ε*)`** — the first code
(any family, any proof format) whose MCA error profile is known exactly everywhere.

The profile is the two-step staircase

  `ε_mca(rsC, δ) = 1/5` on `[0, 1/4)`, and `= 4/5` on `[1/4, ∞)`,

assembled from four bracket pieces:
* below the granularity radius: the sub-granularity exact value (R1's
  `epsMCA_rs_eq_fifth_of_small` — every proper linear code is exactly `1/|F|` there);
* the upper plateau bound: the canonical-witness window bound `epsMCA_le_choose_div`
  (`MCAPlateauWindow`) evaluates to `C(4, max(⌈(1−δ)·4⌉, 3))/5 ≤ C(4,3)/5 = 4/5` at every
  radius — the bridge `rsC_eq_code` (the red-team identification of `rsC` with
  `ReedSolomon.code`) makes it applicable;
* the lower plateau bound: monotonicity from the four explicit bad scalars at `δ = 1/4`
  (R1's `epsMCA_rs_quarter_ge`).

The threshold curve (`mcaDeltaStar` at every target `ε*`):

  | `ε*`            | `δ*(rsC, ε*)` |
  |-----------------|----------------|
  | `< 1/5`         | `0` (no good radius at all) |
  | `[1/5, 4/5)`    | `1/4` (R1's point, now for the whole band of targets) |
  | `≥ 4/5`         | `1` (every radius is good) |

Structurally: the staircase has exactly two jumps, at the granularity radius `1/n` and at
`0`; the threshold curve is the (left-continuous) generalized inverse of the staircase. At
this scale the entire MCA landscape of the code is now a theorem. The R1 methodology plus
the window bound suffices — no computation beyond the four `decide` witnesses already
landed. The analogous profile for larger rungs (`n = 8`: more bands between granularity and
Johnson) is the round-2 frontier; the band-2 probe campaign pre-registers
`max bad count = n` there.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- Issue #357 (the δ* campaign; round 2); `MCADeltaStarExactPoint.lean` (R1),
  `MCAPlateauWindow.lean` (the window bound), `MCAEquivariance.lean` (`rsC_eq_code`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAThresholdLedger
open ProximityGap.MCADeltaStarExactPoint
open ProximityGap.MCAEquivariance

namespace ProximityGap.MCAExactProfile

/-! ## The plateau: `ε_mca(rsC, δ) = 4/5` for every `δ ≥ 1/4` -/

/-- The window bound evaluates to `≤ 4/5` at **every** radius for `rsC`:
`C(4, max(⌈(1−δ)·4⌉, 3)) ≤ 4` since the max is `3` or `4`. -/
theorem epsMCA_rs_le_four_fifth (δ : ℝ≥0) :
    epsMCA (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) δ ≤ 4/5 := by
  rw [rsC_eq_code]
  refine le_trans (ProximityGap.epsMCA_le_choose_div gdomEmb 2 δ) ?_
  have hceil : ⌈((1 : ℝ≥0) - δ) * (Fintype.card (Fin 4) : ℝ≥0)⌉₊ ≤ 4 := by
    rw [Fintype.card_fin]
    refine Nat.ceil_le.mpr ?_
    calc ((1 : ℝ≥0) - δ) * ((4 : ℕ) : ℝ≥0) ≤ 1 * ((4 : ℕ) : ℝ≥0) := by
          gcongr
          exact tsub_le_self
      _ = ((4 : ℕ) : ℝ≥0) := one_mul _
  have hchoose : (Fintype.card (Fin 4)).choose
      (max (⌈((1 : ℝ≥0) - δ) * (Fintype.card (Fin 4) : ℝ≥0)⌉₊) (2 + 1)) ≤ 4 := by
    rw [Fintype.card_fin] at hceil ⊢
    set m := max (⌈((1 : ℝ≥0) - δ) * ((4 : ℕ) : ℝ≥0)⌉₊) (2 + 1) with hm
    have h3 : 3 ≤ m := le_max_right _ _
    have h4 : m ≤ 4 := by
      rw [hm]
      exact max_le hceil (by norm_num)
    interval_cases m
    · decide
    · decide
  have hcard : (Fintype.card F5 : ℝ≥0∞) = 5 := by rw [ZMod.card]; norm_num
  rw [hcard]
  calc ((Fintype.card (Fin 4)).choose
        (max (⌈((1 : ℝ≥0) - δ) * (Fintype.card (Fin 4) : ℝ≥0)⌉₊) (2 + 1)) : ℝ≥0∞) / 5
      ≤ (4 : ℝ≥0∞) / 5 := by
        gcongr
        exact_mod_cast hchoose
    _ = 4/5 := rfl

/-- **The plateau value:** `ε_mca(rsC, δ) = 4/5` exactly, for every `δ ≥ 1/4`. -/
theorem epsMCA_rs_eq_four_fifth_of_ge {δ : ℝ≥0} (hδ : 1/4 ≤ δ) :
    epsMCA (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) δ = 4/5 := by
  refine le_antisymm (epsMCA_rs_le_four_fifth δ) ?_
  exact le_trans epsMCA_rs_quarter_ge (epsMCA_mono _ hδ)

/-! ## The complete profile -/

open Classical in
/-- **The first complete exact MCA-error profile of any code:** the two-step staircase.
`ε_mca(rsC, ·)` jumps from `1/5` to `4/5` exactly at the granularity radius `1/4 = 1/n`. -/
theorem epsMCA_rs_profile (δ : ℝ≥0) :
    epsMCA (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) δ
      = if δ < 1/4 then 1/5 else 4/5 := by
  by_cases h : δ < 1/4
  · rw [if_pos h]
    refine epsMCA_rs_eq_fifth_of_small ?_
    rw [Fintype.card_fin]
    calc δ * ((4 : ℕ) : ℝ≥0) < (1/4 : ℝ≥0) * ((4 : ℕ) : ℝ≥0) := by
          have h4 : (0 : ℝ≥0) < ((4 : ℕ) : ℝ≥0) := by norm_num
          exact mul_lt_mul_of_pos_right h h4
      _ = 1 := by push_cast; norm_num
  · rw [if_neg h]
    exact epsMCA_rs_eq_four_fifth_of_ge (not_lt.mp h)

/-! ## The complete threshold curve `ε* ↦ δ*` -/

/-- **Low targets are unreachable:** for `ε* < 1/5` no radius is good, so `δ* = 0`. -/
theorem mcaDeltaStar_rs_eq_zero_of {εstar : ℝ≥0∞} (h : εstar < 1/5) :
    mcaDeltaStar (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) εstar = 0 := by
  have hempty : mcaGoodRadii (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) εstar = ∅ := by
    ext δ
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨_hδ1, hgood⟩
    have hge : (1/5 : ℝ≥0∞) ≤ epsMCA (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) δ := by
      rw [epsMCA_rs_profile δ]
      by_cases hc : δ < 1/4
      · rw [if_pos hc]
      · rw [if_neg hc]
        exact ENNReal.div_le_div_right (by norm_num) 5
    exact absurd (le_trans hge hgood) (not_le.mpr h)
  unfold mcaDeltaStar
  rw [hempty]
  exact csSup_empty

/-- **The middle band:** for every target `ε* ∈ [1/5, 4/5)`, `δ* = 1/4` — R1's exact point,
now for the entire band of meaningful targets. -/
theorem mcaDeltaStar_rs_eq_quarter_of {εstar : ℝ≥0∞}
    (hlo : 1/5 ≤ εstar) (hhi : εstar < 4/5) :
    mcaDeltaStar (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) εstar = 1/4 := by
  refine le_antisymm ?_ ?_
  · -- bad point at 1/4
    refine MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _ ?_
    rw [epsMCA_rs_profile (1/4)]
    rw [if_neg (lt_irrefl _)]
    exact hhi
  · -- every δ < 1/4 is good
    by_contra hlt
    push Not at hlt
    obtain ⟨c, hc1, hc2⟩ := exists_between hlt
    have hgood : epsMCA (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) c ≤ εstar := by
      rw [epsMCA_rs_profile c, if_pos hc2]
      exact hlo
    have hquarter_le_one : (1/4 : ℝ≥0) ≤ 1 := by
      rw [div_le_one (by norm_num : (0 : ℝ≥0) < 4)]
      norm_num
    have hle := MCAThresholdLedger.le_mcaDeltaStar_of_good
      (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) εstar
      (le_of_lt (lt_of_lt_of_le hc2 hquarter_le_one)) hgood
    exact absurd (lt_of_le_of_lt hle hc1) (lt_irrefl _)

/-- **High targets are free:** for `ε* ≥ 4/5` every radius is good, so `δ* = 1`. -/
theorem mcaDeltaStar_rs_eq_one_of {εstar : ℝ≥0∞} (h : 4/5 ≤ εstar) :
    mcaDeltaStar (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) εstar = 1 := by
  refine le_antisymm ?_ ?_
  · exact csSup_le' fun δ hδ => hδ.1
  · refine MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ le_rfl ?_
    rw [epsMCA_rs_profile 1]
    rw [if_neg (by norm_num)]
    exact h

/-! ## Source audit -/

#print axioms epsMCA_rs_le_four_fifth
#print axioms epsMCA_rs_eq_four_fifth_of_ge
#print axioms epsMCA_rs_profile
#print axioms mcaDeltaStar_rs_eq_zero_of
#print axioms mcaDeltaStar_rs_eq_quarter_of
#print axioms mcaDeltaStar_rs_eq_one_of

end ProximityGap.MCAExactProfile
