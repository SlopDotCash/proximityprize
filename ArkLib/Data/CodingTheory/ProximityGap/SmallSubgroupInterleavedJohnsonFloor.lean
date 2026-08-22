/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EpsMCAInterleavedJohnson
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSMinDistance
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# The interleaved-Johnson good-side floor for small-subgroup RS codes (#389)

`SmallSubgroupUncondQuarter.lean` proves the fully unconditional quarter-window lower
bound on `δ*`, using unique decoding of the two-row interleaved code.  The next
q-independent producer in the same dictionary is the Johnson list bound for that
interleaved code, proved in `EpsMCAInterleavedJohnson.lean`.

This file performs the missing ledger splice for Reed-Solomon codes:

* `rsCode_epsMCA_le_interleavedJohnson` specializes the pair-alphabet Johnson cap to
  `rsCodeFinset dom k`, using local `PairClosed` and RS agreement lemmas.
* `rsCode_deltaStar_ge_interleavedJohnson` converts that `ε_mca` bound into a
  good-side `δ ≤ δ*` statement.
* the `_of_sqrt_window` forms expose the clean real condition
  `2δ + sqrt((k - 1)/n) < 1`.

Honest scope: because the MCA dictionary queries the two-row interleaved list at the
doubled radius, this reaches the **half-Johnson** window
`δ < (1 - sqrt((k - 1)/n))/2`, not the full Johnson radius of the base RS code.
Pushing from here to full Johnson requires a sharper dictionary or an all-pairs list
input beyond what the ordinary Johnson bound supplies.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.SmallSubgroupInterleavedJohnsonFloor

open ProximityGap ProximityGap.MCAThresholdLedger
open ArkLib.CS25

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## Local RS support lemmas -/

/-- Every RS-code Finset is `PairClosed`: the pair-extraction combinations are linear
combinations of codewords in the RS submodule.  This is kept local to avoid importing the
heavier quarter-window wrapper just for this small support fact. -/
theorem pairClosed_rsCodeFinset (dom : Fin n ↪ F) (k : ℕ) :
    Round17CAPair.PairClosed (rsCodeFinset dom k) := by
  classical
  intro c hc c' hc' γ γ' _
  rw [mem_rsCodeFinset] at hc hc'
  have hsub : (γ - γ')⁻¹ • (c - c') ∈ ReedSolomon.code dom k :=
    Submodule.smul_mem _ _ (Submodule.sub_mem _ hc hc')
  have hsub2 : c - γ • ((γ - γ')⁻¹ • (c - c'))
      ∈ ReedSolomon.code dom k :=
    Submodule.sub_mem _ hc (Submodule.smul_mem _ _ hsub)
  refine ⟨?_, ?_⟩
  · rw [mem_rsCodeFinset]
    exact hsub
  · rw [mem_rsCodeFinset]
    exact hsub2

/-- RS-code Finset pairwise agreement in the `filter (g₁ = g₂)` shape consumed by the
interleaved Johnson splice. -/
theorem rsCodeFinset_agree_le (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) :
    ∀ g₁ ∈ rsCodeFinset dom k, ∀ g₂ ∈ rsCodeFinset dom k, g₁ ≠ g₂ →
      (Finset.univ.filter (fun x => g₁ x = g₂ x)).card ≤ k - 1 := by
  classical
  intro g₁ hg₁ g₂ hg₂ hne
  haveI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hdist := rsCodeFinset_hammingDist_ge dom k g₁ g₂ hg₁ hg₂ hne
  have hagree := ArkLib.JohnsonList.agree_card_le_card_sub_of_hammingDist_ge
    (c := g₁) (c' := g₂) hdist
  exact le_trans hagree (by omega)

/-- **RS specialization of the interleaved Johnson `ε_mca` bound.**  For
`rsCodeFinset dom k`, the pair-alphabet Johnson bound gives the q-independent list
cap with agreement parameter `e = k - 1`, hence the usual dictionary numerator

`1 + (n - a) * n^2 / (a^2 - n*(k-1))`, where
`a = 2*ceil((1 - δ)n) - n`.

This is unconditional for every RS evaluation domain; the only radius hypothesis is
the natural Johnson gap for the two-row interleaved list. -/
theorem rsCode_epsMCA_le_interleavedJohnson (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hgap : Fintype.card (Fin n) * (k - 1) <
      (2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ -
        Fintype.card (Fin n)) ^ 2) :
    ProximityGap.epsMCA (F := F) (A := F)
        (↑(rsCodeFinset dom k) : Set (Fin n → F)) δ ≤
      ((1 + (Fintype.card (Fin n) -
          (2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ -
            Fintype.card (Fin n))) *
          (Fintype.card (Fin n) ^ 2 /
            ((2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ -
                Fintype.card (Fin n)) ^ 2 -
              Fintype.card (Fin n) * (k - 1))) : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) :=
  ProximityGap.epsMCA_le_interleavedJohnson (rsCodeFinset dom k)
    (pairClosed_rsCodeFinset dom k) δ (k - 1)
    (rsCodeFinset_agree_le dom hk) hgap

/-- **RS specialization on the named half-Johnson window.**  The clean real condition
`2δ + sqrt((k - 1)/n) < 1` implies the natural Johnson gap for the collapse floor,
so the interleaved Johnson `ε_mca` bound applies directly. -/
theorem rsCode_epsMCA_le_interleavedJohnson_of_sqrt_window
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hδ : 2 * δ + NNReal.sqrt (((k - 1 : ℕ) : ℝ≥0) / Fintype.card (Fin n)) < 1) :
    ProximityGap.epsMCA (F := F) (A := F)
        (↑(rsCodeFinset dom k) : Set (Fin n → F)) δ ≤
      ((1 + (Fintype.card (Fin n) -
          (2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ -
            Fintype.card (Fin n))) *
          (Fintype.card (Fin n) ^ 2 /
            ((2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ -
                Fintype.card (Fin n)) ^ 2 -
              Fintype.card (Fin n) * (k - 1))) : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) :=
  ProximityGap.epsMCA_le_interleavedJohnson_of_sqrt_window (rsCodeFinset dom k)
    (pairClosed_rsCodeFinset dom k) δ (k - 1)
    (rsCodeFinset_agree_le dom hk) hδ

/-- **Good-side `δ*` lower bound from the interleaved Johnson gap.**  If the
Johnson-dictionary numerator clears the target budget, then the radius is good:
`δ ≤ mcaDeltaStar`. -/
theorem rsCode_deltaStar_ge_interleavedJohnson (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hgap : Fintype.card (Fin n) * (k - 1) <
      (2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ -
        Fintype.card (Fin n)) ^ 2)
    (εstar : ℝ≥0∞)
    (hbudget : ((1 + (Fintype.card (Fin n) -
          (2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ -
            Fintype.card (Fin n))) *
          (Fintype.card (Fin n) ^ 2 /
            ((2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ -
                Fintype.card (Fin n)) ^ 2 -
              Fintype.card (Fin n) * (k - 1))) : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := F) (A := F)
        (↑(rsCodeFinset dom k) : Set (Fin n → F)) εstar :=
  le_mcaDeltaStar_of_good _ _ hδ1
    (le_trans (rsCode_epsMCA_le_interleavedJohnson dom hk hgap) hbudget)

/-- **Good-side `δ*` lower bound on the named half-Johnson window.**  This is the
consumer-facing form: the real inequality
`2δ + sqrt((k - 1)/n) < 1` supplies the Johnson gap automatically. -/
theorem rsCode_deltaStar_ge_interleavedJohnson_of_sqrt_window
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hδ : 2 * δ + NNReal.sqrt (((k - 1 : ℕ) : ℝ≥0) / Fintype.card (Fin n)) < 1)
    (εstar : ℝ≥0∞)
    (hbudget : ((1 + (Fintype.card (Fin n) -
          (2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ -
            Fintype.card (Fin n))) *
          (Fintype.card (Fin n) ^ 2 /
            ((2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ -
                Fintype.card (Fin n)) ^ 2 -
              Fintype.card (Fin n) * (k - 1))) : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := F) (A := F)
        (↑(rsCodeFinset dom k) : Set (Fin n → F)) εstar :=
  le_mcaDeltaStar_of_good _ _ hδ1
    (le_trans (rsCode_epsMCA_le_interleavedJohnson_of_sqrt_window dom hk hδ) hbudget)

/-- **Small-subgroup specialization of the interleaved-Johnson good-side floor.** -/
theorem smallSubgroup_deltaStar_ge_interleavedJohnson {p : ℕ} [Fact p.Prime]
    (dom : Fin n ↪ ZMod p) {k : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hgap : Fintype.card (Fin n) * (k - 1) <
      (2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ -
        Fintype.card (Fin n)) ^ 2)
    (εstar : ℝ≥0∞)
    (hbudget : ((1 + (Fintype.card (Fin n) -
          (2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ -
            Fintype.card (Fin n))) *
          (Fintype.card (Fin n) ^ 2 /
            ((2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ -
                Fintype.card (Fin n)) ^ 2 -
              Fintype.card (Fin n) * (k - 1))) : ℕ) : ℝ≥0∞)
        / (Fintype.card (ZMod p) : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (↑(rsCodeFinset dom k) : Set (Fin n → ZMod p)) εstar :=
  rsCode_deltaStar_ge_interleavedJohnson dom hk hδ1 hgap εstar hbudget

/-- **Small-subgroup specialization on the named half-Johnson window.** -/
theorem smallSubgroup_deltaStar_ge_interleavedJohnson_of_sqrt_window
    {p : ℕ} [Fact p.Prime] (dom : Fin n ↪ ZMod p) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hδ : 2 * δ + NNReal.sqrt (((k - 1 : ℕ) : ℝ≥0) / Fintype.card (Fin n)) < 1)
    (εstar : ℝ≥0∞)
    (hbudget : ((1 + (Fintype.card (Fin n) -
          (2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ -
            Fintype.card (Fin n))) *
          (Fintype.card (Fin n) ^ 2 /
            ((2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ -
                Fintype.card (Fin n)) ^ 2 -
              Fintype.card (Fin n) * (k - 1))) : ℕ) : ℝ≥0∞)
        / (Fintype.card (ZMod p) : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (↑(rsCodeFinset dom k) : Set (Fin n → ZMod p)) εstar :=
  rsCode_deltaStar_ge_interleavedJohnson_of_sqrt_window dom hk hδ1 hδ εstar hbudget

end ArkLib.ProximityGap.SmallSubgroupInterleavedJohnsonFloor

/-! ## Source audit -/
#print axioms ArkLib.ProximityGap.SmallSubgroupInterleavedJohnsonFloor.rsCode_epsMCA_le_interleavedJohnson
#print axioms ArkLib.ProximityGap.SmallSubgroupInterleavedJohnsonFloor.rsCode_epsMCA_le_interleavedJohnson_of_sqrt_window
#print axioms ArkLib.ProximityGap.SmallSubgroupInterleavedJohnsonFloor.rsCode_deltaStar_ge_interleavedJohnson
#print axioms ArkLib.ProximityGap.SmallSubgroupInterleavedJohnsonFloor.rsCode_deltaStar_ge_interleavedJohnson_of_sqrt_window
#print axioms ArkLib.ProximityGap.SmallSubgroupInterleavedJohnsonFloor.smallSubgroup_deltaStar_ge_interleavedJohnson
#print axioms ArkLib.ProximityGap.SmallSubgroupInterleavedJohnsonFloor.smallSubgroup_deltaStar_ge_interleavedJohnson_of_sqrt_window
