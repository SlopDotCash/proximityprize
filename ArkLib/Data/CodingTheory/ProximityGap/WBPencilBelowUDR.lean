/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilRationalReduction

/-!
# The below-UDR law from named rational-window residuals (#371, the WB capstone)

The WB programme's original conditional capstone used `WindowRationalBounded`, the
claim that every doubly-WB-solvable stack has bad-scalar count ≤ `w + 3`.  That
residual is now **refuted** by the normalizer-pair family at high rate (see
`DISPROOF_LOG.md` and `probe_normalizer_pair_family.py`).  We keep the old
conditional theorem below as a historical consumer of the false residual.

**`epsMCA_le_below_udr`** — under the Prop, for every radius `δ ≤ w/n` with
`w + k ≤ n`:  `ε_mca(RS, δ) ≤ (w+3)/q`.

At production shape this is `≤ (w+3)/q ≪ 2^{−128}` for every below-UDR radius —
the unconditional-modulo-one-Prop extension of the production floor from the ladder
reach `(1−ρ)/3` to the unique-decoding radius `(1−ρ)/2`.

**Count-residual fallback.**  `WindowRationalLinearBounded` asks for the
rational-window bad count to be at most `n`.  Together with the already-proven
WB-far side (`≤ w+3`) this gives the legacy conditional mass

  `ε_mca(RS, δ) ≤ max n (w+3) / q`.

The repaired capstone lives in `WBPencilLinearBudget.lean`, where
`WindowRationalLinear` proves the sharper canonical `ε_mca ≤ n/q` theorem.  The
linear wrapper here is kept only as a legacy direct-count consumer and therefore
uses noncanonical `_linear_fallback` theorem names.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **Historical residual, now refuted.**  This claims every doubly-WB-solvable
stack has at most `w + 3` bad scalars.  The normalizer-pair family refutes this
at high rate, so new consumers should use `WindowRationalLinear` in
`WBPencilLinearBudget.lean` instead. -/
def WindowRationalBounded (dom : Fin n ↪ F) (k w : ℕ) (δ : ℝ≥0) : Prop :=
  ∀ u₀ u₁ : Fin n → F, WBSolvable dom k w u₀ → WBSolvable dom k w u₁ →
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ w + 3

open Classical in
/-- **Count-residual fallback after the normalizer-pair refutation**:
every doubly-WB-solvable stack has linearly many bad scalars, bounded by `n`.
The refuting normalizer-pair family has `(n - 2) / 2` bad scalars, so a constant
bound is false but this linear target is still compatible with the evidence.
The canonical linear-budget capstone is `WindowRationalLinear` in
`WBPencilLinearBudget.lean`; this legacy fallback deliberately has different
theorem names to avoid exporting duplicate declarations. -/
def WindowRationalLinearBounded (dom : Fin n ↪ F) (k w : ℕ) (δ : ℝ≥0) : Prop :=
  ∀ u₀ u₁ : Fin n → F, WBSolvable dom k w u₀ → WBSolvable dom k w u₁ →
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ n

open Classical in
/-- **THE BELOW-UDR LAW** (conditional on exactly `WindowRationalBounded`): at every
radius `δ ≤ w/n` below the unique-decoding slack,
`ε_mca(RS, δ) ≤ (w+3)/q`. -/
theorem epsMCA_le_below_udr (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    (hwk : w + k ≤ n) {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (hwin : WindowRationalBounded dom k w δ) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ ((w + 3 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  rw [epsMCA]
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  refine ENNReal.div_le_div_right ?_ _
  by_cases h1 : WBSolvable dom k w (u 1)
  · by_cases h0 : WBSolvable dom k w (u 0)
    · -- doubly rational: the named residual
      exact_mod_cast hwin (u 0) (u 1) h0 h1
    · -- offset row far: swap + pencil
      have hswap := badScalars_card_swap_le
        (rsCode dom k : Submodule F (Fin n → F)) δ (u 0) (u 1)
      have hfar := badScalars_card_le_of_far_snd dom hk hwk hδn
        (u₀ := u 1) (u₁ := u 0) h0
      exact_mod_cast le_trans hswap (by omega)
  · -- direction row far: pencil directly
    have := badScalars_card_le_of_far_snd dom hk hwk hδn
      (u₀ := u 0) (u₁ := u 1) h1
    exact_mod_cast le_trans this (by omega)

open Classical in
/-- The threshold form: under the named residual at every below-UDR radius, the
threshold clears UDR-minus-one-band: `δ* ≥ δ` for every `δ ≤ w/n` with
`(w+3)/q ≤ ε*`.  At production (`ε* = 2^{−128}`, `q ≥ (w+3)·2^{128}`) this moves
the floor to the unique-decoding radius. -/
theorem le_mcaDeltaStar_below_udr (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    (hwk : w + k ≤ n) {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (hwin : WindowRationalBounded dom k w δ)
    {εstar : ℝ≥0∞}
    (hbudget : ((w + 3 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar :=
  ProximityGap.MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ hδ1
    (le_trans (epsMCA_le_below_udr dom hk hwk hδn hwin) hbudget)

open Classical in
/-- **Count-residual conditional below-UDR law after the refutation of
`WindowRationalBounded`.**  If the doubly-WB-solvable rational-window part has
at most `n` bad scalars, then all stacks have bad count bounded by
`max n (w+3)`, because the complementary WB-far branches are already proven to
cost at most `w+3`.  This is a generic fallback; the sharper canonical linear
consumer is `epsMCA_le_below_udr_linear` in `WBPencilLinearBudget.lean`. -/
theorem epsMCA_le_below_udr_linear_fallback (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    (hwk : w + k ≤ n) {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (hwin : WindowRationalLinearBounded dom k w δ) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ ((max n (w + 3) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  rw [epsMCA]
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  refine ENNReal.div_le_div_right ?_ _
  by_cases h1 : WBSolvable dom k w (u 1)
  · by_cases h0 : WBSolvable dom k w (u 0)
    · -- doubly rational: the corrected linear residual
      exact_mod_cast le_trans (hwin (u 0) (u 1) h0 h1) (Nat.le_max_left n (w + 3))
    · -- offset row far: swap + pencil
      have hswap := badScalars_card_swap_le
        (rsCode dom k : Submodule F (Fin n → F)) δ (u 0) (u 1)
      have hfar := badScalars_card_le_of_far_snd dom hk hwk hδn
        (u₀ := u 1) (u₁ := u 0) h0
      exact_mod_cast le_trans (le_trans hswap (by omega)) (Nat.le_max_right n (w + 3))
  · -- direction row far: pencil directly
    have := badScalars_card_le_of_far_snd dom hk hwk hδn
      (u₀ := u 0) (u₁ := u 1) h1
    exact_mod_cast le_trans (le_trans this (by omega)) (Nat.le_max_right n (w + 3))

open Classical in
/-- Threshold form of the count-residual fallback.  The canonical repaired
threshold theorem is `le_mcaDeltaStar_below_udr_linear` in
`WBPencilLinearBudget.lean`; this theorem records the older `max n (w+3)`
fallback under a noncanonical name. -/
theorem le_mcaDeltaStar_below_udr_linear_fallback (dom : Fin n ↪ F) {k w : ℕ}
    (hk : 1 ≤ k)
    (hwk : w + k ≤ n) {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (hwin : WindowRationalLinearBounded dom k w δ)
    {εstar : ℝ≥0∞}
    (hbudget : ((max n (w + 3) : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar :=
  ProximityGap.MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ hδ1
    (le_trans (epsMCA_le_below_udr_linear_fallback dom hk hwk hδn hwin) hbudget)

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.epsMCA_le_below_udr
#print axioms ProximityGap.WBPencil.le_mcaDeltaStar_below_udr
#print axioms ProximityGap.WBPencil.epsMCA_le_below_udr_linear_fallback
#print axioms ProximityGap.WBPencil.le_mcaDeltaStar_below_udr_linear_fallback
