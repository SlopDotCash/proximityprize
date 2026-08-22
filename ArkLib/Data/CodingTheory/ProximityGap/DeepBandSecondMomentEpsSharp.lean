/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandFailureClosedFormSharp
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSecondMomentEps

/-!
# The sharp ε_mca / δ*-ledger surface (#389)

The delivery layer of `DeepBandSecondMomentEps.lean`, rebuilt on the SHARP budget
(deep term at `q^(M−(m+1))`), plus the closed-form ledger corollary composing the
whole sharp arc: at every band radius, with `Λ' := P/q^(m+1) + C'/q + 3`,

> **`deep_band_deltaStar_le_closed_form_sharp`** —
> `ε* < ((P·Λ'/q^m)/Λ'²)/q  ⟹  mcaDeltaStar(rsCode dom k, ε*) ≤ δ`,

no side conditions — the factor-`q`-sharper failure floor on the δ* surface.

Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

set_option linter.style.longLine false

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- The sharp `ε_mca` floor from the sharp numeric budget. -/
theorem deep_band_epsMCA_of_moments_sharp (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    {M : ℕ} (hM : 2 * (k + m + 1) ≤ M) {L V : ℕ}
    (hnum : ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card ^ 2 * (Fintype.card F) ^ (M - (2 * m + 1))
        + (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card) * (Fintype.card F) ^ (M - (m + 1))
        + ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card * (Fintype.card F) ^ (M - m)
        + V * (Fintype.card F) ^ M
      ≤ 2 * L * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card * (Fintype.card F) ^ (M - m))) :
    ∃ Q₀ : F[X],
      ((V / L ^ 2 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
        ≤ epsMCA (F := F) (A := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ := by
  obtain ⟨Q₀, hV⟩ := deep_band_badSet_card_of_moments_sharp dom hk hhi hM
    (budget_of_numeric_sharp dom k m hM hnum)
  refine ⟨Q₀, ?_⟩
  set bad := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
    ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
    (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ) with hbad
  have hcount : V / L ^ 2 ≤ bad.card := Nat.div_le_of_le_mul (by
    rw [mul_comm]
    exact hV)
  have hspread := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
    ![fun i => Q₀.eval (dom i), fun i => (dom i) ^ k] bad ?_
  · refine le_trans ?_ hspread
    refine ENNReal.div_le_div_right ?_ _
    exact_mod_cast hcount
  · intro γ hγ
    have h := (Finset.mem_filter.mp hγ).2
    have h0 : (![fun i => Q₀.eval (dom i), fun i => (dom i) ^ k] :
        WordStack F (Fin 2) (Fin n)) 0 = fun i => Q₀.eval (dom i) := rfl
    have h1 : (![fun i => Q₀.eval (dom i), fun i => (dom i) ^ k] :
        WordStack F (Fin 2) (Fin n)) 1 = fun i => (dom i) ^ k := rfl
    rw [h0, h1]
    exact h

open Classical in
/-- The sharp `δ*` ledger bracket from the sharp numeric budget. -/
theorem deep_band_deltaStar_le_of_moments_sharp (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    {M : ℕ} (hM : 2 * (k + m + 1) ≤ M) {L V : ℕ}
    (hnum : ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card ^ 2 * (Fintype.card F) ^ (M - (2 * m + 1))
        + (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card) * (Fintype.card F) ^ (M - (m + 1))
        + ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card * (Fintype.card F) ^ (M - m)
        + V * (Fintype.card F) ^ M
      ≤ 2 * L * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card * (Fintype.card F) ^ (M - m)))
    {εstar : ℝ≥0∞}
    (hε : εstar < ((V / L ^ 2 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar ≤ δ := by
  obtain ⟨Q₀, hfloor⟩ := deep_band_epsMCA_of_moments_sharp dom hk hhi hM hnum
  exact MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le hε hfloor)

open Classical in
/-- **THE SHARP CLOSED-FORM δ* CEILING.**  The whole sharp arc in one ledger
statement: at every band radius, with `Λ' := P/q^(m+1) + C'/q + 3` and
`V' := P·Λ'/q^m`, every error target `ε* < (V'/Λ'²)/q` caps the threshold:
`mcaDeltaStar(rsCode dom k, ε*) ≤ δ` — unconditionally. -/
theorem deep_band_deltaStar_le_closed_form_sharp (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    {εstar : ℝ≥0∞}
    (hε : εstar < (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card / (Fintype.card F) ^ (m + 1) + ((k + m + 1).choose (k + 1) * (n - (k + 1)).choose m) / (Fintype.card F) + 3) / (Fintype.card F) ^ m) / (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card / (Fintype.card F) ^ (m + 1) + ((k + m + 1).choose (k + 1) * (n - (k + 1)).choose m) / (Fintype.card F) + 3) ^ 2 : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞)) :
    MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar ≤ δ :=
  deep_band_deltaStar_le_of_moments_sharp dom hk hhi
    (M := 2 * (k + m + 1)) le_rfl (closedForm_budget_sharp dom k m le_rfl) hε

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.deep_band_epsMCA_of_moments_sharp
#print axioms ProximityGap.PairRank.deep_band_deltaStar_le_of_moments_sharp
#print axioms ProximityGap.PairRank.deep_band_deltaStar_le_closed_form_sharp
