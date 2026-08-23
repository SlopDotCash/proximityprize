/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# The second-moment route, delivered to the MCA surfaces (#389, route 2, brick 4)

The conversion layer: the badSet cardinality produced by the moment machine
(`deep_band_badSet_card_of_moments`) becomes an `ε_mca` floor and a
`mcaDeltaStar` ledger bracket.

* `deep_band_epsMCA_of_moments` — at every band radius, if the numeric budget
  clears for `(L, V)` then

    `(V / L² : ℝ≥0∞) / q ≤ ε_mca(rsCode dom k, δ)`,

  through the witness-spread engine (`epsMCA_ge_card_div_of_mcaEvent_set`).
* `deep_band_deltaStar_le_of_moments` — the ledger bracket: any error target
  `ε* < (V/L²)/q` forces `mcaDeltaStar(rsCode dom k, ε*) ≤ δ`.

Together with `budget_of_numeric` and `deepPairs_card_le`, the full route-2
pipeline is: **one binomial inequality in `(n, k, m, q, M, L, V)` in, one
machine-checked `δ*` upper bracket out** — with no quantification over words,
bypassing the per-word supply wall this issue tracks.

Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The `ε_mca` floor from the moments.**  At every band radius
(`(1−δ)n ≤ k+m+1`), the numeric moment budget delivers a stack whose bad-scalar
mass is at least `(V/L²)/q`. -/
theorem deep_band_epsMCA_of_moments (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    {M : ℕ} (hM : 2 * (k + m + 1) ≤ M) {L V : ℕ}
    (hnum : ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card ^ 2
          * (Fintype.card F) ^ (M - (2 * m + 1))
        + (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
            (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
            (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card
          + ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card)
          * (Fintype.card F) ^ (M - m)
        + V * (Fintype.card F) ^ M
      ≤ 2 * L * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
          * (Fintype.card F) ^ (M - m))) :
    ∃ Q₀ : F[X],
      ((V / L ^ 2 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
        ≤ epsMCA (F := F) (A := F)
            ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ := by
  obtain ⟨Q₀, hV⟩ := deep_band_badSet_card_of_moments dom hk hhi hM
    (budget_of_numeric dom k m hM hnum)
  refine ⟨Q₀, ?_⟩
  set bad := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
    ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
    (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ) with hbad
  -- the count: V/L² ≤ #bad
  have hcount : V / L ^ 2 ≤ bad.card := Nat.div_le_of_le_mul (by
    rw [mul_comm]
    exact hV)
  -- the witness-spread engine on the stack (Q₀∘dom, x^k)
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
/-- **The `δ*` ledger bracket from the moments.**  Any error target below the
delivered floor caps the MCA threshold at the band radius:

  `ε* < (V/L²)/q  ⟹  mcaDeltaStar(rsCode dom k, ε*) ≤ δ`. -/
theorem deep_band_deltaStar_le_of_moments (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    {M : ℕ} (hM : 2 * (k + m + 1) ≤ M) {L V : ℕ}
    (hnum : ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card ^ 2
          * (Fintype.card F) ^ (M - (2 * m + 1))
        + (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
            (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
            (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card
          + ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card)
          * (Fintype.card F) ^ (M - m)
        + V * (Fintype.card F) ^ M
      ≤ 2 * L * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
          * (Fintype.card F) ^ (M - m)))
    {εstar : ℝ≥0∞}
    (hε : εstar < ((V / L ^ 2 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar ≤ δ := by
  obtain ⟨Q₀, hfloor⟩ := deep_band_epsMCA_of_moments dom hk hhi hM hnum
  exact MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le hε hfloor)

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.deep_band_epsMCA_of_moments
#print axioms ProximityGap.PairRank.deep_band_deltaStar_le_of_moments
