/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandFailureClosedForm
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# The deep-band δ* ceiling: the failure programme reaches the threshold ledger

Issue #389. The deep-band failure family (witness-mass law → second-moment machine →
the closed-form count `deep_band_failure_closed_form`) produced quantitative bad-scalar
counts at every band, but none of it was wired to the `mcaDeltaStar` bracket engine —
the counts never became threshold ceilings. This file is that consumer:

* `epsMCA_ge_of_deep_band` — the closed-form count divided by `q` lower-bounds the MCA
  error at every band radius: `(P·Λ/q^m)/(q·Λ²) ≤ ε_mca(rsCode, δ)`;
* `mcaDeltaStar_le_of_deep_band` — **the δ* ceiling**: whenever the closed-form count
  clears the budget `ε*·q·Λ² < P·Λ/q^m`, the band radius is bad and
  `δ*(rsCode dom k, ε*) ≤ δ` for every `δ` with `(1−δ)n ≤ k+m+1`.

With `Λ = P/q^(m+1) + C' + 2` this activates wherever
`P = C(n, k+m+1) ≳ ε*·q^(m+1)·(C'+2)` — at `ε* = 2^(-128)` a zone wider than the
`q/2` bandwidth law's by the factor `2^127`: every band whose witness mass exceeds a
`2^(-127)`-discounted polynomial threshold now carries a machine-checked δ* ceiling.

## References

* Issue #389; `DeepBandFailureClosedForm.lean` (the count), `MCAThresholdLedger.lean`
  (`mcaDeltaStar_le_of_bad`), `MCALowerBound.lean` (`mcaEvent_prob_le_epsMCA`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code
open ProximityGap.MCAThresholdLedger

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- Any stack's bad-scalar count over `q` lower-bounds `ε_mca`. The cardinality form of
`mcaEvent_prob_le_epsMCA`, in the `rsCode` vocabulary of the deep-band family. -/
theorem epsMCA_ge_badSet_card (dom : Fin n ↪ F) (k : ℕ) {δ : ℝ≥0} (Q₀ : F[X]) :
    ((Finset.univ.filter (fun γ : F => mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
          (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ := by
  classical
  refine le_trans ?_ (mcaEvent_prob_le_epsMCA (F := F) (A := F) _ _
    ![fun i => Q₀.eval (dom i), fun i => (dom i) ^ k])
  have h0 : (![fun i => Q₀.eval (dom i), fun i => (dom i) ^ k] :
      WordStack F (Fin 2) (Fin n)) 0 = fun i => Q₀.eval (dom i) := rfl
  have h1 : (![fun i => Q₀.eval (dom i), fun i => (dom i) ^ k] :
      WordStack F (Fin 2) (Fin n)) 1 = fun i => (dom i) ^ k := rfl
  rw [h0, h1, prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr

open Classical in
/-- **The deep-band δ\* ceiling.**  At every band radius `(1−δ)n ≤ k+m+1`: if the
closed-form failure count clears the `ε*` budget — `ε*·q·Λ² < P·Λ/q^m` with
`P := C(n,k+m+1)`, `Λ := P/q^(m+1) + C(k+m+1,k+1)·C(n−(k+1),m) + 2` — then

  `mcaDeltaStar (rsCode dom k) ε* ≤ δ`.

The first wiring of the deep-band failure programme into the threshold ledger: every
band whose witness mass exceeds the `ε*`-discounted polynomial threshold carries a
machine-checked δ* ceiling. -/
theorem mcaDeltaStar_le_of_deep_band (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    (εstar : ℝ≥0∞)
    (hnum : εstar * ((Fintype.card F : ℝ≥0∞)
        * (↑(((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
              / (Fintype.card F) ^ (m + 1)
            + (k + m + 1).choose (k + 1) * (n - (k + 1)).choose m + 2) : ℝ≥0∞) ^ 2)
      < (↑(((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
          * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
              / (Fintype.card F) ^ (m + 1)
            + (k + m + 1).choose (k + 1) * (n - (k + 1)).choose m + 2)
          / (Fintype.card F) ^ m) : ℝ≥0∞)) :
    mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar ≤ δ := by
  classical
  -- abbreviations
  set P : ℕ := ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card with hP
  set Λ : ℕ := P / (Fintype.card F) ^ (m + 1)
    + (k + m + 1).choose (k + 1) * (n - (k + 1)).choose m + 2 with hΛ
  set V : ℕ := P * Λ / (Fintype.card F) ^ m with hV
  -- the closed-form count gives a stack with V ≤ badCard·Λ²
  obtain ⟨Q₀, hQ₀⟩ := deep_band_failure_closed_form dom hk hhi (m := m) (δ := δ)
  set B : ℕ := (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card with hB
  have hVB : V ≤ B * Λ ^ 2 := hQ₀
  -- positivity facts
  have hq0 : (0 : ℝ≥0∞) < (Fintype.card F : ℝ≥0∞) := by
    exact_mod_cast Fintype.card_pos
  have hΛ2 : 2 ≤ Λ := by
    rw [hΛ]
    exact Nat.le_add_left 2 _
  have hΛ0 : ((Λ : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (by omega : Λ ≠ 0)
  have hΛt : ((Λ : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hden0 : (Fintype.card F : ℝ≥0∞) * ((Λ : ℕ) : ℝ≥0∞) ^ 2 ≠ 0 := by
    refine mul_ne_zero (by exact_mod_cast Fintype.card_pos.ne') ?_
    exact pow_ne_zero _ hΛ0
  have hdent : (Fintype.card F : ℝ≥0∞) * ((Λ : ℕ) : ℝ≥0∞) ^ 2 ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_
    exact ENNReal.pow_ne_top hΛt
  -- εstar < V/(q·Λ²) ≤ B·Λ²/(q·Λ²) = B/q ≤ epsMCA
  refine mcaDeltaStar_le_of_bad (F := F) (A := F) _ εstar ?_
  have step1 : εstar < ((V : ℕ) : ℝ≥0∞)
      / ((Fintype.card F : ℝ≥0∞) * ((Λ : ℕ) : ℝ≥0∞) ^ 2) :=
    ENNReal.lt_div_iff_mul_lt (Or.inl hden0) (Or.inl hdent) |>.mpr hnum
  have step2 : ((V : ℕ) : ℝ≥0∞)
        / ((Fintype.card F : ℝ≥0∞) * ((Λ : ℕ) : ℝ≥0∞) ^ 2)
      ≤ ((B * Λ ^ 2 : ℕ) : ℝ≥0∞)
        / ((Fintype.card F : ℝ≥0∞) * ((Λ : ℕ) : ℝ≥0∞) ^ 2) := by
    gcongr
  have step3 : ((B * Λ ^ 2 : ℕ) : ℝ≥0∞)
        / ((Fintype.card F : ℝ≥0∞) * ((Λ : ℕ) : ℝ≥0∞) ^ 2)
      = ((B : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
    push_cast
    exact ENNReal.mul_div_mul_right _ _ (pow_ne_zero _ hΛ0) (ENNReal.pow_ne_top hΛt)
  calc εstar < ((V : ℕ) : ℝ≥0∞)
        / ((Fintype.card F : ℝ≥0∞) * ((Λ : ℕ) : ℝ≥0∞) ^ 2) := step1
    _ ≤ ((B * Λ ^ 2 : ℕ) : ℝ≥0∞)
        / ((Fintype.card F : ℝ≥0∞) * ((Λ : ℕ) : ℝ≥0∞) ^ 2) := step2
    _ = ((B : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := step3
    _ ≤ epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ :=
      epsMCA_ge_badSet_card dom k Q₀

/-! ## Source audit -/

#print axioms epsMCA_ge_badSet_card
#print axioms mcaDeltaStar_le_of_deep_band

end ProximityGap.PairRank
