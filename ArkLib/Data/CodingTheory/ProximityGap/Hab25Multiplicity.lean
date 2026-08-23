/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliza
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.Probability.Instances

/-!
# Hab25 §3 S11: the integer→probability scaling edge for `ε_mca` (proven)

The combinatorial endgame of Hab25 §3 (`Hab25Johnson.claim1_theorem2_integer`) proves the
*integer* mutual-disagreement count bound `|E| ≤ ℓ·n`. The remaining S11 step (paper §3, the
`1/|F|` scaling) turns that integer count into the `ε_mca` *probability* bound. The Hab25
residual bundle's `JohnsonNumericBound` field has so far **assumed** the full inequality
`ε_mca ≤ ofReal boundReal`, swallowing this scaling.

This file discharges the scaling half, with no admitted content:

* `epsMCA_le_of_card_le` — if for every word-stack `u` the bad-scalar set
  `{γ : mcaEvent C δ (u 0) (u 1) γ}` has `Finset.card ≤ N`, then `ε_mca(C, δ) ≤ N / |F|`.
  This routes the `epsMCA` supremum (a worst-case over stacks of a uniform-`γ` probability)
  through the in-tree `prob_uniform_eq_card_filter_div_card`
  (`Pr_{γ ← $F}[P γ] = |filter P univ| / |F|`) and monotone division.

* `epsMCA_le_ofReal_div_of_card_le` — the integer→real edge: from the same per-stack
  cardinality bound `N` plus an elementary real comparison `0 ≤ B`, `(N : ℝ) ≤ B`, conclude
  `ε_mca(C, δ) ≤ ofReal (B / |F|)`. This is the shape consumed by the Hab25/BCHKS25 Johnson
  bound, whose RHS is exactly `(numerator) / |F|`.

**Non-vacuity.** The hypotheses are a *cardinality* bound on a `Finset` (the shape the proven
endgame `|E| ≤ ℓ·n` produces) and an *elementary real inequality*; the conclusion is a
*probability* bound. Neither lemma assumes a hypothesis equivalent to its conclusion — the
scaling content (the `epsMCA` supremum equals counting over `|F|`) is genuinely derived.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ProximityGap

open NNReal Code Finset
open scoped ProbabilityTheory BigOperators ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **S11 scaling (proven).** If for every word-stack `u`, the set of scalars `γ` triggering
`mcaEvent C δ (u 0) (u 1) γ` has cardinality `≤ N`, then `ε_mca(C, δ) ≤ N / |F|`.

The `epsMCA` supremum is over stacks `u` of `Pr_{γ ← $F}[mcaEvent …]`, and each such
probability equals `|{γ : mcaEvent …}| / |F|` by `prob_uniform_eq_card_filter_div_card`; the
per-stack cardinality bound then dominates it via monotone division. -/
theorem epsMCA_le_of_card_le (C : Set (ι → A)) (δ : ℝ≥0) (N : ℕ)
    (hN : ∀ u : WordStack A (Fin 2) ι,
      (Finset.filter (fun γ : F => mcaEvent C δ (u 0) (u 1) γ) Finset.univ).card ≤ N) :
    epsMCA (F := F) C δ ≤ ((N : ℝ≥0) : ENNReal) / (Fintype.card F : ℝ≥0) := by
  classical
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card (F := F)
        (P := fun γ => mcaEvent C δ (u 0) (u 1) γ)]
  gcongr
  exact_mod_cast hN u

open Classical in
/-- **S11 integer→real bridge (proven).** From the per-stack bad-set cardinality bound `N` and
an elementary real comparison `0 ≤ B`, `(N : ℝ) ≤ B`, conclude `ε_mca(C, δ) ≤ ofReal (B/|F|)`.

This is the genuine integer→probability edge: the integer disagreement count `N` — the output
of the proven endgame `|E| ≤ ℓ·n` — scales to the closed-form probability bound `ofReal (B/|F|)`
whenever the real numerator `B` dominates `N`. -/
theorem epsMCA_le_ofReal_div_of_card_le (C : Set (ι → A)) (δ : ℝ≥0) (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hN : ∀ u : WordStack A (Fin 2) ι,
      (Finset.filter (fun γ : F => mcaEvent C δ (u 0) (u 1) γ) Finset.univ).card ≤ N) :
    epsMCA (F := F) C δ ≤ ENNReal.ofReal (B / (Fintype.card F : ℝ)) := by
  classical
  refine le_trans (epsMCA_le_of_card_le (F := F) C δ N hN) ?_
  have hFne : (Fintype.card F : ℝ≥0) ≠ 0 := by
    have h0 : Fintype.card F ≠ 0 := Fintype.card_ne_zero
    exact_mod_cast h0
  have hkey : ((N : ℝ≥0) : ENNReal) / (Fintype.card F : ℝ≥0)
      = ENNReal.ofReal ((N : ℝ) / (Fintype.card F : ℝ)) := by
    rw [← ENNReal.coe_div hFne, ENNReal.coe_nnreal_eq]
    congr 1
  rw [hkey]
  apply ENNReal.ofReal_le_ofReal
  gcongr

end ProximityGap
