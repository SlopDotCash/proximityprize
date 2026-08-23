/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PMOneWordCap
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonSplitSupply

/-!
# The formal floor on the capped supply residual (#389, the open core)

Wires the two supply-side theorems into the named residual: any `B` satisfying
`SubJohnsonSupplyResidual dom k m B` — the issue's sharpest capped form of the open
supply statement — must dominate the class structure of the ±1 words:

> **`subJohnsonSupplyResidual_pm_one_floor`** — if a `{1,−1}`-valued word has both
> value classes of size `≤ 2k+m+1`, then `C(s₊, k+m+1) ≤ B` (and symmetrically `s₋`).

The word is admissible for the residual by `pm_one_agreement_le` (every codeword
agreement `≤ max(2k−2, s±) ≤ 2k+m+1`), and its supply is `≥ C(s₊, k+m+1)` by
`class_supply_floor`.  At the balanced boundary `s± = 2k+m+1` this is the proven
statement that **the capped residual's optimal `B` is at least `C(2k+m+1, k+m+1)
≈ 4^k`-shaped from class structure alone** — and the probe-measured character words
(class sizes `n/2` at instances where `n/2 ≤ 2k+m+1`-adjacent shapes exist) realize
it.  The open wall is now formally two-sided at toy scale: proven floors from class
words below, the Johnson-split fiber above.  Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The class floor on the CAPPED residual**: any admissible `B` for
`SubJohnsonSupplyResidual` dominates `C(s₊, k+m+1)` for every `{1,−1}`-valued word
whose value classes both fit under the agreement cap. -/
theorem subJohnsonSupplyResidual_pm_one_floor (dom : Fin n ↪ F) {k : ℕ}
    (hk : 1 ≤ k) (m : ℕ) {B : ℕ}
    (hres : SubJohnsonSupplyResidual dom k m B)
    {w : Fin n → F} (hw : ∀ i, w i = 1 ∨ w i = -1)
    (hcap1 : ((Finset.univ : Finset (Fin n)).filter (fun i => w i = 1)).card
      ≤ 2 * k + m + 1)
    (hcap2 : ((Finset.univ : Finset (Fin n)).filter (fun i => w i = -1)).card
      ≤ 2 * k + m + 1) :
    (((Finset.univ : Finset (Fin n)).filter (fun i => w i = 1)).card).choose (k + m + 1)
      ≤ B := by
  classical
  refine le_trans
    (class_supply_floor dom hk m
      (S := (Finset.univ : Finset (Fin n)).filter (fun i => w i = 1)) (v := 1)
      (fun i hi => (Finset.mem_filter.mp hi).2))
    (hres w ?_)
  intro c hc
  refine le_trans (le_of_eq ?_) (le_trans (pm_one_agreement_le dom hk hw hc)
    (max_le (by omega) (max_le hcap1 hcap2)))
  rfl

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.subJohnsonSupplyResidual_pm_one_floor
