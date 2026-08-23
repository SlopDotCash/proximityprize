/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RSLambdaSubJohnsonMCA
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# A good-side δ* lower bound for RS via LD⇒MCA (#389)

The δ* programme's good side (`δ ≤ mcaDeltaStar`) is currently driven either by the granularity
ladder (unconditional, reach `≈ (1−ρ)/3`) or by the Johnson package (`CellPackageSupply`-gated).
Composing the sub-Johnson LD⇒MCA chain (`rsCode_epsMCA_subJohnson_le_of_residual`) with the ledger
`le_mcaDeltaStar_of_good` gives an **alternative good-side route near the Johnson lift**, driven by
the list-decoding side:

> **`rsCode_mcaDeltaStar_ge_johnsonLift_of_residual`** — if the sub-Johnson LD⇒MCA bound at the
> Johnson-lifted radius is `≤ ε*`, then
> ```
> 1 − √(1−δ+η) ≤ mcaDeltaStar(rsCode dom k, ε*).
> ```
> conditional only on the named GKL24 maximal-domain residual.

So a good list-decoding bound for explicit RS (the `C(n,k)/C(a,k)` Deza–Frankl list, supplied
below Johnson by `rsCode_Lambda_subJohnson_le`) pushes `δ*` up to the Johnson lift — the
list-decoding face of the good side.
-/

open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap ProximityGap.MCAThresholdLedger

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **Good-side δ* from LD⇒MCA.** When the sub-Johnson LD⇒MCA bound at the Johnson-lifted radius
is `≤ ε*`, that radius is `mcaDeltaStar`-good. -/
theorem rsCode_mcaDeltaStar_ge_johnsonLift_of_residual (dom : Fin n ↪ F) {k a : ℕ} {δ η : ℝ}
    (hk : 1 ≤ k) (hka : k ≤ a) (hn : 0 < Fintype.card (Fin n))
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1) (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (ha : (a : ℝ) ≤ (1 - δ) * (Fintype.card (Fin n) : ℝ))
    (hres : ProximityGap.GKL24MaxCorrWitnessCoverHypothesis (rsCode dom k)
        ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal) δ.toNNReal
        (((n.choose k / a.choose k : ℕ) : ℝ) ^ 2))
    {εstar : ℝ≥0∞}
    (hε : ENNReal.ofReal
        ((((n.choose k / a.choose k : ℕ) : ℝ) ^ 2 * δ * Fintype.card (Fin n) + 1 / η)
          / Fintype.card F) ≤ εstar) :
    ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal)
      ≤ mcaDeltaStar (F := F) (A := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar := by
  have hle1 : ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal) ≤ (1 : ℝ≥0) := by
    rw [Real.toNNReal_le_one]
    have : (0 : ℝ) ≤ (1 - δ + η) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
    linarith
  refine le_mcaDeltaStar_of_good (F := F) (A := F) _ εstar hle1 ?_
  exact le_trans
    (rsCode_epsMCA_subJohnson_le_of_residual dom hk hka hn
      hδ_pos hδ_lt hη_pos hη_lt hη_le_δ ha hres)
    hε

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.rsCode_mcaDeltaStar_ge_johnsonLift_of_residual
