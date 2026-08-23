/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.CheckedFinalBlock
import ArkLib.Data.CodingTheory.Basic.RelativeDistance

/-!
# The spot-check salvage bound (#301)

**The spot-check salvage bound** — the quantitative `ε_fin` kernel for the
checked STIR final block. If the in-the-clear final word disagrees with the incoming oracle
on at least a `δ` fraction of indices, then a uniformly sampled index passes the pointwise
check with probability at most `1 − δ` — the classic `(1−δ)^t` repetition bound at `t = 1`,
in the exact index space (`Fin (Fintype.card ι)`) that `stirFinalVectorVerifierChecked`
queries. -/

namespace StirIOP

namespace Round3

open OracleComp NNReal Finset
open scoped ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The agreement set of two words over the queried index space. -/
def agreementSet (vWord vIn : Fin (Fintype.card ι) → F) : Finset (Fin (Fintype.card ι)) :=
  Finset.univ.filter (fun k => vWord k = vIn k)

/-- Disagreement on at least a `δ` fraction bounds the agreement-set size. -/
theorem agreementSet_card_le {vWord vIn : Fin (Fintype.card ι) → F} {δ : ℝ≥0}
    (hfar : (δ : ℝ) * Fintype.card ι
      ≤ (Finset.univ.filter (fun k => vWord k ≠ vIn k)).card) :
    ((agreementSet (ι := ι) vWord vIn).card : ℝ)
      ≤ (1 - δ) * Fintype.card ι := by
  classical
  have hsplit : (agreementSet (ι := ι) vWord vIn).card
      + (Finset.univ.filter (fun k => vWord k ≠ vIn k)).card
      = Fintype.card ι := by
    rw [agreementSet]
    rw [Finset.filter_card_add_filter_neg_card_eq_card
      (p := fun k : Fin (Fintype.card ι) => vWord k = vIn k)]
    exact Fintype.card_fin _
  have h1 : ((agreementSet (ι := ι) vWord vIn).card : ℝ)
      = (Fintype.card ι : ℝ)
        - (Finset.univ.filter (fun k => vWord k ≠ vIn k)).card := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hsplit
    push_cast at this
    linarith
  rw [h1, sub_mul, one_mul]
  linarith

/-- **The spot-check salvage bound** (the `ε_fin` kernel at `t = 1`): if the final word
disagrees with the incoming oracle on at least a `δ` fraction of the queried index space,
a uniformly sampled index lands in the agreement set — i.e. the pointwise check of
`stirFinalVectorVerifierChecked` passes — with probability at most `1 − δ`. -/
theorem probEvent_spotCheck_le {vWord vIn : Fin (Fintype.card ι) → F} {δ : ℝ≥0}
    [Nonempty ι] (hδ1 : δ ≤ 1)
    (hfar : (δ : ℝ) * Fintype.card ι
      ≤ (Finset.univ.filter (fun k => vWord k ≠ vIn k)).card) :
    Pr[fun k : Fin (Fintype.card ι) => vWord k = vIn k | $ᵗ (Fin (Fintype.card ι))]
      ≤ ((1 - δ : ℝ≥0) : ℝ≥0∞) := by
  classical
  haveI : Nonempty (Fin (Fintype.card ι)) :=
    ⟨⟨0, Fintype.card_pos⟩⟩
  rw [probEvent_uniformSample]
  have hcard := agreementSet_card_le (ι := ι) (vWord := vWord) (vIn := vIn) hfar
  have hcoe : ((1 - δ : ℝ≥0) : ℝ) = 1 - (δ : ℝ) := by
    rw [NNReal.coe_sub hδ1, NNReal.coe_one]
  have hnn : ((agreementSet (ι := ι) vWord vIn).card : ℝ≥0)
      ≤ (1 - δ) * (Fintype.card ι : ℝ≥0) := by
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, hcoe, NNReal.coe_natCast, NNReal.coe_natCast]
    exact hcard
  have hineq : ((Finset.univ.filter
        (fun k : Fin (Fintype.card ι) => vWord k = vIn k)).card : ℝ≥0∞)
      ≤ ((1 - δ : ℝ≥0) : ℝ≥0∞) * (Fintype.card ι : ℝ≥0∞) := by
    calc ((Finset.univ.filter
          (fun k : Fin (Fintype.card ι) => vWord k = vIn k)).card : ℝ≥0∞)
        = (((agreementSet (ι := ι) vWord vIn).card : ℝ≥0) : ℝ≥0∞) := by norm_cast
      _ ≤ (((1 - δ) * (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hnn
      _ = ((1 - δ : ℝ≥0) : ℝ≥0∞) * (Fintype.card ι : ℝ≥0∞) := by
          rw [ENNReal.coe_mul]; norm_cast
  rw [Fintype.card_fin]
  exact ENNReal.div_le_of_le_mul hineq

end Round3

end StirIOP

#print axioms StirIOP.Round3.agreementSet_card_le
#print axioms StirIOP.Round3.probEvent_spotCheck_le
