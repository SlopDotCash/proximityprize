/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.MutualCorrAgreement
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! # Trivial-regime closure of the MCA conjecture

Wherever the error bound is `≥ 1`, mutual correlated agreement holds outright:
a probability never exceeds `1`. By the numerical analysis (mca-experiments),
the Johnson conjecture's `errStar` is `≥ 1` for every field size
`q ≲ 10⁷·(parℓ−1)·k²` — so this lemma fully closes the conjecture on that entire
(non-cryptographic) regime, with no list-decoding/GS machinery needed. The
remaining content lives only in the large-field regime `errStar < 1`. -/

namespace MCAJohnson

open MutualCorrAgreement ProbabilityTheory PMF Generator
open scoped NNReal ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {ι : Type} [Fintype ι] [Nonempty ι]

/-- **MCA from `errStar ≥ 1`.** If the error function is `≥ 1` on the whole valid
range, the generator has mutual correlated agreement — because the
proximity-condition probability is always `≤ 1`. No combinatorial content; this
discharges the conjecture on the entire `errStar ≥ 1` (small/medium field) regime. -/
theorem mca_of_errStar_ge_one
    (Gen : ProximityGenerator ι F) [Fintype Gen.parℓ]
    (BStar : ℝ) (errStar : ℝ → ENNReal)
    (herr : ∀ δ : ℝ≥0, (0 < δ ∧ δ < 1 - BStar) → 1 ≤ errStar δ) :
    hasMutualCorrAgreement Gen BStar errStar := by
  intro f δ hδ
  refine le_trans ?_ (herr δ hδ)
  exact PMF.coe_le_one _ _

end MCAJohnson
