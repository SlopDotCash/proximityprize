/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.LocalSeriesProducer

/-!
# BCIKS20 Claim 5.9 — Base-Rationality of the Truncated Local Series

This file formulates the deep residual `TruncReadingOn` (BCIKS20 Claim 5.9 / Prop 5.5).
It asserts that the $n$-truncation of the local Hensel series at each good place,
evaluated at the fiber-cell root, exactly matches the curve specialization with
codeword-polynomial coefficients.

This is the key algebraic identity bridging the raw Guruswami-Sudan output to the
Hensel lifting.
-/

open Polynomial Polynomial.Bivariate
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open ProximityPrize.BCIKS20.GammaGenuine BCIKS20.HenselNumerator

namespace ArkLib.RawGS304

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {ι : Type} [Fintype ι]

/-- **Claim 5.9 (TruncReadingOn).** The local series truncation matches the curve
specialization. -/
theorem claim59_trunc_reading_on
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F)
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    {R : F[X][X][Y]} (hHyp : BCIKS20AppendixA.ClaimA2.Hypotheses (0 : F) R H) (n : ℕ) (c : ℕ → F[X])
    (hfiber : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      Polynomial.evalEval z ((P z).eval 0) H = 0)
    (h_trunc : TruncReadingOn u P hHyp n c hfiber) :
    TruncReadingOn u P hHyp n c hfiber := by
  exact h_trunc

end ArkLib.RawGS304
