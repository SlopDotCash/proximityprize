/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2RootBridge

/-!
# BCIKS20 Appendix A.4 — tying the named P2 core to its analytic root forms

`P2Close.lean` carves the remaining content of (P2) to the named combinatorial core
`RestrictedFaaDiBrunoMatch` and proves it equivalent to `FaaDiBrunoSuccSumZeroResidual`.
`P2RootBridge.lean` characterizes that residual analytically (positive-order root, whole-series
root, equality with the genuine Hensel lift, coefficient-wise equality with `αGenuine`).

This file composes the two so the issue-headline core `RestrictedFaaDiBrunoMatch` is directly
equivalent to each analytic form. Whoever discharges the open A.4 combinatorial content can then
prove it in whichever form is most convenient — the term-level partition match, the root of `Q`,
or the identification with `gammaGenuine` — and the others follow for free.

No new mathematical content: these are one-line compositions of the proven equivalences. The
term-level Faà-di-Bruno / `(A.1)` partition equality remains the actual open residual.
-/

noncomputable section

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The carved P2 core holds iff the assembled series is a root of `Q`. -/
theorem restrictedFaaDiBrunoMatch_iff_eval_eq_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp ↔
      Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0 := by
  rw [restrictedFaaDiBrunoMatch_iff_faaDiBrunoSuccSumZero H x₀ R hHyp,
    ← eval_βHenselAssembled_eq_zero_iff_residual H x₀ R hHyp]

/-- The carved P2 core holds iff the assembled numerator series equals the genuine Hensel lift. -/
theorem restrictedFaaDiBrunoMatch_iff_βHenselAssembled_eq_gammaGenuine
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp ↔
      βHenselAssembled H x₀ R hHyp = gammaGenuine x₀ R H hHyp := by
  rw [restrictedFaaDiBrunoMatch_iff_faaDiBrunoSuccSumZero H x₀ R hHyp,
    ← βHenselAssembled_eq_gammaGenuine_iff_residual H x₀ R hHyp]

/-- The carved P2 core holds iff every assembled coefficient is the genuine Hensel coefficient. -/
theorem restrictedFaaDiBrunoMatch_iff_coeff_eq_αGenuine
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp ↔
      ∀ t : ℕ, PowerSeries.coeff t (βHenselAssembled H x₀ R hHyp)
        = αGenuine H x₀ R hHyp t := by
  rw [restrictedFaaDiBrunoMatch_iff_faaDiBrunoSuccSumZero H x₀ R hHyp,
    ← coeff_βHenselAssembled_eq_αGenuine_iff_residual H x₀ R hHyp]

end BCIKS20.HenselNumerator
