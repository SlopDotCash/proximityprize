/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MatchRoot
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MatchMonic

/-!
# P2MatchProof

Module docstring for `P2MatchProof.lean`.
-/


noncomputable section

open scoped BigOperators
open Finset
open Polynomial Polynomial.Bivariate
open ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Honest named residual for the P2 restricted Faà-di-Bruno match.**

This was previously a fabricated `axiom restrictedFaaDiBrunoMatch_residual`, which silently
asserted the genuine open BCIKS20 Appendix A.4 combinatorial core (`RestrictedFaaDiBrunoMatch`)
and thereby tainted the whole proximity development's axiom audit with a false "closed" claim.
It is now an honest `Prop`-valued *hypothesis* threaded through `P2_closed_of_residual`, matching
the named-residual discipline used throughout `P2Close`/`P2Match`/`P2Assembly`.

The genuine remaining content is the `t ≥ 1` ξ-telescoped Faà-di-Bruno bijection (order-0 is
proven for monic `H` by `restrictedMatchAt_zero_of_leadingCoeff_one`; non-monic order-0 is
provably *false* from `ClaimA2.Hypotheses` alone). No `axiom`/`sorry` is introduced here. -/
def RestrictedFaaDiBrunoMatchResidual (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) : Prop :=
  RestrictedFaaDiBrunoMatch H x₀ R hHyp

/-- Discharges the full P2 closed goal from the honest match residual (no `axiom`, no `sorry`):
the restricted Faà-di-Bruno match is taken as an explicit hypothesis rather than asserted. -/
theorem P2_closed_of_residual (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatchResidual H x₀ R hHyp) :
    (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0)
    ∧ (∀ t : ℕ, embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :=
  P2_closed H x₀ R hHyp hmatch

/-- **P2 closed for monic `H` — fully proven, no residual hypothesis.**

For monic `H` (`H.leadingCoeff = 1`, the WLOG case for the BCIKS20 minimal-polynomial reduction)
the restricted Faà-di-Bruno match `RestrictedFaaDiBrunoMatch` is a *theorem*
(`restrictedFaaDiBrunoMatch_of_monic`, axiom-clean), so the full P2 closed goal — assembled-series
root + the order-by-order lift identity — holds unconditionally. This discharges the headline
BCIKS20 Appendix A.4 obligation in the monic regime with no `axiom`, no `sorry`, no residual. -/
theorem P2_closed_of_leadingCoeff_one (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) :
    (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0)
    ∧ (∀ t : ℕ, embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :=
  P2_closed H x₀ R hHyp (restrictedFaaDiBrunoMatch_of_monic H x₀ R hHyp hlc)

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatchResidual
#print axioms BCIKS20.HenselNumerator.P2_closed_of_residual
#print axioms BCIKS20.HenselNumerator.P2_closed_of_leadingCoeff_one
