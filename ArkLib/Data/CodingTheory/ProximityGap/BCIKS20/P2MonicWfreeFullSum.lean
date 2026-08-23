/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MonicWfreeGlobal
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Match

/-!
# BCIKS20 Appendix A.4 — monic W-free full-sum interface

`P2MonicWfreeGlobal.lean` names the all-order W-free target left after the monic hypothesis
removes the `W`-power obstruction. `P2Match.lean` connects the carved residual to the full
Faà-di-Bruno sum vanishing statement. This file composes those two interfaces.

The result is a full-sum-facing statement of the remaining monic P2 work: under
`H.leadingCoeff = 1`, proving the all-order W-free equations is equivalent to proving
`FaaDiBrunoFullSumVanishes`.
-/

noncomputable section

open scoped BigOperators
open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- Under monic `H`, full Faà-di-Bruno sum vanishing is equivalent to the global W-free target. -/
theorem fullVanishes_iff_WfreeMatch_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1) :
    FaaDiBrunoFullSumVanishes H x₀ R hHyp ↔
      RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp :=
  (restrictedMatch_iff_fullVanishes H x₀ R hHyp).symm.trans
    (restrictedFaaDiBrunoMatch_iff_WfreeMatch_of_leadingCoeff_one H x₀ R hHyp hlc)

/-- Build full Faà-di-Bruno sum vanishing from the global W-free target under monic `H`. -/
theorem FaaDiBrunoFullSumVanishes.of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp) :
    FaaDiBrunoFullSumVanishes H x₀ R hHyp :=
  (fullVanishes_iff_WfreeMatch_of_leadingCoeff_one H x₀ R hHyp hlc).2 hWfree

/-- Project the global W-free target from full Faà-di-Bruno sum vanishing under monic `H`. -/
theorem RestrictedFaaDiBrunoWfreeMatch.of_fullVanishes
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp) :
    RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp :=
  (fullVanishes_iff_WfreeMatch_of_leadingCoeff_one H x₀ R hHyp hlc).1 hvan

/-- Non-namespace alias for the forward full-sum projection from the global W-free target. -/
theorem fullVanishes_of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp) :
    FaaDiBrunoFullSumVanishes H x₀ R hHyp :=
  FaaDiBrunoFullSumVanishes.of_WfreeMatch H x₀ R hHyp hlc hWfree

/-- Non-namespace alias for the reverse W-free projection from full-sum vanishing. -/
theorem WfreeMatch_of_fullVanishes
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp) :
    RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp :=
  RestrictedFaaDiBrunoWfreeMatch.of_fullVanishes H x₀ R hHyp hlc hvan

end BCIKS20.HenselNumerator

set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.fullVanishes_iff_WfreeMatch_of_leadingCoeff_one
#print axioms BCIKS20.HenselNumerator.FaaDiBrunoFullSumVanishes.of_WfreeMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoWfreeMatch.of_fullVanishes
#print axioms BCIKS20.HenselNumerator.fullVanishes_of_WfreeMatch
#print axioms BCIKS20.HenselNumerator.WfreeMatch_of_fullVanishes
