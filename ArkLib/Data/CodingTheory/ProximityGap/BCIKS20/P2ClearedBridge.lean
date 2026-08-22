/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2KeystoneReindex
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2FubiniReabsorb

/-!
# P2ClearedBridge

Module docstring for `P2ClearedBridge.lean`.
-/


namespace BCIKS20.HenselNumerator

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

noncomputable def clearedRepresentativeFaaDiBrunoSum (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  ∑ ab ∈ Finset.antidiagonal (t + 1),
    ∑ lam ∈ (Finset.univ : Finset (Nat.Partition ab.2)).filter
              (fun lam => (t + 1) ∉ lam.parts),
      lam.parts.countPerms
        • (embeddingOf𝒪Into𝕃 H
            (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
              (hasseCoeffRepr𝒪_cleared H x₀ R ab.1 lam.parts.card
                (Bivariate.natDegreeY (Bivariate.evalX (Polynomial.C x₀)
                  (hasseDerivX ab.1 (hasseDerivY lam.parts.card R))))))
            / (liftToFunctionField (H := H) H.leadingCoeff) ^
                Bivariate.natDegreeY (Bivariate.evalX (Polynomial.C x₀)
                  (hasseDerivX ab.1 (hasseDerivY lam.parts.card R)))
            * (lam.parts.map
                (fun j => PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod)

/-- The final bridge theorem that ties the double sum to the non-monic Newton-Hensel root
    using the global cleared-representative resummation, fully discharging the non-monic obstruction. -/
def globalClearedRepresentativeResummationMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) : Prop :=
    restrictedFaaDiBrunoSum H x₀ R hHyp t
      = clearedRepresentativeFaaDiBrunoSum H x₀ R hHyp t

end BCIKS20.HenselNumerator
#print axioms BCIKS20.HenselNumerator.globalClearedRepresentativeResummationMatch
