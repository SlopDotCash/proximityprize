/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2KeystoneReindex
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2FubiniReabsorb

/-!
# P2ClearedBridge — the global cleared-representative resummation (statement only, OPEN)

This file defines the cleared-representative Faà-di-Bruno double sum
`clearedRepresentativeFaaDiBrunoSum` and the proposition
`globalClearedRepresentativeResummationMatch` asserting that it equals
`restrictedFaaDiBrunoSum`. That proposition is a `def … : Prop` — an **unproved statement**, not a
theorem. Nothing in this file proves it, and `#print axioms` on it only audits the dependencies of
the statement. It does **not** discharge the non-monic obstruction of #139.

Status context: multiplying both sides of the restricted match by a power of the (nonzero) leading
coefficient is equivalent to the restricted match for every `H`
(`ClearedFaaDiBrunoProof.cleared_iff_restricted`), so such clearing cannot by itself repair the
non-monic case; the non-monic order-zero unrestricted match is refuted
(`P2OrderZeroRefutationWitness`). The monic restricted match is proved
(`restrictedFaaDiBrunoMatch_of_monic`). A genuine non-monic bridge still needs correct hypotheses
and a proved non-monic normalization before it can be stated as a theorem.
-/


namespace BCIKS20.HenselNumerator

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

noncomputable def clearedRepresentativeFaaDiBrunoSum (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal (t + 1),
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

/-- **Unproved statement (OPEN, #139).** The proposition that the restricted Faà-di-Bruno sum
equals the cleared-representative double sum at order `t`. This is a `Prop`-valued definition, not
a proof: nothing in-tree proves it, and it does not discharge the non-monic obstruction. It is the
canonical form of this statement; `BCIKS20AppA.faa_di_bruno_global_cleared_match` is an alias. -/
def globalClearedRepresentativeResummationMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) : Prop :=
    restrictedFaaDiBrunoSum H x₀ R hHyp t
      = clearedRepresentativeFaaDiBrunoSum H x₀ R hHyp t

end BCIKS20.HenselNumerator
#print axioms BCIKS20.HenselNumerator.globalClearedRepresentativeResummationMatch
