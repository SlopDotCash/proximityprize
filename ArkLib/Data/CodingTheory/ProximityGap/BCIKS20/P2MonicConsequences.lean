/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MatchProof
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Vanish
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight

/-!
# BCIKS20 Appendix A.4 — monic consequences of the proven Faà-di-Bruno match

`P2MatchMonic.restrictedFaaDiBrunoMatch_of_monic` proves the carved P2 core
`RestrictedFaaDiBrunoMatch` for monic `H` (axiom-clean, all orders). This file propagates that
genuine theorem through the *already-proven* `_of_restrictedMatch` bridges, turning every
match-conditional P2 obligation into a monic-unconditional theorem (no `axiom`, no `sorry`, no
residual hypothesis):

* `faaDiBrunoSuccSumZeroResidual_of_leadingCoeff_one` — the legacy successor-sum P2 residual
  (consumed by the §5 / `P1Conditional` / `StrictCoeffPolys` chain) holds for monic `H`.
* `lift_identity_of_leadingCoeff_one` — the order-by-order lift identity
  `embed(βHensel t) = αGenuine t · W^{t+1} · ξ^{2t-1}`, i.e. the `hlift` hypothesis of
  `alphaWeight_iff_divWeight`, is now a *theorem* for monic `H`.

The remaining open content of BCIKS20 A.4 is the **P1 weight-1 core** (`DivWeightLe` /
`AlphaGenuineRegularWeightLe`): that `αGenuine t` is the embedding of an `𝒪`-element of
`Λ_𝒪`-weight `≤ 1`. By `alphaWeight_iff_divWeight` this is an `𝒪`-divisibility-with-weight fact,
*distinct* from the lift identity proven here, and genuinely open (see issue #138). It is NOT
discharged here.
-/

noncomputable section
open scoped BigOperators
open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

open AlphaWeight

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Monic ⟹ the legacy successor-sum P2 residual (fully proven, axiom-clean).** -/
theorem faaDiBrunoSuccSumZeroResidual_of_leadingCoeff_one (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) :
    FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp :=
  faaDiBrunoSuccSumZeroResidual_of_restrictedMatch H x₀ R hHyp
    (restrictedFaaDiBrunoMatch_of_monic H x₀ R hHyp hlc)

/-- **Monic ⟹ the order-by-order lift identity (fully proven, axiom-clean).**

This is exactly the `hlift` hypothesis required by `alphaWeight_iff_divWeight`; for monic `H` it is
now a theorem, so the P1 ⟺ `DivWeightLe` equivalence holds unconditionally and the *only* remaining
P1 content is the weight-1 quotient bound (open, #138). -/
theorem lift_identity_of_leadingCoeff_one (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) :
    ∀ t : ℕ, embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
      = αGenuine H x₀ R hHyp t
          * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) :=
  (P2_closed_of_leadingCoeff_one H x₀ R hHyp hlc).2

/-- **Monic ⟹ P1 ⟺ `DivWeightLe`, with `hlift` discharged.** Given monic `H`, the carved
regularity form `AlphaGenuineRegularWeightLe` and the `𝒪`-divisibility form `DivWeightLe` are
equivalent — the lift identity (`hlift`) is supplied by `lift_identity_of_leadingCoeff_one`. The
common content (the weight-1 quotient) remains open (#138). -/
theorem alphaWeight_iff_divWeight_of_leadingCoeff_one (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlc : H.leadingCoeff = 1) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D ↔ DivWeightLe H x₀ R hHyp hH D :=
  alphaWeight_iff_divWeight H x₀ R hHyp hH D
    (lift_identity_of_leadingCoeff_one H x₀ R hHyp hlc)

end BCIKS20.HenselNumerator
