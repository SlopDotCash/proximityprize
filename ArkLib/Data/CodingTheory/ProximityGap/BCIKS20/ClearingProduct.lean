/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight

/-!
# The 𝒪-clearing product is a non-zero-divisor (BCIKS20 A.4, issue #138)

The (A.4) lift normalizes `βHensel … t` by the **clearing product** `W^{t+1}·ξ^{2t-1} ∈ 𝒪 H`.
For the `DivWeightLe`/`AlphaGenuineRegularWeightLe` quotient `a` to be well-defined and unique, this
clearing product must be a non-zero-divisor.

* `embeddingOf𝒪Into𝕃_clearingProduct` — the `Y↦T` embedding of the clearing product is the genuine
  `𝕃`-denominator `(lift lc)^{t+1}·(embed ξ)^{2t-1}` (the `den` of `den_ne_zero`). A one-line
  `map_*` rewrite on top of the proven `embeddingOf𝒪Into𝕃_W𝒪` (the #138 sibling of #139's
  `embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared`).
* `clearingProduct_ne_zero` — hence the clearing product is nonzero in `𝒪 H`: its embedding equals
  the nonzero denominator (`den_ne_zero`), and `embeddingOf𝒪Into𝕃` sends `0 ↦ 0`.
-/

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator.AlphaWeight

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The `Y↦T` embedding of the (A.4) clearing product `W^{t+1}·ξ^{2t-1}` is the genuine
`𝕃`-denominator `(lift lc)^{t+1}·(embed ξ)^{2t-1}`. -/
theorem embeddingOf𝒪Into𝕃_clearingProduct (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    embeddingOf𝒪Into𝕃 H ((W𝒪 H) ^ (t + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t - 1))
      = (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) := by
  rw [map_mul, map_pow, map_pow, embeddingOf𝒪Into𝕃_W𝒪]

/-- The (A.4) clearing product is a non-zero-divisor in `𝒪 H` (its embedding is the nonzero
denominator), so the `DivWeightLe` quotient is well-defined. -/
theorem clearingProduct_ne_zero (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    ((W𝒪 H) ^ (t + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t - 1)) ≠ 0 := by
  intro hzero
  have hden := den_ne_zero H x₀ R hHyp t
  apply hden
  rw [← embeddingOf𝒪Into𝕃_clearingProduct H x₀ R hHyp t, hzero, map_zero]

/-- The general-`t` `Dvd` form: given the (P2) lift identity at order `t` and a carved `𝒪`-preimage
`a` of `αGenuine t`, the clearing product `W𝒪^{t+1}·ξ^{2t-1}` divides `βHensel t`. Generalizes the
`t = 0`-only `W𝒪_dvd_βHensel_zero_of_alpha`. -/
theorem clearingProduct_dvd_βHensel_of_alpha (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (t : ℕ) {a : 𝒪 H}
    (ha : embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp t)
    (hlift_t :
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :
    ((W𝒪 H) ^ (t + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t - 1)) ∣ βHensel H x₀ R hHyp t := by
  refine ⟨a, ?_⟩
  rw [βHensel_eq_alpha_mul_of_lift H x₀ R hHyp hH t ha hlift_t, mul_assoc, mul_comm a]

/-- From `AlphaGenuineRegularWeightLe` + the all-orders (P2) lift identity, at every order `t` the
clearing product `W𝒪^{t+1}·ξ^{2t-1}` divides `βHensel t` — the general-`t` necessary divisibility
obstruction (the `t = 0` slice is `W𝒪_dvd_βHensel_zero_of_alphaWeight`). -/
theorem clearingProduct_dvd_βHensel_of_alphaWeight (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    ((W𝒪 H) ^ (t + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t - 1)) ∣ βHensel H x₀ R hHyp t := by
  obtain ⟨a, ha_eq, _⟩ := hα t
  exact clearingProduct_dvd_βHensel_of_alpha H x₀ R hHyp hH t ha_eq (hlift t)

/-- **The `DivWeightLe` quotient is unique.** Any two `𝒪`-elements that both clear `βHensel t` by
the clearing product are equal. As `𝒪 H` has no `NoZeroDivisors` instance, cancellation routes
through the injective field embedding `embeddingOf𝒪Into𝕃` and the nonzero denominator
(`den_ne_zero`). -/
theorem divWeight_quotient_unique (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (t : ℕ) {a₁ a₂ : 𝒪 H}
    (h₁ : βHensel H x₀ R hHyp t
      = a₁ * (W𝒪 H) ^ (t + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t - 1))
    (h₂ : βHensel H x₀ R hHyp t
      = a₂ * (W𝒪 H) ^ (t + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t - 1)) :
    a₁ = a₂ := by
  have heq : a₁ * (W𝒪 H) ^ (t + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t - 1)
      = a₂ * (W𝒪 H) ^ (t + 1) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t - 1) := by
    rw [← h₁, ← h₂]
  apply embeddingOf𝒪Into𝕃_injective hH
  have hL : embeddingOf𝒪Into𝕃 H a₁
        * ((liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
      = embeddingOf𝒪Into𝕃 H a₂
        * ((liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) := by
    have hcongr := congrArg (embeddingOf𝒪Into𝕃 H) heq
    simp only [map_mul, map_pow, embeddingOf𝒪Into𝕃_W𝒪, mul_assoc] at hcongr
    exact hcongr
  exact mul_right_cancel₀ (den_ne_zero H x₀ R hHyp t) hL

end BCIKS20.HenselNumerator.AlphaWeight

#print axioms BCIKS20.HenselNumerator.AlphaWeight.embeddingOf𝒪Into𝕃_clearingProduct
#print axioms BCIKS20.HenselNumerator.AlphaWeight.clearingProduct_ne_zero
#print axioms BCIKS20.HenselNumerator.AlphaWeight.clearingProduct_dvd_βHensel_of_alpha
#print axioms BCIKS20.HenselNumerator.AlphaWeight.clearingProduct_dvd_βHensel_of_alphaWeight
#print axioms BCIKS20.HenselNumerator.AlphaWeight.divWeight_quotient_unique
