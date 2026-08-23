/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight
import ArkLib.Data.Polynomial.WeightZLinear

/-!
# BCIKS20 App-A.4 — the #138 weight invariant ⟸ Claim 5.9 + an X-degree budget (issue #232)

This file is the **capstone** unifying the two open Johnson-regime residuals. It proves that the
BCIKS20 weight-1 invariant `AlphaGenuineRegularWeightLe` (#138) — `∀ t, αGenuine t` is the embedding
of an `𝒪`-element of `Λ_𝒪`-weight `≤ 1` — follows from:

1. **Claim 5.9 (Z-linearity):** every `αGenuine t` is in the `{1, T}`-shape
   `lift c₀ + T · lift c₁` (`c₀, c₁ ∈ F[X]`); plus
2. **an explicit X-degree budget** on those coefficients: `deg_X c₀ ≤ 1` and
   `(D+1−natDegreeY H) + deg_X c₁ ≤ 1` (the output of the GS interpolant's `deg_X`/`deg_{Y,Z}`
   budget — e.g. `D = natDegreeY H` so the per-`Y`-power weight is `1`, and `deg_X c₁ = 0`).

The proof composes three landed pieces:
* the embedding compatibility `liftToFunctionField_add_T_mul_eq_embed` (the `{1,T}` combination over
  `𝕃 H` IS the embedding of the `{1,Y}`-element `mk(C c₀ + X·C c₁)` over `𝒪 H` — via the ring-hom
  `liftBivariate` and `liftBivariate_C`/`liftBivariate_X`), so the `𝒪`-preimage is explicit;
* the `{1,Y}` weight computation `weight_Λ_over_𝒪_zLinear_le_one` (`WeightZLinear.lean`);
* (uniqueness of the `{1,T}` representation, `FunctionFieldZLinear.lean`, is what makes this preimage
  the genuine one).

Net effect: the *entire* remaining open content of the monic weight-1 invariant (#138) is reduced to
**Claim 5.9 + the GS X-degree budget** — both supplied by the BCIKS20 §5.2.7 interpolation argument.
Everything around that geometric input is now mechanized. Axiom-clean.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Polynomial Polynomial.Bivariate BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator.AlphaWeight

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Embedding compatibility.** The `{1, T}` combination over the function field `𝕃 H` is exactly
the embedding of the `{1, Y}`-element `mk(C c₀ + X·C c₁)` over `𝒪 H`. (`liftBivariate` is a ring
hom with `liftBivariate (C c) = liftToFunctionField c` and `liftBivariate X = functionFieldT`.) -/
lemma liftToFunctionField_add_T_mul_eq_embed (c₀ c₁ : F[X]) :
    liftToFunctionField (H := H) c₀ + functionFieldT (H := H) * liftToFunctionField (H := H) c₁
      = embeddingOf𝒪Into𝕃 H (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
          (Polynomial.C c₀ + Polynomial.X * Polynomial.C c₁)) := by
  rw [embeddingOf𝒪Into𝕃_mk, map_add, map_mul, liftBivariate_C, liftBivariate_X, liftBivariate_C]

/-- **Per-index: weight-1 from the Claim 5.9 form + X-degree bounds.** If `αGenuine t` has the
`{1, T}` shape `lift c₀ + T·lift c₁` with `deg_X c₀ ≤ 1` and `(D+1−natDegreeY H)+deg_X c₁ ≤ 1`, then
`αGenuine t` is the embedding of the explicit `𝒪`-element `mk(C c₀ + X·C c₁)`, whose `Λ_𝒪`-weight is
`≤ 1` (`weight_Λ_over_𝒪_zLinear_le_one`). -/
theorem alphaGenuine_regular_weight_le_one_of_zLinear
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (D t : ℕ) (c₀ c₁ : F[X])
    (hz : αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H) c₀
        + functionFieldT (H := H) * liftToFunctionField (H := H) c₁)
    (hc0 : c₀.natDegree ≤ 1)
    (hc1 : (D + 1 - Bivariate.natDegreeY H) + c₁.natDegree ≤ 1) :
    ∃ a : 𝒪 H, embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp t
      ∧ weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 := by
  refine ⟨Ideal.Quotient.mk (Ideal.span {H_tilde' H})
      (Polynomial.C c₀ + Polynomial.X * Polynomial.C c₁), ?_, ?_⟩
  · rw [← liftToFunctionField_add_T_mul_eq_embed, hz]
  · exact weight_Λ_over_𝒪_zLinear_le_one hH hd c₀ c₁ D hc0 hc1

/-- **The #138 weight invariant ⟸ Claim 5.9 + an X-degree budget (capstone).**
For monic-degree `≥ 2` `H`, if every `αGenuine t` is `Z`-linear (`{1, T}` shape, Claim 5.9) with the
`{1, T}` coefficients satisfying the X-degree budget `deg_X c₀ ≤ 1`, `(D+1−natDegreeY H)+deg_X c₁ ≤ 1`,
then the full BCIKS20 weight-1 invariant `AlphaGenuineRegularWeightLe` holds. This reduces the entire
remaining open content of #138 (monic) to the BCIKS20 §5.2.7 geometric inputs (Claim 5.9 + the GS
`deg_{Y,Z}` budget); the weight calculus around them is mechanized. -/
theorem alphaGenuineRegularWeightLe_of_zLinear_of_degree_bounds
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (D : ℕ)
    (hzlin : ∀ t : ℕ, ∃ c₀ c₁ : F[X],
      αGenuine H x₀ R hHyp t
          = liftToFunctionField (H := H) c₀
            + functionFieldT (H := H) * liftToFunctionField (H := H) c₁
        ∧ c₀.natDegree ≤ 1
        ∧ (D + 1 - Bivariate.natDegreeY H) + c₁.natDegree ≤ 1) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D := by
  intro t
  obtain ⟨c₀, c₁, hz, hc0, hc1⟩ := hzlin t
  exact alphaGenuine_regular_weight_le_one_of_zLinear H hH hd hHyp D t c₀ c₁ hz hc0 hc1

end BCIKS20.HenselNumerator.AlphaWeight

section AxiomAudit
#print axioms BCIKS20.HenselNumerator.AlphaWeight.liftToFunctionField_add_T_mul_eq_embed
#print axioms BCIKS20.HenselNumerator.AlphaWeight.alphaGenuine_regular_weight_le_one_of_zLinear
#print axioms BCIKS20.HenselNumerator.AlphaWeight.alphaGenuineRegularWeightLe_of_zLinear_of_degree_bounds
end AxiomAudit
