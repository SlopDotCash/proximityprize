/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.HenselNumerator
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2BijectionApply

/-!
# Un-cleared embedding of the iterated-Hasse coefficient (BCIKS20 A.4, issue #139)

`embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared` names the **un-cleared** `Y ↦ T` embedding of the
genuine iterated-Hasse coefficient `hasseCoeffRepr𝒪` as `eval₂ liftToFunctionField T p` with
`p = (Δ_X^{i1} Δ_Y^{m} R)|x₀`. The companion Taylor-sum theorem expands this as the shifted
Hasse sum with `T^i`, parallel to `hasseEvalAtRoot_eq_taylorSum` where the power is `(T/W)^i`.

Together they make the BCIKS20 Appendix-A.4 STEP-8 obstruction explicit at the `eval₂` level: the
LHS partition form collapses onto `hasseEvalAtRoot` (cleared) while `B_coeff` on the RHS carries
this un-cleared embedding.  The `…WDivTarget` variants additionally name the stronger target where
the cleared root evaluation is the un-cleared embedding divided by a prescribed power of `W`.  See
issue #139 for the obstruction analysis.
-/

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The un-cleared `Y ↦ T` embedding of `hasseCoeffRepr𝒪`: `embed (hasseCoeffRepr𝒪 i1 m)
= eval₂ liftToFunctionField T ((Δ_X^{i1} Δ_Y^{m} R)|x₀)`, the un-cleared sibling of
`hasseEvalAtRoot` (`eval₂ liftToFunctionField (T/W) …`). -/
theorem embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R i1 m)
      = Polynomial.eval₂ (liftToFunctionField (H := H)) (functionFieldT (H := H))
          (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R))) := by
  rw [hasseCoeffRepr𝒪, embeddingOf𝒪Into𝕃_mk, liftBivariate_eq_eval₂_functionFieldT]

/-- The un-cleared `Y ↦ T` embedding of `hasseCoeffRepr𝒪` in shifted Hasse-Taylor
sum form, parallel to `hasseEvalAtRoot_eq_taylorSum` with `T/W` replaced by `T`. -/
theorem embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared_eq_taylorSum
    (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R i1 m)
      = ∑ i ∈ Finset.range ((Bivariate.evalX (Polynomial.C x₀)
              (hasseDerivX i1 (hasseDerivY m R))).natDegree + 1),
          (i + m).choose m
            • (liftToFunctionField (H := H)
                  ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff (i + m))
                * (functionFieldT (H := H)) ^ i) := by
  rw [embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared, Polynomial.eval₂_eq_sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [evalX_hasseDeriv_Y_coeff, map_nsmul (liftToFunctionField (H := H)), smul_mul_assoc]

/-- The per-term equality target asserting that the plain `hasseCoeffRepr𝒪` embedding already
matches the cleared root evaluation.  This is intentionally a named target, not a theorem: #139's
STEP-8 obstruction shows this equality is not available by a uniform per-term scaling argument. -/
def HasseCoeffRepr𝒪UnclearedMatchesRoot (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) : Prop :=
  embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R i1 m)
    = hasseEvalAtRoot H x₀ R i1 m

/-- The named un-cleared/root per-term target is exactly equality of the two shifted
Hasse-Taylor sums, with powers `T^i` on the un-cleared side and `(T/W)^i` on the root side. -/
theorem hasseCoeffRepr𝒪UnclearedMatchesRoot_iff_taylorSums
    (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    HasseCoeffRepr𝒪UnclearedMatchesRoot H x₀ R i1 m ↔
      (∑ i ∈ Finset.range ((Bivariate.evalX (Polynomial.C x₀)
              (hasseDerivX i1 (hasseDerivY m R))).natDegree + 1),
          (i + m).choose m
            • (liftToFunctionField (H := H)
                  ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff (i + m))
                * (functionFieldT (H := H)) ^ i))
        =
        ∑ i ∈ Finset.range ((Bivariate.evalX (Polynomial.C x₀)
              (hasseDerivX i1 (hasseDerivY m R))).natDegree + 1),
          (i + m).choose m
            • (liftToFunctionField (H := H)
                  ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff (i + m))
                * (functionFieldT (H := H)
                    / liftToFunctionField (H := H) H.leadingCoeff) ^ i) := by
  unfold HasseCoeffRepr𝒪UnclearedMatchesRoot
  rw [embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared_eq_taylorSum, hasseEvalAtRoot_eq_taylorSum]

/-- The same per-term target in raw `eval₂` form: `Y ↦ T` equals `Y ↦ T/W` on the specialized
iterated-Hasse coefficient.  This is the exact false-path/mismatch surface identified in #139. -/
def HasseCoeffRepr𝒪UnclearedEval₂Target (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) : Prop :=
  Polynomial.eval₂ (liftToFunctionField (H := H)) (functionFieldT (H := H))
      (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R)))
    =
    Polynomial.eval₂ (liftToFunctionField (H := H))
      (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
      (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R)))

/-- The un-cleared/W-divisor target in embedded-coefficient form.  For a supplied exponent `e`,
it says the cleared root evaluation is the un-cleared `𝒪`-coefficient embedding divided by
`W ^ e`.  The order-zero #139 target specializes this with `(i1, m, e) = (1, 0, R.natDegree)`. -/
def HasseCoeffRepr𝒪UnclearedWDivTarget (x₀ : F) (R : F[X][X][Y])
    (i1 m e : ℕ) : Prop :=
  hasseEvalAtRoot H x₀ R i1 m
    = embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R i1 m)
      / (liftToFunctionField (H := H) H.leadingCoeff) ^ e

/-- The same un-cleared/W-divisor target in raw `eval₂` form:
`Y ↦ T/W` equals `Y ↦ T` divided by `W ^ e` on the specialized iterated-Hasse coefficient. -/
def HasseCoeffRepr𝒪UnclearedEval₂WDivTarget (x₀ : F) (R : F[X][X][Y])
    (i1 m e : ℕ) : Prop :=
  Polynomial.eval₂ (liftToFunctionField (H := H))
      (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
      (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R)))
    =
    Polynomial.eval₂ (liftToFunctionField (H := H)) (functionFieldT (H := H))
      (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R)))
      / (liftToFunctionField (H := H) H.leadingCoeff) ^ e

/-- The embedded-coefficient/root equality is exactly the raw `eval₂ T = eval₂ (T/W)` equality. -/
theorem hasseCoeffRepr𝒪UnclearedMatchesRoot_iff_eval₂Target
    (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    HasseCoeffRepr𝒪UnclearedMatchesRoot H x₀ R i1 m ↔
      HasseCoeffRepr𝒪UnclearedEval₂Target H x₀ R i1 m := by
  unfold HasseCoeffRepr𝒪UnclearedMatchesRoot HasseCoeffRepr𝒪UnclearedEval₂Target
  unfold hasseEvalAtRoot
  rw [embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared]

/-- The embedded un-cleared/W-divisor target is exactly its raw `eval₂` formulation. -/
theorem hasseCoeffRepr𝒪UnclearedWDivTarget_iff_eval₂WDivTarget
    (x₀ : F) (R : F[X][X][Y]) (i1 m e : ℕ) :
    HasseCoeffRepr𝒪UnclearedWDivTarget H x₀ R i1 m e ↔
      HasseCoeffRepr𝒪UnclearedEval₂WDivTarget H x₀ R i1 m e := by
  unfold HasseCoeffRepr𝒪UnclearedWDivTarget HasseCoeffRepr𝒪UnclearedEval₂WDivTarget
  unfold hasseEvalAtRoot
  rw [embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared]

/-- Build the embedded-coefficient/root target from the raw `eval₂` target. -/
theorem HasseCoeffRepr𝒪UnclearedMatchesRoot.of_eval₂Target
    (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ)
    (htarget : HasseCoeffRepr𝒪UnclearedEval₂Target H x₀ R i1 m) :
    HasseCoeffRepr𝒪UnclearedMatchesRoot H x₀ R i1 m :=
  (hasseCoeffRepr𝒪UnclearedMatchesRoot_iff_eval₂Target H x₀ R i1 m).2 htarget

/-- Project the raw `eval₂` target from the embedded-coefficient/root target. -/
theorem HasseCoeffRepr𝒪UnclearedEval₂Target.of_matchesRoot
    (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ)
    (hmatch : HasseCoeffRepr𝒪UnclearedMatchesRoot H x₀ R i1 m) :
    HasseCoeffRepr𝒪UnclearedEval₂Target H x₀ R i1 m :=
  (hasseCoeffRepr𝒪UnclearedMatchesRoot_iff_eval₂Target H x₀ R i1 m).1 hmatch

/-- Build the embedded un-cleared/W-divisor target from the raw `eval₂` W-divisor target. -/
theorem HasseCoeffRepr𝒪UnclearedWDivTarget.of_eval₂WDivTarget
    (x₀ : F) (R : F[X][X][Y]) (i1 m e : ℕ)
    (htarget : HasseCoeffRepr𝒪UnclearedEval₂WDivTarget H x₀ R i1 m e) :
    HasseCoeffRepr𝒪UnclearedWDivTarget H x₀ R i1 m e :=
  (hasseCoeffRepr𝒪UnclearedWDivTarget_iff_eval₂WDivTarget H x₀ R i1 m e).2 htarget

/-- Project the raw `eval₂` W-divisor target from the embedded un-cleared/W-divisor target. -/
theorem HasseCoeffRepr𝒪UnclearedEval₂WDivTarget.of_wDivTarget
    (x₀ : F) (R : F[X][X][Y]) (i1 m e : ℕ)
    (hmatch : HasseCoeffRepr𝒪UnclearedWDivTarget H x₀ R i1 m e) :
    HasseCoeffRepr𝒪UnclearedEval₂WDivTarget H x₀ R i1 m e :=
  (hasseCoeffRepr𝒪UnclearedWDivTarget_iff_eval₂WDivTarget H x₀ R i1 m e).1 hmatch

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared_eq_taylorSum
#print axioms BCIKS20.HenselNumerator.HasseCoeffRepr𝒪UnclearedMatchesRoot
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.hasseCoeffRepr𝒪UnclearedMatchesRoot_iff_taylorSums
#print axioms BCIKS20.HenselNumerator.HasseCoeffRepr𝒪UnclearedEval₂Target
#print axioms BCIKS20.HenselNumerator.HasseCoeffRepr𝒪UnclearedWDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.HasseCoeffRepr𝒪UnclearedEval₂WDivTarget
#print axioms BCIKS20.HenselNumerator.hasseCoeffRepr𝒪UnclearedMatchesRoot_iff_eval₂Target
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.hasseCoeffRepr𝒪UnclearedWDivTarget_iff_eval₂WDivTarget
#print axioms BCIKS20.HenselNumerator.HasseCoeffRepr𝒪UnclearedMatchesRoot.of_eval₂Target
#print axioms BCIKS20.HenselNumerator.HasseCoeffRepr𝒪UnclearedEval₂Target.of_matchesRoot
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.HasseCoeffRepr𝒪UnclearedWDivTarget.of_eval₂WDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.HasseCoeffRepr𝒪UnclearedEval₂WDivTarget.of_wDivTarget
