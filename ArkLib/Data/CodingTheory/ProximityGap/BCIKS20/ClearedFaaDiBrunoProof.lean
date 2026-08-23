/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ClearedFaaDiBruno
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MatchMonic

/-!
# Cleared Faà di Bruno Match — honest status

The previous content of this file was a placeholder: a vacuous `MonomialPartitionBijection`
(`∀ i, ∃ b, b = b`), an `X = X` "Fubini" lemma, and a `sorry`-terminated
`clearedFaaDiBrunoMatch_monomial`. None of it proved anything. This module replaces that with the
genuine, axiom-clean facts.

**Key correction.** `ClearedFaaDiBrunoMatchAt` (see `ClearedFaaDiBruno.lean`) multiplies *both*
sides of `RestrictedFaaDiBrunoMatchAt` by `liftToFunctionField H.leadingCoeff ^ (t+1)`. Since
`H.leadingCoeff ≠ 0` (H irreducible, positive degree) that factor is a unit in `𝕃 H`, so the cleared
match is **logically equivalent to the restricted match for every `H`** (`cleared_iff_restricted`),
*not just monic ones*. Therefore the cleared form does NOT independently repair the non-monic
obstruction — it inherits the restricted match's truth value verbatim. The genuine non-monic repair
remains the global cleared-representative resummation (the open content of #139).

* `cleared_iff_restricted` — the cleared match ⟺ the restricted match, for all `H` (cancel the unit).
* `clearedFaaDiBrunoMatch_of_monic` — the cleared match holds for monic `H` (the real, relevant
  case), via the equivalence and the proven `restrictedFaaDiBrunoMatch_of_monic`.
-/

noncomputable section

open scoped BigOperators
open Polynomial Polynomial.Bivariate
open ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The cleared match is logically equivalent to the restricted match for **every** `H`: the
clearing factor `liftToFunctionField H.leadingCoeff ^ (t+1)` is a nonzero unit in `𝕃 H`, so it
cancels on both sides. Consequently the cleared form does not, on its own, repair the non-monic
obstruction — it has the same truth value as the restricted match. -/
theorem cleared_iff_restricted (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    ClearedFaaDiBrunoMatch H x₀ R hHyp ↔ RestrictedFaaDiBrunoMatch H x₀ R hHyp := by
  have hw : (liftToFunctionField (H := H) H.leadingCoeff) ≠ 0 :=
    liftToFunctionField_leadingCoeff_ne_zero (H := H)
  -- `RestrictedFaaDiBrunoMatch` is defined directly via `restrictedFaaDiBrunoSum` (no longer through
  -- `RestrictedFaaDiBrunoMatchAt`), so that name is not in the goal — dropped from the unfold list.
  unfold ClearedFaaDiBrunoMatch RestrictedFaaDiBrunoMatch
    ClearedFaaDiBrunoMatchAt ClearedRestrictedFaaDiBrunoSum
  constructor
  · intro h t
    have ht := h t
    have hcancel : (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
        * restrictedFaaDiBrunoSum H x₀ R hHyp t
      = (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
        * (-(ClaimA2.ζ R x₀ H * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp))) := by
      rw [ht]; ring
    exact mul_left_cancel₀ (pow_ne_zero _ hw) hcancel
  · intro h t
    have ht := h t
    rw [ht]; ring

/-- The cleared Faà-di-Bruno match holds for monic `H` (the genuinely-relevant case): combine the
all-`H` equivalence with the proven monic restricted match `restrictedFaaDiBrunoMatch_of_monic`. -/
theorem clearedFaaDiBrunoMatch_of_monic (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) :
    ClearedFaaDiBrunoMatch H x₀ R hHyp :=
  (cleared_iff_restricted H x₀ R hHyp).mpr
    (restrictedFaaDiBrunoMatch_of_monic H x₀ R hHyp hlc)

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.cleared_iff_restricted
#print axioms BCIKS20.HenselNumerator.clearedFaaDiBrunoMatch_of_monic
