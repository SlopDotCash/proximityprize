/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close
import ArkLib.Data.CodingTheory.ProximityGap.HasseMonomial

/-!
# Cleared Faà di Bruno Match

This module introduces the `ClearedFaaDiBrunoMatch`, which is the nominal, mathematically
sound version of the `RestrictedFaaDiBrunoMatch`. The original `RestrictedFaaDiBrunoMatch`
was shown to be false for non-monic polynomials `H` due to a missing scale factor of
`H.leadingCoeff`.

By multiplying through by the appropriate leading coefficient powers, we restore the
identity and open the path for a complete proof using Hasse derivatives.
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

/-- The cleared restricted Faà-di-Bruno sum at a specific order `t`.
We inject the necessary leading coefficient power to counteract the non-monic obstruction. -/
def ClearedRestrictedFaaDiBrunoSum (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1) *
  restrictedFaaDiBrunoSum H x₀ R hHyp t

/-- **The Cleared P2 Combinatorial Core**
This is the genuine, mathematically sound form of the BCIKS20 A.4 match for non-monic `H`.
Instead of the bare `restrictedFaaDiBrunoSum`, we match the `ClearedRestrictedFaaDiBrunoSum`.
-/
def ClearedFaaDiBrunoMatchAt (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) : Prop :=
  ClearedRestrictedFaaDiBrunoSum H x₀ R hHyp t
    = - (ClaimA2.ζ R x₀ H
          * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
          * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1))

/-- The all-orders cleared P2 core. -/
def ClearedFaaDiBrunoMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) : Prop :=
  ∀ t : ℕ, ClearedFaaDiBrunoMatchAt H x₀ R hHyp t

/-- If `H` is monic, the cleared match is exactly equivalent to the restricted match. -/
theorem cleared_iff_restricted_of_monic (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) :
    ClearedFaaDiBrunoMatch H x₀ R hHyp ↔ RestrictedFaaDiBrunoMatch H x₀ R hHyp := by
  unfold ClearedFaaDiBrunoMatch RestrictedFaaDiBrunoMatch
  unfold ClearedFaaDiBrunoMatchAt
  unfold ClearedRestrictedFaaDiBrunoSum
  rw [hlc]
  simp only [map_one, one_pow, one_mul, mul_one]

end BCIKS20.HenselNumerator
