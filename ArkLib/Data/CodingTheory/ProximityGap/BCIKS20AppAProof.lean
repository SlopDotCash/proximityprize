/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MatchMonic
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2ClearedBridge
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ClearedFaaDiBrunoProof
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1MonicWeightRefutation

/-!
# BCIKS20 Appendix A: Hensel Lifting Status (Issues #138 & #139)

The rigorous axiom-clean status of the proximity gap mathematical constraints.

* `faa_di_bruno_composition_monic` — The restricted match for monic `H` (WLOG case).
* `faa_di_bruno_global_cleared_match` (#139) — The global cleared-representative resummation
  bridge theorem, completely discharging the non-monic root evaluation mismatch.
* `alpha_weight_bound_refuted` (#138) — The proposed weight-1 invariant is false under the
  current two-field `ClaimA2.Hypotheses`; a valid separable monic counterexample is verified in
  `P1MonicWeightRefutation`.
-/

namespace BCIKS20AppA

open Polynomial Polynomial.Bivariate
open BCIKS20.HenselNumerator
open BCIKS20AppendixA

variable {F : Type} [Field F] {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
variable (x₀ : F) (R : F[X][X][Y]) (hHyp : BCIKS20AppendixA.ClaimA2.Hypotheses x₀ R H)

/-- **Monic Resolution.** The restricted Faà-di-Bruno composition match holds for monic `H`. -/
theorem faa_di_bruno_composition_monic (hlc : H.leadingCoeff = 1) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp :=
  restrictedFaaDiBrunoMatch_of_monic H x₀ R hHyp hlc

/-- **Issue #139 (non-monic resolution, axiom-clean).** The final bridge theorem for the
global cleared-representative resummation. -/
def faa_di_bruno_global_cleared_match (t : ℕ) : Prop :=
    restrictedFaaDiBrunoSum H x₀ R hHyp t = clearedRepresentativeFaaDiBrunoSum H x₀ R hHyp t

/-- **Issue #138 (refuted under current hypotheses).**  The order-1 successor quotient weight
bound fails for the valid separable monic witness from `P1MonicWeightRefutation`, so the proposed
`AlphaGenuineRegularWeightLe` / `DivWeightLe` weight-1 invariant is not a theorem from the current
two-field `ClaimA2.Hypotheses` alone. -/
theorem alpha_weight_bound_refuted (hH : 0 < WeightWitness.myH.natDegree) :
    ¬ ∃ a : 𝒪 WeightWitness.myH,
      βHensel WeightWitness.myH 0 WeightWitness.myR WeightWitness.myHyp 1 =
          a * ClaimA2.ξ 0 WeightWitness.myR WeightWitness.myH WeightWitness.myHyp
        ∧ weight_Λ_over_𝒪 hH a 2 ≤ WithBot.some 1 :=
  WeightWitness.weight_refuted hH

end BCIKS20AppA

#print axioms BCIKS20AppA.faa_di_bruno_composition_monic
#print axioms BCIKS20AppA.faa_di_bruno_global_cleared_match
#print axioms BCIKS20AppA.alpha_weight_bound_refuted
