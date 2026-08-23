/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeightDivisibility
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MatchProof

/-!
# BCIKS20 Appendix A.4 (P1) — monic reduction of the weight invariant to the successor core (#138)

This file lands the **monic-`H` reduction** of the BCIKS20 Appendix A.4 weight invariant
`AlphaGenuineRegularWeightLe` (#138), the P1 analogue of the now-proven monic P2 match
`restrictedFaaDiBrunoMatch_of_monic` (#139).

For monic `H` (`H.leadingCoeff = 1`, the WLOG case of the minimal-polynomial reduction) three of the
four inputs to the assembly lemma `AlphaGenuineRegularWeightLe.of_normalized_divWeight_cases_succLift`
are already discharged, **axiom-clean**:

* the successor **lift identity** `hliftSucc` is `(P2_closed_of_leadingCoeff_one …).2` at order `t+1`
  (proven via the monic P2 match);
* the **base** `h0` (`βHensel 0 = a · W𝒪` with `Λ_𝒪`-weight `≤ 1`) is `βHensel_zero_weight_le_one`
  together with the monic collapse `W𝒪 = 1` (`AlphaWeight.W𝒪_eq_one_of_monic`);
* the `W`-factor of the successor clearing product collapses (`W𝒪 ^ (t+2) = 1`).

Hence the *entire* monic invariant follows from a single remaining obligation: the **successor
divisibility-with-weight core** `SuccDivWeightLe_of_monic` — at every order, `βHensel (t+1)` is
`ξ^{2t+1}`-divisible in `𝒪 H` with a quotient of `Λ_𝒪`-weight `≤ 1`. This is exactly the irreducible
BCIKS20 Newton ξ-order-gain / `Λ(α_t) = 1` regularity claim; it is carried here as an explicit
hypothesis, never an `axiom` or `sorry`. The reduction pins the open #138 obligation (in the monic
case) to this single core, the same way `P2_closed_of_leadingCoeff_one` pinned #139.
-/

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator.AlphaWeight

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
variable {D : ℕ}

/-- **The monic successor divisibility-with-weight obligation — the irreducible #138 core.**
For monic `H` the clearing product collapses to `ξ^{2t+1}`, so the only open content of the
successor divisibility-with-weight is: each `βHensel (t+1)` is `ξ^{2t+1}`-divisible in `𝒪 H` with a
quotient of `Λ_𝒪`-weight `≤ 1`. This is the BCIKS20 Newton ξ-order-gain / weight-1 regularity core;
it is genuinely open (the same weight-`≤-1` wall flagged in `AlphaWeight.lean`). -/
def SuccDivWeightLe_of_monic (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ) : Prop :=
  ∀ t : ℕ, ∃ a : 𝒪 H,
    βHensel H x₀ R hHyp (t + 1) = a * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1)
      ∧ weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1

/-- **Monic reduction of the full A.4 weight invariant (#138) to its successor core.**
For monic `H`, the order-0 invariant, the `W𝒪 = 1` collapse, and the successor lift identity
(`P2_closed_of_leadingCoeff_one`, axiom-clean) are all discharged, so the full
`AlphaGenuineRegularWeightLe` follows from *only* `SuccDivWeightLe_of_monic`. This is the P1 analogue
of the proven monic P2 match: it reduces the remaining #138 obligation in the monic (WLOG) case to
exactly the BCIKS20 Newton ξ-order-gain / weight-1 regularity core, with no `axiom`, no `sorry`. -/
theorem AlphaGenuineRegularWeightLe_of_monic_of_succDivWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hmonic : H.Monic) (hd : 2 ≤ H.natDegree) (hD : D ≤ H.natDegree)
    (hsucc : SuccDivWeightLe_of_monic H x₀ R hHyp hH D) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D := by
  have hlc : H.leadingCoeff = 1 := hmonic
  refine AlphaGenuineRegularWeightLe.of_normalized_divWeight_cases_succLift
    H x₀ R hHyp hH D (fun t => ?_) ?_ (fun t => ?_)
  · exact (BCIKS20.HenselNumerator.P2_closed_of_leadingCoeff_one H x₀ R hHyp hlc).2 (t + 1)
  · refine ⟨βHensel H x₀ R hHyp 0, ?_, βHensel_zero_weight_le_one H x₀ R hHyp hH hd hD⟩
    rw [W𝒪_eq_one_of_monic H hmonic, mul_one]
  · obtain ⟨a, ha, hwt⟩ := hsucc t
    refine ⟨a, ?_, hwt⟩
    rw [W𝒪_eq_one_of_monic H hmonic, one_pow, mul_one]
    exact ha

/-- In the monic regime the proved P2 lift identity transports the P1 carved alpha regularity
predicate to its divisibility-with-weight endpoint. -/
theorem alphaWeight_iff_divWeight_of_monic
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hmonic : H.Monic) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D ↔
      DivWeightLe H x₀ R hHyp hH D := by
  have hlc : H.leadingCoeff = 1 := hmonic
  exact alphaWeight_iff_divWeight_of_succLift H x₀ R hHyp hH D
    (fun t => (BCIKS20.HenselNumerator.P2_closed_of_leadingCoeff_one H x₀ R hHyp hlc).2 (t + 1))

/-- Monic reduction of the explicit successor core directly to the P1 divisibility endpoint. -/
theorem DivWeightLe_of_monic_of_succDivWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hmonic : H.Monic) (hd : 2 ≤ H.natDegree) (hD : D ≤ H.natDegree)
    (hsucc : SuccDivWeightLe_of_monic H x₀ R hHyp hH D) :
    DivWeightLe H x₀ R hHyp hH D :=
  (alphaWeight_iff_divWeight_of_monic H x₀ R hHyp hH hmonic).1
    (AlphaGenuineRegularWeightLe_of_monic_of_succDivWeight
      H x₀ R hHyp hH hmonic hd hD hsucc)

/-- Reverse direction: in the monic regime the normalized `DivWeightLe` successor cases collapse
back to the named successor core because `W𝒪 = 1`. -/
theorem SuccDivWeightLe_of_monic_of_divWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hmonic : H.Monic) (hdiv : DivWeightLe H x₀ R hHyp hH D) :
    SuccDivWeightLe_of_monic H x₀ R hHyp hH D := by
  intro t
  rcases (DivWeightLe.normalized_cases H x₀ R hHyp hH D hdiv).2 t with ⟨a, ha, hwt⟩
  refine ⟨a, ?_, hwt⟩
  simpa [W𝒪_eq_one_of_monic H hmonic] using ha

/-- In the monic/degree-budget regime, the named successor core is exactly the existing
divisibility-with-weight endpoint. -/
theorem succDivWeightLe_iff_divWeightLe_of_monic
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hmonic : H.Monic) (hd : 2 ≤ H.natDegree) (hD : D ≤ H.natDegree) :
    SuccDivWeightLe_of_monic H x₀ R hHyp hH D ↔
      DivWeightLe H x₀ R hHyp hH D := by
  exact ⟨DivWeightLe_of_monic_of_succDivWeight H x₀ R hHyp hH hmonic hd hD,
    SuccDivWeightLe_of_monic_of_divWeight H x₀ R hHyp hH hmonic⟩

/-- In the monic/degree-budget regime, carved alpha regularity is equivalent to the named
successor divisibility-with-weight core. -/
theorem alphaWeight_iff_succDivWeightLe_of_monic
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hmonic : H.Monic) (hd : 2 ≤ H.natDegree) (hD : D ≤ H.natDegree) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D ↔
      SuccDivWeightLe_of_monic H x₀ R hHyp hH D := by
  constructor
  · intro hα
    exact SuccDivWeightLe_of_monic_of_divWeight H x₀ R hHyp hH hmonic
      ((alphaWeight_iff_divWeight_of_monic H x₀ R hHyp hH hmonic).1 hα)
  · intro hsucc
    exact AlphaGenuineRegularWeightLe_of_monic_of_succDivWeight
      H x₀ R hHyp hH hmonic hd hD hsucc

/-- Normalized P1 divisibility cases obtained from the monic successor core. -/
theorem normalized_divWeight_cases_of_monic_of_succDivWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hmonic : H.Monic) (hd : 2 ≤ H.natDegree) (hD : D ≤ H.natDegree)
    (hsucc : SuccDivWeightLe_of_monic H x₀ R hHyp hH D) :
      (∃ a : 𝒪 H,
        βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
          weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) ∧
        ∀ t : ℕ, ∃ a : 𝒪 H,
          βHensel H x₀ R hHyp (t + 1)
            = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
            weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  DivWeightLe.normalized_cases H x₀ R hHyp hH D
    (DivWeightLe_of_monic_of_succDivWeight H x₀ R hHyp hH hmonic hd hD hsucc)

/-- The monic successor core packages into the existing structured prefix invariant endpoint. -/
theorem βHenselStructuredWeightInvariant_of_monic_of_succDivWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hmonic : H.Monic) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hsucc : SuccDivWeightLe_of_monic H x₀ R hHyp hH D) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k := by
  have hlc : H.leadingCoeff = 1 := hmonic
  exact βHenselStructuredWeightInvariant_of_alphaWeight_succLift' H x₀ R hHyp hH
    hDH hDRx0 hdR2
    (fun u => (BCIKS20.HenselNumerator.P2_closed_of_leadingCoeff_one H x₀ R hHyp hlc).2 (u + 1))
    (AlphaGenuineRegularWeightLe_of_monic_of_succDivWeight
      H x₀ R hHyp hH hmonic hd hD hsucc)
    k

/-- All-prefix structured invariant endpoint obtained from the monic successor core. -/
theorem βHenselStructuredWeightInvariant_all_of_monic_of_succDivWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hmonic : H.Monic) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hsucc : SuccDivWeightLe_of_monic H x₀ R hHyp hH D) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_of_monic_of_succDivWeight
      H x₀ R hHyp hH hmonic hd hD hDH hDRx0 hdR2 hsucc k

/-- The monic successor core feeds the existing P1 beta-weight endpoint, with the `ξ` side
condition discharged by `ClaimA2.weight_ξ_bound`. -/
theorem βHensel_weight_bound_of_monic_of_succDivWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hmonic : H.Monic) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hsucc : SuccDivWeightLe_of_monic H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) := by
  have hlc : H.leadingCoeff = 1 := hmonic
  exact βHensel_weight_bound_of_alphaWeight_succLift' H x₀ R hHyp hH
    hDH hDRx0 hdR2 hdHR hW
    (fun u => (BCIKS20.HenselNumerator.P2_closed_of_leadingCoeff_one H x₀ R hHyp hlc).2 (u + 1))
    (AlphaGenuineRegularWeightLe_of_monic_of_succDivWeight
      H x₀ R hHyp hH hmonic hd hD hsucc)
    t

/-- All-order beta-weight endpoint obtained from the monic successor core. -/
theorem βHensel_weight_bound_all_of_monic_of_succDivWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hmonic : H.Monic) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hsucc : SuccDivWeightLe_of_monic H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_of_monic_of_succDivWeight H x₀ R hHyp hH hmonic hd
      hD hDH hDRx0 hdR2 hdHR hW hsucc t

end BCIKS20.HenselNumerator.AlphaWeight

/-! ## Source audit -/
#print axioms
  BCIKS20.HenselNumerator.AlphaWeight.AlphaGenuineRegularWeightLe_of_monic_of_succDivWeight
#print axioms
  BCIKS20.HenselNumerator.AlphaWeight.alphaWeight_iff_divWeight_of_monic
#print axioms
  BCIKS20.HenselNumerator.AlphaWeight.DivWeightLe_of_monic_of_succDivWeight
#print axioms
  BCIKS20.HenselNumerator.AlphaWeight.SuccDivWeightLe_of_monic_of_divWeight
#print axioms
  BCIKS20.HenselNumerator.AlphaWeight.succDivWeightLe_iff_divWeightLe_of_monic
#print axioms
  BCIKS20.HenselNumerator.AlphaWeight.alphaWeight_iff_succDivWeightLe_of_monic
#print axioms
  BCIKS20.HenselNumerator.AlphaWeight.normalized_divWeight_cases_of_monic_of_succDivWeight
#print axioms
  BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_of_monic_of_succDivWeight
#print axioms
  BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_all_of_monic_of_succDivWeight
#print axioms
  BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_monic_of_succDivWeight
#print axioms
  BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_all_of_monic_of_succDivWeight
