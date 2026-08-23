/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Agreement

/-!
# hlin end-to-end — heavy monic branches are `Y`-linear, from GS surface data (#302)

The terminal composition of the geometric hlin route: **one theorem** from the named GS-side
data to the curve collapse.  Consumes:

* the decoded GS surface `w` (`(Y′ − C w) ∣ R`, per-place base-point roots, `R.Separable`,
  per-place `ξ_z ≠ 0`) — the S4/S10 outputs;
* the coefficient tail `αGenuine t = 0` for `t ≥ n` — the in-tree truncation capstones;
* the **proximity agreement** at `n` distinct heavy Reed–Solomon coordinates `ω j`:
  `w(ω j)(z) = u₀ j + z·u₁ j` on the per-coordinate matching sets — the fold-decoding data;
* the graded weight side conditions and the heavy cardinality
  `killBudget·d_H < |matchingSet j|` — the `Hab25HeavyPoints` budget.

Conclusion: `H.natDegree = 1` (`natDegree_eq_one_of_decoded_heavy`), equivalently the
`d_H ≥ 2` contradiction (`false_of_decoded_heavy_of_two_le`) — **hlin**: no per-`z` decoded
root lives on a `Y`-degree ≥ 2 monic branch.  [BCIKS20] §5 Steps 5–7 / [Hab25] Claim 1.

## References

* [BCIKS20] ePrint 2020/654 — §5.2.5–5.2.7, Appendix A.
* [Hab25] ePrint 2025/2110 — Claim 1.
-/

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open BCIKS20.Claim510Kill BCIKS20.Claim510Supply BCIKS20.Claim510Agreement
open ProximityPrize.BCIKS20.GammaGenuine

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

namespace BCIKS20.Claim510EndToEnd

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
variable {x₀ : F} {R : F[X][X][Y]}

/-- **hlin end-to-end (collapse form).**  From the decoded GS surface data, the coefficient
tail, the proximity agreement at `n` distinct heavy coordinates, the graded weight side
conditions, and the heavy cardinality: `H.natDegree = 1`. -/
theorem natDegree_eq_one_of_decoded_heavy [Fintype F]
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    -- the decoded GS surface
    {w : F[X][Y]} {n : ℕ} (hwn : w.natDegree < n)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hR : R.Separable)
    -- the coefficient tail (Claim 5.8′, in-tree truncation capstones)
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    -- the `n` heavy coordinates and the words
    (ω : Fin n → F) (hω : Function.Injective ω) (u₀ u₁ : Fin n → F)
    -- per-coordinate matching sets with the per-place GS data + proximity agreement
    (matchingSet : Fin n → Finset F)
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ j, ∀ z ∈ matchingSet j, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    (hbase : ∀ j, ∀ z ∈ matchingSet j, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hprox : ∀ j, ∀ z ∈ matchingSet j,
      (w.eval (Polynomial.C (ω j))).eval z = u₀ j + z * u₁ j)
    -- the graded weight side conditions
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {xw : ℕ}
    (hξw : weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
      (ξ x₀ R H hHyp) D ≤ (WithBot.some xw : WithBot ℕ))
    -- the heavy cardinality
    (hcard : ∀ j, killBudget n D H.natDegree (Bivariate.natDegreeY R) xw * H.natDegree
      < (matchingSet j).card) :
    H.natDegree = 1 := by
  -- the injective node family `e j := ω j − x₀`
  have he : Function.Injective (fun j => ω j - x₀) := fun a b hab => hω (by
    have := congrArg (· + x₀) hab
    simpa using this)
  refine natDegree_eq_one_of_heavy_agreement H x₀ R hHyp hlc htail
    (fun j => ω j - x₀) he u₀ u₁ hD matchingSet ?_ ?_ hcard
  · -- the agreement, from the decoded surface (per coordinate)
    intro j
    exact agreement_of_decoded hHyp hξ hlc hwn root (hx j) hdvd (hbase j) hR
      (ω j) (u₀ j) (u₁ j) (hprox j)
  · -- the weight bound (uniform over coordinates)
    intro j
    exact weight_killTarget_le H x₀ R hHyp hD (Fact.out (p := 0 < H.natDegree))
      hmonic hd2 hdHD hD_Rx0 hRgrade hξw n (ω j - x₀) (u₀ j) (u₁ j)

/-- **hlin end-to-end (contradiction form).**  No `Y`-degree ≥ 2 monic branch carries the
decoded heavy data: per-`z` decoded roots cannot hide in a `Y`-degree ≥ 2 factor. -/
theorem false_of_decoded_heavy_of_two_le [Fintype F]
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (hdeg : 2 ≤ H.natDegree)
    {w : F[X][Y]} {n : ℕ} (hwn : w.natDegree < n)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hR : R.Separable)
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (ω : Fin n → F) (hω : Function.Injective ω) (u₀ u₁ : Fin n → F)
    (matchingSet : Fin n → Finset F)
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ j, ∀ z ∈ matchingSet j, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    (hbase : ∀ j, ∀ z ∈ matchingSet j, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hprox : ∀ j, ∀ z ∈ matchingSet j,
      (w.eval (Polynomial.C (ω j))).eval z = u₀ j + z * u₁ j)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {xw : ℕ}
    (hξw : weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
      (ξ x₀ R H hHyp) D ≤ (WithBot.some xw : WithBot ℕ))
    (hcard : ∀ j, killBudget n D H.natDegree (Bivariate.natDegreeY R) xw * H.natDegree
      < (matchingSet j).card) :
    False := by
  have h1 := natDegree_eq_one_of_decoded_heavy hHyp hξ hlc hwn hdvd hR htail ω hω u₀ u₁
    matchingSet root hx hbase hprox hD hmonic hd2 hdHD hD_Rx0 hRgrade hξw hcard
  omega

end BCIKS20.Claim510EndToEnd

/-! ## Axiom audit -/
#print axioms BCIKS20.Claim510EndToEnd.natDegree_eq_one_of_decoded_heavy
#print axioms BCIKS20.Claim510EndToEnd.false_of_decoded_heavy_of_two_le
