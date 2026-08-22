/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.CoeffExtraction

/-!
# CoeffExtractionResidual

Module docstring for `CoeffExtractionResidual.lean`.
-/


namespace ProximityGap

set_option linter.unusedSectionVars false

open NNReal Finset Function ProbabilityTheory Code Polynomial
open scoped BigOperators LinearCode ProbabilityTheory ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Geometric form of the strict-Johnson coefficient-polynomial residual.**

Instead of asserting (algebraically) that the decoded coefficients are low-degree polynomials,
this asserts (geometrically) that the decoded family `P` admits `k+1` sample parameters whose
decodings share a `≥ deg`-size common agreement set with `P z` at every good parameter `z`.

This is the genuinely deep content of [BCIKS20] §6: in the regime `(1-ρ)/2 < δ < 1-√ρ`, the
decoded family is forced onto a single global low-degree bivariate structure, so the agreement
sets of different parameters overlap on `≥ deg` points. The algebraic conclusion follows from
this geometric one by pure Lagrange interpolation (`RS_coeffPolys_of_commonAgreement`). -/
def CurveCommonAgreementResidual {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} : Prop :=
  ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
    Pr_{
      let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
        ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
    (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
    δ < 1 - ReedSolomon.sqrtRate deg domain →
    ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
      ∃ s : Fin (k + 1) → F, Function.Injective s ∧
        (∀ i, s i ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∃ S : Finset ι, deg ≤ S.card ∧
            (∀ x ∈ S, (P z).eval (domain x) = ∑ t : Fin (k + 1), (z ^ (t : ℕ)) * u t x) ∧
            (∀ i : Fin (k + 1), ∀ x ∈ S, (P (s i)).eval (domain x)
                = ∑ t : Fin (k + 1), ((s i) ^ (t : ℕ)) * u t x)

/-- **The strict-Johnson coefficient-polynomial residual reduces to its geometric form.**

The opaque algebraic residual `StrictCoeffPolysResidual` (decoded coefficients are degree-`≤k`
polynomials in the curve parameter) follows from the transparent geometric residual
`CurveCommonAgreementResidual` (the decoded family has large common agreement with `k+1` sampled
decodings), via the bivariate Lagrange lift `RS_coeffPolys_of_commonAgreement`. This isolates
the genuinely deep BCIKS Johnson-radius counting (the common agreement) from the mechanical
interpolation, which is fully discharged. -/
theorem strictCoeffPolysResidual_of_commonAgreement {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (h : CurveCommonAgreementResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  obtain ⟨s, hsinj, hsG, hCommon⟩ := h hk u hprob hJ hsqrt P hP
  exact RS_coeffPolys_of_commonAgreement u P s hsinj (fun z hz => (hP z hz).1) hsG hCommon

end ProximityGap
