/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.ToMathlib.BetaToCurveCoeffPolys
import ArkLib.ToMathlib.BCIKS20PointwiseConditional
import ArkLib.ToMathlib.CorrelatedAgreementListDecodingClosed

/-!
# BetaRec-Built Power Series and Correlated Agreement Integration

This module defines the power series $\gamma'$ constructed directly from the Hensel
recurrence relation $\text{betaRec}$, and establishes its relation to the in-tree power
series $\gamma$. This provides the integration bridge for correlated agreement proofs in
Section 5 of [BCIKS20].

## Mathematical Context

Let $F$ be a field and $H \in F[X][Y]$ be an irreducible polynomial. The power series
$\gamma'$ is defined by substituting the shift series $X \mapsto X - x_0$ into the series
$\alpha_{\mathrm{fromBeta}}$, whose coefficients are given by:
$$\alpha_{\mathrm{fromBeta}}(t) = \frac{\phi(\text{betaRec}(t))}{W^{t+1} \cdot \xi^{e_t}}$$
where $\phi: \mathcal{O}_H \to \mathbb{L}_H$ is the canonical embedding.

We show that if the opaque in-tree numerator $\beta(t)$ coincides with the recurrence
$\text{betaRec}(t)$, then the in-tree coefficients $\alpha(t)$ coincide with
$\alpha_{\mathrm{fromBeta}}(t)$, and hence the power series $\gamma$ is equal to $\gamma'$.
This allows us to automatically satisfy the power series substitution relation needed for
the correlated agreement list-decoding results.

## Key Formalizations
* `γ'`: The power series constructed from the $\text{betaRec}$ coefficients.
* `alpha_eq_alphaFromBeta_of_betaEq`: pointwise equivalence of the coefficients under
  numerator identification.
* `intree_gamma_eq_γ'`: equivalence of the power series $\gamma$ and $\gamma'$.
* `section5StrictData_of_betaEq`: A constructor for the Section 5 correlated agreement data
  that automatically discharges the substitution relation given numerator equivalence.

## References
* [BCIKS20] Binswood, Crites, Iyer, Kamara, Stewart. *Solving Algebraic Equations over
  Power Series*, 2020.
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal

namespace ArkLib

namespace GammaFromBeta

variable {F : Type} [Field F]

/-! ### Definition of the betaRec-Built Power Series -/

/-- The power series $\gamma'$ constructed by substituting the shift series into the power series
whose coefficients are $\alpha_{\mathrm{fromBeta}}$. -/
noncomputable def γ' (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) : PowerSeries (𝕃 H) :=
  (PowerSeries.mk (BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff)).subst
    (Claim59Conditional.shiftSeries x₀ H)

/-- Definitional lemma for $\gamma'$ showing it is equal to the shift substitution. -/
theorem γ'_eq_subst_shiftSeries (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) :
    γ' x₀ R H hHyp Bcoeff =
      (PowerSeries.mk (BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff)).subst
        (Claim59Conditional.shiftSeries x₀ H) :=
  rfl

/-! ### Equivalence Under Numerator Identification -/

/-- Pointwise equivalence of the coefficients $\alpha_t$ and $\alpha_{\mathrm{fromBeta}, t}$
assuming the in-tree numerators $\beta(t)$ match the recurrence relation $\text{betaRec}(t)$. -/
theorem alpha_eq_alphaFromBeta_of_betaEq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hβ : ∀ t, β (H := H) R t = betaRec x₀ R H hHyp Bcoeff t) (t : ℕ) :
    α x₀ R H hHyp t = BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t := by
  unfold α BetaToCurveCoeffPolys.αFromBeta
  rw [hβ t]

/-- Equivalence of the in-tree power series $\gamma$ and the constructed series $\gamma'$
under numerator identification. -/
theorem intree_gamma_eq_γ' (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hβ : ∀ t, β (H := H) R t = betaRec x₀ R H hHyp Bcoeff t) :
    γ x₀ R H hHyp = γ' x₀ R H hHyp Bcoeff := by
  rw [Claim59Conditional.gamma_eq_subst_shiftSeries, γ']
  congr 1
  exact PowerSeries.ext fun n => by
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      alpha_eq_alphaFromBeta_of_betaEq x₀ R H hHyp Bcoeff hβ]

/-- Proves the substitution relation required for Section 5 correlated agreement from the
numerator identification. -/
theorem hγ_field_of_betaEq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hβ : ∀ t, β (H := H) R t = betaRec x₀ R H hHyp Bcoeff t) :
    γ x₀ R H hHyp =
      (PowerSeries.mk (BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff)).subst
        (Claim59Conditional.shiftSeries x₀ H) := by
  rw [intree_gamma_eq_γ' x₀ R H hHyp Bcoeff hβ, γ'_eq_subst_shiftSeries]

end GammaFromBeta

/-! ### Section 5 Correlated Agreement Data Builder -/

section Builder

open BetaToCurveCoeffPolys Claim59Conditional
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace CorrelatedAgreementListDecodingClosed

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Constructor for the Section 5 correlated agreement data.
Takes the numerator equivalence $\beta(t) = \text{betaRec}(t)$ as a hypothesis and
automatically supplies the required substitution relation for the power series $\gamma$. -/
noncomputable def section5StrictData_of_betaEq {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hIrr : Fact (Irreducible H)) (hPos : Fact (0 < H.natDegree))
    (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (matchingSet : Finset F) (root : (z : F) → rationalRoot (H_tilde' H) z)
    (mp : ∀ t, k ≤ t → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z))
    (hcard : ∀ t, k ≤ t → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree)
    (hsubst : PowerSeries.HasSubst (shiftSeries x₀ H))
    -- the honest residual replacing the `hγ` field:
    (hβ : ∀ t, β (H := H) R t = betaRec x₀ R H hHyp Bcoeff t)
    (Ppoly : F[X][Y]) (hrep : polyToPowerSeries𝕃 H Ppoly = γ x₀ R H hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (hPz : ∀ v₀ v₁ : F[X],
      γ x₀ R H hHyp = polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀) + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ, P z =
        ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval (Polynomial.C z))
        ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    Section5StrictData (k := k) (deg := deg) (domain := domain) (δ := δ) u P where
  x₀ := x₀
  R := R
  H := H
  hIrr := hIrr
  hPos := hPos
  hHyp := hHyp
  Bcoeff := Bcoeff
  hH := hH
  D := D
  hD := hD
  matchingSet := matchingSet
  root := root
  mp := mp
  hcard := hcard
  hsubst := hsubst
  hγ := GammaFromBeta.hγ_field_of_betaEq x₀ R H hHyp Bcoeff hβ
  Ppoly := Ppoly
  hrep := hrep
  hdegX := hdegX
  hPz := hPz

end CorrelatedAgreementListDecodingClosed

end Builder

end ArkLib


