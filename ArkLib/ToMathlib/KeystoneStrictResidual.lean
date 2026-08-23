/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.ToMathlib.BetaToCurveCoeffPolys
import ArkLib.ToMathlib.BetaToCurveCoeffPolysOffcentre
import ArkLib.ToMathlib.HcardDischarge

/-!
# Keystone Front-Door Wiring for Strict Coefficient Polynomials

This module formalizes the integration of the $\text{betaRec}$-based power series reconstruction
into the strict coefficient polynomial residual required by the correlated agreement front-door
theorem (`ProximityGap.correlatedAgreement_affine_curves`).

## Mathematical Context

Let $C \subset F^\iota$ be a Reed-Solomon code of rate $\rho$. In the list-decoding proximity gap
reduction, the strict Johnson-radius branch assumes that the coefficient polynomials of the decoded
families are bounded in degree. This property is formalised by the `StrictCoeffPolysResidual`
predicate.

We show that under the $\text{betaRec}$ input configuration (which bundles the specialized
Guruswami-Sudan factor multiplicities and Hensel-lifted recurrences), the pointwise curve-polynomial
datum:
$$\forall j < \text{deg}, \exists B_j \in F[X], \quad \text{deg}(B_j) < k+1$$
$$\text{and} \quad \forall z \in S, \quad P_z(j) = B_j(z)$$
can be bundled into a single polynomial map $B: \mathbb{N} \to F[X]$ satisfying the joint degree and
evaluation bounds demanded by the correlated agreement curves front door.

We formalize both the infinite-range input configuration (`BetaCurveInput`) and its F5-corrected,
satisfiable finite-range counterpart (`BetaCurveInputFin`), proving that the latter successfully
avoids cardinality bounds issues on the matching sets.

## Key Formalizations
* `hcoeffPoly_witness_of_betaRecCurveCoeffPolys`: Bundles the per-index coefficient polynomial
  existentials into a single witness map.
* `BetaCurveInput`: Input configuration for the infinite-range matching bounds.
* `BetaCurveInputFin`: Satisfiable finite-range input configuration incorporating tail-degree
  truncation.
* `hcoeffPoly_of_betaRecFin`: Proves the coefficient polynomial bounds from the finite-range input
  configuration.
* `strictCoeffPolysResidual_of_betaRecFin`: Discharges the strict coefficient polynomial residual
  from the finite-range input.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement), Appendix A.4 (the `W`-power-numerator recursion (A.1)).
-/

-- This file is documentation-heavy (extended BCIKS §5 prose in the docstrings); the long-line
-- style linter is disabled locally, matching the sibling `BetaToCurveCoeffPolys.lean`.
set_option linter.style.longLine false

-- The keystone wrapper carries `[DecidableEq ι]` because `correlatedAgreement_affine_curves`'s
-- proof needs it.
set_option linter.unusedDecidableInType false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Polynomial Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace KeystoneStrictResidual

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ### Bundling Per-Coefficient Existentials -/

omit [Nonempty ι] [DecidableEq ι] [Fintype ι] [Fintype F] [DecidableEq F] in
/-- Bundling lemma showing that a collection of per-index coefficient polynomials can be packaged
into a single map. -/
theorem hcoeffPoly_witness_of_betaRecCurveCoeffPolys
    {k deg : ℕ} {good : Finset F} {P : F → Polynomial F}
    (hCurve : BetaToCurveCoeffPolys.CurveCoeffPolys (F := F) k deg good P) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ good, ∀ j < deg, (P z).coeff j = (B j).eval z := by
  classical
  refine ⟨fun j => if h : j < deg then (hCurve j h).choose else 0, ?_, ?_⟩
  · intro j hj
    simp only [hj, dif_pos]
    exact (hCurve j hj).choose_spec.1
  · intro z hz j hj
    simp only [hj, dif_pos]
    exact (hCurve j hj).choose_spec.2 z hz

/-! ### Infinite-Range Input Configuration -/

/-- BCIKS Section 5 input configuration for infinite-range matching bounds. -/
structure BetaCurveInput {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) : Type 1 where
  x₀ : F
  R : F[X][X][Y]
  H : F[X][Y]
  [hHirr : Fact (Irreducible H)]
  [hHpos : Fact (0 < H.natDegree)]
  hHyp : Hypotheses x₀ R H
  Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H
  hH : 0 < H.natDegree
  D : ℕ
  hD : D ≥ Bivariate.totalDegree H
  matchingSet : Finset F
  root : (z : F) → rationalRoot (H_tilde' H) z
  hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ H)
  hγ : γ x₀ R H hHyp =
    (PowerSeries.mk (BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff)).subst
      (Claim59Conditional.shiftSeries x₀ H)
  Ppoly : F[X][Y]
  hrep : polyToPowerSeries𝕃 H Ppoly = γ x₀ R H hHyp
  hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1
  mp : ∀ t, k ≤ t → ∀ z ∈ matchingSet,
    BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z)
  hcard : ∀ t, k ≤ t → (↑matchingSet.card : WithBot ℕ)
    > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree
  hPz : ∀ (P : F → Polynomial F) (v₀ v₁ : F[X]),
    γ x₀ R H hHyp = polyToPowerSeries𝕃 H
      ((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
    (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ, P z =
      ((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval (Polynomial.C z))
      ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1

attribute [instance] BetaCurveInput.hHirr BetaCurveInput.hHpos

omit [Nonempty ι] [DecidableEq ι] in
/-- Proves the existence of the coefficient polynomial map under the infinite-range input
configuration. -/
theorem hcoeffPoly_of_betaRec
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι}
    (inp : BetaCurveInput (k := k) (deg := deg) (domain := domain) (δ := δ) u)
    (P : F → Polynomial F) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ j < deg, (P z).coeff j = (B j).eval z := by
  have hCurve :
      BetaToCurveCoeffPolys.CurveCoeffPolys (F := F) k deg
        (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) P :=
    BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec
      inp.x₀ inp.R inp.H inp.hHyp inp.Bcoeff inp.hH inp.D inp.hD
      (matchingSet := inp.matchingSet) (root := inp.root)
      (inp.mp) (inp.hcard) inp.hsubst inp.hγ
      (Ppoly := inp.Ppoly) inp.hrep inp.hdegX
      (inp.hPz P)
  exact hcoeffPoly_witness_of_betaRecCurveCoeffPolys hCurve

omit [Nonempty ι] [DecidableEq ι] in
/-- Off-centre `betaRec` route to the bundled coefficient-polynomial witness.

This is the `gammaLocal`/Taylor-shift counterpart of `hcoeffPoly_of_betaRec`: it consumes the
off-centre representative and specialization bridge required by
`BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec_offcentre`, then reuses the same bundling lemma
to expose the front-door `hcoeffPoly` existential. It does not assume an `hcoeffPoly`-shaped
conclusion. -/
theorem hcoeffPoly_of_betaRec_offcentre
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι}
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (matchingSet : Finset F) (root : (z : F) → rationalRoot (H_tilde' H) z)
    (mp : ∀ t, k ≤ t → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z))
    (hcard : ∀ t, k ≤ t → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree)
    {Ppoly : F[X][Y]}
    (hrep : polyToPowerSeries𝕃 H Ppoly = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp Bcoeff)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (P : F → Polynomial F)
    (hPz : ∀ v₀ v₁ : F[X],
      polyToPowerSeries𝕃 H
          ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))
        = ((PowerSeries.trunc k (BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp Bcoeff) :
            Polynomial (𝕃 H)) : PowerSeries (𝕃 H)) →
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ, P z =
        ((Polynomial.map Polynomial.C (Polynomial.taylor (-x₀) v₀))
            + (Polynomial.C Polynomial.X)
              * (Polynomial.map Polynomial.C (Polynomial.taylor (-x₀) v₁))).eval
            (Polynomial.C z))
        ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ j < deg, (P z).coeff j = (B j).eval z := by
  have hCurve :
      BetaToCurveCoeffPolys.CurveCoeffPolys (F := F) k deg
        (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) P :=
    BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec_offcentre
      x₀ R H hHyp Bcoeff hH D hD
      (matchingSet := matchingSet) (root := root)
      mp hcard hrep hdegX hPz
  exact hcoeffPoly_witness_of_betaRecCurveCoeffPolys hCurve

/-! ### Off-Centre Input Configuration -/

/-- BCIKS Section 5 input configuration for the off-centre local-variable route.

This packages the inputs of `hcoeffPoly_of_betaRec_offcentre` in the same style as
`BetaCurveInput`, but replaces the centred-only `hsubst`/`hγ` fields with the
`gammaLocal` representative and truncated-local specialization bridge. -/
structure BetaCurveInputOffcentre {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) : Type 1 where
  x₀ : F
  R : F[X][X][Y]
  H : F[X][Y]
  [hHirr : Fact (Irreducible H)]
  [hHpos : Fact (0 < H.natDegree)]
  hHyp : Hypotheses x₀ R H
  Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H
  hH : 0 < H.natDegree
  D : ℕ
  hD : D ≥ Bivariate.totalDegree H
  matchingSet : Finset F
  root : (z : F) → rationalRoot (H_tilde' H) z
  Ppoly : F[X][Y]
  hrep : polyToPowerSeries𝕃 H Ppoly = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp Bcoeff
  hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1
  mp : ∀ t, k ≤ t → ∀ z ∈ matchingSet,
    BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z)
  hcard : ∀ t, k ≤ t → (↑matchingSet.card : WithBot ℕ)
    > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree
  hPz : ∀ (P : F → Polynomial F) (v₀ v₁ : F[X]),
    polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))
      = ((PowerSeries.trunc k (BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp Bcoeff) :
          Polynomial (𝕃 H)) : PowerSeries (𝕃 H)) →
    (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ, P z =
      ((Polynomial.map Polynomial.C (Polynomial.taylor (-x₀) v₀))
          + (Polynomial.C Polynomial.X)
            * (Polynomial.map Polynomial.C (Polynomial.taylor (-x₀) v₁))).eval
          (Polynomial.C z))
      ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1

attribute [instance] BetaCurveInputOffcentre.hHirr BetaCurveInputOffcentre.hHpos

omit [Nonempty ι] [DecidableEq ι] in
/-- Proves the coefficient-polynomial witness from the packaged off-centre input configuration. -/
theorem hcoeffPoly_of_betaRecOffcentre
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι}
    (inp : BetaCurveInputOffcentre (k := k) (deg := deg) (domain := domain) (δ := δ) u)
    (P : F → Polynomial F) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ j < deg, (P z).coeff j = (B j).eval z := by
  exact hcoeffPoly_of_betaRec_offcentre
    (k := k) (deg := deg) (domain := domain) (δ := δ) (u := u)
    inp.x₀ inp.R inp.H inp.hHyp inp.Bcoeff inp.hH inp.D inp.hD
    inp.matchingSet inp.root inp.mp inp.hcard inp.hrep inp.hdegX P (inp.hPz P)

/-! ### Finite Off-Centre Input Configuration -/

/-- BCIKS Section 5 finite-range input configuration for the off-centre local-variable route.

This is the F5-corrected counterpart of `BetaCurveInputOffcentre`: the cardinality and matching
inputs are required only for the finite range `k ≤ t ≤ T`, while `htailDeg` supplies the algebraic
tail beyond `T`.  It still avoids the centred-only `hsubst`/`hγ` fields by using `gammaLocal`. -/
structure BetaCurveInputOffcentreFin {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) : Type 1 where
  x₀ : F
  R : F[X][X][Y]
  H : F[X][Y]
  [hHirr : Fact (Irreducible H)]
  [hHpos : Fact (0 < H.natDegree)]
  hHyp : Hypotheses x₀ R H
  Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H
  hH : 0 < H.natDegree
  D : ℕ
  hD : D ≥ Bivariate.totalDegree H
  matchingSet : Finset F
  root : (z : F) → rationalRoot (H_tilde' H) z
  T : ℕ
  Ppoly : F[X][Y]
  hrep : polyToPowerSeries𝕃 H Ppoly = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp Bcoeff
  hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1
  mpFin : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
    BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z)
  hcardFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
    > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree
  htailDeg : ∀ t, T < t → BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t = 0
  hPz : ∀ (P : F → Polynomial F) (v₀ v₁ : F[X]),
    polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))
      = ((PowerSeries.trunc k (BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp Bcoeff) :
          Polynomial (𝕃 H)) : PowerSeries (𝕃 H)) →
    (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ, P z =
      ((Polynomial.map Polynomial.C (Polynomial.taylor (-x₀) v₀))
          + (Polynomial.C Polynomial.X)
            * (Polynomial.map Polynomial.C (Polynomial.taylor (-x₀) v₁))).eval
          (Polynomial.C z))
      ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1

attribute [instance] BetaCurveInputOffcentreFin.hHirr BetaCurveInputOffcentreFin.hHpos

omit [Nonempty ι] [DecidableEq ι] in
/-- Proves the coefficient-polynomial witness from the finite off-centre input configuration. -/
theorem hcoeffPoly_of_betaRecOffcentreFin
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι}
    (inp : BetaCurveInputOffcentreFin (k := k) (deg := deg) (domain := domain) (δ := δ) u)
    (P : F → Polynomial F) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ j < deg, (P z).coeff j = (B j).eval z := by
  have hCurve :
      BetaToCurveCoeffPolys.CurveCoeffPolys (F := F) k deg
        (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) P :=
    BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec_offcentreFin
      inp.x₀ inp.R inp.H inp.hHyp inp.Bcoeff inp.hH inp.D inp.hD
      (k := k) (T := inp.T)
      (matchingSet := inp.matchingSet) (root := inp.root)
      inp.mpFin inp.hcardFin inp.htailDeg inp.hrep inp.hdegX (inp.hPz P)
  exact hcoeffPoly_witness_of_betaRecCurveCoeffPolys hCurve

/-! ### Finite-Range Input Configuration -/

/-- BCIKS Section 5 finite-range input configuration. -/
structure BetaCurveInputFin {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) : Type 1 where
  x₀ : F
  R : F[X][X][Y]
  H : F[X][Y]
  [hHirr : Fact (Irreducible H)]
  [hHpos : Fact (0 < H.natDegree)]
  hHyp : Hypotheses x₀ R H
  Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H
  hH : 0 < H.natDegree
  D : ℕ
  hD : D ≥ Bivariate.totalDegree H
  matchingSet : Finset F
  root : (z : F) → rationalRoot (H_tilde' H) z
  T : ℕ
  hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ H)
  hγ : γ x₀ R H hHyp =
    (PowerSeries.mk (BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff)).subst
      (Claim59Conditional.shiftSeries x₀ H)
  Ppoly : F[X][Y]
  hrep : polyToPowerSeries𝕃 H Ppoly = γ x₀ R H hHyp
  hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1
  mpFin : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
    BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z)
  hcardFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
    > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree
  htailDeg : ∀ t, T < t → BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t = 0
  hPz : ∀ (P : F → Polynomial F) (v₀ v₁ : F[X]),
    γ x₀ R H hHyp = polyToPowerSeries𝕃 H
      ((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
    (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ, P z =
      ((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval (Polynomial.C z))
      ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1

attribute [instance] BetaCurveInputFin.hHirr BetaCurveInputFin.hHpos

omit [Nonempty ι] [DecidableEq ι] [Fintype ι] [Field F] [Fintype F] [DecidableEq F] in
/-- Proves that the finite cardinality bounds are satisfiable on the bounded range $[k, T]$. -/
theorem betaCurveInputFin_hcardFin_satisfiable
    {dR D dH k T : ℕ} {matchingSet : Finset F}
    (hmax : ((2 * T + 1) * dR * D * dH : ℕ) < matchingSet.card) :
    ∀ t, k ≤ t → t ≤ T →
      (((2 * t + 1) * dR * D * dH : ℕ) : WithBot ℕ) < (↑matchingSet.card : WithBot ℕ) := by
  intro t _hkt htT
  have hmono : (2 * t + 1) * dR * D * dH ≤ (2 * T + 1) * dR * D * dH := by
    have : 2 * t + 1 ≤ 2 * T + 1 := by omega
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this))
  have hlt : (2 * t + 1) * dR * D * dH < matchingSet.card := lt_of_le_of_lt hmono hmax
  exact_mod_cast hlt

omit [Nonempty ι] [DecidableEq ι] in
/-- Proves the existence of the coefficient polynomial map under the finite-range input
configuration. -/
theorem hcoeffPoly_of_betaRecFin
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι}
    (inp : BetaCurveInputFin (k := k) (deg := deg) (domain := domain) (δ := δ) u)
    (P : F → Polynomial F) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ j < deg, (P z).coeff j = (B j).eval z := by
  haveI := inp.hHirr
  haveI := inp.hHpos
  exact HcardDischarge.hcoeffPoly_witness_of_section5DataFin
    (k := k) (deg := deg) (domain := domain) (δ := δ) (u := u) (P := P)
    { x₀ := inp.x₀, R := inp.R, H := inp.H, hIrr := inp.hHirr, hPos := inp.hHpos,
      hHyp := inp.hHyp, Bcoeff := inp.Bcoeff, hH := inp.hH, D := inp.D, hD := inp.hD,
      matchingSet := inp.matchingSet, root := inp.root, T := inp.T,
      mpFin := inp.mpFin, hcardFin := inp.hcardFin, htailDeg := inp.htailDeg,
      hsubst := inp.hsubst, hγ := inp.hγ, Ppoly := inp.Ppoly, hrep := inp.hrep,
      hdegX := inp.hdegX, hPz := inp.hPz P }

/-! ### Strict Coefficient Polynomial Residual Discharge -/

omit [Nonempty ι] [DecidableEq ι] in
/-- Discharges the strict coefficient polynomial residual using the infinite-range input
configuration. -/
theorem strictCoeffPolysResidual_of_betaRec
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      BetaCurveInput (k := k) (deg := deg) (domain := domain) (δ := δ) u) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  exact hcoeffPoly_of_betaRec (hInput hk u hprob hJ hsqrt) P

omit [Nonempty ι] [DecidableEq ι] in
/-- Discharges the strict coefficient polynomial residual using the off-centre local-variable
input configuration. -/
theorem strictCoeffPolysResidual_of_betaRec_offcentre
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      BetaCurveInputOffcentre (k := k) (deg := deg) (domain := domain) (δ := δ) u) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  exact hcoeffPoly_of_betaRecOffcentre (hInput hk u hprob hJ hsqrt) P

omit [Nonempty ι] [DecidableEq ι] in
/-- Discharges the strict coefficient polynomial residual using the finite off-centre local-variable
input configuration. -/
theorem strictCoeffPolysResidual_of_betaRec_offcentreFin
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      BetaCurveInputOffcentreFin (k := k) (deg := deg) (domain := domain) (δ := δ) u) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  exact hcoeffPoly_of_betaRecOffcentreFin (hInput hk u hprob hJ hsqrt) P

omit [Nonempty ι] [DecidableEq ι] in
/-- Discharges the strict coefficient polynomial residual using the finite-range input
configuration. -/
theorem strictCoeffPolysResidual_of_betaRecFin
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      BetaCurveInputFin (k := k) (deg := deg) (domain := domain) (δ := δ) u) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  exact hcoeffPoly_of_betaRecFin (hInput hk u hprob hJ hsqrt) P

omit [Nonempty ι] [DecidableEq ι] in
/-- The strict coefficient polynomial residual is vacuously satisfied when $k = 0$. -/
theorem strictCoeffPolysResidual_zero
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} :
    StrictCoeffPolysResidual (k := 0) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk
  omega

/-! ### Keystone Assembly Theorems -/

/-- Proves the correlated agreement curves bound from the infinite-range input configuration
and boundary conditions. -/
theorem correlatedAgreement_affine_curves_johnson_of_betaRec
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      BetaCurveInput (k := k) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundaryCard : BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_boundaryCardResidual
    (k := k) (deg := deg) (domain := domain) (δ := δ)
    (strictCoeffPolysResidual_of_betaRec hInput) hBoundaryCard hδ

/-- Proves the correlated agreement curves bound from the off-centre local-variable input
configuration and boundary conditions. -/
theorem correlatedAgreement_affine_curves_johnson_of_betaRec_offcentre
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      BetaCurveInputOffcentre (k := k) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundaryCard : BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_boundaryCardResidual
    (k := k) (deg := deg) (domain := domain) (δ := δ)
    (strictCoeffPolysResidual_of_betaRec_offcentre hInput) hBoundaryCard hδ

/-- Proves the correlated agreement curves bound from the finite off-centre local-variable input
configuration and boundary conditions. -/
theorem correlatedAgreement_affine_curves_johnson_of_betaRec_offcentreFin
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      BetaCurveInputOffcentreFin (k := k) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundaryCard : BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_boundaryCardResidual
    (k := k) (deg := deg) (domain := domain) (δ := δ)
    (strictCoeffPolysResidual_of_betaRec_offcentreFin hInput) hBoundaryCard hδ

omit [DecidableEq ι] in
/-- Proves the correlated agreement curves bound under strict Johnson radius limits. -/
theorem correlatedAgreement_affine_curves_johnson_of_betaRec_strict
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      BetaCurveInput (k := k) (deg := deg) (domain := domain) (δ := δ) u) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_strict_coeff_polys
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun hk u hprob hJ P hP =>
      strictCoeffPolysResidual_of_betaRec hInput hk u hprob hJ hδ P hP)

omit [DecidableEq ι] in
/-- Proves the strict correlated agreement curves bound from the off-centre local-variable input
configuration. -/
theorem correlatedAgreement_affine_curves_johnson_of_betaRec_offcentre_strict
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      BetaCurveInputOffcentre (k := k) (deg := deg) (domain := domain) (δ := δ) u) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_strict_coeff_polys
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun hk u hprob hJ P hP =>
      strictCoeffPolysResidual_of_betaRec_offcentre hInput hk u hprob hJ hδ P hP)

omit [DecidableEq ι] in
/-- Proves the strict correlated agreement curves bound from the finite off-centre local-variable
input configuration. -/
theorem correlatedAgreement_affine_curves_johnson_of_betaRec_offcentreFin_strict
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      BetaCurveInputOffcentreFin (k := k) (deg := deg) (domain := domain) (δ := δ) u) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_strict_coeff_polys
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun hk u hprob hJ P hP =>
      strictCoeffPolysResidual_of_betaRec_offcentreFin hInput hk u hprob hJ hδ P hP)

/-- Proves the correlated agreement curves bound using the finite-range input configuration. -/
theorem correlatedAgreement_affine_curves_johnson_of_betaRecFin
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      BetaCurveInputFin (k := k) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundaryCard : BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_boundaryCardResidual
    (k := k) (deg := deg) (domain := domain) (δ := δ)
    (strictCoeffPolysResidual_of_betaRecFin hInput) hBoundaryCard hδ

omit [DecidableEq ι] in
/-- Proves the strict correlated agreement curves bound using the finite-range input
configuration. -/
theorem correlatedAgreement_affine_curves_johnson_of_betaRecFin_strict
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      BetaCurveInputFin (k := k) (deg := deg) (domain := domain) (δ := δ) u) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_strict_coeff_polys
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun hk u hprob hJ P hP =>
      strictCoeffPolysResidual_of_betaRecFin hInput hk u hprob hJ hδ P hP)

omit [DecidableEq ι] in
/-- Proves the strict correlated agreement curves bound from the finite-range data structure. -/
theorem correlatedAgreement_affine_curves_johnson_of_section5DataFin_strict
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
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
        HcardDischarge.Section5StrictDataFin
          (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_strict_coeff_polys
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun hk u hprob hJ P hP =>
      HcardDischarge.hcoeffPoly_witness_of_section5DataFin
        (hInput hk u hprob hJ hδ P hP))

end KeystoneStrictResidual

end ArkLib

/-! ## Axiom audit — betaRec/`hPz` consumer front doors. -/
#print axioms ArkLib.KeystoneStrictResidual.BetaCurveInput
#print axioms ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentre
#print axioms ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentreFin
#print axioms ArkLib.KeystoneStrictResidual.BetaCurveInputFin
#print axioms ArkLib.KeystoneStrictResidual.hcoeffPoly_of_betaRec
#print axioms ArkLib.KeystoneStrictResidual.hcoeffPoly_of_betaRec_offcentre
#print axioms ArkLib.KeystoneStrictResidual.hcoeffPoly_of_betaRecOffcentre
#print axioms ArkLib.KeystoneStrictResidual.hcoeffPoly_of_betaRecOffcentreFin
#print axioms ArkLib.KeystoneStrictResidual.hcoeffPoly_of_betaRecFin
#print axioms ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRec
#print axioms ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRec_offcentre
#print axioms ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRec_offcentreFin
#print axioms ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRecFin
#print axioms ArkLib.KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_betaRec_offcentre
#print axioms ArkLib.KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_betaRec_offcentreFin
#print axioms ArkLib.KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_betaRec_offcentre_strict
#print axioms ArkLib.KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_betaRec_offcentreFin_strict
#print axioms ArkLib.KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_betaRecFin
#print axioms ArkLib.KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_section5DataFin_strict
