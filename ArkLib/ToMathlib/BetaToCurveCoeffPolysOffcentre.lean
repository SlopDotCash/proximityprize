/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.BetaToCurveCoeffPolys
import ArkLib.ToMathlib.PolynomialCombinatorialAuxiliary
import ArkLib.ToMathlib.HcardDischarge

/-!
# The off-centre keystone: `betaRec ⟹ CurveCoeffPolys` at every expansion centre (F1 fix)

`BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec` consumes the pair `hsubst`/`hγ`, which
expresses the Hensel-lift series `γ` as `PowerSeries.subst (shiftSeries x₀ H) (mk (αFromBeta …))`.
By `SubstFieldCaveat.hasSubst_shiftSeries_iff_eq_zero` the `hsubst` input is *only satisfiable at
`x₀ = 0`*, so as stated the keystone is silently centred-only — exactly the F1 caveat recorded in
`RationalFunctions.lean` and `GammaSubstObstruction.lean`.  The faithful off-centre fix prescribed
there is to avoid `PowerSeries.subst` entirely and work with the series **in the local variable**
`X' = X − x₀`:

* `gammaLocal x₀ R H hHyp Bcoeff := PowerSeries.mk (αFromBeta x₀ R H hHyp Bcoeff)` — the
  Hensel-lift series in the local variable.  No substitution, no `HasSubst`, well-defined for
  *every* `x₀`.
* `gammaLocal_eq_trunc_of_betaRec` — the genuine `betaRec` polynomiality content, off-centre
  included: under the §5 matching-point/cardinality inputs the local series **is** its
  `k`-truncation (the tail vanishes by
  `BetaMatchingVanishes.betaRec_embedding_eq_zero_of_matchingSet_large`, routed through
  `tail_zero_of_betaRec_embedding_zero`).
* `curveCoeffPolys_of_betaRec_offcentre` — the keystone with `(hsubst, hγ, hrep)` replaced by a
  representative hypothesis against `gammaLocal`; the recentering to global coordinates happens
  where it is finite and legal, namely on the degree-`≤ 1` linear representative: the global
  coefficient profiles are the Taylor shifts `Polynomial.taylor (-x₀) v₀`,
  `Polynomial.taylor (-x₀) v₁` of the local ones (`(taylor (-x₀) v).eval z = v.eval (z - x₀)`),
  with the degree bounds transported by `Polynomial.natDegree_taylor`.

**Anti-vacuity** (issue #61 acceptance criterion 1): the proof of
`curveCoeffPolys_of_betaRec_offcentre` is load-bearing on `betaRec` — the `hPz` bridge consumes
the representative identity in *truncated* form, and the conversion from the honest full-series
identity `hrep` to that truncated form is exactly `gammaLocal_eq_trunc_of_betaRec`, i.e. the
matching-set/weight inputs `mp`/`hcard` flow through
`betaRec_embedding_eq_zero_of_matchingSet_large` into the conclusion.  No `hcoeffPoly`-equivalent
hypothesis is assumed (the F4 trap).

At the centre this specialises consistently: `shiftSeries 0 H = PowerSeries.X` and
`taylor 0 = id`, so the centred bridge (the `x₀ = 0` subst↔mk identity, tracked separately on
issue #61) recovers `curveCoeffPolys_of_betaRec` from this statement.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 and Appendix A.4.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal

namespace ArkLib

namespace BetaToCurveCoeffPolys

variable {F : Type} [Field F]

/-! ## The local-variable Hensel series (no substitution, valid at every centre) -/

/-- The Hensel-lift series **in the local variable** `X' = X − x₀`: the bare coefficient
series `∑ₜ αFromBeta(t) · X'^t`.  This is the F1-faithful object: it avoids
`PowerSeries.subst` of the shift series (which is not a valid substitution for `x₀ ≠ 0`,
`SubstFieldCaveat.hasSubst_shiftSeries_iff_eq_zero`) and is well-defined for every centre. -/
noncomputable def gammaLocal (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) : PowerSeries (𝕃 H) :=
  PowerSeries.mk (αFromBeta x₀ R H hHyp Bcoeff)

@[simp]
theorem coeff_gammaLocal (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ) :
    PowerSeries.coeff t (gammaLocal x₀ R H hHyp Bcoeff) = αFromBeta x₀ R H hHyp Bcoeff t :=
  PowerSeries.coeff_mk t _

/-! ## Generic truncation identity for tail-vanishing series -/

/-- A power series whose coefficients vanish from index `k` on **is** (the coercion of) its
`k`-truncation. -/
theorem mk_eq_trunc_of_tail_zero {K : Type*} [CommSemiring K] (f : ℕ → K) (k : ℕ)
    (h : ∀ t, k ≤ t → f t = 0) :
    PowerSeries.mk f = ((PowerSeries.trunc k (PowerSeries.mk f) : Polynomial K) : PowerSeries K) :=
  _root_.PowerSeries.mk_eq_trunc_of_tail_zero f k h

/-! ## The genuine `betaRec` polynomiality content, off-centre included -/

/-- **Off-centre polynomiality of the local Hensel series.**  Under the §5 matching-point and
matching-set-cardinality/weight inputs, the local series `gammaLocal` *is* its `k`-truncation —
i.e. the Hensel lift is a polynomial of degree `< k` in the local variable.  This is the genuine
`betaRec` content (routed through `tail_zero_of_betaRec_embedding_zero`, hence through
`BetaMatchingVanishes.betaRec_embedding_eq_zero_of_matchingSet_large`), and it holds at **every**
expansion centre `x₀` — no `HasSubst`, no centred-case restriction. -/
theorem gammaLocal_eq_trunc_of_betaRec (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H) (k : ℕ)
    {matchingSet : Finset F} {root : (z : F) → rationalRoot (H_tilde' H) z}
    (mp : ∀ t, k ≤ t → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z))
    (hcard : ∀ t, k ≤ t → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree) :
    gammaLocal x₀ R H hHyp Bcoeff
      = ((PowerSeries.trunc k (gammaLocal x₀ R H hHyp Bcoeff) : Polynomial (𝕃 H)) :
          PowerSeries (𝕃 H)) := by
  have htail : ∀ t, k ≤ t → αFromBeta x₀ R H hHyp Bcoeff t = 0 :=
    tail_zero_of_betaRec_embedding_zero x₀ R H hHyp Bcoeff hH D hD k mp hcard
  exact mk_eq_trunc_of_tail_zero (αFromBeta x₀ R H hHyp Bcoeff) k htail

/-- **Finite-range off-centre polynomiality of the local Hensel series.**  This is the F5-corrected
counterpart of `gammaLocal_eq_trunc_of_betaRec`: the matching/cardinality argument is required only
on a finite range `k ≤ t ≤ T`, while the explicit algebraic-degree datum `htailDeg` supplies the
tail for `T < t`.  The conclusion is the same local truncation identity, still valid at every
expansion centre and still routed through the genuine `betaRec` coefficients. -/
theorem gammaLocal_eq_trunc_of_finite_betaRec (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H) (k T : ℕ)
    {matchingSet : Finset F} {root : (z : F) → rationalRoot (H_tilde' H) z}
    (mpFin : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z))
    (hcardFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree)
    (htailDeg : ∀ t, T < t → αFromBeta x₀ R H hHyp Bcoeff t = 0) :
    gammaLocal x₀ R H hHyp Bcoeff
      = ((PowerSeries.trunc k (gammaLocal x₀ R H hHyp Bcoeff) : Polynomial (𝕃 H)) :
          PowerSeries (𝕃 H)) := by
  have htail : ∀ t, k ≤ t → αFromBeta x₀ R H hHyp Bcoeff t = 0 :=
    HcardDischarge.tail_zero_of_finite_card_and_degree
      x₀ R H hHyp Bcoeff hH D hD k T mpFin hcardFin htailDeg
  exact mk_eq_trunc_of_tail_zero (αFromBeta x₀ R H hHyp Bcoeff) k htail

/-! ## Degree transport along the affine recentering -/

/-- Taylor shift preserves the strict degree bound of a coefficient profile. -/
theorem natDegree_taylor_lt {v : F[X]} {k : ℕ} (x₀ : F) (h : v.natDegree < k + 1) :
    (Polynomial.taylor (-x₀) v).natDegree < k + 1 :=
  _root_.Polynomial.natDegree_taylor_lt (-x₀) v h

/-! ## The off-centre keystone -/

/-- **Off-centre keystone: `betaRec` reconstructs the curve coefficient polynomials at every
expansion centre.**  Identical conclusion to `curveCoeffPolys_of_betaRec`, with the
centred-only inputs `(hsubst, hγ, hrep)` replaced by a representative hypothesis `hrep`
against the local-variable series `gammaLocal` (the F1-faithful object), and the
decoded-family bridge `hPz` stated against the *truncated* local representative with the
recentering to global coordinates carried by the finite Taylor shifts
`taylor (-x₀) v₀`, `taylor (-x₀) v₁` of the linear-representative components
(`(taylor (-x₀) v).eval z = v.eval (z - x₀)`).

The proof is load-bearing on `betaRec`: `hPz` consumes the representative identity in
truncated form, and the conversion from the full-series `hrep` to that form is
`gammaLocal_eq_trunc_of_betaRec`, i.e. the matching-set inputs `mp`/`hcard` genuinely flow
into the conclusion. -/
theorem curveCoeffPolys_of_betaRec_offcentre
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    {k deg : ℕ} {good : Finset F} {P : F → Polynomial F}
    {matchingSet : Finset F} {root : (z : F) → rationalRoot (H_tilde' H) z}
    (mp : ∀ t, k ≤ t → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z))
    (hcard : ∀ t, k ≤ t → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree)
    {Ppoly : F[X][Y]}
    (hrep : polyToPowerSeries𝕃 H Ppoly = gammaLocal x₀ R H hHyp Bcoeff)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (hPz : ∀ v₀ v₁ : F[X],
      polyToPowerSeries𝕃 H
          ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))
        = ((PowerSeries.trunc k (gammaLocal x₀ R H hHyp Bcoeff) : Polynomial (𝕃 H)) :
            PowerSeries (𝕃 H)) →
      (∀ z ∈ good, P z =
        ((Polynomial.map Polynomial.C (Polynomial.taylor (-x₀) v₀))
            + (Polynomial.C Polynomial.X)
              * (Polynomial.map Polynomial.C (Polynomial.taylor (-x₀) v₁))).eval
            (Polynomial.C z))
        ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    CurveCoeffPolys k deg good P := by
  -- the genuine betaRec content: the local series is its k-truncation (off-centre included)
  have htrunc : gammaLocal x₀ R H hHyp Bcoeff
      = ((PowerSeries.trunc k (gammaLocal x₀ R H hHyp Bcoeff) : Polynomial (𝕃 H)) :
          PowerSeries (𝕃 H)) :=
    gammaLocal_eq_trunc_of_betaRec x₀ R H hHyp Bcoeff hH D hD k mp hcard
  -- decompose the degree-≤1 representative
  obtain ⟨v₀, v₁, hPpoly⟩ :=
    FiniteSeriesToPoly.exists_linear_decomposition_of_degreeX_le_one hdegX
  -- the representative identity, in the truncated form the bridge consumes
  have hlin : polyToPowerSeries𝕃 H
      ((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))
      = ((PowerSeries.trunc k (gammaLocal x₀ R H hHyp Bcoeff) : Polynomial (𝕃 H)) :
          PowerSeries (𝕃 H)) := by
    rw [← hPpoly, hrep, ← htrunc]
  obtain ⟨hPeval, hd₀, hd₁⟩ := hPz v₀ v₁ hlin
  -- assemble at the Taylor-shifted (global-coordinate) components
  exact curveCoeffPolys_of_linear_representative
    (Polynomial.taylor (-x₀) v₀) (Polynomial.taylor (-x₀) v₁)
    (natDegree_taylor_lt x₀ hd₀) (natDegree_taylor_lt x₀ hd₁) hPeval

/-- **Finite-range off-centre keystone.**  This is the satisfiable finite-range counterpart of
`curveCoeffPolys_of_betaRec_offcentre`: it uses `mpFin`/`hcardFin` only for `k ≤ t ≤ T` and the
explicit tail-degree datum `htailDeg` for `T < t`, then runs the same finite Taylor-shift
recentring argument to produce the coefficient-polynomial datum. -/
theorem curveCoeffPolys_of_betaRec_offcentreFin
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    {k T deg : ℕ} {good : Finset F} {P : F → Polynomial F}
    {matchingSet : Finset F} {root : (z : F) → rationalRoot (H_tilde' H) z}
    (mpFin : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z))
    (hcardFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree)
    (htailDeg : ∀ t, T < t → αFromBeta x₀ R H hHyp Bcoeff t = 0)
    {Ppoly : F[X][Y]}
    (hrep : polyToPowerSeries𝕃 H Ppoly = gammaLocal x₀ R H hHyp Bcoeff)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (hPz : ∀ v₀ v₁ : F[X],
      polyToPowerSeries𝕃 H
          ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))
        = ((PowerSeries.trunc k (gammaLocal x₀ R H hHyp Bcoeff) : Polynomial (𝕃 H)) :
            PowerSeries (𝕃 H)) →
      (∀ z ∈ good, P z =
        ((Polynomial.map Polynomial.C (Polynomial.taylor (-x₀) v₀))
            + (Polynomial.C Polynomial.X)
              * (Polynomial.map Polynomial.C (Polynomial.taylor (-x₀) v₁))).eval
            (Polynomial.C z))
        ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    CurveCoeffPolys k deg good P := by
  have htrunc : gammaLocal x₀ R H hHyp Bcoeff
      = ((PowerSeries.trunc k (gammaLocal x₀ R H hHyp Bcoeff) : Polynomial (𝕃 H)) :
          PowerSeries (𝕃 H)) :=
    gammaLocal_eq_trunc_of_finite_betaRec x₀ R H hHyp Bcoeff hH D hD k T
      mpFin hcardFin htailDeg
  obtain ⟨v₀, v₁, hPpoly⟩ :=
    FiniteSeriesToPoly.exists_linear_decomposition_of_degreeX_le_one hdegX
  have hlin : polyToPowerSeries𝕃 H
      ((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))
      = ((PowerSeries.trunc k (gammaLocal x₀ R H hHyp Bcoeff) : Polynomial (𝕃 H)) :
          PowerSeries (𝕃 H)) := by
    rw [← hPpoly, hrep, ← htrunc]
  obtain ⟨hPeval, hd₀, hd₁⟩ := hPz v₀ v₁ hlin
  exact curveCoeffPolys_of_linear_representative
    (Polynomial.taylor (-x₀) v₀) (Polynomial.taylor (-x₀) v₁)
    (natDegree_taylor_lt x₀ hd₀) (natDegree_taylor_lt x₀ hd₁) hPeval

end BetaToCurveCoeffPolys

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.BetaToCurveCoeffPolys.gammaLocal
#print axioms ArkLib.BetaToCurveCoeffPolys.coeff_gammaLocal
#print axioms ArkLib.BetaToCurveCoeffPolys.mk_eq_trunc_of_tail_zero
#print axioms ArkLib.BetaToCurveCoeffPolys.gammaLocal_eq_trunc_of_betaRec
#print axioms ArkLib.BetaToCurveCoeffPolys.gammaLocal_eq_trunc_of_finite_betaRec
#print axioms ArkLib.BetaToCurveCoeffPolys.natDegree_taylor_lt
#print axioms ArkLib.BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec_offcentre
#print axioms ArkLib.BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec_offcentreFin
