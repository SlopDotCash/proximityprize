/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ProximityPrize.Extensions.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.ToMathlib.BetaToCurveCoeffPolys
import ArkLib.ToMathlib.BetaToCurveCoeffPolysOffcentre
import ArkLib.ToMathlib.HcardDischarge

/-!
# Keystone Front-Door Wiring for Strict Coefficient Polynomials

This module wires the $\text{betaRec}$-based power series reconstruction into the strict
coefficient polynomial residual required by the correlated agreement front-door theorem
(`ProximityGap.correlatedAgreement_affine_curves`). Every theorem here is an explicitly
conditional adapter: it assumes a supplier of one of the §5 input bundles below and forwards it.

## Mathematical Context

Let $C \subset F^\iota$ be a Reed-Solomon code of rate $\rho$. In the list-decoding proximity gap
reduction, the strict Johnson-radius branch assumes that the coefficient polynomials of the decoded
families are bounded in degree. This property is formalised by the `StrictCoeffPolysResidual`
predicate.

We show that, given a $\text{betaRec}$ input configuration for a decoded family `P` (which bundles
the specialized Guruswami-Sudan factor data and the Hensel-lifted recurrences), the pointwise
curve-polynomial datum:
$$\forall j < \text{deg}, \exists B_j \in F[X], \quad \text{deg}(B_j) < k+1$$
$$\text{and} \quad \forall z \in S, \quad P_z(j) = B_j(z)$$
can be bundled into a single polynomial map $B: \mathbb{N} \to F[X]$ satisfying the joint degree and
evaluation bounds demanded by the correlated agreement curves front door.

We formalize both the infinite-range input configuration (`BetaCurveInput`) and its F5-corrected
finite-range counterpart (`BetaCurveInputFin`), which asks for the matching/cardinality data only
on a finite range `k ≤ t ≤ T` and supplies the tail `t > T` through the explicit datum `htailDeg`.

## The input configurations are per decoded family (audit L72)

All four input configurations (`BetaCurveInput`, `BetaCurveInputOffcentre`,
`BetaCurveInputOffcentreFin`, `BetaCurveInputFin`) take the decoded family
`P : F → Polynomial F` as a structure **parameter**, and their specialisation bridge `hPz` is a
statement about that family only. The residual adapters therefore consume a supplier
`∀ u, (regime premises) → ∀ P, (P decoded on the good set) → Bundle u P`, which is the quantifier
order of `StrictCoeffPolysResidual` and of the per-`P` bundles
`HcardDischarge.Section5StrictDataFin` and `OffcentreKeystone.Section5StrictDataOffcentreFin`.

Earlier versions quantified `hPz` over **every** `P : F → Polynomial F` inside the bundle. The
bundle's own `hrep`/`hdegX` (plus the truncation identity, off-centre) provide a linear
representative satisfying the premise of `hPz`, so instantiating that field at `P := 0` and
`P := 1` forces `0 = 1` at any good parameter: no input of the old shape existed whenever the
good-coefficient set is nonempty, which the adapters' own probability premise guarantees
(`ProximityGap.goodCoeffsCurve_card_pos_of_prob_gt_zero`). The checked regressions
`not_forall_decodedFamily_specialisation` and `BetaCurveInput.not_uniform_hPz` (with its three
siblings) record this.

## What is *not* established here

No inhabitant of any of the four bundles is constructed in-tree, in any regime; the per-`P`
repair removes only the contradiction above. Independent obstructions remain, tracked elsewhere:

* the `hPz` conclusion is affine in the codeword variable, so it fails for every decoded family
  with a member of degree `≥ 2` at a good point (`FaithfulCurveExtraction.no_linRep_of_nonaffine`);
* the centred bundles state `hγ`/`hrep` against the in-tree `γ`, which is built from the legacy
  opaque numerator `β` (see the `BetaIdentify` and `OffcentreKeystoneAssembly` headers), and
  their `hsubst` field holds only at `x₀ = 0` (`SubstFieldCaveat.hasSubst_shiftSeries_iff_eq_zero`);
* the off-centre bundles state `hrep` against `gammaLocal`, which no polynomial represents when
  `2 ≤ H.natDegree` (`LocalSeriesCorrected.not_hrep_gammaLocal_of_two_le_natDegree`), so any
  off-centre input has `H.natDegree = 1`;
* the total selector `root : (z : F) → rationalRoot (H_tilde' H) z` cannot exist as soon as one
  rational-root fibre is empty (`IngredientC.not_exists_total_matchingVanishes_of_isEmpty`);
* every adapter concludes `StrictCoeffPolysResidual`, which is refuted in-tree at `k = 1`,
  `deg = 2`, `δ = 3/7` by an adversarial decoded family
  (`ProximityGap.StrictCanonicalCoeffPolysRefutation.not_strictCoeffPolysResidual`), so at those
  parameters no per-`(u, P)` supplier exists.

`betaCurveInputFin_hcardFin_satisfiable` is only the arithmetic fact that one concrete cardinality
bound at `T` implies the concrete bounds on `[k, T]`; it does not construct a `BetaCurveInputFin`.

## Key Formalizations
* `hcoeffPoly_witness_of_betaRecCurveCoeffPolys`: Bundles the per-index coefficient polynomial
  existentials into a single witness map.
* `BetaCurveInput`: per-`P` input configuration for the infinite-range matching bounds.
* `BetaCurveInputFin`: per-`P` finite-range input configuration incorporating tail-degree
  truncation.
* `hcoeffPoly_of_betaRecFin`: the coefficient polynomial bounds for `P` from a finite-range input
  configuration for `P`.
* `strictCoeffPolysResidual_of_betaRecFin`: `StrictCoeffPolysResidual` from a per-`(u, P)`
  supplier of finite-range inputs.
* `not_forall_decodedFamily_specialisation`, `BetaCurveInputFin.not_uniform_hPz`: regressions for
  the retired `∀ P` form of the `hPz` field.

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

/-! ### Regression: the retired `∀ P` specialisation field (audit L72) -/

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- **Regression for audit L72 (generic form).** A specialisation identity demanded for *every*
decoded family `P` — the shape of the `hPz` fields before the per-`P` repair — is contradictory
as soon as the good set is nonempty and the premise of the identity holds for one pair
`(v₀, v₁)`: instantiating it at the constant families `P := 0` and `P := 1` forces `0 = 1`. -/
theorem not_forall_decodedFamily_specialisation {good : Finset F} (hgood : good.Nonempty)
    {premise : F[X] → F[X] → Prop} {rep : F[X] → F[X] → F → F[X]}
    {side : F[X] → F[X] → Prop} (hex : ∃ v₀ v₁, premise v₀ v₁) :
    ¬ ∀ (P : F → Polynomial F) (v₀ v₁ : F[X]), premise v₀ v₁ →
        (∀ z ∈ good, P z = rep v₀ v₁ z) ∧ side v₀ v₁ := by
  intro h
  obtain ⟨v₀, v₁, hp⟩ := hex
  obtain ⟨z, hz⟩ := hgood
  have hzero := (h (fun _ => 0) v₀ v₁ hp).1 z hz
  have hone := (h (fun _ => 1) v₀ v₁ hp).1 z hz
  have hbad : (0 : F[X]) = 1 := hzero.trans hone.symm
  exact zero_ne_one hbad

/-! ### Infinite-Range Input Configuration -/

/-- BCIKS Section 5 input configuration for infinite-range matching bounds, for the decoded
family `P`.

`P` is a structure parameter and the specialisation bridge `hPz` concerns `P` only. (Before the
audit-L72 repair `hPz` quantified over every `P : F → Polynomial F`, which made the structure
empty whenever the good set is nonempty; see `BetaCurveInput.not_uniform_hPz`.) No inhabitant is
constructed in-tree; the module docstring lists the obstructions this bundle still carries. -/
structure BetaCurveInput {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F) : Type 1 where
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
  /-- the §5 specialisation bridge for the decoded family `P` (and only for `P`). -/
  hPz : ∀ v₀ v₁ : F[X],
    γ x₀ R H hHyp = polyToPowerSeries𝕃 H
      ((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
    (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ, P z =
      ((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval (Polynomial.C z))
      ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1

attribute [instance] BetaCurveInput.hHirr BetaCurveInput.hHpos

omit [Nonempty ι] [DecidableEq ι] in
/-- Proves the existence of the coefficient polynomial map for the decoded family `P` under the
infinite-range input configuration for `P`. -/
theorem hcoeffPoly_of_betaRec
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (inp : BetaCurveInput (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
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
      inp.hPz
  exact hcoeffPoly_witness_of_betaRecCurveCoeffPolys hCurve

omit [Nonempty ι] [DecidableEq ι] in
/-- **Regression for audit L72.** The retired uniform form of `hPz` — the specialisation identity
demanded for every decoded family `P'` — is false over the head data of any `BetaCurveInput` once
the good set is nonempty: the head's own `hrep`/`hdegX` give a linear representative, and the
identity cannot hold for both `P' := 0` and `P' := 1`. So no input of the retired shape existed
whenever a good parameter exists. -/
theorem BetaCurveInput.not_uniform_hPz
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (inp : BetaCurveInput (k := k) (deg := deg) (domain := domain) (δ := δ) u P)
    (hgood : (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).Nonempty) :
    ¬ ∀ (P' : F → Polynomial F) (v₀ v₁ : F[X]),
      γ inp.x₀ inp.R inp.H inp.hHyp = polyToPowerSeries𝕃 inp.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ, P' z =
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
          (Polynomial.C z))
        ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1 := by
  refine not_forall_decodedFamily_specialisation hgood ?_
  obtain ⟨v₀, v₁, hdec⟩ :=
    FiniteSeriesToPoly.exists_linear_decomposition_of_degreeX_le_one inp.hdegX
  exact ⟨v₀, v₁, by rw [← inp.hrep, hdec]⟩

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

/-- BCIKS Section 5 input configuration for the off-centre local-variable route, for the decoded
family `P`.

This packages the inputs of `hcoeffPoly_of_betaRec_offcentre` in the same style as
`BetaCurveInput`, but replaces the centred-only `hsubst`/`hγ` fields with the
`gammaLocal` representative and truncated-local specialization bridge. As for `BetaCurveInput`,
`P` is a structure parameter and `hPz` concerns `P` only (audit L72; see
`BetaCurveInputOffcentre.not_uniform_hPz`). No inhabitant is constructed in-tree. -/
structure BetaCurveInputOffcentre {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F) : Type 1 where
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
  /-- the off-centre §5 specialisation bridge for the decoded family `P` (and only for `P`). -/
  hPz : ∀ v₀ v₁ : F[X],
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
/-- Proves the coefficient-polynomial witness for `P` from the packaged off-centre input
configuration for `P`. -/
theorem hcoeffPoly_of_betaRecOffcentre
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (inp : BetaCurveInputOffcentre (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ j < deg, (P z).coeff j = (B j).eval z := by
  exact hcoeffPoly_of_betaRec_offcentre
    (k := k) (deg := deg) (domain := domain) (δ := δ) (u := u)
    inp.x₀ inp.R inp.H inp.hHyp inp.Bcoeff inp.hH inp.D inp.hD
    inp.matchingSet inp.root inp.mp inp.hcard inp.hrep inp.hdegX P inp.hPz

omit [Nonempty ι] [DecidableEq ι] in
/-- **Regression for audit L72 (off-centre).** The retired uniform form of the off-centre `hPz`
is false over the head data of any `BetaCurveInputOffcentre` once the good set is nonempty: the
matching data make the local series equal to its truncation, `hrep`/`hdegX` then give a linear
representative of that truncation, and the identity cannot hold for both `P' := 0` and
`P' := 1`. -/
theorem BetaCurveInputOffcentre.not_uniform_hPz
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (inp : BetaCurveInputOffcentre (k := k) (deg := deg) (domain := domain) (δ := δ) u P)
    (hgood : (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).Nonempty) :
    ¬ ∀ (P' : F → Polynomial F) (v₀ v₁ : F[X]),
      polyToPowerSeries𝕃 inp.H
          ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))
        = ((PowerSeries.trunc k
              (BetaToCurveCoeffPolys.gammaLocal inp.x₀ inp.R inp.H inp.hHyp inp.Bcoeff) :
            Polynomial (𝕃 inp.H)) : PowerSeries (𝕃 inp.H)) →
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ, P' z =
        ((Polynomial.map Polynomial.C (Polynomial.taylor (-inp.x₀) v₀))
            + (Polynomial.C Polynomial.X)
              * (Polynomial.map Polynomial.C (Polynomial.taylor (-inp.x₀) v₁))).eval
            (Polynomial.C z))
        ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1 := by
  refine not_forall_decodedFamily_specialisation hgood ?_
  have htrunc :=
    BetaToCurveCoeffPolys.gammaLocal_eq_trunc_of_betaRec inp.x₀ inp.R inp.H inp.hHyp inp.Bcoeff
      inp.hH inp.D inp.hD k inp.mp inp.hcard
  obtain ⟨v₀, v₁, hdec⟩ :=
    FiniteSeriesToPoly.exists_linear_decomposition_of_degreeX_le_one inp.hdegX
  exact ⟨v₀, v₁, by rw [← hdec, inp.hrep, ← htrunc]⟩

/-! ### Finite Off-Centre Input Configuration -/

/-- BCIKS Section 5 finite-range input configuration for the off-centre local-variable route, for
the decoded family `P`.

This is the F5-corrected counterpart of `BetaCurveInputOffcentre`: the cardinality and matching
inputs are required only for the finite range `k ≤ t ≤ T`, while `htailDeg` supplies the algebraic
tail beyond `T`.  It still avoids the centred-only `hsubst`/`hγ` fields by using `gammaLocal`.
`P` is a structure parameter and `hPz` concerns `P` only (audit L72; see
`BetaCurveInputOffcentreFin.not_uniform_hPz`); it now carries the same fields as
`OffcentreKeystone.Section5StrictDataOffcentreFin u P`. No inhabitant is constructed in-tree. -/
structure BetaCurveInputOffcentreFin {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F) : Type 1 where
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
  /-- the off-centre §5 specialisation bridge for the decoded family `P` (and only for `P`). -/
  hPz : ∀ v₀ v₁ : F[X],
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
/-- Proves the coefficient-polynomial witness for `P` from the finite off-centre input
configuration for `P`. -/
theorem hcoeffPoly_of_betaRecOffcentreFin
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (inp : BetaCurveInputOffcentreFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
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
      inp.mpFin inp.hcardFin inp.htailDeg inp.hrep inp.hdegX inp.hPz
  exact hcoeffPoly_witness_of_betaRecCurveCoeffPolys hCurve

omit [Nonempty ι] [DecidableEq ι] in
/-- **Regression for audit L72 (finite off-centre).** The retired uniform form of the off-centre
`hPz` is false over the head data of any `BetaCurveInputOffcentreFin` once the good set is
nonempty: the finite-range matching data and `htailDeg` make the local series equal to its
truncation, `hrep`/`hdegX` then give a linear representative of that truncation, and the
identity cannot hold for both `P' := 0` and `P' := 1`. -/
theorem BetaCurveInputOffcentreFin.not_uniform_hPz
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (inp : BetaCurveInputOffcentreFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P)
    (hgood : (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).Nonempty) :
    ¬ ∀ (P' : F → Polynomial F) (v₀ v₁ : F[X]),
      polyToPowerSeries𝕃 inp.H
          ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))
        = ((PowerSeries.trunc k
              (BetaToCurveCoeffPolys.gammaLocal inp.x₀ inp.R inp.H inp.hHyp inp.Bcoeff) :
            Polynomial (𝕃 inp.H)) : PowerSeries (𝕃 inp.H)) →
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ, P' z =
        ((Polynomial.map Polynomial.C (Polynomial.taylor (-inp.x₀) v₀))
            + (Polynomial.C Polynomial.X)
              * (Polynomial.map Polynomial.C (Polynomial.taylor (-inp.x₀) v₁))).eval
            (Polynomial.C z))
        ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1 := by
  refine not_forall_decodedFamily_specialisation hgood ?_
  have htrunc :=
    BetaToCurveCoeffPolys.gammaLocal_eq_trunc_of_finite_betaRec inp.x₀ inp.R inp.H inp.hHyp
      inp.Bcoeff inp.hH inp.D inp.hD k inp.T inp.mpFin inp.hcardFin inp.htailDeg
  obtain ⟨v₀, v₁, hdec⟩ :=
    FiniteSeriesToPoly.exists_linear_decomposition_of_degreeX_le_one inp.hdegX
  exact ⟨v₀, v₁, by rw [← hdec, inp.hrep, ← htrunc]⟩

/-! ### Finite-Range Input Configuration -/

/-- BCIKS Section 5 finite-range input configuration, for the decoded family `P`.

The matching/cardinality data are required only on the finite range `k ≤ t ≤ T`, and `htailDeg`
supplies the tail beyond `T`. `P` is a structure parameter and `hPz` concerns `P` only (audit L72;
see `BetaCurveInputFin.not_uniform_hPz`); it now carries the same fields as
`HcardDischarge.Section5StrictDataFin u P`. No inhabitant is constructed in-tree; see the module
docstring for the obstructions this bundle still carries. -/
structure BetaCurveInputFin {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F) : Type 1 where
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
  /-- the §5 specialisation bridge for the decoded family `P` (and only for `P`). -/
  hPz : ∀ v₀ v₁ : F[X],
    γ x₀ R H hHyp = polyToPowerSeries𝕃 H
      ((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
    (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ, P z =
      ((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval (Polynomial.C z))
      ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1

attribute [instance] BetaCurveInputFin.hHirr BetaCurveInputFin.hHpos

omit [Nonempty ι] [DecidableEq ι] [Fintype ι] [Field F] [Fintype F] [DecidableEq F] in
/-- Arithmetic monotonicity of the concrete finite-range cardinality budget: one concrete bound
`(2T+1)·dR·D·dH < #matchingSet` at the truncation index `T` implies the concrete bound for every
`t ≤ T`. This concerns only that arithmetic budget (the shape of `hcardConcreteFin` in
`BetaInputSupply`); it does not construct a `BetaCurveInputFin`, whose other fields are not
addressed here. -/
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
/-- Proves the existence of the coefficient polynomial map for the decoded family `P` under the
finite-range input configuration for `P`. -/
theorem hcoeffPoly_of_betaRecFin
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (inp : BetaCurveInputFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
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
      hdegX := inp.hdegX, hPz := inp.hPz }

omit [Nonempty ι] [DecidableEq ι] in
/-- **Regression for audit L72 (finite range).** The retired uniform form of `hPz` is false over
the head data of any `BetaCurveInputFin` once the good set is nonempty: the head's own
`hrep`/`hdegX` give a linear representative, and the identity cannot hold for both `P' := 0` and
`P' := 1`. This is the statement the audit kernel-checked against the old structure, restated
for the per-`P` bundle's head. -/
theorem BetaCurveInputFin.not_uniform_hPz
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (inp : BetaCurveInputFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P)
    (hgood : (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).Nonempty) :
    ¬ ∀ (P' : F → Polynomial F) (v₀ v₁ : F[X]),
      γ inp.x₀ inp.R inp.H inp.hHyp = polyToPowerSeries𝕃 inp.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ, P' z =
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
          (Polynomial.C z))
        ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1 := by
  refine not_forall_decodedFamily_specialisation hgood ?_
  obtain ⟨v₀, v₁, hdec⟩ :=
    FiniteSeriesToPoly.exists_linear_decomposition_of_degreeX_le_one inp.hdegX
  exact ⟨v₀, v₁, by rw [← inp.hrep, hdec]⟩

/-! ### Strict Coefficient Polynomial Residual Discharge

Each adapter below derives `StrictCoeffPolysResidual` from a supplier that produces, for every
received curve `u` in the regime and every decoded family `P` on its good set, an input bundle
for that `P`. These are conditional reductions only: `StrictCoeffPolysResidual` is refuted
in-tree at `k = 1`, `deg = 2`, `δ = 3/7`
(`ProximityGap.StrictCanonicalCoeffPolysRefutation.not_strictCoeffPolysResidual`), so no such
supplier exists at those parameters. -/

omit [Nonempty ι] [DecidableEq ι] in
/-- Derives the strict coefficient polynomial residual from a per-`(u, P)` supplier of
infinite-range input configurations (conditional; see the section docstring). -/
theorem strictCoeffPolysResidual_of_betaRec
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
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
        BetaCurveInput (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  exact hcoeffPoly_of_betaRec (hInput hk u hprob hJ hsqrt P hP)

omit [Nonempty ι] [DecidableEq ι] in
/-- Derives the strict coefficient polynomial residual from a per-`(u, P)` supplier of off-centre
local-variable input configurations (conditional; see the section docstring). -/
theorem strictCoeffPolysResidual_of_betaRec_offcentre
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
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
        BetaCurveInputOffcentre (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  exact hcoeffPoly_of_betaRecOffcentre (hInput hk u hprob hJ hsqrt P hP)

omit [Nonempty ι] [DecidableEq ι] in
/-- Derives the strict coefficient polynomial residual from a per-`(u, P)` supplier of finite
off-centre local-variable input configurations (conditional; see the section docstring). -/
theorem strictCoeffPolysResidual_of_betaRec_offcentreFin
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
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
        BetaCurveInputOffcentreFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  exact hcoeffPoly_of_betaRecOffcentreFin (hInput hk u hprob hJ hsqrt P hP)

omit [Nonempty ι] [DecidableEq ι] in
/-- Derives the strict coefficient polynomial residual from a per-`(u, P)` supplier of
finite-range input configurations (conditional; see the section docstring). -/
theorem strictCoeffPolysResidual_of_betaRecFin
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
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
        BetaCurveInputFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  exact hcoeffPoly_of_betaRecFin (hInput hk u hprob hJ hsqrt P hP)

omit [Nonempty ι] [DecidableEq ι] in
/-- The strict coefficient polynomial residual is vacuously satisfied when $k = 0$. -/
theorem strictCoeffPolysResidual_zero
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} :
    StrictCoeffPolysResidual (k := 0) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk
  omega

/-! ### Keystone Assembly Theorems

Each front door below takes a per-`(u, P)` supplier `hInput` of one of the four input bundles and
routes it through the corresponding residual adapter above, so each is conditional in the same
way: its `hInput` implies `StrictCoeffPolysResidual`, which is refuted in-tree at `k = 1`,
`deg = 2`, `δ = 3/7`. -/

-- Native conclusions quantify the canonical sampler; all extraction data above remain PMF-based.

/-- Proves the correlated agreement curves bound from the infinite-range input configuration
and boundary conditions. -/
theorem correlatedAgreement_affine_curves_johnson_of_betaRec
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg] [SampleableType F]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
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
        BetaCurveInput (k := k) (deg := deg) (domain := domain) (δ := δ) u P)
    (hBoundaryCard : BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_boundaryCardResidual
    (k := k) (deg := deg) (domain := domain) (δ := δ)
    (strictCoeffPolysResidual_of_betaRec hInput) hBoundaryCard hδ

/-- Proves the correlated agreement curves bound from the off-centre local-variable input
configuration and boundary conditions. -/
theorem correlatedAgreement_affine_curves_johnson_of_betaRec_offcentre
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg] [SampleableType F]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
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
        BetaCurveInputOffcentre (k := k) (deg := deg) (domain := domain) (δ := δ) u P)
    (hBoundaryCard : BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_boundaryCardResidual
    (k := k) (deg := deg) (domain := domain) (δ := δ)
    (strictCoeffPolysResidual_of_betaRec_offcentre hInput) hBoundaryCard hδ

/-- Proves the correlated agreement curves bound from the finite off-centre local-variable input
configuration and boundary conditions. -/
theorem correlatedAgreement_affine_curves_johnson_of_betaRec_offcentreFin
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg] [SampleableType F]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
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
        BetaCurveInputOffcentreFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P)
    (hBoundaryCard : BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_boundaryCardResidual
    (k := k) (deg := deg) (domain := domain) (δ := δ)
    (strictCoeffPolysResidual_of_betaRec_offcentreFin hInput) hBoundaryCard hδ

omit [DecidableEq ι] in
/-- Proves the correlated agreement curves bound under strict Johnson radius limits. -/
theorem correlatedAgreement_affine_curves_johnson_of_betaRec_strict
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg] [SampleableType F]
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
        BetaCurveInput (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
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
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg] [SampleableType F]
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
        BetaCurveInputOffcentre (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
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
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg] [SampleableType F]
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
        BetaCurveInputOffcentreFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_strict_coeff_polys
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun hk u hprob hJ P hP =>
      strictCoeffPolysResidual_of_betaRec_offcentreFin hInput hk u hprob hJ hδ P hP)

/-- Proves the correlated agreement curves bound using the finite-range input configuration. -/
theorem correlatedAgreement_affine_curves_johnson_of_betaRecFin
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg] [SampleableType F]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
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
        BetaCurveInputFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P)
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
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg] [SampleableType F]
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
        BetaCurveInputFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_strict_coeff_polys
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun hk u hprob hJ P hP =>
      strictCoeffPolysResidual_of_betaRecFin hInput hk u hprob hJ hδ P hP)

omit [DecidableEq ι] in
/-- Proves the strict correlated agreement curves bound from the finite-range data structure. -/
theorem correlatedAgreement_affine_curves_johnson_of_section5DataFin_strict
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg] [SampleableType F]
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
#print axioms ArkLib.KeystoneStrictResidual.not_forall_decodedFamily_specialisation
#print axioms ArkLib.KeystoneStrictResidual.BetaCurveInput.not_uniform_hPz
#print axioms ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentre.not_uniform_hPz
#print axioms ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentreFin.not_uniform_hPz
#print axioms ArkLib.KeystoneStrictResidual.BetaCurveInputFin.not_uniform_hPz
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
