/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.OffcentreKeystoneAssembly
import ArkLib.ToMathlib.CurveFamilyHensel

/-!
# Issue #304 — the off-centre per-`P` §5 bundle, re-targeted at the faithful curve-family `hPz`

## Why this file exists

`OffcentreKeystone.Section5StrictDataOffcentreFin` is the satisfiable off-centre per-`P` §5
bundle — γ-free, `hsubst`-free, with `htailDeg` derivable from `hrep` — but its `hPz` field still
carries the **transposed** linear-representative conclusion

```
P z = ((map C v₀) + (C X) * (map C v₁)).eval (C z)
```

which (`FaithfulCurveExtraction.no_linRep_of_nonaffine`, kernel-checked) forces every decoded
member `P z` to be **affine in the codeword variable**: a single good `z` with
`2 ≤ (P z).natDegree` refutes the field.  The faithful [BCIKS20] Prop-5.5 conclusion is the
opposite transposition — low degree in the **curve parameter**, full degree on the codeword side:

```
P z = ∑_{t<n} (z − x₀)^t • c_t,   n ≤ k + 1,   c_t ∈ F[X].
```

This file provides the missing combination — the **full off-centre machinery bundle** (matching
set, per-point matching data, finite-range weight bound, tail vanishing, the Prop-5.5 local
representative) **with the faithful curve-family `hPz`**:

* `Section5StrictDataOffcentreFaithful u P` — field-for-field identical to
  `Section5StrictDataOffcentreFin` except that the transposed `hPz` is replaced by the faithful
  per-`z` curve-family identity (`x₀`-centred, at most `k + 1` coefficients `c`), matching the
  input shape of `FaithfulCurveExtraction.curveCoeffPolys_of_curveFamily` exactly.
* `curveFamilyData_of_section5DataOffcentreFaithful` — the forgetful consumer into the lean
  faithful datum `FaithfulCurveExtraction.CurveFamilyData`.
* `curveCoeffPolys_of_section5DataOffcentreFaithful` /
  `hcoeffPoly_witness_of_section5DataOffcentreFaithful` — the extraction consumers, routing
  through the faithful extraction (NOT through the affine-only
  `curveCoeffPolys_of_betaRec_offcentreFin`).
* `strictCoeffPolysResidual_of_section5DataOffcentreFaithful` — the residual discharge from a
  per-`(u, P)` producer of the bundle.
* `correlatedAgreement_affine_curves_johnson_of_section5DataOffcentreFaithful_strict` (and the
  closed-radius variant) — the §5 keystone front doors, mirroring
  `OffcentreKeystoneAssembly` Parts 3–4 verbatim.
* `section5DataOffcentreFaithful_of_producers` — the producer assembly:
  `htailDeg` **derived** from `hrep` via
  `OffcentreKeystone.htailDeg_of_offcentre_representative` (which is `hPz`-shape-independent),
  and the faithful `hPz` **derived by Hensel uniqueness** from the per-`z` curve-Hensel root
  datum `FaithfulCurveExtraction.CurveHenselDatum` — the in-tree generalization of the
  `HPzBridge` route in which the competitor pinned equal to `P z` is the **curve-family
  evaluation** `∑_{t<n} (z − x₀)^t • c_t` (Hensel uniqueness pins `P z` equal to ANY competing
  root; `eval_identity_of_curveHensel`).
* `section5DataOffcentreFaithful_of_producers_gradedDisc` — the graded/discriminant capstone at
  the canonical `Bcoeff := BCIKS20.HenselNumerator.B_coeff`, with `hcardFin` discharged by the
  proven graded weight collapse fed by the §6 discriminant counting (as in
  `OffcentreKeystoneAssembly` Part 7), and the `hPz` supply faithful.

## The honest remaining frontier after this file

The strict-Johnson §5 keystone for the canonical coefficients reduces to exactly the per-word
data: the GS factor bundle, the Prop-5.5 local representative (`hrep`/`hdegX`), the per-point
matching geometry (`mpPoint`), the §6 discriminant counting (`hdisc`/`hcover`/`hbig`), and —
new on this surface — the faithful curve data `(n, c)` with the per-`z` curve-Hensel root datum
(`CurveHenselDatum`), whose own production lanes are
`CurveHenselDatumProducers.curveHenselDatum_of_matchesGraph` (GS interpolant route) and
`curveHenselDatum_of_truncatedLocalRoot` (analytic route at the constructed local series).
No transposed representative is consumed anywhere on the extraction path.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (Prop. 5.5, the polynomial-curve conclusion), §6.2 (Hensel uniqueness `π_z(γ) = P_z`),
  Appendix A.2/A.4.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

-- The bundle carries `[DecidableEq ι]` context because the downstream front doors need it.
set_option linter.unusedDecidableInType false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace OffcentreFaithful

section Bundle

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Part 1 — the bundle: the off-centre machinery with the faithful curve-family `hPz` -/

/-- **The off-centre per-`P` §5 extraction datum, faithful interface.**  Field-for-field
identical to `OffcentreKeystone.Section5StrictDataOffcentreFin` except for the final bridge: the
transposed linear-representative `hPz` (refuted for non-affine decoded families by
`FaithfulCurveExtraction.no_linRep_of_nonaffine`) is replaced by the faithful per-`z`
curve-family identity `P z = ∑_{t<n} (z − x₀)^t • c_t` with `n < k + 2` — exactly the input
shape of `FaithfulCurveExtraction.curveCoeffPolys_of_curveFamily`.  The machinery fields
(`mpFin`/`hcardFin`/`htailDeg`/`hrep`/`hdegX`) are the unchanged §5/§6/App-A production context:
they feed the *construction* of the curve coefficients `c` (the base-rational readings of the
truncated local series), not the extraction interface. -/
structure Section5StrictDataOffcentreFaithful {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F) : Type where
  /-- centre / curve data of [BCIKS20] §5. -/
  x₀ : F
  R : F[X][X][Y]
  H : F[X][Y]
  hIrr : Fact (Irreducible H)
  hPos : Fact (0 < H.natDegree)
  hHyp : Hypotheses x₀ R H
  Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H
  hH : 0 < H.natDegree
  D : ℕ
  hD : D ≥ Bivariate.totalDegree H
  matchingSet : Finset F
  root : (z : F) → rationalRoot (H_tilde' H) z
  /-- the Lemma-A.1 truncation index. -/
  T : ℕ
  /-- ingredient-C per-point matching data over the finite counting range `k ≤ t ≤ T`. -/
  mpFin : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
    BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z)
  /-- the L9/L10 weight bound over the finite counting range `k ≤ t ≤ T`. -/
  hcardFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
      > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree
  /-- the algebraic-degree tail datum beyond `T` (producible from `hrep` via
  `OffcentreKeystone.htailDeg_of_offcentre_representative` when `T ≥ deg Ppoly`). -/
  htailDeg : ∀ t, T < t → BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t = 0
  /-- the Prop-5.5 polynomial representative of the **local** Hensel series. -/
  Ppoly : F[X][Y]
  hrep : polyToPowerSeries𝕃 H Ppoly = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp Bcoeff
  hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1
  /-- the number of curve coefficients (at most `k + 1`). -/
  n : ℕ
  hn : n < k + 2
  /-- the codeword-polynomial curve coefficients. -/
  c : ℕ → F[X]
  /-- **the faithful §5 bridge**: at each good `z`, the decoded member equals the curve-family
  evaluation — low degree in the curve parameter, no degree restriction on the codeword side. -/
  hPz : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    P z = ∑ t ∈ Finset.range n, (z - x₀) ^ t • c t

/-! ## Part 2 — bundle consumers (the faithful extraction path) -/

omit [Nonempty ι] [DecidableEq ι] in
/-- The faithful off-centre bundle forgets onto the lean faithful per-`(u, P)` datum
`FaithfulCurveExtraction.CurveFamilyData` (whose in-tree consumers reach the keystone). -/
def curveFamilyData_of_section5DataOffcentreFaithful {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : Section5StrictDataOffcentreFaithful (k := k) (deg := deg) (domain := domain) (δ := δ)
      u P) :
    FaithfulCurveExtraction.CurveFamilyData (k := k) (deg := deg) (domain := domain) (δ := δ)
      u P :=
  { x₀ := d.x₀
    n := d.n
    hn := d.hn
    c := d.c
    hPz := d.hPz }

omit [Nonempty ι] [DecidableEq ι] in
/-- The faithful off-centre bundle yields the per-coefficient curve-polynomial datum on the good
set, via the **faithful** extraction `curveCoeffPolys_of_curveFamily` — NOT via the affine-only
`curveCoeffPolys_of_betaRec_offcentreFin`. -/
theorem curveCoeffPolys_of_section5DataOffcentreFaithful {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : Section5StrictDataOffcentreFaithful (k := k) (deg := deg) (domain := domain) (δ := δ)
      u P) :
    BetaToCurveCoeffPolys.CurveCoeffPolys (F := F) k deg
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) P :=
  FaithfulCurveExtraction.curveCoeffPolys_of_curveFamily d.x₀ d.n d.c d.hn d.hPz

omit [Nonempty ι] [DecidableEq ι] in
/-- The faithful off-centre bundle yields the bundled `hcoeffPoly` existential the front door
consumes. -/
theorem hcoeffPoly_witness_of_section5DataOffcentreFaithful {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : Section5StrictDataOffcentreFaithful (k := k) (deg := deg) (domain := domain) (δ := δ)
      u P) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ j < deg, (P z).coeff j = (B j).eval z :=
  KeystoneCapstone.hcoeffPoly_witness_of_curveCoeffPolys u P
    (curveCoeffPolys_of_section5DataOffcentreFaithful d)

/-! ## Part 3 — residual discharge and keystone front doors -/

omit [Nonempty ι] [DecidableEq ι] in
/-- **`StrictCoeffPolysResidual` from a per-`(u, P)` faithful off-centre bundle producer.**  The
producer receives the probability/Johnson hypotheses *and* the decoded-family hypothesis `hP` —
the satisfiable quantifier order. -/
theorem strictCoeffPolysResidual_of_section5DataOffcentreFaithful
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
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        Section5StrictDataOffcentreFaithful (k := k) (deg := deg) (domain := domain) (δ := δ)
          u P) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  exact hcoeffPoly_witness_of_section5DataOffcentreFaithful (hInput hk u hprob hJ hsqrt P hP)

omit [DecidableEq ι] in
/-- **Strict square-root-radius keystone front door (off-centre, per-`P`, faithful).**  The §5
keystone goal `δ_ε_correlatedAgreementCurves` in the strict Johnson regime, from a per-`(u, P)`
producer of the faithful off-centre bundle.  The extraction path is the faithful one: the
producer's `hPz` is satisfiable for honest (non-affine) decoded families. -/
theorem correlatedAgreement_affine_curves_johnson_of_section5DataOffcentreFaithful_strict
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
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        Section5StrictDataOffcentreFaithful (k := k) (deg := deg) (domain := domain) (δ := δ)
          u P) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_strict_coeff_polys
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun hk u hprob hJ P hP =>
      hcoeffPoly_witness_of_section5DataOffcentreFaithful (hInput hk u hprob hJ hδ P hP))

/-- **Closed square-root-radius keystone front door (off-centre, per-`P`, faithful).**  As the
strict front door, with the boundary branch supplied as the packaged `BoundaryCardResidual`. -/
theorem correlatedAgreement_affine_curves_johnson_of_section5DataOffcentreFaithful
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
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
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        Section5StrictDataOffcentreFaithful (k := k) (deg := deg) (domain := domain) (δ := δ)
          u P)
    (hBoundaryCard : BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_boundaryCardResidual
    (k := k) (deg := deg) (domain := domain) (δ := δ)
    (strictCoeffPolysResidual_of_section5DataOffcentreFaithful hInput) hBoundaryCard hδ

/-! ## Part 4 — the producer assembly

The faithful analogue of `OffcentreKeystone.section5DataOffcentreFin_of_producers`.  Two
substitutions relative to the transposed assembly:

* `htailDeg` is derived from `hrep` exactly as before —
  `OffcentreKeystone.htailDeg_of_offcentre_representative` is `hPz`-shape-independent;
* the `hPz` supply is the **generalized `HPzBridge` route**: Hensel uniqueness
  (`HPzBridge.decoded_eq_specialization_of_hensel`) pins `P z` equal to ANY competing root of the
  separable matching polynomial sharing its mod-`X` approximation; instantiating the competitor
  at the **curve-family evaluation** `∑_{t<n} (z − x₀)^t • c_t` (the in-tree
  `FaithfulCurveExtraction.eval_identity_of_curveHensel`) yields the faithful per-`z` identity
  from the per-`(u, P)` curve-Hensel datum `FaithfulCurveExtraction.CurveHenselDatum`. -/

/-- **The faithful off-centre producer assembly.**  Builds the faithful off-centre per-`P` bundle
from: the GS factor bundle, the Prop-5.5 local representative (`hrep` against `gammaLocal`), the
per-point matching data, the finite-range cardinality bound, the curve data `(n, hn, c)`, and the
per-`z` curve-Hensel root datum — with the truncation index fixed at `T := Ppoly.natDegree`,
`htailDeg` **derived** from `hrep`, and the faithful `hPz` **derived** from the curve-Hensel
datum by Hensel uniqueness.  No transposed linear representative appears in the `hPz` lane. -/
noncomputable def section5DataOffcentreFaithful_of_producers
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 b.H)
    (matchingSet : Finset F)
    (root : (z : F) → rationalRoot (H_tilde' b.H) z)
    -- the Prop-5.5 linear representative of the local series
    -- (fixes the truncation index `T := Ppoly.natDegree`):
    (Ppoly : F[X][Y])
    (hrep : polyToPowerSeries𝕃 b.H Ppoly
      = BetaToCurveCoeffPolys.gammaLocal x₀ b.R b.H b.hHyp Bcoeff)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    -- finite-range per-point matching producer (ingredient-C geometry on `[k, deg Ppoly]`):
    (mpPoint : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ b.R b.H b.hHyp Bcoeff t z (root z))
    -- the satisfiable finite-range L9/L10 weight bound:
    (hcardFin : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 b.hH (betaRec x₀ b.R b.H b.hHyp Bcoeff t) b.D * b.H.natDegree)
    -- the faithful curve data and the per-`z` curve-Hensel root datum:
    (n : ℕ) (hn : n < k + 2) (c : ℕ → F[X])
    (hHensel : FaithfulCurveExtraction.CurveHenselDatum
      (k := k) (deg := deg) (domain := domain) (δ := δ) u P x₀ n c) :
    Section5StrictDataOffcentreFaithful (k := k) (deg := deg) (domain := domain) (δ := δ)
      u P :=
  { x₀ := x₀
    R := b.R
    H := b.H
    hIrr := b.hIrr
    hPos := b.hPos
    hHyp := b.hHyp
    Bcoeff := Bcoeff
    hH := b.hH
    D := b.D
    hD := b.hD
    matchingSet := matchingSet
    root := root
    T := Ppoly.natDegree
    mpFin := mpPoint
    hcardFin := hcardFin
    htailDeg := OffcentreKeystone.htailDeg_of_offcentre_representative hrep
    Ppoly := Ppoly
    hrep := hrep
    hdegX := hdegX
    n := n
    hn := hn
    c := c
    hPz := fun z hz =>
      FaithfulCurveExtraction.eval_identity_of_curveHensel
        (f := hHensel.f z) (a₀ := hHensel.a₀ z)
        (hHensel.hProot z hz) (hHensel.hQroot z hz) (hHensel.hPapprox z hz)
        (hHensel.hQapprox z hz) (hHensel.hderiv z hz) }

/-! ## Part 5 — the graded/discriminant capstone at the canonical coefficients -/

/-- **The faithful graded/discriminant capstone.**  The faithful off-centre per-`P` bundle at the
canonical `Bcoeff := BCIKS20.HenselNumerator.B_coeff`, with the cardinality front fully
discharged from: monic `H`, the Y-degree bound `2 ≤ d`, the paper grading `hR`, a nonzero
discriminant `disc` whose non-vanishing locus the matching set covers, and the field-size bound
`gradedCardBudget(deg Ppoly) + deg disc < |F|`.  The remaining genuine inputs are exactly the
§5/§6 geometry: `hrep`/`hdegX` (Prop 5.5), `mpPoint` (ingredient C / L12), the curve data
`(n, c)`, and the per-`z` curve-Hensel root datum (§6.2, faithful competitor). -/
noncomputable def section5DataOffcentreFaithful_of_producers_gradedDisc
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (matchingSet : Finset F)
    (root : (z : F) → rationalRoot (H_tilde' b.H) z)
    (Ppoly : F[X][Y])
    (hrep : polyToPowerSeries𝕃 b.H Ppoly
      = BetaToCurveCoeffPolys.gammaLocal x₀ b.R b.H b.hHyp
          (BCIKS20.HenselNumerator.B_coeff b.H x₀ b.R))
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (mpPoint : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ b.R b.H b.hHyp
        (BCIKS20.HenselNumerator.B_coeff b.H x₀ b.R) t z (root z))
    -- the graded-collapse side conditions (the App-A.4 budget suppliers):
    (hmonic : b.H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY b.R)
    (hdHD : b.H.natDegree ≤ b.D)
    (hD_Rx0 : b.D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) b.R))
    (hR : ∀ j, Bivariate.degreeX (b.R.coeff j) ≤ b.D - j)
    -- the §6 discriminant counting facts:
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY b.R) b.D b.H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F)
    -- the faithful curve data and the per-`z` curve-Hensel root datum:
    (n : ℕ) (hn : n < k + 2) (c : ℕ → F[X])
    (hHensel : FaithfulCurveExtraction.CurveHenselDatum
      (k := k) (deg := deg) (domain := domain) (δ := δ) u P x₀ n c) :
    Section5StrictDataOffcentreFaithful (k := k) (deg := deg) (domain := domain) (δ := δ)
      u P :=
  section5DataOffcentreFaithful_of_producers
    (k := k) (deg := deg) (domain := domain) (δ := δ) (u := u) (P := P)
    b (BCIKS20.HenselNumerator.B_coeff b.H x₀ b.R) matchingSet root Ppoly hrep hdegX mpPoint
    (hcardFin_of_graded x₀ b.R b.H b.hHyp b.hD b.hH hmonic hd2 hdHD hD_Rx0 hR
      (gradedConcreteFin_of_disc hdisc hcover hbig))
    n hn c hHensel

end Bundle

end OffcentreFaithful

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.OffcentreFaithful.Section5StrictDataOffcentreFaithful
#print axioms ArkLib.OffcentreFaithful.curveFamilyData_of_section5DataOffcentreFaithful
#print axioms ArkLib.OffcentreFaithful.curveCoeffPolys_of_section5DataOffcentreFaithful
#print axioms ArkLib.OffcentreFaithful.hcoeffPoly_witness_of_section5DataOffcentreFaithful
#print axioms ArkLib.OffcentreFaithful.strictCoeffPolysResidual_of_section5DataOffcentreFaithful
#print axioms ArkLib.OffcentreFaithful.correlatedAgreement_affine_curves_johnson_of_section5DataOffcentreFaithful_strict
#print axioms ArkLib.OffcentreFaithful.correlatedAgreement_affine_curves_johnson_of_section5DataOffcentreFaithful
#print axioms ArkLib.OffcentreFaithful.section5DataOffcentreFaithful_of_producers
#print axioms ArkLib.OffcentreFaithful.section5DataOffcentreFaithful_of_producers_gradedDisc
