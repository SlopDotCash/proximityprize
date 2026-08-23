/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.ToMathlib.BetaToCurveCoeffPolys
import ArkLib.ToMathlib.KeystoneCapstone

/-!
# The closed list-decoding keystone — `correlatedAgreement_affine_curves_listDecoding_closed`

This file is the **keystone integration**: it closes the list-decoding branch of the BCIKS20 curve
theorem `ProximityGap.correlatedAgreement_affine_curves` (`Curves.lean:1819`) *end-to-end from the
genuine §5 bricks*, kernel-clean (no `sorry`/`admit`/`axiom`/`native_decide`), as a STANDALONE
theorem against the live base — i.e. without editing the live-session-owned `RationalFunctions.lean`
`β_regular`.

## What is genuinely wired

The chain feeds the real front door
`ProximityGap.RS_jointAgreement_of_prob_gt_and_errorBound_lower_bounds` (`Curves.lean:1199`) and
`ProximityGap.correlatedAgreement_affine_curves_of_strict_coeff_polys_and_boundary`
(`Curves.lean:1720`):

```
Section5StrictDatum u P        (the genuine §5 per-decoding extraction data: betaRec setup +
                                ingredient-C matching + Prop-5.5 representative + specialisation
                                bridge)
  ──BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec──►          (betaRec ⟹ CurveCoeffPolys; uses
  βRec)
CurveCoeffPolys k deg (RS_goodCoeffsCurve …) P
  ──KeystoneCapstone.hcoeffPoly_witness_of_curveCoeffPolys──►    (bundle per-index ⟹ ∃ B : ℕ → …)
∃ B, (∀ j<deg, (B j).natDegree < k+1) ∧ ∀ z ∈ good, ∀ j<deg, (P z).coeff j = (B j).eval z
  ──ProximityGap.RS_jointAgreement_of_prob_gt_strict_johnson_and_coeff_polys (front door, L1459)──►
jointAgreement
  ──ProximityGap.correlatedAgreement_affine_curves_of_strict_coeff_polys_and_boundary (L1720)──►
δ_ε_correlatedAgreementCurves                                    (the keystone goal)
```

`betaRec` appears in the proof term via `curveCoeffPolys_of_betaRec` (which routes
`tail_zero_of_betaRec_embedding_zero` ⟹ `αFromBeta` ⟹
`betaRec_embedding_eq_zero_of_matchingSet_large`).

## The smallest honest residual hypotheses (NEVER a `sorry`/`axiom`)

1. `hStrictData` — for **each** candidate decoding `P` good on the good set in the strict-Johnson
   range, the genuine §5 extraction data exist: the App-A.4 `betaRec` setup `(x₀, R, H, Bcoeff)`,
   the ingredient-C per-point matching data `(matchingSet, root, mp, hcard)`, the substitution
   validity `hsubst`, the Claim-5.9 form `hγ`, the Prop-5.5 representative `(Ppoly, hrep, hdegX)`,
   and the specialisation bridge `hPz`.  This is *exactly* the input bundle of
   `curveCoeffPolys_of_betaRec`; it is the genuine §5 list-decoding extraction, NOT the conclusion
   (the per-coefficient identity `(P z).coeff j = Bj.eval z` is *derived*, never assumed).

2. `hBoundary` — the closed square-root boundary discharge (`¬δ < 1 - sqrtRate`).  In-tree this
gives
   only `0 < (RS_goodCoeffsCurve …).card`
   (`goodCoeffsCurve_card_pos_of_prob_gt_closed_sqrt_boundary`); reaching `jointAgreement` there
   needs the same §5 input, so it stays an explicit residual.

Neither residual is `≡` the front-door `hcoeffPoly`/the goal: `hStrictData` is a per-`P`
*function-field
extraction* (about `γ`, `betaRec`, the representative), from which the per-coefficient conclusion is
*proven* here.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement chain), §6.2 (Theorem 6.2), Appendix A.4 (recursion (A.1)).
-/

set_option linter.style.longLine false


open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace CorrelatedAgreementListDecodingClosed

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The genuine §5 per-decoding extraction datum (the residual hypothesis)

`Section5StrictData u P` bundles *exactly* the input arguments that
`BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec` consumes, specialised to the good set
`RS_goodCoeffsCurve … u δ`.  It is the genuine §5 list-decoding extraction for the decoding `P`:
the App-A.4 `betaRec` setup, the ingredient-C matching data, the Prop-5.5 representative, and the
specialisation bridge.  Crucially, the per-coefficient conclusion `(P z).coeff j = Bj.eval z` is
**not** part of the datum — it is *proven* from it by `curveCoeffPolys_of_betaRec`. -/
structure Section5StrictData {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
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
  /-- ingredient-C per-point matching data for every tail index `t ≥ k` (uses `betaRec`). -/
  mp : ∀ t, k ≤ t → ∀ z ∈ matchingSet,
    BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z)
  /-- the L9/L10 weight bound for every tail index `t ≥ k` (uses `betaRec`). -/
  hcard : ∀ t, k ≤ t → (↑matchingSet.card : WithBot ℕ)
      > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree
  /-- validity of the BCIKS substitution `X ↦ X − x₀`. -/
  hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ H)
  /-- the Claim-5.9 substitution form of `γ` built from the genuine Hensel coefficients. -/
  hγ : γ x₀ R H hHyp =
    (PowerSeries.mk (BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff)).subst
      (Claim59Conditional.shiftSeries x₀ H)
  /-- the Prop-5.5 polynomial representative of `γ`. -/
  Ppoly : F[X][Y]
  hrep : polyToPowerSeries𝕃 H Ppoly = γ x₀ R H hHyp
  hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1
  /-- the §5 specialisation bridge: at each good `z`, `P z` equals the linear representative at
      `Z = z` (per-point evaluation identity, NOT the per-coefficient conclusion). -/
  hPz : ∀ v₀ v₁ : F[X],
    γ x₀ R H hHyp = polyToPowerSeries𝕃 H
      ((Polynomial.map Polynomial.C v₀) + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
    (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ, P z =
      ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval (Polynomial.C z))
      ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1

/-! ### Transporting §5 data across canonical-family uniqueness

The §5 datum depends on the decoded family only through the final specialization bridge `hPz`.
Thus, if a decoded family agrees with a canonical family on the good set, the canonical datum can be
reused for that decoded family. -/

omit [Nonempty ι] [DecidableEq ι] in
/-- Transport `Section5StrictData` along equality on the good-coefficient set. -/
def section5StrictDataOfEqOnGood {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P P₀ : F → Polynomial F}
    (d : Section5StrictData (k := k) (deg := deg) (domain := domain) (δ := δ) u P₀)
    (hEq : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      P z = P₀ z) :
    Section5StrictData (k := k) (deg := deg) (domain := domain) (δ := δ) u P where
  x₀ := d.x₀
  R := d.R
  H := d.H
  hIrr := d.hIrr
  hPos := d.hPos
  hHyp := d.hHyp
  Bcoeff := d.Bcoeff
  hH := d.hH
  D := d.D
  hD := d.hD
  matchingSet := d.matchingSet
  root := d.root
  mp := d.mp
  hcard := d.hcard
  hsubst := d.hsubst
  hγ := d.hγ
  Ppoly := d.Ppoly
  hrep := d.hrep
  hdegX := d.hdegX
  hPz := by
    intro v₀ v₁ hγlin
    rcases d.hPz v₀ v₁ hγlin with ⟨hPz₀, hv₀, hv₁⟩
    exact ⟨fun z hz => by rw [hEq z hz, hPz₀ z hz], hv₀, hv₁⟩

/-- Canonical §5 data for one received word stack, bundled as data.

The uniqueness field is propositional, but the whole structure lives in `Type`, so it can be used as
an input hypothesis to wrappers that must construct `Section5StrictData` for arbitrary decoded
families. -/
structure StrictCanonicalSection5Data {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) : Type where
  /-- The canonical decoded family for this word stack. -/
  family : F → Polynomial F
  /-- The genuine §5 extraction data for the canonical family. -/
  section5 :
    Section5StrictData (k := k) (deg := deg) (domain := domain) (δ := δ) u family
  /-- Any good decoded family agrees with the canonical family on the good-coefficient set. -/
  unique : ∀ P : F → Polynomial F,
    (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).natDegree < deg ∧
        δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          (P z).eval ∘ domain) ≤ δ) →
    ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      P z = family z

/-! ## Step 1 — the genuine `betaRec ⟹ CurveCoeffPolys` call

From the §5 datum for a decoding `P`, the `betaRec`-driven brick produces the per-coefficient
curve-polynomial datum on the good set.  `betaRec` is consumed in the proof term. -/

omit [Nonempty ι] [DecidableEq ι] in
/-- The §5 datum for `P` yields the per-coefficient curve-polynomial datum on the good set,
**via `curveCoeffPolys_of_betaRec`** (so the proof genuinely uses `betaRec`).  The per-coefficient
identity is derived, not assumed. -/
theorem curveCoeffPolys_of_section5Data {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : Section5StrictData (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    BetaToCurveCoeffPolys.CurveCoeffPolys (F := F) k deg
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) P := by
  haveI := d.hIrr
  haveI := d.hPos
  exact BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec
    d.x₀ d.R d.H d.hHyp d.Bcoeff d.hH d.D d.hD
    d.mp d.hcard d.hsubst d.hγ d.hrep d.hdegX d.hPz

/-! ## Step 2 — bundle into the front-door `hcoeffPoly` shape

`BetaToCurveCoeffPolys.CurveCoeffPolys k deg good P` is *defeq* to
`KeystoneCapstone.CurveCoeffPolys u P` once `good := RS_goodCoeffsCurve … u δ`, so the bundling
lemma
`KeystoneCapstone.hcoeffPoly_witness_of_curveCoeffPolys` applies directly to produce the single
`B : ℕ → Polynomial F` the front door consumes. -/

omit [Nonempty ι] [DecidableEq ι] in
/-- The §5 datum for `P` yields the bundled `hcoeffPoly` existential the front door consumes. -/
theorem hcoeffPoly_witness_of_section5Data {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : Section5StrictData (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ j < deg, (P z).coeff j = (B j).eval z := by
  -- `curveCoeffPolys_of_section5Data d : ∀ j < deg, ∃ Bj, natDegree < k+1 ∧ ∀ z ∈ good, …`
  -- which is defeq to `KeystoneCapstone.CurveCoeffPolys u P`.
  exact KeystoneCapstone.hcoeffPoly_witness_of_curveCoeffPolys u P
    (curveCoeffPolys_of_section5Data d)

/-! ## The strict-Johnson `hcoeffPoly` from the per-decoding §5 datum

The front door's `hcoeffPoly` is `∀ P, (P good) → ∃ B, …`.  The genuine residual is therefore a
*per-`P`* §5 extraction: for every good `P`, the §5 datum exists.  This is the honest minimal
hypothesis (it is `∀ P, (P good) → Section5StrictData u P`, never the per-coefficient conclusion).
-/

omit [Nonempty ι] [DecidableEq ι] in
/-- If every good decoding `P` carries the §5 extraction datum, then the front-door `hcoeffPoly`
hypothesis holds. -/
theorem hcoeffPoly_of_section5Extraction {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι}
    (hExtract : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
      Section5StrictData (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ j < deg, (P z).coeff j = (B j).eval z := by
  intro P hP
  exact hcoeffPoly_witness_of_section5Data (hExtract P hP)

/-! ## The closed keystone

We feed the assembled `hcoeffPoly` to the real strict-Johnson front door and the boundary residual
to
`ProximityGap.correlatedAgreement_affine_curves_of_strict_coeff_polys_and_boundary`, obtaining the
keystone goal `δ_ε_correlatedAgreementCurves`.  No `sorry`. -/

omit [DecidableEq ι] in
/-- **The closed list-decoding keystone (the deliverable).**

Conclusion: *literally* the keystone goal `δ_ε_correlatedAgreementCurves` of
`ProximityGap.correlatedAgreement_affine_curves` (`Curves.lean:1801-1802`).

Residual hypotheses (the smallest honest §5 residuals; none is a `sorry`/`axiom`, none is `≡` the
goal):
* `hExtract` — for every good decoding `P` in the strict-Johnson range, the genuine §5 extraction
  datum `Section5StrictData u P` exists (the `betaRec`/ingredient-C/Prop-5.5 bundle);
* `hBoundary` — the closed square-root boundary `jointAgreement` discharge.

The strict-Johnson branch is wired through `curveCoeffPolys_of_betaRec` (so `betaRec` is consumed),
through the bundling lemma, and through the real front door. -/
theorem correlatedAgreement_affine_curves_listDecoding_closed {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hExtract : ∀ (u : WordStack F (Fin (k + 1)) ι),
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
        Section5StrictData (k := k) (deg := deg) (domain := domain) (δ := δ) u P)
    (hBoundary : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_strict_coeff_polys_and_boundary
    (deg := deg) (domain := domain) (δ := δ) hδ ?_ hBoundary
  -- strict-Johnson branch: assemble `hcoeffPoly` from the per-decoding §5 datum, via `betaRec`.
  intro hk u hprob hJ hsqrt P hP
  exact hcoeffPoly_of_section5Extraction
    (hExtract u hprob hJ hsqrt) P hP

omit [DecidableEq ι] in
/-- Closed list-decoding keystone with the strict branch phrased as one
canonical decoded family per received word stack.

This is the target shape produced by the newer selected-domain/canonical-coefficient
bridges: the strict branch supplies a single `P₀` with coefficient polynomials and
uniqueness for each stack, while the closed square-root boundary is reduced to its
actual data, equality at the boundary plus nonempty good-coefficient set. -/
theorem correlatedAgreement_affine_curves_listDecoding_closed_canonical {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictCanonicalCoeff :
      ∀ u : WordStack F (Fin (k + 1)) ι,
        ∃ P₀ : F → Polynomial F,
          (∃ B : ℕ → Polynomial F,
            (∀ j < deg, (B j).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ j < deg, (P₀ z).coeff j = (B j).eval z) ∧
          ∀ P : F → Polynomial F,
            (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              (P z).natDegree < deg ∧
                δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
                  (P z).eval ∘ domain) ≤ δ) →
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                P z = P₀ z)
    (hBoundaryCard : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      δ = 1 - ReedSolomon.sqrtRate deg domain →
      0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  exact correlatedAgreement_affine_curves_of_uniform_strict_canonical_coeff_polys_and_boundary_card
    (deg := deg) (domain := domain) (δ := δ) hδ hStrictCanonicalCoeff hBoundaryCard

omit [DecidableEq ι] in
/-- Closed list-decoding keystone with branch-specific canonical
coefficient-polynomial data.

This is the coefficient-polynomial analogue of
`correlatedAgreement_affine_curves_listDecoding_closed_of_strict_section5_canonical`: the strict
Johnson branch may use the probability/radius hypotheses to choose its canonical decoded family and
coefficient witnesses, while the closed square-root boundary remains explicit. -/
theorem correlatedAgreement_affine_curves_listDecoding_closed_of_strict_canonical_coeff
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictCanonicalCoeff : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ∃ P₀ : F → Polynomial F,
        (∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ j < deg, (P₀ z).coeff j = (B j).eval z) ∧
        ∀ P : F → Polynomial F,
          (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
            (P z).natDegree < deg ∧
              δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
                (P z).eval ∘ domain) ≤ δ) →
          ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
            P z = P₀ z)
    (hBoundary : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  exact correlatedAgreement_affine_curves_of_strict_canonical_coeff_polys_and_boundary
    (deg := deg) (domain := domain) (δ := δ) hδ hStrictCanonicalCoeff hBoundary

omit [DecidableEq ι] in
/-- Closed list-decoding keystone with the strict branch phrased as one
canonical decoded family with evaluation-polynomial witnesses.

This is the evaluation-polynomial analogue of
`correlatedAgreement_affine_curves_listDecoding_closed_of_strict_canonical_coeff`.
It exposes the existing curve front door through the non-cyclic closed layer. -/
theorem correlatedAgreement_affine_curves_listDecoding_closed_of_strict_canonical_eval
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hStrictCanonicalEval :
      ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
        Pr_{
          let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ] >
            ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
        (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
        δ < 1 - ReedSolomon.sqrtRate deg domain →
        ∃ P₀ : F → Polynomial F,
          (∃ E : ι → Polynomial F,
            (∀ x, (E x).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ x, (P₀ z).eval (domain x) = (E x).eval z) ∧
          ∀ P : F → Polynomial F,
            (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              (P z).natDegree < deg ∧
                δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
                  (P z).eval ∘ domain) ≤ δ) →
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                P z = P₀ z)
    (hBoundary : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  exact correlatedAgreement_affine_curves_of_strict_canonical_eval_polys_and_boundary
    (deg := deg) (domain := domain) (δ := δ) hδ hStrictCanonicalEval hBoundary

omit [Nonempty ι] [DecidableEq ι] in
/-- Turn the genuine §5 extraction datum for one canonical decoded family into
the canonical coefficient-polynomial package consumed by the closed keystone.

The coefficient witnesses are still derived from `Section5StrictData` through
`curveCoeffPolys_of_betaRec`; the only extra assumption is the expected
uniqueness statement identifying every good decoding with the chosen canonical
family `P₀`. -/
theorem canonicalCoeffPolys_of_section5CanonicalData {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P₀ : F → Polynomial F}
    (d : Section5StrictData (k := k) (deg := deg) (domain := domain) (δ := δ) u P₀)
    (hunique : ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
      ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        P z = P₀ z) :
    (∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ j < deg, (P₀ z).coeff j = (B j).eval z) ∧
    ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
      ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        P z = P₀ z := by
  exact ⟨hcoeffPoly_witness_of_section5Data d, hunique⟩

omit [DecidableEq ι] in
/-- Closed list-decoding keystone where the strict branch supplies exactly the
canonical §5 extraction data for one family `P₀` per stack, plus uniqueness.

This is the direct residual target for the current §5 assembly: the betaRec
extraction datum is still genuine `Section5StrictData`, while the theorem
packages it into the canonical-coefficient front door automatically. -/
theorem correlatedAgreement_affine_curves_listDecoding_closed_of_section5_canonical
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hCanonicalExtract :
      ∀ u : WordStack F (Fin (k + 1)) ι,
        ∃ P₀ : F → Polynomial F,
          ∃ _ : Section5StrictData (k := k) (deg := deg) (domain := domain) (δ := δ) u P₀,
          ∀ P : F → Polynomial F,
            (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              (P z).natDegree < deg ∧
                δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
                  (P z).eval ∘ domain) ≤ δ) →
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              P z = P₀ z)
    (hBoundaryCard : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      δ = 1 - ReedSolomon.sqrtRate deg domain →
      0 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_listDecoding_closed_canonical
    (deg := deg) (domain := domain) (δ := δ) hδ ?_ hBoundaryCard
  intro u
  obtain ⟨P₀, d, hunique⟩ := hCanonicalExtract u
  exact ⟨P₀, canonicalCoeffPolys_of_section5CanonicalData d hunique⟩

omit [DecidableEq ι] in
/-- Closed list-decoding keystone with branch-specific canonical §5 extraction data.

In the strict Johnson branch, it is enough to provide one canonical decoded family `P₀` carrying
`Section5StrictData`, plus uniqueness of all good decodings against `P₀`.  The proof transports the
canonical datum to each decoded family using `section5StrictData_of_eq_on_good`, then calls the
per-decoding closed keystone. -/
theorem correlatedAgreement_affine_curves_listDecoding_closed_of_strict_section5_canonical
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hCanonicalExtract : ∀ (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      StrictCanonicalSection5Data (k := k) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundary : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_listDecoding_closed
    (deg := deg) (domain := domain) (δ := δ) hδ ?_ hBoundary
  intro u hprob hJ hsqrt P hP
  let c := hCanonicalExtract u hprob hJ hsqrt
  exact section5StrictDataOfEqOnGood c.section5 (c.unique P hP)

end CorrelatedAgreementListDecodingClosed

end ArkLib
