/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.KeystoneStrictResidual
import ArkLib.ToMathlib.HPzBridge
import ArkLib.ToMathlib.GSFactorData
import ArkLib.ToMathlib.BetaWeightGradedSupply

/-!
# Issue #304 — the off-centre per-`P` §5 bundle and its producer assembly

## Why this file exists (two satisfiability obstructions in the existing surfaces)

The two existing §5 keystone surfaces each carry a *constructibility* defect:

1. **The centred surface is pinned to the opaque legacy numerator.**
   `HcardDischarge.Section5StrictDataFin` (and `KeystoneAssembly.section5DataFin_of_producers`,
   which carries the residual `hβ : ∀ t, β R t = betaRec …`) state their `hγ`/`hrep`/`hPz`
   fields against the in-tree `γ x₀ R H hHyp`, which is built from the legacy
   `RationalFunctions.β` — an `Exists.choose` of the weight-only `β_regular`.  Nothing beyond
   the weight bound is provable about an `Exists.choose`, so `hβ` (hence `hγ`, hence the bundle)
   is **permanently undischargeable**: the centred producer route can organize hypotheses but can
   never be instantiated.  (This is the L13 finding; `RationalFunctionsStrong.β_strong` repairs
   the *definition*, but the centred bundle still names the legacy `γ`.)  Independently, the
   centred `hsubst` field is satisfiable only at `x₀ = 0`
   (`SubstFieldCaveat.hasSubst_shiftSeries_iff_eq_zero`).

2. **The off-centre bundles quantify `hPz` over an unconstrained `P`.**
   `KeystoneStrictResidual.BetaCurveInputOffcentre`/`…OffcentreFin` are γ-free (they use the
   `betaRec`-built `gammaLocal`), but their `hPz` field quantifies over **all**
   `P : F → Polynomial F` with no decoded-family constraint.  Once the good set is nonempty and
   the linear-representative premise is satisfiable (which `hrep`/`hdegX` guarantee — the §5
   construction *produces* such a representative), the conclusion `∀ z ∈ good, P z = …` must hold
   for *every* `P` simultaneously, which is absurd: the bundle is **unsatisfiable** exactly in the
   regime it is meant to serve.  The satisfiable shape is the per-`P` one used by
   `Section5StrictDataFin`, where `P` is a structure parameter supplied *with* its decoded-family
   hypothesis by the residual's quantifier order (`∀ u … ∀ P, hP → bundle`).

This file provides the missing combination — **off-centre AND per-`P`**:

* `Section5StrictDataOffcentreFin u P` — the γ-free, `hsubst`-free, per-`P` §5 extraction
  datum.  Every field is honestly satisfiable: `hrep` is stated against
  `BetaToCurveCoeffPolys.gammaLocal` (the `betaRec`-built local series — genuine mathematics,
  no opaque choice anywhere), and `hPz` is per-`P` with the Taylor-shift recentering of the
  off-centre keystone.
* `htailDeg_of_offcentre_representative` — the off-centre `htailDeg` producer.  Strictly simpler
  than the centred `TailDegProducer.htailDeg_of_polynomial_representative`: since `hrep` is
  directly against `gammaLocal = mk (αFromBeta …)`, no `hsubst`/`hγ` collapse is needed — the
  tail vanishing is pure coefficient reading of a polynomial coercion.
* `hPz_offcentre_of_henselDatum` — the off-centre `hPz` producer: the per-`z` Hensel root datum
  (`HPzBridge.HenselDatum`, at the Taylor-shifted representative) yields the per-`z` identity by
  Hensel uniqueness (`HPzBridge.eval_identity_of_henselDatum`), plus the degree bounds.
* `curveCoeffPolys_of_section5DataOffcentreFin` / `hcoeffPoly_witness_of_section5DataOffcentreFin`
  — the bundle consumers, routing through the proven off-centre keystone
  `BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec_offcentreFin`.
* `strictCoeffPolysResidual_of_section5DataOffcentreFin` — the residual discharge: a per-`(u, P)`
  producer of the bundle discharges `StrictCoeffPolysResidual`.
* `correlatedAgreement_affine_curves_johnson_of_section5DataOffcentreFin_strict` (and the
  closed-radius variant) — the keystone front doors: `δ_ε_correlatedAgreementCurves` from the
  per-`(u, P)` off-centre bundle producer.
* `section5DataOffcentreFin_of_producers` — the producer assembly (the off-centre analogue of
  `KeystoneAssembly.section5DataFin_of_producers`): builds the bundle from the GS factor bundle,
  the matching geometry, the Hensel data, and the Prop-5.5 representative — with `htailDeg`
  *derived* (not assumed) and **no `hβ`, no `hγ`, no `hsubst` anywhere in the hypothesis list**.
* `section5DataOffcentreFin_of_producers_gradedDisc` — the capstone instantiation at the
  **canonical** `Bcoeff := BCIKS20.HenselNumerator.B_coeff`: the `hcardFin` item is discharged by
  the proven graded weight collapse (`betaRec_weight_le_graded` via `hcardFin_of_graded`) fed by
  the discriminant bad-set counting (`gradedConcreteFin_of_disc`).  The App-A.4 weight budgets
  are **theorems** here (`B_coeff_weight_le_graded`, `weight_ξ_bound`, monic `W`-weight), not
  hypotheses.

## The honest remaining frontier after this file

With this assembly, the strict-Johnson §5 keystone for the canonical coefficients reduces to
exactly the per-word data:
1. the GS factor bundle `b : GSFactorData.Bundle x₀` with `b.H` monic, `2 ≤ natDegreeY b.R`,
   and the paper grading `hR : degreeX (R.coeff j) ≤ D − j` (the GS interpolant shape);
2. the Prop-5.5 representative `Ppoly` with `hrep : polyToPowerSeries𝕃 H Ppoly = gammaLocal …`
   and `hdegX : degreeX Ppoly ≤ 1` (linearity of the lift in `Z`);
3. the per-point matching data `mpPoint` on `[k, deg Ppoly]` (ingredient C / L12 geometry);
4. the per-`z` Hensel root data `hHensel`/`hdeg` at the Taylor-shifted representative;
5. the §6 discriminant counting: a nonzero `disc` whose non-vanishing locus the matching set
   covers, with `|F|` beyond the graded budget plus `deg disc`.

None of these names an opaque object; each is a genuine [BCIKS20] §5/§6/App-A obligation.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement chain), §6.2 (Theorem 6.2), Appendix A.2/A.4.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

-- The bundle carries `[DecidableEq ι]` context because the downstream front doors need it.
set_option linter.unusedDecidableInType false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace OffcentreKeystone

/-! ## Part 1 — the off-centre `htailDeg` producer (pure coefficient reading)

The centred producer (`TailDegProducer.htailDeg_of_polynomial_representative`) needed
`hsubst`/`hγ` to collapse the substitution before reading coefficients.  Off-centre there is
nothing to collapse: `hrep` equates the polynomial coercion with `gammaLocal = mk (αFromBeta …)`
directly, so the tail vanishing is the coefficient identity
`αFromBeta t = liftToFunctionField (Ppoly.coeff t)` plus `coeff_eq_zero_of_natDegree_lt`. -/

section TailDeg

variable {F : Type} [Field F]

/-- **The off-centre `htailDeg` producer.**  From the off-centre Prop-5.5 representative
`hrep : polyToPowerSeries𝕃 H Ppoly = gammaLocal …` alone (no `hsubst`, no `hγ`), the Hensel-lift
coefficients vanish past the representative's degree:
`∀ t > deg Ppoly, αFromBeta … t = 0`. -/
theorem htailDeg_of_offcentre_representative {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H} {Ppoly : F[X][Y]}
    (hrep : polyToPowerSeries𝕃 H Ppoly = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp Bcoeff) :
    ∀ t, Ppoly.natDegree < t → BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t = 0 := by
  intro t ht
  have h := congrArg (PowerSeries.coeff t) hrep
  rw [coeff_polyToPowerSeries𝕃, BetaToCurveCoeffPolys.coeff_gammaLocal] at h
  rw [← h, Polynomial.coeff_eq_zero_of_natDegree_lt ht, map_zero]

/-- Monotone form: the off-centre tail producer for any cutoff at least the representative's
degree. -/
theorem htailDeg_of_offcentre_representative_le_bound {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H} {Ppoly : F[X][Y]}
    (hrep : polyToPowerSeries𝕃 H Ppoly = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp Bcoeff)
    {T : ℕ} (hT : Ppoly.natDegree ≤ T) :
    ∀ t, T < t → BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t = 0 := fun t ht =>
  htailDeg_of_offcentre_representative hrep t (lt_of_le_of_lt hT ht)

end TailDeg

/-! ## Part 2 — the off-centre per-`P` §5 bundle

`Section5StrictDataFin` with the two centred-only (and `Exists.choose`-pinned) fields removed:
* no `hsubst` (provably false off-centre, vacuous at the centre);
* no `hγ` (the legacy-`γ` identification, undischargeable);
* `hrep` stated against the `betaRec`-built local series `gammaLocal`;
* `hPz` in the off-centre Taylor-shift shape, **per-`P`** (the structure parameter), so the
  bundle is satisfiable — unlike the `∀ P`-quantified `BetaCurveInputOffcentreFin.hPz`. -/

section Bundle

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The off-centre per-`P` §5 extraction datum** — the satisfiable, γ-free, `hsubst`-free
counterpart of `HcardDischarge.Section5StrictDataFin`.  All series-level fields are stated
against the `betaRec`-built `gammaLocal`; the per-`z` bridge `hPz` carries the off-centre
Taylor-shift recentering and is per-`P` (the structure parameter). -/
structure Section5StrictDataOffcentreFin {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
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
  `htailDeg_of_offcentre_representative` when `T ≥ deg Ppoly`). -/
  htailDeg : ∀ t, T < t → BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t = 0
  /-- the Prop-5.5 polynomial representative of the **local** Hensel series. -/
  Ppoly : F[X][Y]
  hrep : polyToPowerSeries𝕃 H Ppoly = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp Bcoeff
  hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1
  /-- the §5 specialisation bridge at each good `z`, in the off-centre Taylor-shift shape:
  for any local linear representative `(v₀, v₁)` of the truncated local series, the decoded
  `P z` equals the recentred representative at `Z = z`, and the local components obey the
  §5 degree bounds. -/
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

/-! ## Part 3 — bundle consumers -/

omit [Nonempty ι] [DecidableEq ι] in
/-- The off-centre per-`P` datum yields the per-coefficient curve-polynomial datum on the good
set, via the proven off-centre keystone `curveCoeffPolys_of_betaRec_offcentreFin`.  `betaRec` is
genuinely consumed; no legacy `β`/`γ` appears anywhere on this path. -/
theorem curveCoeffPolys_of_section5DataOffcentreFin {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : Section5StrictDataOffcentreFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    BetaToCurveCoeffPolys.CurveCoeffPolys (F := F) k deg
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) P := by
  haveI := d.hIrr
  haveI := d.hPos
  exact BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec_offcentreFin
    d.x₀ d.R d.H d.hHyp d.Bcoeff d.hH d.D d.hD
    d.mpFin d.hcardFin d.htailDeg d.hrep d.hdegX d.hPz

omit [Nonempty ι] [DecidableEq ι] in
/-- The off-centre per-`P` datum yields the bundled `hcoeffPoly` existential the front door
consumes. -/
theorem hcoeffPoly_witness_of_section5DataOffcentreFin {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : Section5StrictDataOffcentreFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ j < deg, (P z).coeff j = (B j).eval z :=
  KeystoneCapstone.hcoeffPoly_witness_of_curveCoeffPolys u P
    (curveCoeffPolys_of_section5DataOffcentreFin d)

/-! ## Part 4 — residual discharge and keystone front doors -/

omit [Nonempty ι] [DecidableEq ι] in
/-- **`StrictCoeffPolysResidual` from a per-`(u, P)` off-centre bundle producer.**  The producer
receives the probability/Johnson hypotheses *and* the decoded-family hypothesis `hP` — the
satisfiable quantifier order. -/
theorem strictCoeffPolysResidual_of_section5DataOffcentreFin
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
        Section5StrictDataOffcentreFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  exact hcoeffPoly_witness_of_section5DataOffcentreFin (hInput hk u hprob hJ hsqrt P hP)

omit [DecidableEq ι] in
/-- **Strict square-root-radius keystone front door (off-centre, per-`P`).**  The §5 keystone
goal `δ_ε_correlatedAgreementCurves` in the strict Johnson regime, from a per-`(u, P)` producer
of the off-centre bundle.  No `hβ`/`hγ`/`hsubst` residual appears in the hypothesis list. -/
theorem correlatedAgreement_affine_curves_johnson_of_section5DataOffcentreFin_strict
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
        Section5StrictDataOffcentreFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_strict_coeff_polys
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun hk u hprob hJ P hP =>
      hcoeffPoly_witness_of_section5DataOffcentreFin (hInput hk u hprob hJ hδ P hP))

/-- **Closed square-root-radius keystone front door (off-centre, per-`P`).**  As the strict
front door, with the boundary branch supplied as the packaged `BoundaryCardResidual`. -/
theorem correlatedAgreement_affine_curves_johnson_of_section5DataOffcentreFin
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
        Section5StrictDataOffcentreFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P)
    (hBoundaryCard : BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_boundaryCardResidual
    (k := k) (deg := deg) (domain := domain) (δ := δ)
    (strictCoeffPolysResidual_of_section5DataOffcentreFin hInput) hBoundaryCard hδ

/-! ## Part 5 — the off-centre `hPz` producer (Hensel-uniqueness route) -/

omit [Nonempty ι] [DecidableEq ι] in
/-- **The off-centre `hPz` field from the per-`z` Hensel root datum.**  For every local linear
representative `(v₀, v₁)` consistent with the truncated local series, the per-`z` Hensel datum
at the **Taylor-shifted** (recentred) representative pins `P z` equal to the recentred
specialisation by Hensel uniqueness (`HPzBridge.eval_identity_of_henselDatum`); the degree bounds
are carried by `hdeg`.  This is the off-centre analogue of `HPzBridge.hPz_of_henselDatum`. -/
theorem hPz_offcentre_of_henselDatum {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (hHensel : ∀ v₀ v₁ : F[X],
      polyToPowerSeries𝕃 H
          ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))
        = ((PowerSeries.trunc k (BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp Bcoeff) :
            Polynomial (𝕃 H)) : PowerSeries (𝕃 H)) →
      HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P
        (Polynomial.taylor (-x₀) v₀) (Polynomial.taylor (-x₀) v₁))
    (hdeg : ∀ v₀ v₁ : F[X],
      polyToPowerSeries𝕃 H
          ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))
        = ((PowerSeries.trunc k (BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp Bcoeff) :
            Polynomial (𝕃 H)) : PowerSeries (𝕃 H)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    ∀ v₀ v₁ : F[X],
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
        ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1 := by
  intro v₀ v₁ hlin
  exact ⟨HPzBridge.eval_identity_of_henselDatum (hHensel v₀ v₁ hlin),
    (hdeg v₀ v₁ hlin).1, (hdeg v₀ v₁ hlin).2⟩

/-! ## Part 6 — the producer assembly -/

/-- **The off-centre producer assembly** (the satisfiable analogue of
`KeystoneAssembly.section5DataFin_of_producers`).  Builds the off-centre per-`P` bundle from:
the GS factor bundle, the Prop-5.5 local representative (`hrep` against `gammaLocal`), the
per-point matching data, the finite-range cardinality bound, and the per-`z` Hensel data — with
the truncation index fixed at `T := Ppoly.natDegree` and `htailDeg` **derived** from `hrep`.

Compare the centred assembly's hypothesis list: the `hβ` numerator residual, the `hγ`
substitution form, and the `hsubst` validity are all **gone** — none was satisfiable as stated
(the first two name the opaque legacy `β`/`γ`; the third forces `x₀ = 0`). -/
noncomputable def section5DataOffcentreFin_of_producers {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
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
    -- the per-`z` Hensel root datum + degree bounds at the recentred representative:
    (hHensel : ∀ v₀ v₁ : F[X],
      polyToPowerSeries𝕃 b.H
          ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))
        = ((PowerSeries.trunc k (BetaToCurveCoeffPolys.gammaLocal x₀ b.R b.H b.hHyp Bcoeff) :
            Polynomial (𝕃 b.H)) : PowerSeries (𝕃 b.H)) →
      HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P
        (Polynomial.taylor (-x₀) v₀) (Polynomial.taylor (-x₀) v₁))
    (hdeg : ∀ v₀ v₁ : F[X],
      polyToPowerSeries𝕃 b.H
          ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))
        = ((PowerSeries.trunc k (BetaToCurveCoeffPolys.gammaLocal x₀ b.R b.H b.hHyp Bcoeff) :
            Polynomial (𝕃 b.H)) : PowerSeries (𝕃 b.H)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    Section5StrictDataOffcentreFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
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
    htailDeg := htailDeg_of_offcentre_representative hrep
    Ppoly := Ppoly
    hrep := hrep
    hdegX := hdegX
    hPz := hPz_offcentre_of_henselDatum hHensel hdeg }

/-! ## Part 7 — the graded/discriminant capstone at the canonical coefficients

The assembly with `Bcoeff := BCIKS20.HenselNumerator.B_coeff` (the genuine Faà-di-Bruno
coefficients) and the `hcardFin` item **discharged**: the App-A.4 weight budgets are the proven
theorems `B_coeff_weight_le_graded` / `weight_ξ_bound` / monic `W`-weight, collapsed by
`betaRec_weight_le_graded` and fed by the §6 discriminant counting
(`gradedConcreteFin_of_disc`). -/

/-- **The graded/discriminant capstone.**  The off-centre per-`P` bundle at the canonical
`Bcoeff`, with the cardinality front fully discharged from: monic `H`, the Y-degree bound
`2 ≤ d`, the paper grading `hR`, a nonzero discriminant `disc` whose non-vanishing locus the
matching set covers, and the field-size bound `gradedCardBudget(deg Ppoly) + deg disc < |F|`.
The remaining genuine inputs are exactly the §5/§6 geometry: `hrep`/`hdegX` (Prop 5.5),
`mpPoint` (ingredient C / L12), and `hHensel`/`hdeg` (per-`z` Hensel root data). -/
noncomputable def section5DataOffcentreFin_of_producers_gradedDisc
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
    -- the per-`z` Hensel root datum + degree bounds at the recentred representative:
    (hHensel : ∀ v₀ v₁ : F[X],
      polyToPowerSeries𝕃 b.H
          ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))
        = ((PowerSeries.trunc k (BetaToCurveCoeffPolys.gammaLocal x₀ b.R b.H b.hHyp
              (BCIKS20.HenselNumerator.B_coeff b.H x₀ b.R)) :
            Polynomial (𝕃 b.H)) : PowerSeries (𝕃 b.H)) →
      HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P
        (Polynomial.taylor (-x₀) v₀) (Polynomial.taylor (-x₀) v₁))
    (hdeg : ∀ v₀ v₁ : F[X],
      polyToPowerSeries𝕃 b.H
          ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁))
        = ((PowerSeries.trunc k (BetaToCurveCoeffPolys.gammaLocal x₀ b.R b.H b.hHyp
              (BCIKS20.HenselNumerator.B_coeff b.H x₀ b.R)) :
            Polynomial (𝕃 b.H)) : PowerSeries (𝕃 b.H)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    Section5StrictDataOffcentreFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  section5DataOffcentreFin_of_producers
    (k := k) (deg := deg) (domain := domain) (δ := δ) (u := u) (P := P)
    b (BCIKS20.HenselNumerator.B_coeff b.H x₀ b.R) matchingSet root Ppoly hrep hdegX mpPoint
    (hcardFin_of_graded x₀ b.R b.H b.hHyp b.hD b.hH hmonic hd2 hdHD hD_Rx0 hR
      (gradedConcreteFin_of_disc hdisc hcover hbig))
    hHensel hdeg

end Bundle

end OffcentreKeystone

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.OffcentreKeystone.htailDeg_of_offcentre_representative
#print axioms ArkLib.OffcentreKeystone.htailDeg_of_offcentre_representative_le_bound
#print axioms ArkLib.OffcentreKeystone.Section5StrictDataOffcentreFin
#print axioms ArkLib.OffcentreKeystone.curveCoeffPolys_of_section5DataOffcentreFin
#print axioms ArkLib.OffcentreKeystone.hcoeffPoly_witness_of_section5DataOffcentreFin
#print axioms ArkLib.OffcentreKeystone.strictCoeffPolysResidual_of_section5DataOffcentreFin
#print axioms ArkLib.OffcentreKeystone.correlatedAgreement_affine_curves_johnson_of_section5DataOffcentreFin_strict
#print axioms ArkLib.OffcentreKeystone.correlatedAgreement_affine_curves_johnson_of_section5DataOffcentreFin
#print axioms ArkLib.OffcentreKeystone.hPz_offcentre_of_henselDatum
#print axioms ArkLib.OffcentreKeystone.section5DataOffcentreFin_of_producers
#print axioms ArkLib.OffcentreKeystone.section5DataOffcentreFin_of_producers_gradedDisc
