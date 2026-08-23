/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.FaithfulCurveExtraction
import ArkLib.ToMathlib.HPzBridge

/-!
# Issue #304 — the per-`z` Hensel production of the faithful curve-family datum

`FaithfulCurveExtraction.lean` established the faithful §5 extraction surface: the per-`(u, P)`
`CurveFamilyData` (the decoded family lies on a polynomial curve
`P z = ∑_{t<n} (z − x₀)^t • c_t`) discharges `StrictCoeffPolysResidual` and reaches the keystone
`δ_ε_correlatedAgreementCurves`.  This file retargets the per-`z` Hensel-uniqueness machinery of
`HPzBridge` (BCIKS20 §6.2: "`π_z(γ) = P_z` by Hensel uniqueness") at that faithful surface:

* `eval_identity_of_curveHensel` — at each good `z`, if the coordinate power-series lifts of the
  decoded `P z` and of the **curve specialization** `∑_{t<n} (z − x₀)^t • c_t` are both roots of
  a common separable matching polynomial `f z`, both congruent mod `X` to a common approximation
  `a₀ z` at which `f z`'s derivative is a unit, then `P z` **equals** the curve specialization —
  `HPzBridge.decoded_eq_specialization_of_hensel` applied with the faithful competing root.
* `CurveHenselDatum` — the per-`(u, P)` bundle of that per-`z` Hensel root data, for a given
  centre `x₀` and curve coefficients `c : ℕ → F[X]` (the faithful analogue of
  `HPzBridge.HenselDatum`, with the curve specialization replacing the transposed
  linear-representative specialization).
* `curveFamilyData_of_curveHenselDatum` — the production: the Hensel datum yields the full
  `CurveFamilyData`, hence (composing `FaithfulCurveExtraction`) the keystone front doors:
* `strictCoeffPolysResidual_of_curveHenselDatum` and
  `correlatedAgreement_affine_curves_johnson_of_curveHenselDatum_strict` — the §5 keystone goal
  from a per-`(u, P)` producer of the per-`z` curve-Hensel data.

## The honest remaining inputs after this file

For each word `u` and decoded family `P` (good in the strict-Johnson range), the producer must
supply: a centre `x₀`, at most `k + 1` curve coefficients `c_t ∈ F[X]`, and per good `z` the
matching polynomial `f z` over `F⟦X⟧` with the two root facts, the two mod-`X` congruences, and
the unit derivative.  In BCIKS20 these come from the GS interpolant specialized at `z` (the
matching-factor divisibility) together with the genuine Hensel-lift chain: the curve coefficients
are the base-rational readings of the truncated `αGenuine` (the §5 rational-section content), and
the root facts are the §6.2 specialization geometry.  All of these are statements about genuine
analytic objects — no transposed representative, no `polyToPowerSeries𝕃`-shape, no opaque legacy
`β`/`γ` anywhere.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (Prop. 5.5), §6.2 (Hensel uniqueness `π_z(γ) = P_z`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace FaithfulCurveExtraction

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Part 1 — the per-`z` pin: Hensel uniqueness against the curve specialization -/

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- **The per-`z` identity from the curve-Hensel datum.**  At a single good `z`, if `↑(P z)` and
the lift of the curve specialization `∑_{t<n} (z − x₀)^t • c_t` are both roots of a common
separable matching polynomial, both congruent mod `X` to a common approximation with unit
derivative, then `P z` equals the curve specialization.  This is
`HPzBridge.decoded_eq_specialization_of_hensel` with the faithful competing root. -/
theorem eval_identity_of_curveHensel {P : F → Polynomial F}
    {x₀ : F} {n : ℕ} {c : ℕ → F[X]} {z : F}
    (f : Polynomial (PowerSeries F)) {a₀ : PowerSeries F}
    (hProot : f.IsRoot ((P z : F[X]) : PowerSeries F))
    (hQroot : f.IsRoot
      (((∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X])) : PowerSeries F))
    (hPapprox : ((P z : F[X]) : PowerSeries F) - a₀
      ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hQapprox : (((∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X])) : PowerSeries F) - a₀
      ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hderiv : IsUnit (f.derivative.eval a₀)) :
    P z = ∑ t ∈ Finset.range n, (z - x₀) ^ t • c t :=
  HPzBridge.decoded_eq_specialization_of_hensel (f := f) (a₀ := a₀)
    hProot hQroot hPapprox hQapprox hderiv

/-! ## Part 2 — the per-`(u, P)` curve-Hensel bundle -/

/-- **The faithful per-`z` Hensel root datum** for a given centre `x₀` and curve coefficients
`c`.  At every good `z` it supplies the matching polynomial `f z`, the common approximation
`a₀ z`, the two root facts (for the decoded `P z` and for the **curve specialization**
`∑_{t<n} (z − x₀)^t • c_t`), the two mod-`X` congruences, and the unit derivative — exactly the
input of `HPzBridge.decoded_eq_specialization_of_hensel`, with the faithful competing root
replacing the (refuted) transposed linear-representative specialization. -/
structure CurveHenselDatum {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F)
    (x₀ : F) (n : ℕ) (c : ℕ → F[X]) : Type where
  /-- per-`z` matching polynomial over `F⟦X⟧`. -/
  f : F → Polynomial (PowerSeries F)
  /-- per-`z` common approximation. -/
  a₀ : F → PowerSeries F
  /-- `↑(P z)` is a root of the matching polynomial. -/
  hProot : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (f z).IsRoot ((P z : F[X]) : PowerSeries F)
  /-- the lift of the curve specialization is a root of the matching polynomial. -/
  hQroot : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (f z).IsRoot (((∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X])) : PowerSeries F)
  /-- `↑(P z)` reduces to the approximation mod `X`. -/
  hPapprox : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    ((P z : F[X]) : PowerSeries F) - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}
  /-- the curve specialization reduces to the approximation mod `X`. -/
  hQapprox : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (((∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X])) : PowerSeries F) - a₀ z
      ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}
  /-- the matching coordinate is a simple root (unit derivative). -/
  hderiv : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    IsUnit ((f z).derivative.eval (a₀ z))

omit [Nonempty ι] [DecidableEq ι] in
/-- **The production: curve-Hensel datum ⟹ the faithful curve-family datum.**  Per good `z`,
Hensel uniqueness pins `P z` equal to the curve specialization; with `n < k + 2` this is the
full `CurveFamilyData`. -/
noncomputable def curveFamilyData_of_curveHenselDatum {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} {n : ℕ} {c : ℕ → F[X]} (hn : n < k + 2)
    (d : CurveHenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P x₀ n c) :
    CurveFamilyData (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  { x₀ := x₀
    n := n
    hn := hn
    c := c
    hPz := fun z hz =>
      eval_identity_of_curveHensel (f := d.f z) (a₀ := d.a₀ z)
        (d.hProot z hz) (d.hQroot z hz) (d.hPapprox z hz) (d.hQapprox z hz) (d.hderiv z hz) }

/-! ## Part 3 — keystone front doors from the curve-Hensel producer -/

omit [Nonempty ι] [DecidableEq ι] in
/-- **`StrictCoeffPolysResidual` from a per-`(u, P)` curve-Hensel producer.**  The producer
supplies, for each word and decoded family in the strict-Johnson range, a centre, at most
`k + 1` curve coefficients, and the per-`z` Hensel root data — the honest §6.2 inputs. -/
theorem strictCoeffPolysResidual_of_curveHenselDatum
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
        Σ' (x₀ : F) (n : ℕ) (_ : n < k + 2) (c : ℕ → F[X]),
          CurveHenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P x₀ n c) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  obtain ⟨x₀, n, hn, c, d⟩ := hInput hk u hprob hJ hsqrt P hP
  exact hcoeffPoly_witness_of_curveFamilyData (curveFamilyData_of_curveHenselDatum hn d)

omit [DecidableEq ι] in
/-- **Strict square-root-radius keystone front door from the curve-Hensel producer.**  The §5
keystone goal `δ_ε_correlatedAgreementCurves` in the strict Johnson regime, from per-`(u, P)`
curve-Hensel data.  Every hypothesis is an honest BCIKS20 §5/§6.2 object. -/
theorem correlatedAgreement_affine_curves_johnson_of_curveHenselDatum_strict
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
        Σ' (x₀ : F) (n : ℕ) (_ : n < k + 2) (c : ℕ → F[X]),
          CurveHenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P x₀ n c) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_strict_coeff_polys
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun hk u hprob hJ P hP => by
      obtain ⟨x₀, n, hn, c, d⟩ := hInput hk u hprob hJ hδ P hP
      exact hcoeffPoly_witness_of_curveFamilyData (curveFamilyData_of_curveHenselDatum hn d))

end FaithfulCurveExtraction

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.FaithfulCurveExtraction.eval_identity_of_curveHensel
#print axioms ArkLib.FaithfulCurveExtraction.CurveHenselDatum
#print axioms ArkLib.FaithfulCurveExtraction.curveFamilyData_of_curveHenselDatum
#print axioms ArkLib.FaithfulCurveExtraction.strictCoeffPolysResidual_of_curveHenselDatum
#print axioms ArkLib.FaithfulCurveExtraction.correlatedAgreement_affine_curves_johnson_of_curveHenselDatum_strict
