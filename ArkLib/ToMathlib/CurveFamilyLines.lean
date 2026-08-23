/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.CurveFamilyHensel
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.Main
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# Issue #304 — anti-vacuity of the faithful surface + the affine-lines front door

* **Anti-vacuity** (the F-trap guard for the new interface): `curveFamilyData_self` exhibits the
  datum for any family *defined* as a polynomial curve — the bundle is satisfiable, with the
  `hPz` field holding definitionally.  In particular (`curveFamilyData_self_nonaffine_exists`)
  the surface accommodates families whose members have arbitrary codeword degree — exactly what
  the refuted transposed interface could not (`no_linRep_of_nonaffine`).
* **The affine-lines (Theorem 1.4) front door**:
  `RS_correlatedAgreement_affineLines_johnson_of_curveFamilyData_strict` — the BCIKS20
  lines-version correlated agreement (`δ_ε_correlatedAgreementAffineLines`, the statement the
  FRI/STIR batching analyses cite) in the strict square-root regime, from a per-`(u, P)`
  producer of the faithful curve-family datum at `k = 1`: each good decoded family must lie on
  an affine line of codeword polynomials `P z = c₀ + (z − x₀) • c₁`.
* **The numeric (epsCA) keystone wrappers**: `keystone_curves_bound_of_curveFamilyData` and
  `keystone_affineLines_bound_of_curveFamilyData` — the per-round numeric bounds
  `epsCA_curves ≤ k · errorBound` resp. `epsCA ≤ errorBound` that the WHIR keystone reduction
  and the FRI `roundError` accounting consume, through the bridges
  `δ_ε_correlatedAgreementCurves_iff_epsCA_curves_le` /
  `δ_ε_correlatedAgreementAffineLines_iff_epsCA_le` — from the satisfiable faithful front door
  instead of the vacuous small-field one (`keystone_curves_bound_of_card_le`).

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  Theorem 1.4 (lines), §5 (Prop. 5.5).
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

/-! ## Part 1 — anti-vacuity -/

omit [Nonempty ι] [DecidableEq ι] in
/-- **Anti-vacuity witness.**  For any family *defined* as a polynomial curve, the faithful
datum exists — the `hPz` field holds definitionally.  (Contrast `no_linRep_of_nonaffine`: the
refuted transposed interface admits no witness once a member has codeword degree ≥ 2; here the
`c_t` are arbitrary codeword polynomials.) -/
noncomputable def curveFamilyData_self {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (x₀ : F) (n : ℕ) (hn : n < k + 2) (c : ℕ → F[X]) :
    CurveFamilyData (k := k) (deg := deg) (domain := domain) (δ := δ) u
      (fun z => ∑ t ∈ Finset.range n, (z - x₀) ^ t • c t) :=
  { x₀ := x₀, n := n, hn := hn, c := c, hPz := fun _ _ => rfl }

omit [Nonempty ι] [DecidableEq ι] in
/-- The faithful surface accommodates non-affine codeword polynomials: for any `c₀` (of any
codeword degree) the constant family `P z = c₀` carries the datum.  With `2 ≤ c₀.natDegree`
this family refutes the transposed interface (`no_linRep_of_nonaffine`) while carrying the
faithful one — the two interfaces are genuinely separated. -/
noncomputable def curveFamilyData_const {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (c₀ : F[X]) :
    CurveFamilyData (k := k) (deg := deg) (domain := domain) (δ := δ) u (fun _ => c₀) :=
  { x₀ := 0, n := 1, hn := by omega, c := fun _ => c₀,
    hPz := fun z _ => by simp }

/-! ## Part 2 — the affine-lines (Theorem 1.4) front door -/

omit [DecidableEq ι] in
/-- **The faithful affine-lines front door (strict square-root radius).**  The BCIKS20
Theorem-1.4 lines correlated agreement from a per-`(u, P)` producer of the faithful datum at
`k = 1`: each good decoded family lies on an affine line of codeword polynomials.  This is the
statement shape the FRI/STIR batching analyses consume, now reachable through the satisfiable
faithful interface. -/
theorem RS_correlatedAgreement_affineLines_johnson_of_curveFamilyData_strict
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        CurveFamilyData (k := 1) (deg := deg) (domain := domain) (δ := δ) u P) :
    δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_strict (ι := ι) (F := F) (deg := deg)
    (domain := domain) (δ := δ)
    (strictCoeffPolysResidual_of_curveFamilyData
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hInput)
    hδ

/-! ## Part 3 — the numeric (epsCA) keystone wrappers

The per-round quantities the protocol analyses consume are the numeric bounds
`epsCA_curves C k δ δ ≤ k · errorBound` (WHIR keystone reduction, FRI `roundError`) and
`epsCA C δ δ ≤ errorBound` (pairwise batching).  These mirror
`ProximityGap.keystone_curves_bound_of_card_le` (which routes through the *vacuous*
small-field instance) but consume the satisfiable faithful front door instead. -/

/-- **Per-round numeric keystone bound (curves), faithful interface.**  `epsCA_curves ≤
k · errorBound` from a per-`(u, P)` producer of the faithful curve-family datum, via the
numeric bridge `δ_ε_correlatedAgreementCurves_iff_epsCA_curves_le`.  This is the exact
quantity the WHIR keystone reduction and the FRI round-error accounting consume. -/
theorem keystone_curves_bound_of_curveFamilyData
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
        CurveFamilyData (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    epsCA_curves (F := F) (ReedSolomon.code domain deg : Set (ι → F)) k δ δ ≤
      ((k * errorBound δ deg domain : ℝ≥0) : ENNReal) :=
  (δ_ε_correlatedAgreementCurves_iff_epsCA_curves_le (F := F) (k := k)
    (C := (ReedSolomon.code domain deg : Set (ι → F))) δ (errorBound δ deg domain)).mp
    (correlatedAgreement_affine_curves_johnson_of_curveFamilyData_strict hδ hInput)

/-- **Per-round numeric keystone bound (affine lines), faithful interface.**  The pairwise
batching bound `epsCA ≤ errorBound` from a per-`(u, P)` faithful curve-family producer at
`k = 1`, via the bridge `δ_ε_correlatedAgreementAffineLines_iff_epsCA_le`. -/
theorem keystone_affineLines_bound_of_curveFamilyData
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        CurveFamilyData (k := 1) (deg := deg) (domain := domain) (δ := δ) u P) :
    epsCA (F := F) (ReedSolomon.code domain deg : Set (ι → F)) δ δ ≤
      ((errorBound δ deg domain : ℝ≥0) : ENNReal) :=
  (δ_ε_correlatedAgreementAffineLines_iff_epsCA_le (F := F)
    (C := (ReedSolomon.code domain deg : Set (ι → F))) δ (errorBound δ deg domain)).mp
    (RS_correlatedAgreement_affineLines_johnson_of_curveFamilyData_strict hδ hInput)

end FaithfulCurveExtraction

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.FaithfulCurveExtraction.curveFamilyData_self
#print axioms ArkLib.FaithfulCurveExtraction.curveFamilyData_const
#print axioms ArkLib.FaithfulCurveExtraction.RS_correlatedAgreement_affineLines_johnson_of_curveFamilyData_strict
#print axioms ArkLib.FaithfulCurveExtraction.keystone_curves_bound_of_curveFamilyData
#print axioms ArkLib.FaithfulCurveExtraction.keystone_affineLines_bound_of_curveFamilyData
