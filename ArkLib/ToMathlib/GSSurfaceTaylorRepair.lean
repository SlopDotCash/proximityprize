/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.GSSurfaceKeystone
import ArkLib.ToMathlib.PerZProximateRoot

/-!
# Issue #304 — the Taylor-faithful per-place cargo (the coordinate repair)

**The finding.**  The matching polynomial `f z = (R.map (coeffHom_loc x₀)).map (π̂_z)` is
built through `taylorAlgHom (C x₀)`: its series coordinate is the **domain variable
recentred at `x₀`**.  The faithful decoded root is therefore the Taylor coercion
`aPTaylor x₀ (P z) = ↑(taylor x₀ (P z))` (what `PerZProximateRoot.aPTaylor_dvd` produces) —
NOT the plain coercion `↑(P z)` appearing in the `hdvd`/`hcong` fields of
`curveFamilyData_of_truncatedLocalRoot` and `GSSurfaceData`.  Those plain-coercion fields
are instantiable only at recentring-invariant families (e.g. the constants of the
non-vacuity witness).

**The repair (no re-proving).**  The Taylor cargo for the family `P` IS the plain cargo for
the shifted family `z ↦ taylor x₀ (P z)`:

* `aPTaylor_eq_coe` — `aPTaylor x₀ P = ↑(taylor x₀ P)`;
* `hdvdP_of_matching` / `hcong_of_branch_value` — the shifted bundle's per-place fields are
  literally the matching-lane outputs (`aPTaylor_dvd`, `aPTaylor_cong`);
* `taylor_comp_sub` / `curveFamilyData_comp_shift` — `CurveFamilyData` transports back
  through `X ↦ X − s`: the curve identity for the shifted family yields the curve identity
  for `P` with coefficients `c_t ∘ (X − C s)` (same `n`, same curve centre);
* `correlatedAgreement_affine_curves_of_GS_surface_taylor` — **the faithful keystone front
  door**: correlated agreement from a per-`(u, P)` producer of the bundle at a shifted
  family `(s, GSSurfaceData u (taylor s ∘ P))` — the exact shape the GS matching lane
  instantiates.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5–§6, Appendix A.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open scoped BigOperators

namespace ArkLib

namespace GSSurfaceKeystone

variable {F : Type} [Field F]

/-- The proximate root IS the plain coercion of the Taylor-shifted polynomial. -/
theorem aPTaylor_eq_coe (x₀ : F) (P : F[X]) :
    PerZProximateRoot.aPTaylor x₀ P
      = ((Polynomial.taylor x₀ P : F[X]) : PowerSeries F) := by
  ext n
  rw [PerZProximateRoot.aPTaylor, PerZProximateRoot.coeff_taylorCoerce,
    Polynomial.coeff_coe]

section Cargo

variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The faithful `hdvdP`**: the shifted bundle's per-place divisibility is literally the
matching-lane output. -/
theorem hdvdP_of_matching {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) {P : F[X]}
    (hdvd : Polynomial.X - Polynomial.C P ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) :
    (Polynomial.X - Polynomial.C ((Polynomial.taylor x₀ P : F[X]) : PowerSeries F)) ∣
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z root hx))) := by
  rw [← aPTaylor_eq_coe]
  exact PerZProximateRoot.aPTaylor_dvd hHyp z root hx hdvd

/-- **The faithful `hcong`**: the shifted bundle's order-0 congruence from the decoded
branch value. -/
theorem hcong_of_branch_value {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z) {P : F[X]}
    (hval : (P.eval x₀ : F) = root.1) :
    ((Polynomial.taylor x₀ P : F[X]) : PowerSeries F)
        - PowerSeries.C ((π_z z root) (βHensel H x₀ R hHyp 0))
      ∈ Ideal.span {(PowerSeries.X : PowerSeries F)} := by
  rw [← aPTaylor_eq_coe]
  exact PerZProximateRoot.aPTaylor_cong hHyp z root hval

end Cargo

/-- Finite sums distribute over composition. -/
theorem finset_sum_comp {κ : Type} (t : Finset κ) (f : κ → F[X]) (q : F[X]) :
    (∑ i ∈ t, f i).comp q = ∑ i ∈ t, (f i).comp q := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha,
      Polynomial.add_comp, ih]

/-- Taylor shift inverts by composition with `X − C s`. -/
theorem taylor_comp_sub (s : F) (p : F[X]) :
    (Polynomial.taylor s p).comp (Polynomial.X - Polynomial.C s) = p := by
  rw [Polynomial.taylor_apply, Polynomial.comp_assoc, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp, sub_add_cancel, Polynomial.comp_X]

section Transport

open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped ENNReal ProbabilityTheory LinearCode

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Fintype F] [DecidableEq F]

/-- **`CurveFamilyData` transports through the Taylor shift**: a curve datum for the shifted
family `z ↦ taylor s (P z)` yields one for `P`, with coefficients `c_t ∘ (X − C s)`. -/
noncomputable def curveFamilyData_comp_shift {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F} (s : F)
    (D : FaithfulCurveExtraction.CurveFamilyData (k := k) (deg := deg) (domain := domain)
      (δ := δ) u (fun z => Polynomial.taylor s (P z))) :
    FaithfulCurveExtraction.CurveFamilyData (k := k) (deg := deg) (domain := domain)
      (δ := δ) u P where
  x₀ := D.x₀
  n := D.n
  hn := D.hn
  c := fun t => (D.c t).comp (Polynomial.X - Polynomial.C s)
  hPz := fun z hz => by
    have h := congrArg (fun q : Polynomial F => q.comp (Polynomial.X - Polynomial.C s))
      (D.hPz z hz)
    simp only at h
    rw [taylor_comp_sub] at h
    rw [h, finset_sum_comp]
    exact Finset.sum_congr rfl fun t _ => Polynomial.smul_comp _ _ _

/-- **THE FAITHFUL KEYSTONE FRONT DOOR (Taylor-corrected)**: correlated agreement for affine
curves in the Johnson regime from a per-`(u, P)` producer of the GS-surface bundle at a
Taylor-shifted family — the exact shape the GS matching lane instantiates
(`hdvdP_of_matching`, `hcong_of_branch_value`). -/
theorem correlatedAgreement_affine_curves_of_GS_surface_taylor
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
        (s : F) ×' GSSurfaceData (k := k) (deg := deg) (domain := domain) (δ := δ) u
          (fun z => Polynomial.taylor s (P z))) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  FaithfulCurveExtraction.correlatedAgreement_affine_curves_johnson_of_curveFamilyData_strict
    hδ
    (fun hk u hprob hJ hδ' P hP =>
      curveFamilyData_comp_shift (hInput hk u hprob hJ hδ' P hP).1
        (curveFamilyData_of_gsSurfaceData (hInput hk u hprob hJ hδ' P hP).2))

end Transport

end GSSurfaceKeystone

end ArkLib

/-! ## Axiom audit. -/
#print axioms ArkLib.GSSurfaceKeystone.aPTaylor_eq_coe
#print axioms ArkLib.GSSurfaceKeystone.hdvdP_of_matching
#print axioms ArkLib.GSSurfaceKeystone.hcong_of_branch_value
#print axioms ArkLib.GSSurfaceKeystone.taylor_comp_sub
#print axioms ArkLib.GSSurfaceKeystone.curveFamilyData_comp_shift
#print axioms ArkLib.GSSurfaceKeystone.correlatedAgreement_affine_curves_of_GS_surface_taylor
