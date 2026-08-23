/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.OffcentreKeystoneAssembly

/-!
# Issue #304 — the transposed-representative finding and the faithful curve-family surface

## The finding (machine-checked below)

Every §5 keystone surface in-tree routes the coefficient-polynomial extraction through the
"linear representative" shape

```
P z = ((map C v₀) + (C X) * (map C v₁)).eval (C z)        (the hPz conclusion)
```

But (`eval_linear_representative`, already in-tree) this evaluation is
`C (v₀.eval z) + (v₁.eval z) • X` — a polynomial of **degree ≤ 1 in the codeword variable**.
So the `hPz` field of every bundle (`Section5StrictData`, `Section5StrictDataFin`,
`BetaCurveInput*`, `Section5StrictDataOffcentreFin`) can be supplied **only for decoded families
that are affine in the codeword variable**:

* `natDegree_linRep_eval_le_one` — the specialization has `natDegree ≤ 1`, always;
* `no_linRep_of_nonaffine` — any decoded family with a single member of degree `≥ 2` on a good
  point **refutes** the existence of such a representative (hence the `hPz` field, hence the
  bundle).

This is a *transposition* of [BCIKS20] Prop. 5.5: the faithful §5 conclusion is that the decoded
family is **low-degree in the curve parameter `z`** with full-degree codeword-polynomial
coefficients — `P z = ∑_{t<n} (z − x₀)^t • c_t` with `c_t ∈ F[X]` of degree `< deg` and
`n ≤ k + 1` — not affine in the codeword variable with `z`-polynomial coefficients.

## The faithful surface

* `curveCoeffPolys_of_curveFamily` — the faithful extraction: a curve-family datum
  `P z = ∑_{t<n} (z − x₀)^t • c_t` (with `n < k + 2`, i.e. at most `k + 1` coefficients) yields
  `CurveCoeffPolys k deg good P` with `B_j(w) := ∑_{t<n} (c_t).coeff j · (w − x₀)^t` — degree
  `≤ k < k + 1` in the curve parameter, **no degree restriction on the codeword side**.
* `CurveFamilyData` — the per-`(u, P)` faithful §5 extraction datum: a centre, at most `k + 1`
  codeword-polynomial coefficients, and the per-`z` curve identity on the good set.  This is
  literally the BCIKS20 §5 output ("the decoded family lies on a polynomial curve").
* consumers + residual discharge + the strict keystone front door:
  `δ_ε_correlatedAgreementCurves` from a per-`(u, P)` `CurveFamilyData` producer.

The matching/weight/truncation machinery (ingredient C, L9/L10, the graded collapse, the genuine
`gammaGenuine` chain) is unaffected — it feeds the *production* of the curve-family datum; what
changes is only the final extraction interface, which is now both satisfiable and faithful.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (Prop. 5.5, the polynomial-curve conclusion), §6.2.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace FaithfulCurveExtraction

/-! ## Part 1 — the transposition finding, machine-checked -/

section Finding

variable {F : Type} [Field F]

/-- **The linear-representative specialization is always affine in the codeword variable.**
`((map C v₀) + (C X)·(map C v₁)).eval (C z) = C (v₀(z)) + v₁(z) • X` has `natDegree ≤ 1` —
for every `v₀, v₁, z`. -/
theorem natDegree_linRep_eval_le_one (v₀ v₁ : F[X]) (z : F) :
    (((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
        (Polynomial.C z)).natDegree ≤ 1 := by
  rw [BetaToCurveCoeffPolys.eval_linear_representative]
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  simp only [Polynomial.natDegree_C, max_le_iff]
  exact ⟨Nat.zero_le 1, le_trans (Polynomial.natDegree_smul_le _ _) Polynomial.natDegree_X_le⟩

/-- **The transposition refutation.**  If a decoded family has a single member of degree `≥ 2`
at a good point, then NO linear representative satisfies the in-tree `hPz` conclusion — the
`hPz` field of every `Section5StrictData*`/`BetaCurveInput*` bundle is unsatisfiable for that
family.  (The faithful Prop-5.5 shape is affine in the *curve parameter*, not in the codeword
variable; see `curveCoeffPolys_of_curveFamily` for the repaired interface.) -/
theorem no_linRep_of_nonaffine {good : Finset F} {P : F → Polynomial F} {z₀ : F}
    (hz₀ : z₀ ∈ good) (h2 : 2 ≤ (P z₀).natDegree) :
    ¬ ∃ v₀ v₁ : F[X], ∀ z ∈ good, P z =
      ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
          (Polynomial.C z) := by
  rintro ⟨v₀, v₁, hPz⟩
  have h := natDegree_linRep_eval_le_one v₀ v₁ z₀
  rw [← hPz z₀ hz₀] at h
  omega

end Finding

/-! ## Part 2 — the faithful extraction -/

section Extraction

variable {F : Type} [Field F]

/-- **The faithful §5 coefficient extraction.**  If the decoded family lies on a polynomial
curve of at most `k + 1` coefficients centred at `x₀` —
`P z = ∑_{t<n} (z − x₀)^t • c_t` with `n < k + 2` — then `CurveCoeffPolys k deg good P` holds
with the interpolants `B_j(w) := ∑_{t<n} (c_t).coeff j · (w − x₀)^t` (degree `≤ k` in the curve
parameter).  No degree restriction on the codeword-polynomial coefficients `c_t` is needed:
this is the [BCIKS20] Prop-5.5-faithful shape, affine/low-degree in the **curve parameter**. -/
theorem curveCoeffPolys_of_curveFamily {k deg : ℕ} {good : Finset F} {P : F → Polynomial F}
    (x₀ : F) (n : ℕ) (c : ℕ → F[X]) (hn : n < k + 2)
    (hPz : ∀ z ∈ good, P z = ∑ t ∈ Finset.range n, (z - x₀) ^ t • c t) :
    BetaToCurveCoeffPolys.CurveCoeffPolys (F := F) k deg good P := by
  intro j _hj
  refine ⟨∑ t ∈ Finset.range n,
    Polynomial.C ((c t).coeff j) * (Polynomial.X - Polynomial.C x₀) ^ t, ?_, ?_⟩
  · -- degree bound: each term has degree ≤ t ≤ n − 1 ≤ k < k + 1
    refine lt_of_le_of_lt
      (Polynomial.natDegree_sum_le_of_forall_le _ _ (fun t ht => ?_)) (by omega : k < k + 1)
    have ht' : t ≤ k := by
      have := Finset.mem_range.mp ht
      omega
    calc (Polynomial.C ((c t).coeff j) * (Polynomial.X - Polynomial.C x₀) ^ t).natDegree
        ≤ (Polynomial.C ((c t).coeff j)).natDegree
            + ((Polynomial.X - Polynomial.C x₀) ^ t).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ 0 + t * 1 := by
          refine Nat.add_le_add (le_of_eq (Polynomial.natDegree_C _)) ?_
          refine le_trans (Polynomial.natDegree_pow_le) ?_
          exact Nat.mul_le_mul_left t (le_of_eq (Polynomial.natDegree_X_sub_C x₀))
      _ ≤ k := by omega
  · intro z hz
    rw [hPz z hz, Polynomial.finset_sum_coeff, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Polynomial.coeff_smul, smul_eq_mul, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    ring

end Extraction

/-! ## Part 3 — the faithful per-`P` §5 bundle and its keystone front doors -/

section Bundle

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The faithful per-`(u, P)` §5 extraction datum**: the decoded family lies on a polynomial
curve with at most `k + 1` codeword-polynomial coefficients.  This is literally the BCIKS20 §5
output shape — satisfiable for honest decoded families (unlike the linear-representative `hPz`
fields, refuted above for any non-affine family). -/
structure CurveFamilyData {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F) : Type where
  /-- the expansion centre. -/
  x₀ : F
  /-- the number of curve coefficients (at most `k + 1`). -/
  n : ℕ
  hn : n < k + 2
  /-- the codeword-polynomial curve coefficients. -/
  c : ℕ → F[X]
  /-- the per-`z` curve identity on the good set. -/
  hPz : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    P z = ∑ t ∈ Finset.range n, (z - x₀) ^ t • c t

omit [Nonempty ι] [DecidableEq ι] in
/-- The faithful datum yields the per-coefficient curve-polynomial datum on the good set. -/
theorem curveCoeffPolys_of_curveFamilyData {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : CurveFamilyData (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    BetaToCurveCoeffPolys.CurveCoeffPolys (F := F) k deg
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ) P :=
  curveCoeffPolys_of_curveFamily d.x₀ d.n d.c d.hn d.hPz

omit [Nonempty ι] [DecidableEq ι] in
/-- The faithful datum yields the bundled `hcoeffPoly` existential the front door consumes. -/
theorem hcoeffPoly_witness_of_curveFamilyData {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : CurveFamilyData (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ j < deg, (P z).coeff j = (B j).eval z :=
  KeystoneCapstone.hcoeffPoly_witness_of_curveCoeffPolys u P
    (curveCoeffPolys_of_curveFamilyData d)

omit [Nonempty ι] [DecidableEq ι] in
/-- **`StrictCoeffPolysResidual` from a per-`(u, P)` faithful curve-family producer.** -/
theorem strictCoeffPolysResidual_of_curveFamilyData
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
        CurveFamilyData (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  exact hcoeffPoly_witness_of_curveFamilyData (hInput hk u hprob hJ hsqrt P hP)

omit [DecidableEq ι] in
/-- **Strict square-root-radius keystone front door, faithful interface.**  The §5 keystone goal
`δ_ε_correlatedAgreementCurves` in the strict Johnson regime, from a per-`(u, P)` producer of
the faithful curve-family datum.  This is the BCIKS20 Prop-5.5 shape: the producer must show the
decoded family lies on a polynomial curve — nothing more. -/
theorem correlatedAgreement_affine_curves_johnson_of_curveFamilyData_strict
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
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_strict_coeff_polys
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun hk u hprob hJ P hP =>
      hcoeffPoly_witness_of_curveFamilyData (hInput hk u hprob hJ hδ P hP))

/-- **Closed square-root-radius keystone front door, faithful interface** (boundary branch via
the packaged `BoundaryCardResidual`). -/
theorem correlatedAgreement_affine_curves_johnson_of_curveFamilyData
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
        CurveFamilyData (k := k) (deg := deg) (domain := domain) (δ := δ) u P)
    (hBoundaryCard : BoundaryCardResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_boundaryCardResidual
    (k := k) (deg := deg) (domain := domain) (δ := δ)
    (strictCoeffPolysResidual_of_curveFamilyData hInput) hBoundaryCard hδ

end Bundle

end FaithfulCurveExtraction

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.FaithfulCurveExtraction.natDegree_linRep_eval_le_one
#print axioms ArkLib.FaithfulCurveExtraction.no_linRep_of_nonaffine
#print axioms ArkLib.FaithfulCurveExtraction.curveCoeffPolys_of_curveFamily
#print axioms ArkLib.FaithfulCurveExtraction.CurveFamilyData
#print axioms ArkLib.FaithfulCurveExtraction.curveCoeffPolys_of_curveFamilyData
#print axioms ArkLib.FaithfulCurveExtraction.hcoeffPoly_witness_of_curveFamilyData
#print axioms ArkLib.FaithfulCurveExtraction.strictCoeffPolysResidual_of_curveFamilyData
#print axioms ArkLib.FaithfulCurveExtraction.correlatedAgreement_affine_curves_johnson_of_curveFamilyData_strict
#print axioms ArkLib.FaithfulCurveExtraction.correlatedAgreement_affine_curves_johnson_of_curveFamilyData
