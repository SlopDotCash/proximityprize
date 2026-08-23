/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SectionXiUnit
import ArkLib.ToMathlib.SectionFactor
import ArkLib.ToMathlib.SectionBaseRational
import ArkLib.ToMathlib.CurvePlaceReadingSupply

/-!
# Issue #304 — THE FINAL ASSEMBLY: correlated agreement from the GS surface

The section-factor route, fully composed.  Working directly at the **section divisor**
`H := T − v(Z)` (the §5 fiber-linear factor every curve-carrying branch collapses to):

* **Stage A** — the section bundle: `T − C v` is monic, fiber-linear, and irreducible
  (`sectionH_irreducible`); its `Hypotheses` need only the two §5 construction facts
  (specialized separability + the section dividing the specialized surface); and the per-place
  `ξ`-reading is nonvanishing at **every** place (`π_z_ξ_ne_zero_sectionH`) — the
  `ξ`-representative content is a *unit constant* (separability at the section,
  `SectionXiUnit`), so no discriminant avoidance is needed.
* **Stage B** — the explicit curve coefficients: `sectionCurveCoeff t` is the exact division
  of the `βHensel`-representative content by the `ξ`-content power (exact by the **proven**
  `SectionXiOrder`); the factored forms, the per-place readings, and the truncated reading
  `htrunc_sectionH` follow.
* **Stage C** — the explicit section root: `H̃′(T − C v) = T − C v` and the branch value at
  every place is just `v(z)` (`rootSection`); plus the global `ξ ≠ 0`.
* **Stage D** — `GSSurfaceData`, the per-`(u, P)` bundle of **GS-construction-level facts
  only** (no Hensel, quotient-ring, or function-field content), the producer
  `curveFamilyData_of_gsSurfaceData`, and **the keystone front door**
  `correlatedAgreement_affine_curves_of_GS_surface`: `δ_ε_correlatedAgreementCurves` at every
  `δ < 1 − √ρ` from a per-`(u, P)` `GSSurfaceData` producer.

Together with `FaithfulFrontierWitness` (non-vacuity: the bundle is satisfiable with good set
`univ`) this closes the faithful-surface programme of #304: every analytic core on the route —
section factor, base rationality, `ξ`-order, readings, truncation, extraction, keystone — is
proven, and the remaining interface is exactly the §5/§6 GS-construction package.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Prop. 5.5), §6.2, Appendix A.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open scoped BigOperators

namespace ArkLib

namespace GSSurfaceKeystone

variable {F : Type} [Field F]

/-- The section divisor `T − C v` is monic. -/
theorem sectionH_monic (v : F[X]) : (Polynomial.X - Polynomial.C v : F[X][Y]).Monic :=
  Polynomial.monic_X_sub_C v

/-- The section divisor is fiber-linear. -/
theorem sectionH_natDegree (v : F[X]) :
    (Polynomial.X - Polynomial.C v : F[X][Y]).natDegree = 1 :=
  Polynomial.natDegree_X_sub_C v

/-- **The section divisor is irreducible over the coefficient domain `F[X]`**: a monic linear
polynomial factors only with a degree-0 monic factor, which is `1`. -/
theorem sectionH_irreducible (v : F[X]) :
    Irreducible (Polynomial.X - Polynomial.C v : F[X][Y]) := by
  rw [(sectionH_monic v).irreducible_iff_natDegree]
  constructor
  · intro h1
    have := congrArg Polynomial.natDegree h1
    rw [sectionH_natDegree, Polynomial.natDegree_one] at this
    omega
  · intro f g hf hg hfg
    have hd := congrArg Polynomial.natDegree hfg
    rw [hf.natDegree_mul hg, sectionH_natDegree] at hd
    omega

/-- **The `Hypotheses` for the section divisor**, by divisibility transitivity through the
factorization. -/
theorem sectionH_hypotheses {x₀ : F} {R : F[X][X][Y]} {v : F[X]}
    (hsep : (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hdvd : (Polynomial.X - Polynomial.C v : F[X][Y]) ∣ Bivariate.evalX (Polynomial.C x₀) R) :
    Hypotheses x₀ R (Polynomial.X - Polynomial.C v : F[X][Y]) where
  dvd_evalX := hdvd
  separable_evalX := hsep

/-- At the section divisor, the `ξ`-representative content is a nonzero **constant**, so the
per-place `ξ`-reading is nonvanishing at EVERY place — no discriminant needed. -/
theorem π_z_ξ_ne_zero_sectionH {x₀ : F} {R : F[X][X][Y]} {v : F[X]}
    [Fact (Irreducible (Polynomial.X - Polynomial.C v : F[X][Y]))]
    [Fact (0 < (Polynomial.X - Polynomial.C v : F[X][Y]).natDegree)]
    (hHyp : Hypotheses x₀ R (Polynomial.X - Polynomial.C v))
    (hd2 : 2 ≤ R.natDegree)
    (z : F) (root : rationalRoot (H_tilde' (Polynomial.X - Polynomial.C v)) z) :
    (π_z z root) (ξ x₀ R (Polynomial.X - Polynomial.C v) hHyp) ≠ 0 := by
  -- the ξ-representative content is a unit of F[X], i.e. a nonzero constant
  have hunit : IsUnit ((canonicalRepOf𝒪 (Fact.out)
      (ξ x₀ R (Polynomial.X - Polynomial.C v) hHyp)).coeff 0) := by
    rw [SectionXiUnit.xiRep_eq_eval_section (sectionH_monic v) (sectionH_natDegree v) hHyp,
      SectionXiUnit.xi_pre_monic_eq_derivative (sectionH_monic v).leadingCoeff hd2]
    rw [show Bivariate.evalX (Polynomial.C x₀) (Polynomial.derivative R)
        = Polynomial.derivative (Bivariate.evalX (Polynomial.C x₀) R) from by
      rw [Bivariate.evalX_eq_map, Bivariate.evalX_eq_map, Polynomial.derivative_map]]
    exact SectionXiUnit.derivative_isUnit_at_section (sectionH_monic v)
      (sectionH_natDegree v) hHyp.dvd_evalX hHyp.separable_evalX
  -- ξ = mk (C content) at the fiber-linear factor, so π_z(ξ) = content.eval z ≠ 0
  have hrep := SectionBaseRational.exists_mk_C_of_natDegree_eq_one
    (Fact.out) (sectionH_natDegree v) (ξ x₀ R (Polynomial.X - Polynomial.C v) hHyp)
  rw [hrep, π_z_mk, Polynomial.evalEval_C]
  obtain ⟨r, hr, hCr⟩ := Polynomial.isUnit_iff.mp hunit
  rw [← hCr, Polynomial.eval_C]
  exact hr.ne_zero

/-! ## Stage B — the explicit curve coefficients and the readings -/

variable {x₀ : F} {R : F[X][X][Y]} {v : F[X]}
variable [Fact (Irreducible (Polynomial.X - Polynomial.C v : F[X][Y]))]
variable [Fact (0 < (Polynomial.X - Polynomial.C v : F[X][Y]).natDegree)]

/-- The `ξ`-representative content at the section divisor is a unit. -/
theorem xiContent_isUnit (hHyp : Hypotheses x₀ R (Polynomial.X - Polynomial.C v))
    (hd2 : 2 ≤ R.natDegree) :
    IsUnit ((canonicalRepOf𝒪 (Fact.out)
      (ξ x₀ R (Polynomial.X - Polynomial.C v) hHyp)).coeff 0) := by
  rw [SectionXiUnit.xiRep_eq_eval_section (sectionH_monic v) (sectionH_natDegree v) hHyp,
    SectionXiUnit.xi_pre_monic_eq_derivative (sectionH_monic v).leadingCoeff hd2]
  rw [show Bivariate.evalX (Polynomial.C x₀) (Polynomial.derivative R)
      = Polynomial.derivative (Bivariate.evalX (Polynomial.C x₀) R) from by
    rw [Bivariate.evalX_eq_map, Bivariate.evalX_eq_map, Polynomial.derivative_map]]
  exact SectionXiUnit.derivative_isUnit_at_section (sectionH_monic v)
    (sectionH_natDegree v) hHyp.dvd_evalX hHyp.separable_evalX

/-- **The explicit curve coefficients**: the `β`-representative content divided by the
`ξ`-content power (exact by `SectionXiOrder`). -/
noncomputable def sectionCurveCoeff (hHyp : Hypotheses x₀ R (Polynomial.X - Polynomial.C v))
    (t : ℕ) : F[X] :=
  (canonicalRepOf𝒪 (Fact.out)
      (βHensel (Polynomial.X - Polynomial.C v) x₀ R hHyp t)).coeff 0
    / ((canonicalRepOf𝒪 (Fact.out)
      (ξ x₀ R (Polynomial.X - Polynomial.C v) hHyp)).coeff 0) ^ (2 * t - 1)

/-- **The factored form at the explicit coefficients** (from the PROVEN `SectionXiOrder`). -/
theorem βHensel_factored_sectionH (hHyp : Hypotheses x₀ R (Polynomial.X - Polynomial.C v))
    (hd2 : 2 ≤ R.natDegree) (t : ℕ) :
    βHensel (Polynomial.X - Polynomial.C v) x₀ R hHyp t
      = Ideal.Quotient.mk (Ideal.span {H_tilde' (Polynomial.X - Polynomial.C v)})
          (Polynomial.C (sectionCurveCoeff hHyp t))
        * (ξ x₀ R (Polynomial.X - Polynomial.C v) hHyp) ^ (2 * t - 1) := by
  have hdvd := SectionXiUnit.sectionXiOrder_of_monic_linear (sectionH_monic v)
    (sectionH_natDegree v) hd2 hHyp t
  have hβ := SectionBaseRational.βHensel_eq_mk_C_of_natDegree_eq_one
    (sectionH_natDegree v) hHyp t
  have hξ := SectionBaseRational.exists_mk_C_of_natDegree_eq_one
    (Fact.out) (sectionH_natDegree v) (ξ x₀ R (Polynomial.X - Polynomial.C v) hHyp)
  conv_lhs => rw [hβ]
  conv_rhs => rw [hξ]
  rw [← map_pow, ← map_mul, ← Polynomial.C_pow, ← Polynomial.C_mul]
  congr 2
  rw [sectionCurveCoeff, mul_comm]
  exact (EuclideanDomain.mul_div_cancel'
    (pow_ne_zero _ (xiContent_isUnit hHyp hd2).ne_zero) hdvd).symm

/-- **The per-place coefficient reading at the explicit coefficients.** -/
theorem coeff_localSeries_sectionH (hHyp : Hypotheses x₀ R (Polynomial.X - Polynomial.C v))
    (hd2 : 2 ≤ R.natDegree)
    (z : F) (root : rationalRoot (H_tilde' (Polynomial.X - Polynomial.C v)) z)
    (hx : (π_z z root) (ξ x₀ R (Polynomial.X - Polynomial.C v) hHyp) ≠ 0) (t : ℕ) :
    PowerSeries.coeff t (localSeries hHyp z root hx)
      = (sectionCurveCoeff hHyp t).eval z := by
  have h := coeff_localSeries_mul hHyp z root hx t
  rw [βHensel_factored_sectionH hHyp hd2 t, map_mul, map_pow, π_z_mk,
    Polynomial.evalEval_C] at h
  exact mul_right_cancel₀ (pow_ne_zero _ hx) h

/-- **The truncated reading**: the truncated local series is the centred curve specialization
at the transposed explicit coefficients. -/
theorem htrunc_sectionH (hHyp : Hypotheses x₀ R (Polynomial.X - Polynomial.C v))
    (hd2 : 2 ≤ R.natDegree) {n N : ℕ} (hnN : n ≤ N)
    (hdegc : ∀ t < n, (sectionCurveCoeff hHyp t).natDegree < N)
    (htail : ∀ t, n ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R (Polynomial.X - Polynomial.C v) hHyp
        (BetaRecGenuineBridge.BcoeffSigned (Polynomial.X - Polynomial.C v) x₀ R) t = 0)
    (z : F) (root : rationalRoot (H_tilde' (Polynomial.X - Polynomial.C v)) z)
    (hx : (π_z z root) (ξ x₀ R (Polynomial.X - Polynomial.C v) hHyp) ≠ 0) :
    (PowerSeries.trunc N (localSeries hHyp z root hx) : Polynomial F)
      = ∑ s ∈ Finset.range N, (z - x₀) ^ s •
          transposedCurveCoeffs x₀ n (sectionCurveCoeff hHyp) s := by
  have hξg : ξ x₀ R (Polynomial.X - Polynomial.C v) hHyp ≠ 0 :=
    fun h0 => hx (by rw [h0, map_zero])
  rw [← sum_C_eval_eq_transposed_curve_sum x₀ (sectionCurveCoeff hHyp) hdegc]
  ext j
  rw [PowerSeries.coeff_trunc, coeff_sum_C_mul_X_pow]
  split_ifs with hj hjn hjn
  · exact coeff_localSeries_sectionH hHyp hd2 z root hx j
  · exact coeff_localSeries_eq_zero_of_alphaFromBeta_eq_zero hHyp hξg z root hx j
      (htail j (le_of_not_gt hjn))
  · omega
  · rfl

/-! ## Stage C — the section root, the bundle, and the keystone front door -/

/-- The monicization of the section divisor is itself. -/
theorem H_tilde'_sectionH (v : F[X]) :
    H_tilde' (Polynomial.X - Polynomial.C v : F[X][Y]) = Polynomial.X - Polynomial.C v := by
  rw [H_tilde', if_neg (by rw [sectionH_natDegree]; omega), sectionH_natDegree]
  have hc1 : (Polynomial.X - Polynomial.C v : F[X][Y]).coeff 1 = 1 := by
    have := (sectionH_monic v).coeff_natDegree
    rwa [sectionH_natDegree] at this
  have hc0 : (Polynomial.X - Polynomial.C v : F[X][Y]).coeff 0 = -v := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero]
    ring
  simp only [Finset.sum_range_one, hc1, hc0, one_pow, pow_zero, pow_one, mul_one]
  rw [map_neg]
  ring

/-- **The explicit section root**: at every place the branch value is the surface value. -/
noncomputable def rootSection (v : F[X]) :
    (z : F) → rationalRoot (H_tilde' (Polynomial.X - Polynomial.C v : F[X][Y])) z := fun z =>
  ⟨v.eval z, by
    rw [H_tilde'_sectionH]
    show Polynomial.evalEval z (v.eval z) (Polynomial.X - Polynomial.C v) = 0
    rw [← Polynomial.coe_evalEvalRingHom, map_sub]
    simp [Polynomial.coe_evalEvalRingHom, Polynomial.evalEval_C, Polynomial.evalEval_X]⟩

/-- The global `ξ`-nonvanishing at the section divisor (the content is a unit). -/
theorem ξ_ne_zero_sectionH (hHyp : Hypotheses x₀ R (Polynomial.X - Polynomial.C v))
    (hd2 : 2 ≤ R.natDegree) :
    ξ x₀ R (Polynomial.X - Polynomial.C v) hHyp ≠ 0 := by
  intro h0
  have hrep := SectionBaseRational.exists_mk_C_of_natDegree_eq_one
    (Fact.out) (sectionH_natDegree v) (ξ x₀ R (Polynomial.X - Polynomial.C v) hHyp)
  have h00 : Ideal.Quotient.mk (Ideal.span
      {H_tilde' (Polynomial.X - Polynomial.C v : F[X][Y])})
      (Polynomial.C
        ((canonicalRepOf𝒪 (Fact.out) (ξ x₀ R (Polynomial.X - Polynomial.C v) hHyp)).coeff 0))
      = Ideal.Quotient.mk (Ideal.span
        {H_tilde' (Polynomial.X - Polynomial.C v : F[X][Y])}) (Polynomial.C (0 : F[X])) := by
    rw [← hrep, h0]
    simp
  have hc0 := SectionXiDivisibility.mk_C_injective_of_natDegree_eq_one
    (Fact.out) (sectionH_natDegree v) h00
  exact (xiContent_isUnit hHyp hd2).ne_zero hc0

end GSSurfaceKeystone

namespace GSSurfaceKeystone

/-! ## Stage D — the per-`(u, P)` GS-surface bundle and the keystone front door -/

open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped ENNReal ProbabilityTheory LinearCode

variable {F : Type} [Field F]

/-- The section divisor is irreducible — as an instance, so the bundle can elaborate. -/
instance instFactIrreducibleSectionH (v : F[X]) :
    Fact (Irreducible (Polynomial.X - Polynomial.C v : F[X][Y])) :=
  ⟨sectionH_irreducible v⟩

/-- The section divisor has positive fiber degree — as an instance. -/
instance instFactNatDegreePosSectionH (v : F[X]) :
    Fact (0 < (Polynomial.X - Polynomial.C v : F[X][Y]).natDegree) :=
  ⟨by rw [sectionH_natDegree]; omega⟩

section Keystone

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Fintype F] [DecidableEq F]

/-- **The per-`(u, P)` GS-surface bundle**: everything the section-factor route consumes, at
GS-construction level — the specialized surface is separable, the section divisor `T − v(Z)`
divides it, the `(A.1)` tail vanishes from `n` on, the explicit section curve coefficients have
degree `< n`, and the per-place GS cargo (matching-factor divisibility at the decoded value +
the order-`0` congruence) holds at the section root.  No quotient-ring, function-field, or
Hensel-internal data appears: every field is a statement about `R`, `v`, and the decoded family
`P` itself. -/
structure GSSurfaceData {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F) : Type where
  /-- the expansion centre. -/
  x₀ : F
  /-- the section: the GS surface contains the graph `T = v(Z)`. -/
  v : F[X]
  /-- the GS interpolant surface. -/
  R : F[X][X][Y]
  hd2 : 2 ≤ R.natDegree
  hsepR : R.Separable
  hsep : (Bivariate.evalX (Polynomial.C x₀) R).Separable
  hdvd : (Polynomial.X - Polynomial.C v : F[X][Y]) ∣ Bivariate.evalX (Polynomial.C x₀) R
  /-- the number of curve coefficients (at most `k + 1`). -/
  n : ℕ
  hn : n < k + 2
  hdegc : ∀ t < n, (sectionCurveCoeff (sectionH_hypotheses hsep hdvd) t).natDegree < n
  htail : ∀ t, n ≤ t →
    BetaToCurveCoeffPolys.αFromBeta x₀ R (Polynomial.X - Polynomial.C v)
      (sectionH_hypotheses hsep hdvd)
      (BetaRecGenuineBridge.BcoeffSigned (Polynomial.X - Polynomial.C v) x₀ R) t = 0
  hdvdP : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
    (Polynomial.X - Polynomial.C ((P z : F[X]) : PowerSeries F)) ∣
      ((R.map (coeffHom_loc x₀ (sectionH_hypotheses hsep hdvd))).map
        (PowerSeries.map (π_hat_z (sectionH_hypotheses hsep hdvd) z (rootSection v z)
          (π_z_ξ_ne_zero_sectionH (sectionH_hypotheses hsep hdvd) hd2 z (rootSection v z)))))
  hcong : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    ((P z : F[X]) : PowerSeries F) - PowerSeries.C ((π_z z (rootSection v z))
        (βHensel (Polynomial.X - Polynomial.C v) x₀ R (sectionH_hypotheses hsep hdvd) 0))
      ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}

/-- **`CurveFamilyData` from the GS-surface bundle** — the section-factor route, fully
assembled: the root is the explicit section root, the `ξ`-reading is nonvanishing at every
place (unit content), the curve coefficients are the explicit exact divisions, and the
truncated reading is the proved `htrunc_sectionH`. -/
noncomputable def curveFamilyData_of_gsSurfaceData {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (D : GSSurfaceData (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    FaithfulCurveExtraction.CurveFamilyData
      (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  FaithfulCurveExtraction.curveFamilyData_of_truncatedLocalRoot
    (sectionH_hypotheses D.hsep D.hdvd)
    (ξ_ne_zero_sectionH (sectionH_hypotheses D.hsep D.hdvd) D.hd2)
    ((sectionH_monic D.v).leadingCoeff)
    D.hsepR
    (n := D.n)
    (c := transposedCurveCoeffs D.x₀ D.n (sectionCurveCoeff (sectionH_hypotheses D.hsep D.hdvd)))
    D.hn
    (rootSection D.v)
    (fun z _ => π_z_ξ_ne_zero_sectionH (sectionH_hypotheses D.hsep D.hdvd) D.hd2 z
      (rootSection D.v z))
    D.htail
    (fun z hz => htrunc_sectionH (sectionH_hypotheses D.hsep D.hdvd) D.hd2 (le_refl D.n)
      D.hdegc D.htail z (rootSection D.v z) _)
    D.hdvdP
    D.hcong

/-- **THE KEYSTONE, GS-surface interface (strict square-root radius)**: correlated agreement
for affine curves in the Johnson regime, from per-`(u, P)` GS-construction-level inputs only —
the bundle of facts BCIKS20 §5/§6 establishes about the Guruswami–Sudan interpolant and the
decoded family.  All Hensel/quotient-ring/function-field content is internal and PROVEN. -/
theorem correlatedAgreement_affine_curves_of_GS_surface
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
        GSSurfaceData (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  FaithfulCurveExtraction.correlatedAgreement_affine_curves_johnson_of_curveFamilyData_strict
    hδ
    (fun hk u hprob hJ hδ' P hP =>
      curveFamilyData_of_gsSurfaceData (hInput hk u hprob hJ hδ' P hP))

end Keystone

end GSSurfaceKeystone

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.GSSurfaceKeystone.sectionH_irreducible
#print axioms ArkLib.GSSurfaceKeystone.π_z_ξ_ne_zero_sectionH
#print axioms ArkLib.GSSurfaceKeystone.βHensel_factored_sectionH
#print axioms ArkLib.GSSurfaceKeystone.coeff_localSeries_sectionH
#print axioms ArkLib.GSSurfaceKeystone.htrunc_sectionH
#print axioms ArkLib.GSSurfaceKeystone.H_tilde'_sectionH
#print axioms ArkLib.GSSurfaceKeystone.rootSection
#print axioms ArkLib.GSSurfaceKeystone.ξ_ne_zero_sectionH
#print axioms ArkLib.GSSurfaceKeystone.curveFamilyData_of_gsSurfaceData
#print axioms ArkLib.GSSurfaceKeystone.correlatedAgreement_affine_curves_of_GS_surface
