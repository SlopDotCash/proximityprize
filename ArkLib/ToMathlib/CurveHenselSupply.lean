/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSCurveTuple
import ArkLib.ToMathlib.InterpolantInputSupply
import ArkLib.ToMathlib.CurveHenselDatumProducers
import ArkLib.ToMathlib.OrderZeroAgreementSupply
import ArkLib.ToMathlib.OffcentreFaithfulBundle

/-!
# Issue #304 — `CurveHenselDatum` from the GS surface (the general-`k` S10-converse route)

`InterpolantInputSupply.lean` wired the S10-converse Guruswami–Sudan chain into the Hensel lane
at curve degree `k = 1` (the line case): ONE `K = F(Z)`-level GS interpolant for the generic
fold, specialized per good `z`, swallows every `δ`-close low-degree decoding via the Lagrange
round-trip (`dvd_specialization_of_close`).  This file is the **general-`k` analogue**, targeted
at the faithful curve surface `FaithfulCurveExtraction.CurveHenselDatum` — the per-`z` Hensel
root datum whose in-tree consumers (`curveFamilyData_of_curveHenselDatum`,
`section5DataOffcentreFaithful_of_producers`) reach the §5 keystone
`δ_ε_correlatedAgreementCurves`.

## Part 1 — the curve-fold specialization of the GS `Conditions`

* `intPointYCurve` (+ `map_intPointYCurve`, `eval_intPointYCurve`) — the integral `Y`-point of
  the `L`-ary curve fold: `∑ⱼ Zʲ·C(fⱼ i) ∈ F[Z]`, mapping to `curveFold f i` over `K = F(Z)`
  and evaluating to the scalar curve fold `∑ⱼ zʲ·fⱼ i` at every `z`.
* `curve_specialized_conditions` — the `L`-ary generalization of
  `GuruswamiSudan.OverRatFunc.specialized_conditions`: a GS interpolant of the `L`-ary generic
  curve fold `curveFold f` over `K` with integer representative `(d, Q₀)` specializes, at every
  `z` with `Q₀|_{Z:=z} ≠ 0`, to a valid GS interpolant for the scalar curve fold
  `∑ⱼ zʲ·fⱼ` — same weighted-degree bound, roots, and multiplicities.
* `curve_fold_decoded_divides_specialization` — the `L`-ary S10 converse, composed with the
  in-tree GS list decoder `GuruswamiSudan.gs_divisibility`.

## Part 2 — the core brick and the good-set families

* `curve_dvd_specialization_of_close` — **the general-`k` analogue of
  `InterpolantInputSupply.dvd_specialization_of_close`**: ANY polynomial `W` of degree `< deg`
  whose evaluations lie within the GS Johnson radius of the scalar curve fold satisfies
  `(Y − C W) ∣ Q₀|_{Z:=z}`, via the Lagrange round-trip
  (`GuruswamiSudan.interpolate_eq_of_degree_lt`).
* `curveWord_fold_eq` / `mem_goodCoeffsCurve_iff_fold` — the `RS_goodCoeffsCurve` curve word
  `∑ₜ zᵗ • u t` IS the scalar curve fold of `curveFold u`, so good-set membership is exactly
  `δ`-proximity of the fold to the code.
* `curve_dvd_specialization_family` — the good-set family form for an arbitrary decoding family
  `W : F → F[X]`; instantiated **twice** below: at the decoded family `P` and at the
  curve-family competitor `z ↦ ∑_{t<n} (z − x₀)ᵗ • c t`.
* `curveCompetitor_degree_lt` — the curve-family competitor is a Reed–Solomon codeword
  polynomial whenever its coefficients are (`deg (c t) < deg`).

## Part 3 — the assembled producers

* `GSCurveInput` — the bundled general-`k` GS surface: the `K`-level GS `Conditions` for the
  `L = k + 1`-ary curve fold, an integer representative, and the per-good-`z` residuals
  (non-collapse, degree + fold-proximity of BOTH competitors, order-0 agreement, separability).
* `GSCurveInput.decoded_dvd` / `GSCurveInput.competitor_dvd` — both per-`z` matching
  divisibilities from the SAME specialized interpolant.
* `GSCurveInput.toCurveHenselDatum` — **the production**: all seven `CurveHenselDatum` fields
  from the GS surface, through `curveHenselDatum_of_matchesGraph`.
* `GSCurveInput.toCurveFamilyData` — composed into the faithful `CurveFamilyData`.
* `gsCurveInput_of_uniqueRootOn` — the `h0`-free constructor: the order-0 agreement is
  **derived** from the two matching divisibilities + the centre-fiber uniqueness witness
  (`OrderZeroAgreementSupply` route (i)).
* `h0_curve_of_centre_agreement` — the `h0` field from route (ii) (the centre is a common
  graph point), at the curve-family competitor.
* `hsep_curve_of_discr_isUnit` — the separability field from the unit-discriminant route, on
  the curve good set.
* `GSCurveInput.hPz_eq` — the derived faithful per-`z` identity
  `P z = ∑_{t<n} (z − x₀)ᵗ • c t` on the good set, by Hensel uniqueness.
* `section5DataOffcentreFaithful_of_gsCurve` — **the capstone composition**: the faithful
  off-centre §5 bundle (whose in-tree front doors reach the keystone
  `δ_ε_correlatedAgreementCurves`) from the off-centre counting data PLUS the general-`k` GS
  surface, the `hPz` lane fully discharged by `GSCurveInput.toCurveHenselDatum`.
* `strictCoeffPolysResidual_of_gsCurveInput` /
  `correlatedAgreement_affine_curves_johnson_of_gsCurveInput_strict` — the keystone front
  doors: `StrictCoeffPolysResidual` and the §5 keystone goal `δ_ε_correlatedAgreementCurves`
  in the strict Johnson regime, from a per-`(u, P)` producer of `GSCurveInput`.

## Honest residuals

Nothing here fabricates §5/§6.2 content.  The residual hypotheses of `GSCurveInput` are the
recognized BCIKS20/Hab25 ingredients with their own production lanes: the `K`-level GS
`Conditions` for the curve fold (S2 interpolation, `gs_existence` at `RatFunc F`), the integer
representative, per-`z` non-collapse (the cofinite `d(z) ≠ 0` fact), the two per-`z` proximity
bounds within the GS Johnson radius (§5 agreement counts), order-0 agreement
(`OrderZeroAgreementSupply` routes), and separability (`hsep_curve_of_discr_isUnit` route).
None is `≡` the goal: the per-`z` identity `P z = ∑_{t<n} (z − x₀)ᵗ • c t` is *derived* by
Hensel uniqueness downstream (`eval_identity_of_curveHensel`).

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Prop. 5.5), §6.2; Hab25 §3 Steps S2/S10 (ℓ-ary extension).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

attribute [local instance] Classical.propDecidable

namespace GuruswamiSudan.OverRatFunc

variable {F : Type} [Field F]

/-! ## Part 1 — the curve-fold specialization of the GS `Conditions` -/

/-- The integral `Y`-point of the `L`-ary curve fold: `∑ⱼ Zʲ·C(fⱼ i) ∈ F[Z]` — the `L`-ary
generalization of `intPointY` (which is the case `L = 2`). -/
noncomputable def intPointYCurve {n L : ℕ} (f : Fin L → Fin n → F) (i : Fin n) : F[X] :=
  ∑ j : Fin L, Polynomial.X ^ (j : ℕ) * Polynomial.C (f j i)

/-- At `L = 2` the curve integral point is the affine integral point: the generalization
restricts to the in-tree `k = 1` lane. -/
lemma intPointYCurve_two_eq_intPointY {n : ℕ} (f : Fin 2 → Fin n → F) (i : Fin n) :
    intPointYCurve f i = intPointY (f 0) (f 1) i := by
  rw [intPointYCurve, intPointY, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero,
    pow_one, one_mul]

/-- The integral curve `Y`-point maps to the `K = F(Z)`-level curve fold value. -/
lemma map_intPointYCurve {n L : ℕ} (f : Fin L → Fin n → F) (i : Fin n) :
    algebraMap F[X] (RatFunc F) (intPointYCurve f i) = curveFold f i := by
  rw [intPointYCurve, map_sum]
  simp only [curveFold]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_pow, algebraMap_C_eq, RatFunc.algebraMap_X]

/-- The integral curve `Y`-point evaluates, at every `z`, to the scalar curve fold value
`∑ⱼ zʲ·fⱼ i`. -/
lemma eval_intPointYCurve {n L : ℕ} (f : Fin L → Fin n → F) (i : Fin n) (z : F) :
    Polynomial.evalRingHom z (intPointYCurve f i) = ∑ j : Fin L, z ^ (j : ℕ) * f j i := by
  rw [intPointYCurve, Polynomial.coe_evalRingHom, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]

/-- **The `L`-ary curve-fold specialization of the GS `Conditions`** — the general-`k`
analogue of `specialized_conditions`.

Let `Q` be a GS interpolant of the `L`-ary generic curve fold `∑ⱼ Zʲ·fⱼ` over `K = F(Z)` and
`(d, Q₀)` an integer representative.  Then at **every** `z ∈ F` where the specialization does
not collapse (`Q₀|_{Z:=z} ≠ 0` — a cofinite set), the specialized polynomial
`Q₀|_{Z:=z} ∈ F[X][Y]` is a valid GS interpolant for the scalar curve fold `∑ⱼ zʲ·fⱼ`:
nonzero, same weighted-degree bound, with roots of multiplicity `≥ m` at every
`(ω_i, ∑ⱼ zʲ·fⱼ i)`. -/
theorem curve_specialized_conditions {n k m D L : ℕ} (ωs : Fin n ↪ F) (f : Fin L → Fin n → F)
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : (F[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m D (liftedDomain ωs) (curveFold f) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (z : F)
    (hz : Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ≠ 0) :
    GuruswamiSudan.Conditions k m D ωs (fun i => ∑ j : Fin L, z ^ (j : ℕ) * f j i)
      (Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) := by
  classical
  set φ := algebraMap F[X] (RatFunc F) with hφ
  have hφinj : Function.Injective φ := RatFunc.algebraMap_injective F
  set σ := Polynomial.evalRingHom z with hσ
  refine ⟨hz, ?_, ?_, ?_⟩
  · -- weighted degree
    have h1 : natWeightedDegree (Q₀.map (Polynomial.mapRingHom σ)) 1 (k - 1) ≤
        natWeightedDegree Q₀ 1 (k - 1) := natWeightedDegree_map_le σ Q₀ 1 (k - 1)
    have h2 : natWeightedDegree Q₀ 1 (k - 1) =
        natWeightedDegree (Q₀.map (Polynomial.mapRingHom φ)) 1 (k - 1) :=
      (natWeightedDegree_map_eq_of_injective hφinj Q₀ 1 (k - 1)).symm
    have h3 : natWeightedDegree (Q₀.map (Polynomial.mapRingHom φ)) 1 (k - 1) ≤
        natWeightedDegree Q 1 (k - 1) := by
      rw [hrep]
      exact natWeightedDegree_C_C_mul_le _ Q 1 (k - 1)
    have h4 : natWeightedDegree Q 1 (k - 1) ≤ D := by
      have h := hQ.Q_deg
      rw [weightedDegree_eq_natWeightedDegree] at h
      exact_mod_cast h
    rw [weightedDegree_eq_natWeightedDegree]
    exact_mod_cast le_trans h1 (le_trans (h2.le.trans h3) h4)
  · -- roots
    intro i
    -- the root holds integrally over `F[Z]`
    have h0 : ((Q₀.eval (Polynomial.C (intPointYCurve f i))).eval (intPointX ωs i)) = 0 := by
      apply hφinj
      rw [map_zero]
      have hcomm := Polynomial.map_mapRingHom_evalEval (f := φ)
        (intPointX ωs i) (intPointYCurve f i) (p := Q₀)
      calc φ ((Q₀.eval (Polynomial.C (intPointYCurve f i))).eval (intPointX ωs i))
          = (Q₀.map (Polynomial.mapRingHom φ)).evalEval
              (φ (intPointX ωs i)) (φ (intPointYCurve f i)) := hcomm.symm
        _ = (Polynomial.C (Polynomial.C (φ d)) * Q).evalEval
              (liftedDomain ωs i) (curveFold f i) := by
            rw [hrep, map_intPointX, map_intPointYCurve]
        _ = (Polynomial.C (Polynomial.C (φ d))).evalEval
              (liftedDomain ωs i) (curveFold f i) *
            Q.evalEval (liftedDomain ωs i) (curveFold f i) :=
            Polynomial.evalEval_mul _ _ _ _
        _ = 0 := by
            have hroot := hQ.Q_roots i
            show _ * ((Q.eval (Polynomial.C (curveFold f i))).eval
              (liftedDomain ωs i)) = 0
            rw [hroot, mul_zero]
    -- specialize at `z`
    have hcomm := Polynomial.map_mapRingHom_evalEval (f := σ)
      (intPointX ωs i) (intPointYCurve f i) (p := Q₀)
    show ((Q₀.map (Polynomial.mapRingHom σ)).eval
      (Polynomial.C (∑ j : Fin L, z ^ (j : ℕ) * f j i))).eval (ωs i) = 0
    calc ((Q₀.map (Polynomial.mapRingHom σ)).eval
        (Polynomial.C (∑ j : Fin L, z ^ (j : ℕ) * f j i))).eval (ωs i)
        = (Q₀.map (Polynomial.mapRingHom σ)).evalEval
            (σ (intPointX ωs i)) (σ (intPointYCurve f i)) := by
          rw [eval_intPointX, eval_intPointYCurve]
      _ = σ ((Q₀.eval (Polynomial.C (intPointYCurve f i))).eval (intPointX ωs i)) := hcomm
      _ = 0 := by rw [h0, map_zero]
  · -- multiplicity
    intro i
    apply GuruswamiSudan.rootMultiplicity_ge_of_shift_zero hz
    intro s t hst
    -- extraction over `K`
    have hKvan := shift_coeff_eq_zero_of_le_rootMultiplicity (hQ.Q_multiplicity i) s t hst
    -- descend to `F[Z]`
    have h0 : ((Polynomial.Bivariate.shift Q₀ (intPointX ωs i)
        (intPointYCurve f i)).coeff t).coeff s = 0 := by
      apply hφinj
      rw [map_zero]
      have hsm := shift_map φ Q₀ (intPointX ωs i) (intPointYCurve f i)
      rw [hrep, map_intPointX, map_intPointYCurve] at hsm
      calc φ (((Polynomial.Bivariate.shift Q₀ (intPointX ωs i)
            (intPointYCurve f i)).coeff t).coeff s)
          = ((((Polynomial.Bivariate.shift Q₀ (intPointX ωs i)
              (intPointYCurve f i)).map (Polynomial.mapRingHom φ)).coeff t)).coeff s := by
            rw [Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
        _ = (((Polynomial.Bivariate.shift
              (Polynomial.C (Polynomial.C (φ d)) * Q)
              (liftedDomain ωs i) (curveFold f i)).coeff t)).coeff s := by
            rw [← hsm]
        _ = φ d * (((Polynomial.Bivariate.shift Q (liftedDomain ωs i)
              (curveFold f i)).coeff t)).coeff s := by
            rw [shift_C_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
        _ = 0 := by rw [hKvan, mul_zero]
    -- re-specialize at `z`
    have hsm := shift_map σ Q₀ (intPointX ωs i) (intPointYCurve f i)
    rw [eval_intPointX, eval_intPointYCurve] at hsm
    rw [hsm, Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_map, h0,
      map_zero]

/-- **The `L`-ary S10 converse, composed with the in-tree GS list decoder.**  At every good
`z` (where `Q₀|_{Z:=z} ≠ 0`), every degree-`< k` codeword within the GS Johnson radius of the
scalar curve fold `∑ⱼ zʲ·fⱼ` divides the specialized integer interpolant. -/
theorem curve_fold_decoded_divides_specialization {n k m L : ℕ}
    (ωs : Fin n ↪ F) (f : Fin L → Fin n → F)
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : (F[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions k m (gs_degree_bound k n m)
      (liftedDomain ωs) (curveFold f) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (z : F)
    (hz : Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ≠ 0)
    (hk : k + 1 ≤ n) (hm : 1 ≤ m)
    (p : ReedSolomon.code ωs k)
    (h_dist :
      (hammingDist (fun i => ∑ j : Fin L, z ^ (j : ℕ) * f j i)
          (fun i => (ReedSolomon.codewordToPoly p).eval (ωs i)) : ℝ) / n <
        gs_johnson k n m) :
    Polynomial.X - Polynomial.C (ReedSolomon.codewordToPoly p) ∣
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) := by
  classical
  exact GuruswamiSudan.gs_divisibility (m := m) hk hm p
    (curve_specialized_conditions ωs f hQ hrep z hz) h_dist

/-- **The composed `L`-ary GS existence chain — the `hQ`/`hrep` supply of `GSCurveInput`.**
From the numeric Johnson-regime conditions alone (`2 ≤ deg`, `n ≠ 0`, `1 ≤ m`), the
`K = F(Z)`-level GS interpolant for the `L`-ary generic curve fold exists together with an
integer representative: `gs_existence_curve` composed with `exists_integer_representative`
(both fold-agnostic) — the `L`-ary `GSLineInputSupply.exists_gs_chain`. -/
theorem exists_gs_curve_chain {n L : ℕ} (deg m : ℕ) (ωs : Fin n ↪ F) (f : Fin L → Fin n → F)
    (hdeg2 : 2 ≤ deg) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ (Q : (RatFunc F)[X][Y]) (d : F[X]) (Q₀ : (F[X])[X][Y]),
      d ≠ 0 ∧
      GuruswamiSudan.Conditions deg m (gs_degree_bound deg n m)
        (liftedDomain ωs) (curveFold f) Q ∧
      Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
        Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q := by
  classical
  obtain ⟨Q, hQ⟩ := gs_existence_curve deg m ωs f (by omega) hn hm
  obtain ⟨d, Q₀, hd, hrep⟩ := exists_integer_representative Q
  exact ⟨Q, d, Q₀, hd, hQ, hrep⟩

end GuruswamiSudan.OverRatFunc

namespace ArkLib

namespace CurveHenselSupply

/-! ## Part 2 — the core brick and the good-set families -/

section Core

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The general-`k` S10-converse divisibility for an arbitrary close low-degree
polynomial** — the curve analogue of `InterpolantInputSupply.dvd_specialization_of_close`.

Let `Q` be a `K = F(Z)`-level GS interpolant for the `L`-ary generic curve fold (the S2
`Conditions`) with integer representative `(d, Q₀)`.  At any `z` where the specialization
survives, every polynomial `W` of degree `< deg` whose evaluations lie within the GS Johnson
radius of the scalar curve fold `∑ⱼ zʲ·fⱼ` is a matching factor of the specialized
interpolant: `(Y − C W) ∣ Q₀|_{Z:=z}`.  The upgrade from `codewordToPoly` to an arbitrary
close polynomial is the Lagrange interpolation round-trip
(`GuruswamiSudan.interpolate_eq_of_degree_lt`). -/
theorem curve_dvd_specialization_of_close {n deg m L : ℕ} (ωs : Fin n ↪ F)
    (f : Fin L → Fin n → F)
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : (F[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions deg m (gs_degree_bound deg n m)
      (GuruswamiSudan.OverRatFunc.liftedDomain ωs)
      (GuruswamiSudan.OverRatFunc.curveFold f) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (hk : deg + 1 ≤ n) (hm : 1 ≤ m) (z : F)
    (hz : Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ≠ 0)
    (W : F[X]) (hWdeg : W.degree < (deg : WithBot ℕ))
    (hdist : (hammingDist (fun i => ∑ j : Fin L, z ^ (j : ℕ) * f j i)
        (fun i => W.eval (ωs i)) : ℝ) / n < gs_johnson deg n m) :
    (Polynomial.X - Polynomial.C W) ∣
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) := by
  classical
  -- `W` is a Reed–Solomon codeword polynomial
  have hmem : ReedSolomon.evalOnPoints ωs W ∈ ReedSolomon.code ωs deg :=
    Submodule.mem_map.mpr ⟨W, Polynomial.mem_degreeLT.mpr hWdeg, rfl⟩
  have hWn : W.natDegree < n := by
    rcases eq_or_ne W 0 with rfl | hW
    · simpa using Nat.lt_of_lt_of_le (Nat.succ_pos deg) hk
    · exact Nat.lt_of_lt_of_le ((Polynomial.natDegree_lt_iff_degree_lt hW).mpr hWdeg)
        (Nat.le_of_succ_le hk)
  -- the Lagrange round-trip: `codewordToPoly` of the evaluation codeword is `W` itself
  have hcw : ReedSolomon.codewordToPoly (⟨ReedSolomon.evalOnPoints ωs W, hmem⟩ :
      ReedSolomon.code ωs deg) = W := by
    have h := GuruswamiSudan.interpolate_eq_of_degree_lt (ωs := ωs) W hWn
    simpa [ReedSolomon.codewordToPoly, ReedSolomon.evalOnPoints] using h
  have hmain := GuruswamiSudan.OverRatFunc.curve_fold_decoded_divides_specialization
    ωs f hQ hrep z hz hk hm ⟨ReedSolomon.evalOnPoints ωs W, hmem⟩
    (by rw [hcw]; convert hdist using 3; congr!)
  rwa [hcw] at hmain

variable {nn : ℕ} [NeZero nn]

/-- The degree-`k` curve word of `RS_goodCoeffsCurve` IS the scalar curve fold of the
`(k + 1)`-ary generic curve fold — the general-`k` analogue of `curveWord_line_eq`. -/
theorem curveWord_fold_eq {k : ℕ} (u : WordStack F (Fin (k + 1)) (Fin nn)) (z : F) :
    (∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t)
      = fun i => ∑ j : Fin (k + 1), z ^ (j : ℕ) * u j i := by
  funext i
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

/-- Good-set membership at curve degree `k` is exactly `δ`-proximity of the scalar curve fold
to the Reed–Solomon code — the general-`k` analogue of `mem_lineGoodCoeffs_iff`. -/
theorem mem_goodCoeffsCurve_iff_fold {k deg : ℕ} {ωs : Fin nn ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) (Fin nn)) (z : F) :
    z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ ↔
      δᵣ((fun i => ∑ j : Fin (k + 1), z ^ (j : ℕ) * u j i),
        ReedSolomon.code ωs deg) ≤ δ := by
  have h : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ ↔
      δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, ReedSolomon.code ωs deg) ≤ δ := by
    simp [RS_goodCoeffsCurve]
  rw [h, curveWord_fold_eq]

/-- **Good-set family form of the general-`k` S10-converse divisibility.**  For an arbitrary
decoding family `W : F → F[X]` (instantiate at the decoded family `P` and at the curve-family
competitor `z ↦ ∑_{t<n} (z − x₀)ᵗ • c t`): per-`z` non-collapse, degree, and fold-proximity
hypotheses on the good set produce the matching divisibility family. -/
theorem curve_dvd_specialization_family {k deg m : ℕ} (ωs : Fin nn ↪ F) {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) (Fin nn))
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : (F[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions deg m (gs_degree_bound deg nn m)
      (GuruswamiSudan.OverRatFunc.liftedDomain ωs)
      (GuruswamiSudan.OverRatFunc.curveFold (fun j i => u j i)) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (hk : deg + 1 ≤ nn) (hm : 1 ≤ m) (W : F → F[X])
    (hgood : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ≠ 0)
    (hWdeg : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      (W z).degree < (deg : WithBot ℕ))
    (hWdist : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      (hammingDist (fun i => ∑ j : Fin (k + 1), z ^ (j : ℕ) * u j i)
          (fun i => (W z).eval (ωs i)) : ℝ) / nn < gs_johnson deg nn m) :
    ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      (Polynomial.X - Polynomial.C (W z)) ∣
        Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) :=
  fun z hz => curve_dvd_specialization_of_close ωs (fun j i => u j i) hQ hrep hk hm z
    (hgood z hz) (W z) (hWdeg z hz) (hWdist z hz)

/-- The curve-family competitor `∑_{t<n} (z − x₀)ᵗ • c t` is a degree-`< deg` (Reed–Solomon
codeword) polynomial whenever each of its coefficients is. -/
theorem curveCompetitor_degree_lt {deg : ℕ} {x₀ : F} {c : ℕ → F[X]} {n : ℕ}
    (hc : ∀ t < n, (c t).degree < (deg : WithBot ℕ)) (z : F) :
    (∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X]).degree < (deg : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
    ((Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe deg)).mpr ?_)
  intro t ht
  exact lt_of_le_of_lt (Polynomial.degree_smul_le _ _) (hc t (Finset.mem_range.mp ht))

end Core

/-! ## Part 3 — the assembled producers -/

section Assembly

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {nn : ℕ} [NeZero nn]

/-- **The general-`k` S10-converse input bundle** for the faithful curve-Hensel lane.

Cargo: the `K = F(Z)`-level GS interpolant for the `(k + 1)`-ary generic curve fold with its
`Conditions` (S2), an integer representative `(d, Q₀)`, the Johnson-regime arithmetic side
conditions, and the per-good-`z` residuals: non-collapse of the specialization, degree +
fold-proximity of BOTH competitors (the decoded family `P` and the curve-family competitor
`z ↦ ∑_{t<n} (z − x₀)ᵗ • c t` — the symmetric GS argument applies to each), order-0 agreement,
and `F[X][Y]`-level separability (unit-discriminant route: `hsep_curve_of_discr_isUnit`). -/
structure GSCurveInput {k : ℕ} (deg m : ℕ) (ωs : Fin nn ↪ F) (δ : ℝ≥0)
    (u : WordStack F (Fin (k + 1)) (Fin nn)) (P : F → Polynomial F)
    (x₀ : F) (n : ℕ) (c : ℕ → F[X]) : Type where
  /-- the `K = F(Z)`-level GS interpolant for the generic curve fold. -/
  Q : (RatFunc F)[X][Y]
  /-- the common denominator of the integer representative. -/
  d : F[X]
  /-- the integer representative of the interpolant, over `F[Z][X][Y]`. -/
  Q₀ : (F[X])[X][Y]
  /-- the S2 GS `Conditions` over `K` for the generic curve fold `∑ⱼ Zʲ·uⱼ`. -/
  hQ : GuruswamiSudan.Conditions deg m (gs_degree_bound deg nn m)
    (GuruswamiSudan.OverRatFunc.liftedDomain ωs)
    (GuruswamiSudan.OverRatFunc.curveFold (fun j i => u j i)) Q
  /-- the integer-representative identity `Q₀ ↦ C(C d)·Q`. -/
  hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
    Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q
  /-- Johnson-regime arity: `deg + 1 ≤ nn`. -/
  hdegn : deg + 1 ≤ nn
  /-- positive multiplicity parameter. -/
  hm : 1 ≤ m
  /-- per-good-`z` non-collapse of the specialization (the cofinite `d(z) ≠ 0` fact). -/
  hgood : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
    Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ≠ 0
  /-- the decoded family has Reed–Solomon degree. -/
  hPdeg : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
    (P z).degree < (deg : WithBot ℕ)
  /-- the decoded family is within the GS Johnson radius of the curve fold. -/
  hPdist : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
    (hammingDist (fun i => ∑ j : Fin (k + 1), z ^ (j : ℕ) * u j i)
        (fun i => (P z).eval (ωs i)) : ℝ) / nn < gs_johnson deg nn m
  /-- the curve-family competitor has Reed–Solomon degree (producible from coefficientwise
  degree bounds via `curveCompetitor_degree_lt`). -/
  hCdeg : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
    (∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X]).degree < (deg : WithBot ℕ)
  /-- the curve-family competitor is within the GS Johnson radius of the curve fold. -/
  hCdist : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
    (hammingDist (fun i => ∑ j : Fin (k + 1), z ^ (j : ℕ) * u j i)
        (fun i => (∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X]).eval (ωs i)) : ℝ) / nn <
      gs_johnson deg nn m
  /-- per-`z` order-0 agreement of the two competitors (the common-approximation fact;
  producible by the `OrderZeroAgreementSupply` routes — `h0_curve_of_centre_agreement`, or
  derived from the divisibilities via `gsCurveInput_of_uniqueRootOn`). -/
  h0 : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
    (∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X]).coeff 0 = (P z).coeff 0
  /-- per-`z` `F[X][Y]`-level separability of the specialized interpolant
  (unit-discriminant route: `hsep_curve_of_discr_isUnit`). -/
  hsep : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
    (Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).Separable

/-- **The decoded-family matching divisibility from the GS curve surface.**  At every good
`z`, `(Y − C (P z)) ∣ Q₀|_{Z:=z}` — `curve_dvd_specialization_of_close` at `W := P z`. -/
theorem GSCurveInput.decoded_dvd {k deg m : ℕ} {ωs : Fin nn ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) (Fin nn)} {P : F → Polynomial F}
    {x₀ : F} {n : ℕ} {c : ℕ → F[X]}
    (data : GSCurveInput (k := k) deg m ωs δ u P x₀ n c) :
    ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      (Polynomial.X - Polynomial.C (P z)) ∣
        data.Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) :=
  fun z hz => curve_dvd_specialization_of_close ωs (fun j i => u j i) data.hQ data.hrep
    data.hdegn data.hm z (data.hgood z hz) (P z) (data.hPdeg z hz) (data.hPdist z hz)

/-- **The curve-family-competitor matching divisibility from the GS curve surface.**  At
every good `z`, `(Y − C (∑_{t<n} (z − x₀)ᵗ • c t)) ∣ Q₀|_{Z:=z}` — the SAME GS argument
applied to the competitor, consuming its own proximity hypothesis. -/
theorem GSCurveInput.competitor_dvd {k deg m : ℕ} {ωs : Fin nn ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) (Fin nn)} {P : F → Polynomial F}
    {x₀ : F} {n : ℕ} {c : ℕ → F[X]}
    (data : GSCurveInput (k := k) deg m ωs δ u P x₀ n c) :
    ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      (Polynomial.X - Polynomial.C (∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X])) ∣
        data.Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) :=
  fun z hz => curve_dvd_specialization_of_close ωs (fun j i => u j i) data.hQ data.hrep
    data.hdegn data.hm z (data.hgood z hz) _ (data.hCdeg z hz) (data.hCdist z hz)

/-- **`CurveHenselDatum` from the general-`k` GS surface (the assembly).**  The per-`z`
matching-polynomial family is the specialization family `z ↦ Q₀|_{Z:=z}` of ONE integer
representative of the `K`-level GS interpolant for the curve fold; BOTH matching facts come
from the same S10-converse brick (`curve_dvd_specialization_of_close`), at the decoded family
`P` and at the curve-family competitor respectively, and all seven fields are discharged
through `curveHenselDatum_of_matchesGraph`. -/
noncomputable def GSCurveInput.toCurveHenselDatum {k deg m : ℕ} {ωs : Fin nn ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) (Fin nn)} {P : F → Polynomial F}
    {x₀ : F} {n : ℕ} {c : ℕ → F[X]}
    (data : GSCurveInput (k := k) deg m ωs δ u P x₀ n c) :
    FaithfulCurveExtraction.CurveHenselDatum (k := k) (deg := deg) (domain := ωs) (δ := δ)
      u P x₀ n c :=
  FaithfulCurveExtraction.curveHenselDatum_of_matchesGraph
    (fun z => data.Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    data.hsep
    (fun z hz => (MatchingExtractor.matchesGraph_iff_dvd _ _).mpr (data.decoded_dvd z hz))
    (fun z hz => (MatchingExtractor.matchesGraph_iff_dvd _ _).mpr (data.competitor_dvd z hz))
    data.h0

/-- The GS curve surface, composed into the faithful `CurveFamilyData` (whose in-tree
consumers reach the §5 keystone `δ_ε_correlatedAgreementCurves`). -/
noncomputable def GSCurveInput.toCurveFamilyData {k deg m : ℕ} {ωs : Fin nn ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) (Fin nn)} {P : F → Polynomial F}
    {x₀ : F} {n : ℕ} {c : ℕ → F[X]} (hn : n < k + 2)
    (data : GSCurveInput (k := k) deg m ωs δ u P x₀ n c) :
    FaithfulCurveExtraction.CurveFamilyData (k := k) (deg := deg) (domain := ωs) (δ := δ)
      u P :=
  FaithfulCurveExtraction.curveFamilyData_of_curveHenselDatum hn data.toCurveHenselDatum

/-- **The derived faithful per-`z` identity.**  On the good set, the decoded member equals
the curve-family evaluation: `P z = ∑_{t<n} (z − x₀)ᵗ • c t` — Hensel uniqueness
(`eval_identity_of_curveHensel`) applied to the GS-produced curve-Hensel datum.  This is the
`hPz` field of `Section5StrictDataOffcentreFaithful`, DERIVED (no arity hypothesis `n < k + 2`
is needed for the bare identity). -/
theorem GSCurveInput.hPz_eq {k deg m : ℕ} {ωs : Fin nn ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) (Fin nn)} {P : F → Polynomial F}
    {x₀ : F} {n : ℕ} {c : ℕ → F[X]}
    (data : GSCurveInput (k := k) deg m ωs δ u P x₀ n c) :
    ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      P z = ∑ t ∈ Finset.range n, (z - x₀) ^ t • c t := fun z hz =>
  FaithfulCurveExtraction.eval_identity_of_curveHensel
    (f := data.toCurveHenselDatum.f z) (a₀ := data.toCurveHenselDatum.a₀ z)
    (data.toCurveHenselDatum.hProot z hz) (data.toCurveHenselDatum.hQroot z hz)
    (data.toCurveHenselDatum.hPapprox z hz) (data.toCurveHenselDatum.hQapprox z hz)
    (data.toCurveHenselDatum.hderiv z hz)

/-! ### The `h0` and `hsep` supply routes on the curve surface -/

/-- **The `h0` field from route (ii) (the centre is a common graph point), at the
curve-family competitor**: if the evaluation domain hits the expansion centre
(`ωs i₀ = 0`) and BOTH competitors agree with the curve word at `i₀`, the order-0 agreement
follows — `OrderZeroAgreementSupply.h0_supply_of_centre_agreement` instantiated at
`Qz' := z ↦ ∑_{t<n} (z − x₀)ᵗ • c t`. -/
theorem h0_curve_of_centre_agreement {k deg : ℕ} {ωs : Fin nn ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) (Fin nn)} (P : F → Polynomial F)
    (x₀ : F) (n : ℕ) (c : ℕ → F[X]) (i₀ : Fin nn) (hdom : ωs i₀ = 0)
    (hPagree : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      (P z).eval (ωs i₀) = (∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t) i₀)
    (hCagree : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      (∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X]).eval (ωs i₀)
        = (∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t) i₀) :
    ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      (∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X]).coeff 0 = (P z).coeff 0 :=
  fun z hz => (OrderZeroAgreementSupply.h0_supply_of_centre_agreement P
    (fun z => ∑ t ∈ Finset.range n, (z - x₀) ^ t • c t) i₀ hdom hPagree hCagree z hz).symm

/-- **The separability field from the unit-discriminant route, on the curve good set** —
`InterpolantInputSupply.hsep_of_discr_isUnit` at `S := RS_goodCoeffsCurve u δ`. -/
theorem hsep_curve_of_discr_isUnit {k deg : ℕ} {ωs : Fin nn ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) (Fin nn)} (Q₀ : (F[X])[X][Y])
    (hdeg : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      0 < (Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).natDegree)
    (hlc : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      IsUnit (Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).leadingCoeff)
    (hdiscr : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      IsUnit (Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).discr) :
    ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      (Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).Separable :=
  InterpolantInputSupply.hsep_of_discr_isUnit Q₀ hdeg hlc hdiscr

/-- **The `h0`-free constructor (route (i)): `GSCurveInput` with the order-0 agreement
DERIVED.**  Both matching divisibilities are produced internally from the GS surface
(`curve_dvd_specialization_of_close`), and the order-0 agreement follows from the per-`z`
centre-fiber uniqueness witness on a class containing both base values
(`OrderZeroAgreementSupply.coeff_zero_eq_of_dvd_of_uniqueRootOn` — BCIKS20 App A.5.2's
pinned base point). -/
noncomputable def gsCurveInput_of_uniqueRootOn {k deg m : ℕ} {ωs : Fin nn ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) (Fin nn)} {P : F → Polynomial F}
    {x₀ : F} {n : ℕ} {c : ℕ → F[X]}
    (Q : (RatFunc F)[X][Y]) (d : F[X]) (Q₀ : (F[X])[X][Y])
    (hQ : GuruswamiSudan.Conditions deg m (gs_degree_bound deg nn m)
      (GuruswamiSudan.OverRatFunc.liftedDomain ωs)
      (GuruswamiSudan.OverRatFunc.curveFold (fun j i => u j i)) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (hdegn : deg + 1 ≤ nn) (hm : 1 ≤ m)
    (hgood : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ≠ 0)
    (hPdeg : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      (P z).degree < (deg : WithBot ℕ))
    (hPdist : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      (hammingDist (fun i => ∑ j : Fin (k + 1), z ^ (j : ℕ) * u j i)
          (fun i => (P z).eval (ωs i)) : ℝ) / nn < gs_johnson deg nn m)
    (hCdeg : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      (∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X]).degree < (deg : WithBot ℕ))
    (hCdist : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      (hammingDist (fun i => ∑ j : Fin (k + 1), z ^ (j : ℕ) * u j i)
          (fun i => (∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X]).eval (ωs i)) : ℝ) / nn <
        gs_johnson deg nn m)
    (hsep : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      (Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).Separable)
    -- route (i) inputs: class memberships of both base values + the uniqueness witness
    (S : F → Set F)
    (hPmem : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      (P z).coeff 0 ∈ S z)
    (hCmem : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      (∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X]).coeff 0 ∈ S z)
    (huniq : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
      OrderZeroAgreementSupply.UniqueRootOn
        (OrderZeroAgreementSupply.baseSpec
          (Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))) (S z)) :
    GSCurveInput (k := k) deg m ωs δ u P x₀ n c :=
  { Q := Q
    d := d
    Q₀ := Q₀
    hQ := hQ
    hrep := hrep
    hdegn := hdegn
    hm := hm
    hgood := hgood
    hPdeg := hPdeg
    hPdist := hPdist
    hCdeg := hCdeg
    hCdist := hCdist
    h0 := fun z hz =>
      (OrderZeroAgreementSupply.coeff_zero_eq_of_dvd_of_uniqueRootOn
        (curve_dvd_specialization_of_close ωs (fun j i => u j i) hQ hrep hdegn hm z
          (hgood z hz) (P z) (hPdeg z hz) (hPdist z hz))
        (curve_dvd_specialization_of_close ωs (fun j i => u j i) hQ hrep hdegn hm z
          (hgood z hz) _ (hCdeg z hz) (hCdist z hz))
        (hPmem z hz) (hCmem z hz) (huniq z hz)).symm
    hsep := hsep }

/-! ### The capstone composition into the faithful off-centre §5 bundle -/

/-- **The faithful off-centre §5 bundle from GS + counting data (the capstone).**  The full
`Section5StrictDataOffcentreFaithful` (whose in-tree front doors reach the §5 keystone
`δ_ε_correlatedAgreementCurves`) from: the GS factor bundle, the Prop-5.5 local representative,
the per-point matching data, the finite-range cardinality bound, the curve data `(n, hn, c)` —
AND the general-`k` GS surface `GSCurveInput`, which discharges the entire `hPz` lane (the
per-`z` curve-Hensel root datum) through `GSCurveInput.toCurveHenselDatum`. -/
noncomputable def section5DataOffcentreFaithful_of_gsCurve
    {k deg m : ℕ} {ωs : Fin nn ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) (Fin nn)} {P : F → Polynomial F}
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (Bcoeff : (i₁ : ℕ) → {m' : ℕ} → Nat.Partition m' → 𝒪 b.H)
    (matchingSet : Finset F)
    (root : (z : F) → rationalRoot (H_tilde' b.H) z)
    (Ppoly : F[X][Y])
    (hrep : polyToPowerSeries𝕃 b.H Ppoly
      = BetaToCurveCoeffPolys.gammaLocal x₀ b.R b.H b.hHyp Bcoeff)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (mpPoint : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ b.R b.H b.hHyp Bcoeff t z (root z))
    (hcardFin : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 b.hH (betaRec x₀ b.R b.H b.hHyp Bcoeff t) b.D * b.H.natDegree)
    (n : ℕ) (hn : n < k + 2) (c : ℕ → F[X])
    (data : GSCurveInput (k := k) deg m ωs δ u P x₀ n c) :
    OffcentreFaithful.Section5StrictDataOffcentreFaithful
      (k := k) (deg := deg) (domain := ωs) (δ := δ) u P :=
  OffcentreFaithful.section5DataOffcentreFaithful_of_producers
    (k := k) (deg := deg) (domain := ωs) (δ := δ) (u := u) (P := P)
    b Bcoeff matchingSet root Ppoly hrep hdegX mpPoint hcardFin
    n hn c data.toCurveHenselDatum

/-! ### The keystone front doors from a per-`(u, P)` GS curve-surface producer -/

/-- **`StrictCoeffPolysResidual` from a per-`(u, P)` GS curve-surface producer.**  The
producer supplies, for each word and decoded family in the strict-Johnson range, a centre, at
most `k + 1` curve coefficients, and the bundled general-`k` GS surface — the honest
S2/S10/§6.2 inputs; the per-`z` Hensel root data are then PRODUCED by this file
(`GSCurveInput.toCurveHenselDatum`). -/
theorem strictCoeffPolysResidual_of_gsCurveInput
    {k deg m : ℕ} {ωs : Fin nn ↪ F} {δ : ℝ≥0}
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) (Fin nn)),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code ωs deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg ωs : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code ωs deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg ωs →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ ωs) ≤ δ) →
        Σ' (x₀ : F) (n : ℕ) (_ : n < k + 2) (c : ℕ → F[X]),
          GSCurveInput (k := k) deg m ωs δ u P x₀ n c) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := ωs) (δ := δ) :=
  FaithfulCurveExtraction.strictCoeffPolysResidual_of_curveHenselDatum
    (fun hk u hprob hJ hsqrt P hP => by
      obtain ⟨x₀, n, hn, c, data⟩ := hInput hk u hprob hJ hsqrt P hP
      exact ⟨x₀, n, hn, c, data.toCurveHenselDatum⟩)

/-- **Strict square-root-radius keystone front door from the GS curve surface.**  The §5
keystone goal `δ_ε_correlatedAgreementCurves` in the strict Johnson regime, from per-`(u, P)`
general-`k` GS curve-input data — every hypothesis is an honest BCIKS20 §5/S2/S10/§6.2
object with its own production lane; the per-`z` Hensel geometry is fully discharged by this
file. -/
theorem correlatedAgreement_affine_curves_johnson_of_gsCurveInput_strict
    {k deg m : ℕ} {ωs : Fin nn ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg ωs)
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) (Fin nn)),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code ωs deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg ωs : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code ωs deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg ωs →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := ωs) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ ωs) ≤ δ) →
        Σ' (x₀ : F) (n : ℕ) (_ : n < k + 2) (c : ℕ → F[X]),
          GSCurveInput (k := k) deg m ωs δ u P x₀ n c) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := Fin nn)
      (C := ReedSolomon.code ωs deg) (δ := δ) (ε := errorBound δ deg ωs) :=
  FaithfulCurveExtraction.correlatedAgreement_affine_curves_johnson_of_curveHenselDatum_strict
    hδ
    (fun hk u hprob hJ hsqrt P hP => by
      obtain ⟨x₀, n, hn, c, data⟩ := hInput hk u hprob hJ hsqrt P hP
      exact ⟨x₀, n, hn, c, data.toCurveHenselDatum⟩)

end Assembly

end CurveHenselSupply

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms GuruswamiSudan.OverRatFunc.intPointYCurve
#print axioms GuruswamiSudan.OverRatFunc.intPointYCurve_two_eq_intPointY
#print axioms GuruswamiSudan.OverRatFunc.map_intPointYCurve
#print axioms GuruswamiSudan.OverRatFunc.eval_intPointYCurve
#print axioms GuruswamiSudan.OverRatFunc.curve_specialized_conditions
#print axioms GuruswamiSudan.OverRatFunc.curve_fold_decoded_divides_specialization
#print axioms GuruswamiSudan.OverRatFunc.exists_gs_curve_chain
#print axioms ArkLib.CurveHenselSupply.curve_dvd_specialization_of_close
#print axioms ArkLib.CurveHenselSupply.curveWord_fold_eq
#print axioms ArkLib.CurveHenselSupply.mem_goodCoeffsCurve_iff_fold
#print axioms ArkLib.CurveHenselSupply.curve_dvd_specialization_family
#print axioms ArkLib.CurveHenselSupply.curveCompetitor_degree_lt
#print axioms ArkLib.CurveHenselSupply.GSCurveInput
#print axioms ArkLib.CurveHenselSupply.GSCurveInput.decoded_dvd
#print axioms ArkLib.CurveHenselSupply.GSCurveInput.competitor_dvd
#print axioms ArkLib.CurveHenselSupply.GSCurveInput.toCurveHenselDatum
#print axioms ArkLib.CurveHenselSupply.GSCurveInput.toCurveFamilyData
#print axioms ArkLib.CurveHenselSupply.GSCurveInput.hPz_eq
#print axioms ArkLib.CurveHenselSupply.h0_curve_of_centre_agreement
#print axioms ArkLib.CurveHenselSupply.hsep_curve_of_discr_isUnit
#print axioms ArkLib.CurveHenselSupply.gsCurveInput_of_uniqueRootOn
#print axioms ArkLib.CurveHenselSupply.section5DataOffcentreFaithful_of_gsCurve
#print axioms ArkLib.CurveHenselSupply.strictCoeffPolysResidual_of_gsCurveInput
#print axioms ArkLib.CurveHenselSupply.correlatedAgreement_affine_curves_johnson_of_gsCurveInput_strict
