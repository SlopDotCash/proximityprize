/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.TAffinePlaceReading
import ArkLib.ToMathlib.CurveHenselDatumProducers

/-!
# Issue #304 — the universal Hensel pin and the `CurvePlaceReading` production

Two bricks closing the gap between the `T`-affine reading chain (`TAffinePlaceReading`) and the
`CurveFamilyZLinear` consumer surface:

* `Pz_eq_trunc_of_hensel` — **the universal pin**: at every good place, Hensel uniqueness pins
  the decoded polynomial equal to the truncated local series — *without* any `htrunc`
  hypothesis about what the truncation equals.  (The existing
  `curveHenselDatum_of_truncatedLocalRoot` is the single-family corollary; the `T`-affine
  production below is the two-family one.)  Inputs: the GS cargo (`hdvd` at `↑(P z)`, the
  order-0 congruence `hcong`), the tail vanishing, separability of `R`, and the per-place
  `ξ`-reading nonvanishing.
* `curvePlaceReading_of_zLinear` — **the `CurvePlaceReading` production**: with the `T`-affine
  (Claim 5.9) window `αGenuine t = lift c₀ᵗ + T·lift c₁ᵗ` for `t < n` and the genuine tail, the
  pin + the two-family truncated reading (`trunc_localSeries_of_zLinear`) + the transposition
  identity give the per-place two-series reading
  `P z = (∑ (z−x₀)^s • c₀ᵀ_s) + t_z • (∑ (z−x₀)^s • c₁ᵀ_s)` — i.e. a genuine
  `CurveFamilyZLinear.CurvePlaceReading` with the branch values `r z := t_z` and the transposed
  coefficient families.  Through the proven `curveFamilyData_of_placeReading`, the remaining
  step to the keystone is exactly branch rationality (`hbranch`) plus the degree budget — the
  honest `R3` residual.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (Claim 5.9), §6.2 (Hensel uniqueness `π_z(γ) = P_z`), Appendix A.3–A.4.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open ProximityGap Code NNReal Finset Function
open ProximityPrize.BCIKS20.GammaGenuine BCIKS20.HenselNumerator
open scoped BigOperators ENNReal

namespace ArkLib

namespace FaithfulCurveExtraction

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## Part 1 — the universal Hensel pin -/

/-- **The universal Hensel pin.**  At every good place the decoded polynomial equals the
truncated local series: both are roots of the `π̂_z`-specialized matching polynomial, both
congruent at order 0 to `C (π_z (βHensel 0))`, and the specialization is separable — Hensel
uniqueness (`decoded_eq_specialization_of_hensel`) pins them equal.  No hypothesis is made
about what the truncation equals: this is the `htrunc`-free core of the analytic producers. -/
theorem Pz_eq_trunc_of_hensel {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1) (hR : R.Separable)
    {n : ℕ}
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    (hvanish : ∀ t, n ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t = 0)
    (hdvd : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (Polynomial.X - Polynomial.C ((P z : F[X]) : PowerSeries F)) ∣
        ((R.map (coeffHom_loc x₀ hHyp)).map
          (PowerSeries.map (π_hat_z hHyp z (root z) (hx z hz)))))
    (hcong : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ((P z : F[X]) : PowerSeries F) - PowerSeries.C ((π_z z (root z))
          (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}) :
    ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      P z = (PowerSeries.trunc n (localSeries hHyp z (root z) (hx z hz)) : Polynomial F) := by
  intro z hz
  have htailz : ∀ t, n ≤ t →
      PowerSeries.coeff t (localSeries hHyp z (root z) (hx z hz)) = 0 := fun t ht =>
    coeff_localSeries_eq_zero_of_alphaFromBeta_eq_zero hHyp hξ z (root z) (hx z hz) t
      (hvanish t ht)
  refine HPzBridge.decoded_eq_specialization_of_hensel
    (f := (R.map (coeffHom_loc x₀ hHyp)).map
      (PowerSeries.map (π_hat_z hHyp z (root z) (hx z hz))))
    (a₀ := PowerSeries.C ((π_z z (root z)) (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0)))
    ?_ ?_ ?_ ?_ ?_
  · -- ↑(P z) is a root (from the matching-factor divisibility)
    rw [← Polynomial.dvd_iff_isRoot]
    exact hdvd z hz
  · -- the coerced truncation is a root (it IS the local series, a root)
    rw [← powerSeries_eq_coe_trunc_of_tail_zero htailz]
    exact localSeries_isRoot_of_monic hHyp hξ hlc z (root z) (hx z hz)
  · -- order-0 congruence of ↑(P z)
    exact hcong z hz
  · -- order-0 congruence of the truncation (derived)
    rw [← powerSeries_eq_coe_trunc_of_tail_zero htailz,
      Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub,
      constantCoeff_localSeries hHyp z (root z) (hx z hz), PowerSeries.constantCoeff_C,
      sub_self]
  · -- unit derivative at the approximation, from separability + the decoded root/congruence
    refine HenselDatumProducer.isUnit_derivative_of_separable_of_isRoot_of_congr _
      (specialized_separable_of_R_separable hHyp z (root z) (hx z hz) hR) ?_ (hcong z hz)
    rw [← Polynomial.dvd_iff_isRoot]
    exact hdvd z hz

/-! ## Part 2 — the `CurvePlaceReading` production at `T`-affine orders -/

/-- **The `CurvePlaceReading` production (monic, `T`-affine window).**  From the Claim-5.9
`T`-affine window `αGenuine t = lift c₀ᵗ + T·lift c₁ᵗ` (`t < n`), the genuine tail, and the
per-place GS cargo, the decoded family carries the per-place two-series reading with the
**branch values** as the readings of `T` and the **transposed** coefficient families:
`P z = (∑_{s<N} (z−x₀)^s • c₀ᵀ_s) + t_z • (∑_{s<N} (z−x₀)^s • c₁ᵀ_s)`. -/
noncomputable def curvePlaceReading_of_zLinear {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1) (hR : R.Separable)
    {n N : ℕ} {c₀ c₁ : ℕ → F[X]}
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    (hzl : ∀ t < n, αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H) (c₀ t)
        + liftToFunctionField (H := H) (c₁ t) * functionFieldT (H := H))
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (hdeg₀ : ∀ t < n, (c₀ t).natDegree < N)
    (hdeg₁ : ∀ t < n, (c₁ t).natDegree < N)
    (hdvd : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (Polynomial.X - Polynomial.C ((P z : F[X]) : PowerSeries F)) ∣
        ((R.map (coeffHom_loc x₀ hHyp)).map
          (PowerSeries.map (π_hat_z hHyp z (root z) (hx z hz)))))
    (hcong : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ((P z : F[X]) : PowerSeries F) - PowerSeries.C ((π_z z (root z))
          (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}) :
    CurvePlaceReading (k := k) (deg := deg) (domain := domain) (δ := δ) u P x₀ N
      (transposedCurveCoeffs x₀ n c₀)
      (transposedCurveCoeffs x₀ n c₁) where
  r := fun z => (root z).1
  hread := by
    intro z hz
    have hvanish : ∀ t, n ≤ t →
        BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp
          (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t = 0 := fun t ht => by
      rw [BetaRecGenuineBridge.alphaFromBeta_BcoeffSigned_eq_αGenuine_of_monic x₀ R hHyp hlc t]
      exact htail t ht
    rw [Pz_eq_trunc_of_hensel hHyp hξ hlc hR (n := n) root hx hvanish hdvd hcong z hz,
      TAffineReading.trunc_localSeries_of_zLinear hHyp hlc z (root z) (hx z hz)
        (le_refl n) hzl htail,
      sum_C_eval_eq_transposed_curve_sum x₀ c₀ hdeg₀,
      sum_C_eval_eq_transposed_curve_sum x₀ c₁ hdeg₁]

end FaithfulCurveExtraction

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.FaithfulCurveExtraction.Pz_eq_trunc_of_hensel
#print axioms ArkLib.FaithfulCurveExtraction.curvePlaceReading_of_zLinear
