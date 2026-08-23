/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.CurveFamilyHensel
import ArkLib.ToMathlib.BetaRecGenuineBridge
import ArkLib.ToMathlib.HenselDatumProducer

/-!
# Issue #304 — the genuine curve-series form and its production lanes

The faithful surface (`FaithfulCurveExtraction`/`CurveFamilyHensel`) consumes the per-`(u, P)`
curve-family datum `P z = ∑_{t<n} (z − x₀)^t • c_t`.  Its production from the genuine analytic
chain decomposes into three lanes, whose meeting point this file formalizes:

* **The curve-series form** (`gammaGenuine_eq_mk_curve` / `gammaGenuine_eq_curve_sum`): if the
  genuine Hensel coefficients are base-rational below `n` (`hbase : αGenuine t = lift (c t)`,
  the §5 rational-section content) and vanish from `n` on (`htail`, the truncation content),
  then the genuine root **is** the curve series
  `gammaGenuine = ∑_{t<n} C (lift (c t)) · X^t` — the series-level Prop-5.5 statement.
* **Truncation from the matching machinery, at the genuine coefficients**
  (`αGenuine_eq_zero_on_range_of_matching_monic`): for monic `H`, the ingredient-C matching data
  and the L9/L10 weight bound at the signed canonical family (`BcoeffSigned`) — the exact data
  the graded collapse + discriminant counting supply — force `αGenuine t = 0` on the counting
  range `[k, T]`.  This routes `HcardDischarge.tail_zero_on_finite_range` through the
  `BetaRecGenuineBridge` monic identification: the matching geometry now speaks directly about
  the genuine analytic coefficients.
* **The separability form of the per-`z` Hensel datum** (`curveHenselDatum_of_separable`): the
  unit-derivative field of `CurveHenselDatum` is discharged from per-`z` separability of the
  matching polynomial (`HenselDatumProducer.isUnit_derivative_of_separable_of_isRoot_of_congr`),
  matching the §6.2 shape (`R(x₀, Y, Z)` separable ⟹ simple roots).

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (Claim 5.8/5.8′, Prop. 5.5), §6.2, Appendix A.4.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open ProximityPrize.BCIKS20.GammaGenuine BCIKS20.HenselNumerator
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace FaithfulCurveExtraction

/-! ## Part 1 — the genuine curve-series form -/

section CurveSeries

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The genuine curve-series form (mk shape).**  If the genuine Hensel coefficients are
base-rational below `n` and vanish from `n` on, the genuine root is the truncated series with
base-rational coefficients.  `hbase` is the §5 rational-section content; `htail` is the
truncation content (supplied on `[k, T]` by the matching machinery below, and beyond `T` by the
algebraic-degree argument). -/
theorem gammaGenuine_eq_mk_curve {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    {n : ℕ} {c : ℕ → F[X]}
    (hbase : ∀ t < n, αGenuine H x₀ R hHyp t = liftToFunctionField (H := H) (c t))
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0) :
    gammaGenuine x₀ R H hHyp
      = PowerSeries.mk (fun t => if t < n then liftToFunctionField (H := H) (c t) else 0) := by
  ext s
  rw [PowerSeries.coeff_mk]
  by_cases hs : s < n
  · rw [if_pos hs]
    exact hbase s hs
  · rw [if_neg hs]
    exact htail s (le_of_not_gt hs)

/-- **The genuine curve-series form (finite-sum shape).**  Same hypotheses, with the conclusion
as the explicit polynomial curve `∑_{t<n} C (lift (c t)) · X^t` — the series-level rendering of
[BCIKS20] Prop. 5.5. -/
theorem gammaGenuine_eq_curve_sum {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    {n : ℕ} {c : ℕ → F[X]}
    (hbase : ∀ t < n, αGenuine H x₀ R hHyp t = liftToFunctionField (H := H) (c t))
    (htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0) :
    gammaGenuine x₀ R H hHyp
      = ∑ t ∈ Finset.range n,
          PowerSeries.C (liftToFunctionField (H := H) (c t)) * PowerSeries.X ^ t := by
  rw [gammaGenuine_eq_mk_curve hHyp hbase htail]
  ext s
  rw [PowerSeries.coeff_mk, map_sum]
  by_cases hs : s < n
  · rw [if_pos hs]
    rw [Finset.sum_eq_single s
      (fun t _ hts => by
        rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg (fun h => hts h.symm),
          mul_zero])
      (fun hs' => absurd (Finset.mem_range.mpr hs) hs')]
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_pos rfl, mul_one]
  · rw [if_neg hs]
    refine (Finset.sum_eq_zero (fun t ht => ?_)).symm
    have hts : s ≠ t := fun h => hs (h ▸ Finset.mem_range.mp ht)
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg hts, mul_zero]

end CurveSeries

/-! ## Part 2 — genuine-coefficient vanishing from the matching machinery (monic) -/

section MatchingVanishing

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The matching machinery speaks about the genuine coefficients (monic).**  The ingredient-C
per-point matching data and the L9/L10 weight bound at the **signed canonical family** — exactly
what the graded collapse + discriminant counting supply
(`GenuineMonicCapstone.hcardFin_of_graded_signed` ∘ `gradedConcreteFin_of_disc`) — force the
**genuine** Hensel coefficients to vanish on the counting range:
`αGenuine t = 0` for `k ≤ t ≤ T`.

Route: `HcardDischarge.tail_zero_on_finite_range` (the counting branch, at `BcoeffSigned`)
gives `αFromBeta … (BcoeffSigned …) t = 0`; the `BetaRecGenuineBridge` monic identification
(`alphaFromBeta_BcoeffSigned_eq_αGenuine_of_monic`) transports it to `αGenuine`. -/
theorem αGenuine_eq_zero_on_range_of_matching_monic
    (x₀ : F) (R : F[X][X][Y]) (hHyp : Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1) (hH : 0 < H.natDegree) (D : ℕ)
    (hD : D ≥ Bivariate.totalDegree H) (k T : ℕ)
    {matchingSet : Finset F} {root : (z : F) → rationalRoot (H_tilde' H) z}
    (mpFin : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t z (root z))
    (hcardFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 hH
            (betaRec x₀ R H hHyp (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t) D
          * H.natDegree) :
    ∀ t, k ≤ t → t ≤ T → αGenuine H x₀ R hHyp t = 0 := by
  intro t hkt htT
  rw [← BetaRecGenuineBridge.alphaFromBeta_BcoeffSigned_eq_αGenuine_of_monic x₀ R hHyp hlc t]
  exact HcardDischarge.tail_zero_on_finite_range x₀ R H hHyp
    (BetaRecGenuineBridge.BcoeffSigned H x₀ R) hH D hD k T mpFin hcardFin t hkt htT

end MatchingVanishing

/-! ## Part 3 — the separability form of the per-`z` curve-Hensel datum -/

section Separable

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The curve-Hensel datum from per-`z` separability.**  As `CurveHenselDatum`, with the
unit-derivative field replaced by separability of the per-`z` matching polynomial — the §6.2
shape (`R(x₀, Y, Z)` separable, simple roots).  The derivative-unit is derived via
`HenselDatumProducer.isUnit_derivative_of_separable_of_isRoot_of_congr` at the decoded root. -/
noncomputable def curveHenselDatum_of_separable {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} {n : ℕ} {c : ℕ → F[X]}
    (f : F → Polynomial (PowerSeries F))
    (a₀ : F → PowerSeries F)
    (hProot : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (f z).IsRoot ((P z : F[X]) : PowerSeries F))
    (hQroot : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (f z).IsRoot (((∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X])) : PowerSeries F))
    (hPapprox : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ((P z : F[X]) : PowerSeries F) - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hQapprox : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (((∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X])) : PowerSeries F) - a₀ z
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsep : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (f z).Separable) :
    CurveHenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P x₀ n c :=
  { f := f
    a₀ := a₀
    hProot := hProot
    hQroot := hQroot
    hPapprox := hPapprox
    hQapprox := hQapprox
    hderiv := fun z hz =>
      HenselDatumProducer.isUnit_derivative_of_separable_of_isRoot_of_congr (f z)
        (hsep z hz) (hProot z hz) (hPapprox z hz) }

omit [Nonempty ι] [DecidableEq ι] in
/-- **Curve-family datum from per-`z` separability data** — the composition
`curveFamilyData_of_curveHenselDatum ∘ curveHenselDatum_of_separable`. -/
noncomputable def curveFamilyData_of_separable {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} {n : ℕ} {c : ℕ → F[X]} (hn : n < k + 2)
    (f : F → Polynomial (PowerSeries F))
    (a₀ : F → PowerSeries F)
    (hProot : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (f z).IsRoot ((P z : F[X]) : PowerSeries F))
    (hQroot : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (f z).IsRoot (((∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X])) : PowerSeries F))
    (hPapprox : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ((P z : F[X]) : PowerSeries F) - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hQapprox : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (((∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X])) : PowerSeries F) - a₀ z
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsep : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (f z).Separable) :
    CurveFamilyData (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  curveFamilyData_of_curveHenselDatum hn
    (curveHenselDatum_of_separable f a₀ hProot hQroot hPapprox hQapprox hsep)

end Separable

end FaithfulCurveExtraction

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.FaithfulCurveExtraction.gammaGenuine_eq_mk_curve
#print axioms ArkLib.FaithfulCurveExtraction.gammaGenuine_eq_curve_sum
#print axioms ArkLib.FaithfulCurveExtraction.αGenuine_eq_zero_on_range_of_matching_monic
#print axioms ArkLib.FaithfulCurveExtraction.curveHenselDatum_of_separable
#print axioms ArkLib.FaithfulCurveExtraction.curveFamilyData_of_separable
