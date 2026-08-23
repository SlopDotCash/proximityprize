/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.HcardDischarge
import ArkLib.ToMathlib.BetaMatchingVanishesOn
import ArkLib.ToMathlib.CurveHenselDatumProducers
import ArkLib.ToMathlib.GenuineMonicCapstone
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.StrictCoeffLargeReduction
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.S5GenuineMonic

/-!
# Issue #304 — restricted-root repair of the §5 analytic producer lane

**Satisfiability finding #3** (issue #304): the §5 producer chain demands a TOTAL rational-root
family `root : (z : F) → rationalRoot (H_tilde' H) z`, which is unsatisfiable for typical GS
factors — the fibre type is *empty* at every non-split `z`, and a GS factor of `Y`-degree ≥ 2
is generally not fibrewise totally split.  Every actual USE of `root` is at matching-set /
good-set members only, so the honest, satisfiable shape is the membership-restricted family
`rootOn : ∀ z ∈ S, rationalRoot …`.  `BetaMatchingVanishesOn` repaired the ingredient-C
consumer chain; this file transports the remaining total-root surfaces of the producer lane:

* **Part 1 — the counting branch** (`HcardDischarge`):
  `tail_zero_on_finite_range_on`, `tail_zero_of_finite_card_and_degree_on` — the finite-range
  α-tail vanishing from restricted matching data, through the landed restricted Claim-5.8 chain
  (`BetaMatchingVanishes.betaRec_embedding_eq_zero_of_matchingSet_largeOn`).
* **Part 2 — the genuine-coefficient transport (monic)**:
  `αGenuine_eq_zero_on_range_of_matching_monic_on` — the matching machinery forces the genuine
  Hensel coefficients `αGenuine` to vanish on the counting range, at restricted roots.
* **Part 3 — the Lane-2b analytic producers**:
  `curveHenselDatum_of_truncatedLocalRoot_on` (+ `_genuine_on`) — the per-`(u, P)`
  `CurveHenselDatum` from the constructed local series, demanding rational roots and unit
  conditions at good-set members ONLY (the `f`/`a₀` fields are extended off the good set by
  junk values, which no consumer reads).
* **Part 4 — the weld to the issue-named core**:
  `LocalSeriesDatumOn` — the satisfiable per-`(u, P)` restricted-root analytic §5 datum — and
  the front doors `strictCoeffPolysResidual_of_localSeriesDatumOn` (discharging the exact
  `ProximityGap.StrictCoeffPolysResidual` of `Curves.lean`),
  `strictCoeffPolysLargeResidual_of_localSeriesDatumOn` (the same producer in the reduced
  large-good-set residual shape), and
  `correlatedAgreement_affine_curves_johnson_of_localSeriesDatumOn_strict` (reaching the §5
  keystone `δ_ε_correlatedAgreementCurves` in the strict Johnson regime).

## Honest scope

This file proves NO new counting/geometry mathematics: it repairs the *interfaces* of the
analytic producer lane so that they are satisfiable for honest GS factors (finding #3), and
re-welds them to `StrictCoeffPolysResidual`.  The genuinely open per-`(u, P)` inputs are
unchanged and explicitly carried: the base-rational reading `htrunc` (BCIKS20 §5 Claim 5.9 /
Prop 5.5 content), the tail vanishing `hvanish` (supplied on `[k, T]` by Part 2 + the graded
collapse, beyond `T` by the algebraic-degree lane), the decoded-side GS cargo `hdvd`/`hcong`
(matching-factor divisibility), per-`z` unit conditions `hx`, and one global `R.Separable`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Prop. 5.5, Claim 5.8/5.9), §6.2, Appendix A.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open ProximityPrize.BCIKS20.GammaGenuine BCIKS20.HenselNumerator
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

/-! ## Part 1 — the counting branch at restricted roots -/

namespace HcardDischarge

open BetaToCurveCoeffPolys

variable {F : Type} [Field F]

/-- **Restricted-root finite-range counting branch.**  `tail_zero_on_finite_range` with the
total root family replaced by the satisfiable membership-restricted family
`rootOn : ∀ z ∈ matchingSet, rationalRoot …` — per-point matching data are demanded at
matching-set members only.  Fires through the restricted Claim-5.8 chain
(`BetaMatchingVanishes.betaRec_embedding_eq_zero_of_matchingSet_largeOn`). -/
theorem tail_zero_on_finite_range_on (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H) (k T : ℕ)
    {matchingSet : Finset F}
    {rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' H) z}
    (mpFin : ∀ t, k ≤ t → t ≤ T → ∀ z (hz : z ∈ matchingSet),
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (rootOn z hz))
    (hcardFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree) :
    ∀ t, k ≤ t → t ≤ T → αFromBeta x₀ R H hHyp Bcoeff t = 0 := by
  intro t hkt htT
  have hemb : embeddingOf𝒪Into𝕃 H (betaRec x₀ R H hHyp Bcoeff t) = 0 :=
    BetaMatchingVanishes.betaRec_embedding_eq_zero_of_matchingSet_largeOn
      x₀ R H hHyp Bcoeff t hH D hD (mpFin t hkt htT) (hcardFin t hkt htT)
  exact alphaFromBeta_eq_zero_of_embedding_zero x₀ R H hHyp Bcoeff hemb

/-- **Restricted-root composed truncation lemma.**  `tail_zero_of_finite_card_and_degree` at the
membership-restricted root family: finite-range counting data + the algebraic-degree datum give
the full infinite α-tail vanishing the power-series-truncation consumers need. -/
theorem tail_zero_of_finite_card_and_degree_on (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (hH : 0 < H.natDegree) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H) (k T : ℕ)
    {matchingSet : Finset F}
    {rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' H) z}
    (mpFin : ∀ t, k ≤ t → t ≤ T → ∀ z (hz : z ∈ matchingSet),
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (rootOn z hz))
    (hcardFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D * H.natDegree)
    (htailDeg : ∀ t, T < t → αFromBeta x₀ R H hHyp Bcoeff t = 0) :
    ∀ t, k ≤ t → αFromBeta x₀ R H hHyp Bcoeff t = 0 :=
  tail_zero_of_range_and_degree
    (tail_zero_on_finite_range_on x₀ R H hHyp Bcoeff hH D hD k T mpFin hcardFin)
    htailDeg

end HcardDischarge

namespace FaithfulCurveExtraction

/-! ## Part 2 — genuine-coefficient vanishing from restricted matching data (monic) -/

section MatchingVanishing

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The matching machinery speaks about the genuine coefficients, at restricted roots
(monic).**  `αGenuine_eq_zero_on_range_of_matching_monic` with the total root family replaced
by the satisfiable membership-restricted family: ingredient-C per-point matching data at
matching-set members + the L9/L10 weight bound at the signed canonical family force
`αGenuine t = 0` on the counting range `[k, T]`. -/
theorem αGenuine_eq_zero_on_range_of_matching_monic_on
    (x₀ : F) (R : F[X][X][Y]) (hHyp : Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1) (hH : 0 < H.natDegree) (D : ℕ)
    (hD : D ≥ Bivariate.totalDegree H) (k T : ℕ)
    {matchingSet : Finset F}
    {rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' H) z}
    (mpFin : ∀ t, k ≤ t → t ≤ T → ∀ z (hz : z ∈ matchingSet),
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t z (rootOn z hz))
    (hcardFin : ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 hH
            (betaRec x₀ R H hHyp (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t) D
          * H.natDegree) :
    ∀ t, k ≤ t → t ≤ T → αGenuine H x₀ R hHyp t = 0 := by
  intro t hkt htT
  rw [← BetaRecGenuineBridge.alphaFromBeta_BcoeffSigned_eq_αGenuine_of_monic x₀ R hHyp hlc t]
  exact HcardDischarge.tail_zero_on_finite_range_on x₀ R H hHyp
    (BetaRecGenuineBridge.BcoeffSigned H x₀ R) hH D hD k T mpFin hcardFin t hkt htT

/-- **Genuine-coefficient truncation composition.**  The counting range `[n, T]` (from
`αGenuine_eq_zero_on_range_of_matching_monic_on`) plus the algebraic-degree datum beyond `T`
give the full infinite genuine tail — the exact `hvanish` field of `LocalSeriesDatumOn`.
Pure case split; the genuine §5 content is isolated entirely in the two inputs. -/
theorem αGenuine_tail_zero_of_range_and_degree
    {x₀ : F} {R : F[X][X][Y]} {hHyp : Hypotheses x₀ R H} {n T : ℕ}
    (hrange : ∀ t, n ≤ t → t ≤ T → αGenuine H x₀ R hHyp t = 0)
    (htailDeg : ∀ t, T < t → αGenuine H x₀ R hHyp t = 0) :
    ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0 := by
  intro t hnt
  rcases le_or_gt t T with htT | htT
  · exact hrange t hnt htT
  · exact htailDeg t htT

end MatchingVanishing

/-! ## Part 3 — the Lane-2b analytic producers at restricted roots -/

section LocalSeries

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **`CurveHenselDatum` from the constructed local series, at restricted roots.**
`curveHenselDatum_of_truncatedLocalRoot` with the total root family replaced by the
membership-restricted `rootOn : ∀ z ∈ good, rationalRoot …`: rational roots of the GS factor
and unit conditions are demanded at good-set members ONLY.  The matching polynomial `f z` and
approximation `a₀ z` are extended off the good set by `0` (no consumer evaluates them there).
This is the satisfiable form of the analytic producer for GS factors that are not fibrewise
totally split (finding #3). -/
noncomputable def curveHenselDatum_of_truncatedLocalRoot_on {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1) (hR : R.Separable)
    {n : ℕ} {c : ℕ → F[X]}
    (rootOn : (z : F) → z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ →
      rationalRoot (H_tilde' H) z)
    (hx : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (π_z z (rootOn z hz)) (ξ x₀ R H hHyp) ≠ 0)
    (hvanish : ∀ t, n ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t = 0)
    (htrunc : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (PowerSeries.trunc n (localSeries hHyp z (rootOn z hz) (hx z hz)) : Polynomial F)
        = ∑ t ∈ Finset.range n, (z - x₀) ^ t • c t)
    (hdvd : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (Polynomial.X - Polynomial.C ((P z : F[X]) : PowerSeries F)) ∣
        ((R.map (coeffHom_loc x₀ hHyp)).map
          (PowerSeries.map (π_hat_z hHyp z (rootOn z hz) (hx z hz)))))
    (hcong : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      ((P z : F[X]) : PowerSeries F) - PowerSeries.C ((π_z z (rootOn z hz))
          (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}) :
    CurveHenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P x₀ n c :=
  curveHenselDatum_of_separable
    (fun z =>
      if hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ then
        (R.map (coeffHom_loc x₀ hHyp)).map
          (PowerSeries.map (π_hat_z hHyp z (rootOn z hz) (hx z hz)))
      else 0)
    (fun z =>
      if hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ then
        PowerSeries.C ((π_z z (rootOn z hz))
          (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
      else 0)
    (fun z hz => by
      dsimp only
      rw [dif_pos hz]
      exact Polynomial.dvd_iff_isRoot.mp (hdvd z hz))
    (fun z hz => by
      dsimp only
      rw [dif_pos hz, ← htrunc z hz]
      exact trunc_localSeries_isRoot_of_alphaFromBeta_vanishing hHyp hξ hlc z (rootOn z hz)
        (hx z hz) hvanish)
    (fun z hz => by
      dsimp only
      rw [dif_pos hz]
      exact hcong z hz)
    (fun z hz => by
      dsimp only
      rw [dif_pos hz, ← htrunc z hz,
        ← powerSeries_eq_coe_trunc_of_tail_zero (fun t ht =>
          coeff_localSeries_eq_zero_of_alphaFromBeta_eq_zero hHyp hξ z (rootOn z hz)
            (hx z hz) t (hvanish t ht)),
        Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub,
        constantCoeff_localSeries hHyp z (rootOn z hz) (hx z hz), PowerSeries.constantCoeff_C,
        sub_self])
    (fun z hz => by
      dsimp only
      rw [dif_pos hz]
      exact specialized_separable_of_R_separable hHyp z (rootOn z hz) (hx z hz) hR)

/-- The restricted-root analytic producer with the tail vanishing supplied at the **genuine**
coefficients (`αGenuine t = 0` for `t ≥ n` — the form
`αGenuine_eq_zero_on_range_of_matching_monic_on` produces), transported through the monic
`BetaRecGenuineBridge` identification. -/
noncomputable def curveHenselDatum_of_truncatedLocalRoot_genuine_on {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1) (hR : R.Separable)
    {n : ℕ} {c : ℕ → F[X]}
    (rootOn : (z : F) → z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ →
      rationalRoot (H_tilde' H) z)
    (hx : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (π_z z (rootOn z hz)) (ξ x₀ R H hHyp) ≠ 0)
    (hvanish : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (htrunc : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (PowerSeries.trunc n (localSeries hHyp z (rootOn z hz) (hx z hz)) : Polynomial F)
        = ∑ t ∈ Finset.range n, (z - x₀) ^ t • c t)
    (hdvd : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (Polynomial.X - Polynomial.C ((P z : F[X]) : PowerSeries F)) ∣
        ((R.map (coeffHom_loc x₀ hHyp)).map
          (PowerSeries.map (π_hat_z hHyp z (rootOn z hz) (hx z hz)))))
    (hcong : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      ((P z : F[X]) : PowerSeries F) - PowerSeries.C ((π_z z (rootOn z hz))
          (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}) :
    CurveHenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P x₀ n c :=
  curveHenselDatum_of_truncatedLocalRoot_on hHyp hξ hlc hR rootOn hx
    (fun t ht => by
      rw [BetaRecGenuineBridge.alphaFromBeta_BcoeffSigned_eq_αGenuine_of_monic x₀ R hHyp hlc t]
      exact hvanish t ht)
    htrunc hdvd hcong

omit [Nonempty ι] [DecidableEq ι] in
/-- The restricted-root analytic producer, composed into the faithful `CurveFamilyData`. -/
noncomputable def curveFamilyData_of_truncatedLocalRoot_on {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1) (hR : R.Separable)
    {n : ℕ} {c : ℕ → F[X]} (hn : n < k + 2)
    (rootOn : (z : F) → z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ →
      rationalRoot (H_tilde' H) z)
    (hx : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (π_z z (rootOn z hz)) (ξ x₀ R H hHyp) ≠ 0)
    (hvanish : ∀ t, n ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t = 0)
    (htrunc : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (PowerSeries.trunc n (localSeries hHyp z (rootOn z hz) (hx z hz)) : Polynomial F)
        = ∑ t ∈ Finset.range n, (z - x₀) ^ t • c t)
    (hdvd : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (Polynomial.X - Polynomial.C ((P z : F[X]) : PowerSeries F)) ∣
        ((R.map (coeffHom_loc x₀ hHyp)).map
          (PowerSeries.map (π_hat_z hHyp z (rootOn z hz) (hx z hz)))))
    (hcong : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      ((P z : F[X]) : PowerSeries F) - PowerSeries.C ((π_z z (rootOn z hz))
          (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}) :
    CurveFamilyData (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  curveFamilyData_of_curveHenselDatum hn
    (curveHenselDatum_of_truncatedLocalRoot_on hHyp hξ hlc hR rootOn hx hvanish htrunc
      hdvd hcong)

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- **The family-level `mpFin` supply at restricted roots.**  `mpFin_of_localSeries` with the
total root family replaced by the membership-restricted one: per-`z` factor-level GS cargo at
matching-set members only yields the exact restricted `mpFin` field that
`tail_zero_on_finite_range_on` / `αGenuine_eq_zero_on_range_of_matching_monic_on` consume. -/
noncomputable def mpFin_of_localSeries_on {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (hR : R.Separable)
    {matchingSet : Finset F}
    {rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' H) z}
    (hx : ∀ z (hz : z ∈ matchingSet), (π_z z (rootOn z hz)) (ξ x₀ R H hHyp) ≠ 0)
    (aP : F → PowerSeries F)
    (k T : ℕ)
    (hdvd : ∀ z (hz : z ∈ matchingSet),
      (Polynomial.X - Polynomial.C (aP z)) ∣
        ((R.map (coeffHom_loc x₀ hHyp)).map
          (PowerSeries.map (π_hat_z hHyp z (rootOn z hz) (hx z hz)))))
    (hcong : ∀ z (hz : z ∈ matchingSet),
      aP z - PowerSeries.C ((π_z z (rootOn z hz))
          (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hvanish : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      PowerSeries.coeff t (aP z) = 0) :
    ∀ t, k ≤ t → t ≤ T → ∀ z (hz : z ∈ matchingSet),
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t z (rootOn z hz) :=
  fun t hkt htT z hz =>
    matchingPoint_of_localSeries_dvd hHyp hξ hlc z (rootOn z hz) (hx z hz) (aP z)
      (hdvd z hz) (hcong z hz)
      (specialized_separable_of_R_separable hHyp z (rootOn z hz) (hx z hz) hR)
      t (hvanish t hkt htT z hz)

end LocalSeries

/-! ## Part 4 — the satisfiable per-`(u, P)` datum and the weld to
`StrictCoeffPolysResidual` -/

section Weld

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The satisfiable restricted-root analytic §5 datum** (per word `u`, decoded family `P`).
All series-level hypotheses are stated against the **genuine** Hensel coefficients
(`αGenuine`); the rational-root family and the unit conditions are demanded at good-set
members ONLY (finding #3 repaired); every field is an honest BCIKS20 §5/§6.2 obligation:

* `hvanish` — the truncation tail (supplied on `[k, T]` by
  `αGenuine_eq_zero_on_range_of_matching_monic_on` ∘ graded collapse, beyond `T` by the
  algebraic-degree lane);
* `htrunc` — the per-`z` base-rational reading (§5 Claim-5.9 / Prop-5.5 content);
* `hdvd`/`hcong` — the decoded-side GS matching-factor cargo (§6.2);
* `hx` — per-`z` unit condition; `hR` — GS interpolant separability. -/
structure LocalSeriesDatumOn {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F) : Type where
  /-- the expansion centre. -/
  x₀ : F
  /-- the GS interpolant data. -/
  R : F[X][X][Y]
  /-- the (monic) irreducible GS factor. -/
  H : F[X][Y]
  hIrr : Fact (Irreducible H)
  hPos : Fact (0 < H.natDegree)
  hHyp : Hypotheses x₀ R H
  hξ : ξ x₀ R H hHyp ≠ 0
  hlc : H.leadingCoeff = 1
  hR : R.Separable
  /-- the number of curve coefficients (at most `k + 1`). -/
  n : ℕ
  hn : n < k + 2
  /-- the codeword-polynomial curve coefficients. -/
  c : ℕ → F[X]
  /-- the **membership-restricted** rational-root family (finding #3: total families are
  unsatisfiable for typical GS factors). -/
  rootOn : (z : F) → z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ →
    rationalRoot (H_tilde' H) z
  /-- per-`z` unit condition at good-set members. -/
  hx : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
    (π_z z (rootOn z hz)) (ξ x₀ R H hHyp) ≠ 0
  /-- tail vanishing of the genuine Hensel coefficients from `n` on. -/
  hvanish : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0
  /-- the per-`z` base-rational reading: the truncated local series IS the curve
  specialization. -/
  htrunc : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
    (PowerSeries.trunc n (localSeries hHyp z (rootOn z hz) (hx z hz)) : Polynomial F)
      = ∑ t ∈ Finset.range n, (z - x₀) ^ t • c t
  /-- the decoded-side GS matching-factor divisibility. -/
  hdvd : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
    (Polynomial.X - Polynomial.C ((P z : F[X]) : PowerSeries F)) ∣
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (rootOn z hz) (hx z hz))))
  /-- the decoded-side order-0 congruence. -/
  hcong : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
    ((P z : F[X]) : PowerSeries F) - PowerSeries.C ((π_z z (rootOn z hz))
        (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
      ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}

omit [Nonempty ι] [DecidableEq ι] in
/-- The restricted-root analytic datum yields the faithful `CurveFamilyData`. -/
noncomputable def curveFamilyData_of_localSeriesDatumOn {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : LocalSeriesDatumOn (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    CurveFamilyData (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  haveI := d.hIrr
  haveI := d.hPos
  curveFamilyData_of_curveHenselDatum d.hn
    (curveHenselDatum_of_truncatedLocalRoot_genuine_on d.hHyp d.hξ d.hlc d.hR
      d.rootOn d.hx d.hvanish d.htrunc d.hdvd d.hcong)

omit [Nonempty ι] [DecidableEq ι] in
/-- **`StrictCoeffPolysResidual` from a per-`(u, P)` restricted-root analytic producer.**
The issue-#304 strict Johnson extraction core (`ProximityGap.StrictCoeffPolysResidual`,
`Curves.lean`) from a producer of the satisfiable `LocalSeriesDatumOn` — the first front door
to the §5 core whose per-`z` root demands are satisfiable for GS factors that are not
fibrewise totally split. -/
theorem strictCoeffPolysResidual_of_localSeriesDatumOn
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
        LocalSeriesDatumOn (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  exact hcoeffPoly_witness_of_curveFamilyData
    (curveFamilyData_of_localSeriesDatumOn (hInput hk u hprob hJ hsqrt P hP))

omit [Nonempty ι] [DecidableEq ι] in
/-- **`StrictCoeffPolysLargeResidual` from a per-`(u, P)` restricted-root analytic producer.**
This is the producer-facing form of the #304 residual after
`StrictCoeffLargeReduction.lean` removes the small-good-set sector: the analytic producer may
assume the actual remaining hypothesis `k + 1 < |RS_goodCoeffsCurve|` directly. -/
theorem strictCoeffPolysLargeResidual_of_localSeriesDatumOn
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      k + 1 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        LocalSeriesDatumOn (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    StrictCoeffPolysLargeResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt hcard P hP
  exact hcoeffPoly_witness_of_curveFamilyData
    (curveFamilyData_of_localSeriesDatumOn (hInput hk u hprob hJ hsqrt hcard P hP))

omit [DecidableEq ι] in
/-- **Strict square-root-radius keystone front door from the restricted-root analytic
producer.**  The §5 keystone goal `δ_ε_correlatedAgreementCurves` in the strict Johnson
regime, from per-`(u, P)` restricted-root analytic data — every hypothesis an honest,
*satisfiable* BCIKS20 §5/§6.2 obligation. -/
theorem correlatedAgreement_affine_curves_johnson_of_localSeriesDatumOn_strict
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
        LocalSeriesDatumOn (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_strict_coeff_polys
    (k := k) (deg := deg) (domain := domain) (δ := δ) hδ
    (fun hk u hprob hJ P hP =>
      hcoeffPoly_witness_of_curveFamilyData
        (curveFamilyData_of_localSeriesDatumOn (hInput hk u hprob hJ hδ P hP)))

/-- **The graded-discriminant capstone at restricted roots.**  `LocalSeriesDatumOn` from the
restricted §6 matching geometry and the graded weight collapse: the `hvanish` field is
**derived** — on `[n, T]` from the restricted per-point matching data (`mpFin_of_localSeries_on`,
factor-level GS cargo only) and the discriminant-fed graded cardinality family
(`gradedConcreteFin_of_disc` ∘ `hcardFin_of_graded_signed`, whose App-A.4 weight budgets are
proven theorems), beyond `T` from the algebraic-degree datum.  Remaining per-`(u, P)` inputs are
exactly the honest BCIKS20 obligations: the per-`z` base-rational reading `htrunc` (§5
Claim 5.9 / Prop 5.5), the decoded-side GS cargo (`hdvdP`/`hcongP`), the matching-side GS cargo
(`hdvd'`/`hcong'`/`hwindow`), the §6 discriminant (`hdisc`/`hcover`/`hbig`), the paper grading
(`hRgrade` etc.), and the tail-degree datum `htailDeg`. -/
noncomputable def localSeriesDatumOn_of_matching_gradedDisc
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {H : F[X][Y]} [hIrr : Fact (Irreducible H)] [hPos : Fact (0 < H.natDegree)]
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hmonic : H.Monic) (hRsep : R.Separable)
    {n : ℕ} (hn : n < k + 2) (c : ℕ → F[X])
    (rootOn : (z : F) → z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ →
      rationalRoot (H_tilde' H) z)
    (hx : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (π_z z (rootOn z hz)) (ξ x₀ R H hHyp) ≠ 0)
    (htrunc : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (PowerSeries.trunc n (localSeries hHyp z (rootOn z hz) (hx z hz)) : Polynomial F)
        = ∑ t ∈ Finset.range n, (z - x₀) ^ t • c t)
    (hdvdP : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (Polynomial.X - Polynomial.C ((P z : F[X]) : PowerSeries F)) ∣
        ((R.map (coeffHom_loc x₀ hHyp)).map
          (PowerSeries.map (π_hat_z hHyp z (rootOn z hz) (hx z hz)))))
    (hcongP : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      ((P z : F[X]) : PowerSeries F) - PowerSeries.C ((π_z z (rootOn z hz))
          (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    {matchingSet : Finset F}
    {rootOn' : ∀ z ∈ matchingSet, rationalRoot (H_tilde' H) z}
    (hx' : ∀ z (hz : z ∈ matchingSet), (π_z z (rootOn' z hz)) (ξ x₀ R H hHyp) ≠ 0)
    (T : ℕ) (aP : F → PowerSeries F)
    (hdvd' : ∀ z (hz : z ∈ matchingSet),
      (Polynomial.X - Polynomial.C (aP z)) ∣
        ((R.map (coeffHom_loc x₀ hHyp)).map
          (PowerSeries.map (π_hat_z hHyp z (rootOn' z hz) (hx' z hz)))))
    (hcong' : ∀ z (hz : z ∈ matchingSet),
      aP z - PowerSeries.C ((π_z z (rootOn' z hz))
          (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hwindow : ∀ t, n ≤ t → t ≤ T → ∀ z ∈ matchingSet, PowerSeries.coeff t (aP z) = 0)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree T + disc.natDegree
      < Fintype.card F)
    (htailDeg : ∀ t, T < t → αGenuine H x₀ R hHyp t = 0) :
    LocalSeriesDatumOn (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  { x₀ := x₀, R := R, H := H, hIrr := hIrr, hPos := hPos, hHyp := hHyp, hξ := hξ,
    hlc := hmonic.leadingCoeff, hR := hRsep, n := n, hn := hn, c := c,
    rootOn := rootOn, hx := hx,
    hvanish :=
      αGenuine_tail_zero_of_range_and_degree
        (αGenuine_eq_zero_on_range_of_matching_monic_on x₀ R hHyp hmonic.leadingCoeff
          hPos.out D hD n T
          (mpFin_of_localSeries_on hHyp hξ hmonic.leadingCoeff hRsep hx' aP n T hdvd'
            hcong' hwindow)
          (GenuineMonicCapstone.hcardFin_of_graded_signed x₀ R H hHyp hD hPos.out hmonic
            hd2 hdHD hD_Rx0 hRgrade
            (gradedConcreteFin_of_disc (k := n) (T := T) hdisc hcover hbig)))
        htailDeg,
    htrunc := htrunc, hdvd := hdvdP, hcong := hcongP }

/-- **The Claim-5.8′ capstone at restricted roots.**  `LocalSeriesDatumOn` with the `hvanish`
field discharged from the single recognized §5 largeness hypothesis `SβLargeAt` (the
`(5.13)`/`(5.14)` bound, whose production IS the §6 counting), through the unconditional monic
Claim 5.8 (`claim58prime_genuine_tail_of_monic` ∘ `restrictedFaaDiBrunoMatch_of_monic`).
Alternative to `localSeriesDatumOn_of_matching_gradedDisc`: one hypothesis replaces the
matching-geometry + discriminant + tail-degree block. -/
noncomputable def localSeriesDatumOn_of_SβLarge
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {H : F[X][Y]} [hIrr : Fact (Irreducible H)] [hPos : Fact (0 < H.natDegree)]
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hmonic : H.Monic) (hRsep : R.Separable)
    {n : ℕ} (hn : n < k + 2) (c : ℕ → F[X])
    (hlarge : ∀ t ≥ n, BCIKS20.HenselNumerator.S5Genuine.SβLargeAt H x₀ R hHyp t)
    (rootOn : (z : F) → z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ →
      rationalRoot (H_tilde' H) z)
    (hx : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (π_z z (rootOn z hz)) (ξ x₀ R H hHyp) ≠ 0)
    (htrunc : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (PowerSeries.trunc n (localSeries hHyp z (rootOn z hz) (hx z hz)) : Polynomial F)
        = ∑ t ∈ Finset.range n, (z - x₀) ^ t • c t)
    (hdvdP : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (Polynomial.X - Polynomial.C ((P z : F[X]) : PowerSeries F)) ∣
        ((R.map (coeffHom_loc x₀ hHyp)).map
          (PowerSeries.map (π_hat_z hHyp z (rootOn z hz) (hx z hz)))))
    (hcongP : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      ((P z : F[X]) : PowerSeries F) - PowerSeries.C ((π_z z (rootOn z hz))
          (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}) :
    LocalSeriesDatumOn (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  { x₀ := x₀, R := R, H := H, hIrr := hIrr, hPos := hPos, hHyp := hHyp, hξ := hξ,
    hlc := hmonic.leadingCoeff, hR := hRsep, n := n, hn := hn, c := c,
    rootOn := rootOn, hx := hx,
    hvanish := fun t ht =>
      BCIKS20.HenselNumerator.S5Genuine.claim58prime_genuine_tail_of_monic H hHyp
        hmonic.leadingCoeff hlarge t ht,
    htrunc := htrunc, hdvd := hdvdP, hcong := hcongP }

end Weld

end FaithfulCurveExtraction

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.HcardDischarge.tail_zero_on_finite_range_on
#print axioms ArkLib.HcardDischarge.tail_zero_of_finite_card_and_degree_on
#print axioms ArkLib.FaithfulCurveExtraction.αGenuine_eq_zero_on_range_of_matching_monic_on
#print axioms ArkLib.FaithfulCurveExtraction.αGenuine_tail_zero_of_range_and_degree
#print axioms ArkLib.FaithfulCurveExtraction.mpFin_of_localSeries_on
#print axioms ArkLib.FaithfulCurveExtraction.curveHenselDatum_of_truncatedLocalRoot_on
#print axioms ArkLib.FaithfulCurveExtraction.curveHenselDatum_of_truncatedLocalRoot_genuine_on
#print axioms ArkLib.FaithfulCurveExtraction.curveFamilyData_of_truncatedLocalRoot_on
#print axioms ArkLib.FaithfulCurveExtraction.LocalSeriesDatumOn
#print axioms ArkLib.FaithfulCurveExtraction.curveFamilyData_of_localSeriesDatumOn
#print axioms ArkLib.FaithfulCurveExtraction.strictCoeffPolysResidual_of_localSeriesDatumOn
#print axioms ArkLib.FaithfulCurveExtraction.strictCoeffPolysLargeResidual_of_localSeriesDatumOn
#print axioms ArkLib.FaithfulCurveExtraction.correlatedAgreement_affine_curves_johnson_of_localSeriesDatumOn_strict
#print axioms ArkLib.FaithfulCurveExtraction.localSeriesDatumOn_of_matching_gradedDisc
#print axioms ArkLib.FaithfulCurveExtraction.localSeriesDatumOn_of_SβLarge
