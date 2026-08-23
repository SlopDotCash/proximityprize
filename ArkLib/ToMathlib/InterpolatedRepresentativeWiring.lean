/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.InterpolatedRepresentative
import ArkLib.ToMathlib.SignedGradedSupply
import ArkLib.ToMathlib.GenuineMonicCapstone
import ArkLib.ToMathlib.BetaWeightGradedSupply
import ArkLib.ToMathlib.GSSurfaceTailSupply
import ArkLib.ToMathlib.GSSurfaceHtailPigeonhole
import ArkLib.ToMathlib.PerZProximateRoot
import ArkLib.ToMathlib.PlaceSeriesCanonical
import ArkLib.ToMathlib.MatchingPointFromLocalSeries

/-!
# Issue #304 — wiring the matching lane into the interpolated-representative capstones

`InterpolatedRepresentative.lean` ends in the capstones `hrep_of_cleared_counting` /
`interpolatedRep_hrep_hdegX` / `exists_representative_pair`, whose residual hypotheses are
`hw` (a uniform loose weight budget for the differences `betaRec t − clearedCoeff c t`),
`hcard` (the §6 counting-set largeness `B · d_H < #T`), `hvan` (the per-`(t,z)`
place-evaluation equality — the matching-lane currency), and `htailα` (the `αFromBeta` tail
vanishing).  This file discharges each from in-tree theorems.

## What this file proves

* **Brick W (the `hw` budget, concrete).**  `clearedPairBudget` is the explicit formula
  `max (α(2k−1) + A) (nc + k(D−d_H) + (2k−1)·(d−1)A)` with `A = D − d_H + 1`,
  `α = d·A + D + A`, `d = natDegreeY R`; `hw_of_graded_bounds` proves the capstones' `hw`
  hypothesis at `B := clearedPairBudget` from ANY graded `betaRec` collapse, and
  `hw_of_graded` / `hw_of_graded_signed` instantiate it at the proven collapses
  (`betaRec_weight_le_graded` for the canonical family, `betaRec_weight_le_graded_signed`
  for the signed family).  `natDegree_coeff_linearShape_le_one` supplies the coefficient
  budget `nc := 1` for any `X`-affine representative.
* **Brick T (the `htailα` bridges).**  `htailα_sectionH_of_window` /
  `htailα_sectionH_of_pigeonhole` restate the proven section-divisor tail producers
  (`GSSurfaceTailSupply`, `GSSurfaceHtailPigeonhole`) in the capstones' exact
  `∀ t, s.card ≤ t → αFromBeta … = 0` shape.
* **Brick C (the `hcard` bridge).**  `hcard_of_disc` converts the §6 discriminant counting
  (`Match304.card_matching_gt_of_disc`) into the capstones' exact `B · d_H < #T` shape;
  `hcard_clearedPairBudget_of_disc` instantiates it at the Brick-W budget.
* **Brick V (the `hvan` conversion — the matching-lane weld).**  The lane's per-`z` currency
  is the localized Hensel root `localSeries` (the step-5 `π̂_z`-image of `assembledLoc`) with
  its root fact and the multiplied-out L12 read-off (`coeff_localSeries_mul`).
  - `localSeries_eq_aPTaylor`: per-`z` Hensel uniqueness — from the per-`z` matching
    divisibility, the decoded branch value, `ξ`-nonvanishing, separability, and monicity, the
    local series **equals** the decoded Taylor series `aPTaylor x₀ P`.  (This is the `t < k`
    refinement of the in-tree `MatchingPoint` route, which only consumed the `t ≥ k` corollary.)
  - `hvan_signed_of_match`: the division-clearing step — the Hensel match plus a coefficient
    read-off `taylor x₀ P |_t = c.eval z` yields the capstones' `hvan` equality
    `π_z(betaRec t) = π_z(clearedCoeff c t)` (signed family, monic `H`).
  - `coeff_eval_linearShape_taylor`: for the §6.2 **line** representative
    `linearShape (taylor x₀ u₀) (taylor x₀ u₁)` and the decoded line word `P_z = u₀ + z•u₁`,
    the read-off is **proven** (linearity of `taylor` and `coeff`), not hypothesized.
  - `hvan_line_of_perz_data`: the assembled `hvan` producer — per-`z` matching data for the
    line word implies the capstones' `hvan` for the line representative, at every `t`.
* **The apex.**  `hrep_line_of_perz_data` / `exists_representative_pair_line_of_perz_data`:
  for monic `H`, the line representative built from the decoded line words satisfies the
  bundle pair `(hrep, hdegX)` from: per-`z` matching data (divisibility + branch values +
  `ξ`-nonvanishing + separability) + the graded weight hypotheses + the single counting input
  `clearedPairBudget · d_H < #T` + the tail input `htailα` (discharged at the section divisor
  by Brick T).  No sharp Claim-5.9 budget anywhere; `hvan`, `hw`, `hcard`, `htailP` all
  discharged.

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5, §6.2, Appendix A.1–A.4.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 Ideal

namespace ArkLib

namespace InterpolatedRepresentativeWiring

open InterpolatedRepresentative

variable {F : Type} [Field F]

/-! ## Brick W — the concrete `hw` budget from the graded collapse -/

section WeightBudget

/-- **The concrete `hw` budget.**  The uniform (over `t < k`) loose weight budget for the
differences `betaRec t − clearedCoeff c t`, at coefficient degree budget `nc`:
`max` of the graded `betaRec` budget at the top index and the cleared-competitor budget at the
top index (`A = D − d_H + 1`, `α = dY·A + D + A`, `bξ = (dY−1)·A`). -/
def clearedPairBudget (dY D dH nc k : ℕ) : ℕ :=
  max ((dY * (D - dH + 1) + D + (D - dH + 1)) * (2 * k - 1) + (D - dH + 1))
      (nc + ((k * (D - dH)) + (2 * k - 1) * ((dY - 1) * (D - dH + 1))))

/-- **Brick W (core).**  ANY graded `betaRec` collapse (the exact slack-budget shape of
`betaRec_weight_le_graded`/`_signed`/`_of_budget`) plus the proven `ξ`-budget yields the
capstones' `hw` hypothesis at the explicit uniform budget `clearedPairBudget`, for any
coefficient family `c` with degrees bounded by `nc`. -/
theorem hw_of_graded_bounds (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hβw : ∀ t : ℕ, weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff t) D
      ≤ (WithBot.some ((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D
            + (D - H.natDegree + 1)) * (2 * t - 1)
          + (D - H.natDegree + 1)) : WithBot ℕ))
    (hξw : weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D
      ≤ (WithBot.some ((Bivariate.natDegreeY R - 1) * (D - H.natDegree + 1)) : WithBot ℕ))
    {k nc : ℕ} {c : ℕ → F[X]} (hc : ∀ t, t < k → (c t).natDegree ≤ nc) :
    ∀ t, t < k → weight_Λ_over_𝒪 hH
        (betaRec x₀ R H hHyp Bcoeff t
          - InterpolatedRepresentative.clearedCoeff x₀ R H hHyp (c t) t) D
      ≤ ((clearedPairBudget (Bivariate.natDegreeY R) D H.natDegree nc k : ℕ) : WithBot ℕ) := by
  intro t ht
  refine (InterpolatedRepresentative.weight_betaRec_sub_clearedCoeff_le x₀ R H hHyp Bcoeff
    hD hH (hβw t) hξw (c t)).trans ?_
  have hnat : max ((Bivariate.natDegreeY R * (D - H.natDegree + 1) + D
          + (D - H.natDegree + 1)) * (2 * t - 1) + (D - H.natDegree + 1))
        ((c t).natDegree + ((t + 1) * (D - H.natDegree)
          + henselDenominatorExponent t * ((Bivariate.natDegreeY R - 1) * (D - H.natDegree + 1))))
      ≤ clearedPairBudget (Bivariate.natDegreeY R) D H.natDegree nc k := by
    rw [BetaRecGenuineBridge.henselDenominatorExponent_eq_two_mul_sub_one]
    unfold clearedPairBudget
    have hct := hc t ht
    refine max_le_max ?_ ?_
    · exact Nat.add_le_add_right
        (Nat.mul_le_mul_left _ (by omega : 2 * t - 1 ≤ 2 * k - 1)) _
    · have h1 : (t + 1) * (D - H.natDegree) ≤ k * (D - H.natDegree) :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : (2 * t - 1) * ((Bivariate.natDegreeY R - 1) * (D - H.natDegree + 1))
          ≤ (2 * k - 1) * ((Bivariate.natDegreeY R - 1) * (D - H.natDegree + 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
  exact WithBot.coe_le_coe.mpr hnat

/-- **Brick W at the canonical family.**  The capstones' `hw` hypothesis holds with
`B := clearedPairBudget` for `Bcoeff := B_coeff` (the unsigned canonical Faà-di-Bruno family),
from the proven graded collapse `betaRec_weight_le_graded`. -/
theorem hw_of_graded (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {k nc : ℕ} {c : ℕ → F[X]} (hc : ∀ t, t < k → (c t).natDegree ≤ nc) :
    ∀ t, t < k → weight_Λ_over_𝒪 hH
        (betaRec x₀ R H hHyp (BCIKS20.HenselNumerator.B_coeff H x₀ R) t
          - InterpolatedRepresentative.clearedCoeff x₀ R H hHyp (c t) t) D
      ≤ ((clearedPairBudget (Bivariate.natDegreeY R) D H.natDegree nc k : ℕ) : WithBot ℕ) :=
  hw_of_graded_bounds x₀ R H hHyp _ hD hH
    (betaRec_weight_le_graded x₀ R H hHyp hD hH hmonic hd2 hdHD hD_Rx0 hRgrade)
    (weight_ξ_bound x₀ hH hHyp hd2 hD hD_Rx0) hc

/-- **Brick W at the signed family.**  The capstones' `hw` hypothesis holds with
`B := clearedPairBudget` for `Bcoeff := BcoeffSigned` (the matching-lane family, whose
`betaRec` IS the genuine `βHensel` numerator), from the proven signed graded collapse. -/
theorem hw_of_graded_signed (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {k nc : ℕ} {c : ℕ → F[X]} (hc : ∀ t, t < k → (c t).natDegree ≤ nc) :
    ∀ t, t < k → weight_Λ_over_𝒪 hH
        (betaRec x₀ R H hHyp (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t
          - InterpolatedRepresentative.clearedCoeff x₀ R H hHyp (c t) t) D
      ≤ ((clearedPairBudget (Bivariate.natDegreeY R) D H.natDegree nc k : ℕ) : WithBot ℕ) :=
  hw_of_graded_bounds x₀ R H hHyp _ hD hH
    (GenuineMonicCapstone.betaRec_weight_le_graded_signed x₀ R H hHyp hD hH hmonic hd2
      hdHD hD_Rx0 hRgrade)
    (weight_ξ_bound x₀ hH hHyp hd2 hD hD_Rx0) hc

/-- The coefficient-degree budget `nc := 1` for any `X`-affine (linear-shape) representative:
each `Y`-coefficient `C a + X·C b` has `natDegree ≤ 1`. -/
theorem natDegree_coeff_linearShape_le_one (v₀ v₁ : F[X]) (t : ℕ) :
    ((InterpolatedRepresentative.linearShape v₀ v₁).coeff t).natDegree ≤ 1 := by
  rw [InterpolatedRepresentative.coeff_linearShape]
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
  · simp
  · refine le_trans Polynomial.natDegree_mul_le ?_
    simp

end WeightBudget

/-! ## Brick T — the `htailα` bridges (section divisor) -/

section TailBridges

/-- **Brick T (window form).**  The proven tail-window producer
(`GSSurfaceTailSupply.htail_sectionH_of_window`) in the capstones' exact
`htailα`-at-`s.card` shape. -/
theorem htailα_sectionH_of_window {x₀ : F} {R : F[X][X][Y]} {v : F[X]}
    (hHyp : Hypotheses x₀ R (Polynomial.X - Polynomial.C v))
    {T₀ : ℕ} (hdX : ∀ j, (R.coeff j).natDegree ≤ T₀)
    (hwin : ∀ l, 1 ≤ l → l ≤ T₀ →
      BCIKS20.HenselNumerator.βHensel (Polynomial.X - Polynomial.C v) x₀ R hHyp l = 0)
    {s : Finset F} (hs : s.Nonempty) :
    ∀ t, s.card ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R (Polynomial.X - Polynomial.C v) hHyp
        (BetaRecGenuineBridge.BcoeffSigned (Polynomial.X - Polynomial.C v) x₀ R) t = 0 :=
  GSSurfaceKeystone.htail_sectionH_of_window hHyp hdX hwin hs.card_pos

/-- **Brick T (pigeonhole form).**  The proven pigeonhole-matching tail producer
(`GSSurfaceHtailPigeonhole.htail_sectionH_of_pigeonhole`) in the capstones' exact
`htailα`-at-`s.card` shape. -/
theorem htailα_sectionH_of_pigeonhole [Fintype F] [DecidableEq F]
    {x₀ : F} {R : F[X][X][Y]} {v : F[X]}
    (hHyp : Hypotheses x₀ R (Polynomial.X - Polynomial.C v))
    {D DX : ℕ} {s : Finset F} (hs : s.Nonempty)
    (hD : Bivariate.totalDegree (Polynomial.X - Polynomial.C v : F[X][Y]) ≤ D)
    (hd2 : 2 ≤ Bivariate.natDegreeY R) (hd2' : 2 ≤ R.natDegree)
    (hdHD : (Polynomial.X - Polynomial.C v : F[X][Y]).natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDX : ∀ i, (R.coeff i).natDegree ≤ DX)
    {matchingSet : Finset F} {Pz : F → F[X]}
    (hinc : ∀ z ∈ matchingSet,
      Polynomial.evalEval z ((Pz z).eval x₀) (Polynomial.X - Polynomial.C v) = 0)
    (hdvdM : ∀ z ∈ matchingSet, Polynomial.X - Polynomial.C (Pz z) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hdeg : ∀ z ∈ matchingSet, (Pz z).natDegree < s.card)
    (hR : R.Separable)
    {n : ℕ}
    (hbudget : gradedCardBudget (Bivariate.natDegreeY R) D
        (Polynomial.X - Polynomial.C v : F[X][Y]).natDegree
        (DX + R.natDegree * (s.card - 1)) < n)
    (hcard : n ≤ matchingSet.card) :
    ∀ t, s.card ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R (Polynomial.X - Polynomial.C v) hHyp
        (BetaRecGenuineBridge.BcoeffSigned (Polynomial.X - Polynomial.C v) x₀ R) t = 0 :=
  GSSurfaceKeystone.htail_sectionH_of_pigeonhole hHyp hs.card_pos hD hd2 hd2' hdHD hD_Rx0
    hRgrade hDX hinc hdvdM hdeg hR hbudget hcard

end TailBridges

/-! ## Brick C — the `hcard` bridge from the §6 discriminant counting -/

section CardBridge

variable [Fintype F] [DecidableEq F]

/-- **Brick C.**  The §6 discriminant counting (`Match304.card_matching_gt_of_disc`) in the
capstones' exact `hcard` shape `B · d_H < #T`: a nonzero discriminant whose non-vanishing
locus lies in `T`, with the single field-size bound `B · d_H + deg disc < |F|`. -/
theorem hcard_of_disc {disc : F[X]} (hdisc : disc ≠ 0)
    {T : Finset F} (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ T)
    {B dH : ℕ} (hbig : B * dH + disc.natDegree < Fintype.card F) :
    B * dH < T.card :=
  Match304.card_matching_gt_of_disc hdisc hcover hbig

/-- Brick C at the Brick-W budget: the single field-size bound
`clearedPairBudget · d_H + deg disc < |F|` discharges the capstones' `hcard` at
`B := clearedPairBudget`. -/
theorem hcard_clearedPairBudget_of_disc {disc : F[X]} (hdisc : disc ≠ 0)
    {T : Finset F} (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ T)
    {dY D dH nc k : ℕ}
    (hbig : clearedPairBudget dY D dH nc k * dH + disc.natDegree < Fintype.card F) :
    clearedPairBudget dY D dH nc k * dH < T.card :=
  Match304.card_matching_gt_of_disc hdisc hcover hbig

end CardBridge

/-! ## Brick V — the `hvan` conversion: matching-lane per-`z` data ⟹ the capstones' equality -/

section HvanConversion

variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Per-`z` Hensel uniqueness (the `t < k` refinement of the matching lane).**  From the
per-`z` matching divisibility (the S10-converse output), the decoded branch value at the
incidence root, `ξ`-nonvanishing, separability, and monicity, the localized Hensel root
series **equals** the decoded Taylor series: `localSeries = aPTaylor x₀ P`.  The in-tree
`MatchingPoint` route consumed only the `t ≥ k` corollary (coefficient vanishing); this is
the full series equality, whose `t < k` coefficients carry the `hvan` content. -/
theorem localSeries_eq_aPTaylor {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) {P : F[X]}
    (hdvd : Polynomial.X - Polynomial.C P ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : (P.eval x₀ : F) = root.1)
    (hRsep : R.Separable) :
    localSeries hHyp z root hx = PerZProximateRoot.aPTaylor x₀ P := by
  let g := placeGeometry_of_localSeries hHyp hξ hlc z root hx
    (PerZProximateRoot.aPTaylor x₀ P)
    (Polynomial.dvd_iff_isRoot.mp (PerZProximateRoot.aPTaylor_dvd hHyp z root hx hdvd))
    (PerZProximateRoot.aPTaylor_cong hHyp z root hval)
    (specialized_separable_of_R_separable hHyp z root hx hRsep)
  exact IngredientC.specialization_eq_proximate_root_of_hensel
    g.f g.haβ_root g.haP_root g.haβ_cong g.haP_cong g.hderiv

/-- **The division-clearing step (signed family, monic `H`).**  The per-`z` Hensel match
`localSeries = aPTaylor x₀ P` plus the coefficient read-off `(taylor x₀ P)|_t = c.eval z`
yields the capstones' `hvan` equality `π_z(betaRec t) = π_z(clearedCoeff c t)`.  Routes the
multiplied-out L12 identity (`coeff_localSeries_mul`) through the signed-canonical bridge;
the `W`-reading is `1` by monicity, so no division is ever performed. -/
theorem hvan_signed_of_match {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) {P c : F[X]} {t : ℕ}
    (hmatch : localSeries hHyp z root hx = PerZProximateRoot.aPTaylor x₀ P)
    (hcoeff : (Polynomial.taylor x₀ P).coeff t = c.eval z) :
    (π_z z root) (betaRec x₀ R H hHyp (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t)
      = (π_z z root) (InterpolatedRepresentative.clearedCoeff x₀ R H hHyp c t) := by
  have hread : PowerSeries.coeff t (PerZProximateRoot.aPTaylor x₀ P)
      = (Polynomial.taylor x₀ P).coeff t :=
    PerZProximateRoot.coeff_taylorCoerce x₀ P t
  rw [BetaRecGenuineBridge.betaRec_BcoeffSigned_eq_βHensel,
    ← coeff_localSeries_mul hHyp z root hx t, hmatch, hread, hcoeff,
    InterpolatedRepresentative.pi_z_clearedCoeff,
    PlaceSeriesCanonical.pi_z_W_eq_one_of_monic hlc root, one_pow, one_mul,
    BetaRecGenuineBridge.henselDenominatorExponent_eq_two_mul_sub_one]

/-- **The line read-off (proven, not hypothesized).**  For the §6.2 line representative
`linearShape (taylor x₀ u₀) (taylor x₀ u₁)` and the decoded line word `u₀ + z•u₁`, the
coefficient read-off holds by linearity of `taylor` and `coeff`:
`(Ppoly.coeff t).eval z = (taylor x₀ (u₀ + z•u₁)).coeff t`. -/
theorem coeff_eval_linearShape_taylor (x₀ z : F) (u₀ u₁ : F[X]) (t : ℕ) :
    ((InterpolatedRepresentative.linearShape (Polynomial.taylor x₀ u₀)
        (Polynomial.taylor x₀ u₁)).coeff t).eval z
      = (Polynomial.taylor x₀ (u₀ + z • u₁)).coeff t := by
  rw [InterpolatedRepresentative.coeff_linearShape, map_add, map_smul,
    Polynomial.coeff_add, Polynomial.coeff_smul]
  simp [smul_eq_mul]
  ring

/-- **Brick V (assembled).**  Per-`z` matching data for the decoded line word
`P_z = u₀ + z•u₁` — divisibility, branch value, `ξ`-nonvanishing, separability, monicity —
implies the capstones' `hvan` equality for the **line representative**
`linearShape (taylor x₀ u₀) (taylor x₀ u₁)`, at EVERY index `t` and every `z ∈ T`. -/
theorem hvan_line_of_perz_data {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {u₀ u₁ : F[X]} {T : Finset F}
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ T, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    (hdvd : ∀ z ∈ T, Polynomial.X - Polynomial.C (u₀ + z • u₁) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : ∀ z ∈ T, ((u₀ + z • u₁).eval x₀ : F) = (root z).1)
    (hRsep : R.Separable) :
    ∀ (t : ℕ), ∀ z ∈ T,
      (π_z z (root z)) (betaRec x₀ R H hHyp (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t)
        = (π_z z (root z)) (InterpolatedRepresentative.clearedCoeff x₀ R H hHyp
            ((InterpolatedRepresentative.linearShape (Polynomial.taylor x₀ u₀)
              (Polynomial.taylor x₀ u₁)).coeff t) t) := by
  intro t z hz
  exact hvan_signed_of_match hHyp hlc z (root z) (hx z hz)
    (localSeries_eq_aPTaylor hHyp hξ hlc z (root z) (hx z hz) (hdvd z hz) (hval z hz) hRsep)
    (coeff_eval_linearShape_taylor x₀ z u₀ u₁ t).symm

end HvanConversion

/-! ## The apex — the bundle pair for the line representative, all residuals wired -/

section Apex

variable (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
variable [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The apex weld: `hrep` for the line representative from per-`z` matching data.**
For monic `H`, the §6.2 line representative `linearShape (taylor x₀ u₀) (taylor x₀ u₁)` built
from decoded line words of degree `< k` satisfies the terminal bundle field
`hrep : polyToPowerSeries𝕃 H Ppoly = gammaLocal …` (signed family), from:
* per-`z` matching data on the counting set `T` (Brick V: divisibility + branch values +
  `ξ`-nonvanishing + separability) — discharges `hvan`;
* the graded weight hypotheses (Brick W at `nc := 1`) — discharges `hw`;
* the single counting input `clearedPairBudget · d_H < #T` (supplied by Brick C) — `hcard`;
* the tail input `htailα` (supplied at the section divisor by Brick T);
* `htailP` discharged **by construction** (`coeff_linearShape_eq_zero` + `natDegree_taylor`).

No sharp Claim-5.9 budget anywhere. -/
theorem hrep_line_of_perz_data (hHyp : Hypotheses x₀ R H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {u₀ u₁ : F[X]} {k : ℕ} (h₀ : u₀.natDegree < k) (h₁ : u₁.natDegree < k)
    {T : Finset F} (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ T, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    (hdvd : ∀ z ∈ T, Polynomial.X - Polynomial.C (u₀ + z • u₁) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : ∀ z ∈ T, ((u₀ + z • u₁).eval x₀ : F) = (root z).1)
    (hRsep : R.Separable)
    (hcard : clearedPairBudget (Bivariate.natDegreeY R) D H.natDegree 1 k * H.natDegree
      < T.card)
    (htailα : ∀ t, k ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t = 0) :
    polyToPowerSeries𝕃 H (InterpolatedRepresentative.linearShape
        (Polynomial.taylor x₀ u₀) (Polynomial.taylor x₀ u₁))
      = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp
          (BetaRecGenuineBridge.BcoeffSigned H x₀ R) :=
  InterpolatedRepresentative.hrep_of_cleared_counting x₀ R H hHyp
    (BetaRecGenuineBridge.BcoeffSigned H x₀ R) hH D hD
    (emb_ξ_ne_zero hHyp hξ) root
    (fun t _ z hz =>
      hvan_line_of_perz_data hHyp hξ hmonic.leadingCoeff root hx hdvd hval hRsep t z hz)
    (hw_of_graded_signed x₀ R H hHyp hD hH hmonic hd2 hdHD hD_Rx0 hRgrade
      (fun t _ => natDegree_coeff_linearShape_le_one _ _ t))
    hcard
    (fun t hkt => InterpolatedRepresentative.coeff_linearShape_eq_zero
      (by rw [Polynomial.natDegree_taylor]; exact h₀)
      (by rw [Polynomial.natDegree_taylor]; exact h₁) hkt)
    htailα

/-- **The apex pair (existential form).**  The bundle's terminal per-`P` field pair
`(Ppoly, hrep, hdegX)` (plus the truncation bound `natDegree < k`) **exists** for monic `H`,
produced from the decoded line words and the per-`z` matching data, with `hdegX` and the tail
by construction.  This is the wired, satisfiable replacement for the refuted sharp-Claim-5.9
lane: every capstone residual except `htailα` (Brick T at the section divisor) and the single
counting inequality (Brick C) is fully discharged from in-tree theorems. -/
theorem exists_representative_pair_line_of_perz_data (hHyp : Hypotheses x₀ R H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {u₀ u₁ : F[X]} {k : ℕ} (h₀ : u₀.natDegree < k) (h₁ : u₁.natDegree < k)
    {T : Finset F} (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ T, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    (hdvd : ∀ z ∈ T, Polynomial.X - Polynomial.C (u₀ + z • u₁) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : ∀ z ∈ T, ((u₀ + z • u₁).eval x₀ : F) = (root z).1)
    (hRsep : R.Separable)
    (hcard : clearedPairBudget (Bivariate.natDegreeY R) D H.natDegree 1 k * H.natDegree
      < T.card)
    (htailα : ∀ t, k ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t = 0) :
    ∃ Ppoly : F[X][Y],
      polyToPowerSeries𝕃 H Ppoly
          = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp
              (BetaRecGenuineBridge.BcoeffSigned H x₀ R)
        ∧ Polynomial.Bivariate.degreeX Ppoly ≤ 1
        ∧ Ppoly.natDegree < k :=
  ⟨InterpolatedRepresentative.linearShape (Polynomial.taylor x₀ u₀) (Polynomial.taylor x₀ u₁),
    hrep_line_of_perz_data x₀ R H hHyp hD hH hmonic hd2 hdHD hD_Rx0 hRgrade hξ h₀ h₁
      root hx hdvd hval hRsep hcard htailα,
    InterpolatedRepresentative.degreeX_linearShape_le_one _ _,
    lt_of_le_of_lt (InterpolatedRepresentative.natDegree_linearShape_le _ _)
      (by rw [Polynomial.natDegree_taylor, Polynomial.natDegree_taylor]; exact max_lt h₀ h₁)⟩

end Apex

end InterpolatedRepresentativeWiring

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.InterpolatedRepresentativeWiring.clearedPairBudget
#print axioms ArkLib.InterpolatedRepresentativeWiring.hw_of_graded_bounds
#print axioms ArkLib.InterpolatedRepresentativeWiring.hw_of_graded
#print axioms ArkLib.InterpolatedRepresentativeWiring.hw_of_graded_signed
#print axioms ArkLib.InterpolatedRepresentativeWiring.natDegree_coeff_linearShape_le_one
#print axioms ArkLib.InterpolatedRepresentativeWiring.htailα_sectionH_of_window
#print axioms ArkLib.InterpolatedRepresentativeWiring.htailα_sectionH_of_pigeonhole
#print axioms ArkLib.InterpolatedRepresentativeWiring.hcard_of_disc
#print axioms ArkLib.InterpolatedRepresentativeWiring.hcard_clearedPairBudget_of_disc
#print axioms ArkLib.InterpolatedRepresentativeWiring.localSeries_eq_aPTaylor
#print axioms ArkLib.InterpolatedRepresentativeWiring.hvan_signed_of_match
#print axioms ArkLib.InterpolatedRepresentativeWiring.coeff_eval_linearShape_taylor
#print axioms ArkLib.InterpolatedRepresentativeWiring.hvan_line_of_perz_data
#print axioms ArkLib.InterpolatedRepresentativeWiring.hrep_line_of_perz_data
#print axioms ArkLib.InterpolatedRepresentativeWiring.exists_representative_pair_line_of_perz_data
