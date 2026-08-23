/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Supply
import ArkLib.ToMathlib.DecodedProximateRoot

/-!
# The agreement supply — per-place Hensel uniqueness reads the decoded surface (#302 hlin)

The LAST per-place input of the hlin weld (`Claim510Supply.natDegree_eq_one_of_heavy_agreement`)
was the **agreement** `∑_t π_z (aPre t)·e^t = u₀ + z·u₁`.  This file produces it from the
decoded GS surface data, closing the per-place side of the chain:

* `localSeries_eq_aPDecoded` — **per-place Hensel uniqueness** (the App-A §5.2.6
  `π_z(γ) = P_z`): the canonical local Hensel series at the place equals the decoded
  proximate root, via `specialization_eq_proximate_root_of_hensel` applied to the proven
  `placeGeometry_of_localSeries` (whose `aβ`-side facts — root, congruence, simple-root
  derivative — are all discharged in-tree).

* `pi_z_aPre_eq_taylor_coeff` — the coefficient reading: `π_z (aPre t)` equals the `t`-th
  Taylor coefficient of the decoded surface at the centre, read at the place (cancel the
  nonvanishing `ξ_z`-power against `coeff_localSeries_mul` + the automatic pinning).

* `aPre_sum_eq_surface_eval` — the **value reading**: the weld's coefficient sum at the node
  `e = ω − x₀` equals the surface value `w(ω)(z)` (Taylor evaluation,
  `Polynomial.taylor_eval`).

* `agreement_of_decoded` — the weld's `hagree` input, given the per-place proximity
  agreement `w(ω)(z) = u₀ + z·u₁` (the fold-decoding data of the §5 setup).

Together with `Claim510Supply` and the weld, **hlin for monic branches now rests on**: the
GS surface data (`(Y′−C w) ∣ R`, base-point roots, `R.Separable`, `ξ_z ≠ 0` — all S4/S10
outputs), the coefficient tail (in-tree truncation capstones), the proximity agreement at
heavy coordinates, and the heavy cardinality.

## References

* [BCIKS20] ePrint 2020/654 — §5.2.6–5.2.7, Appendix A.
* [Hab25] ePrint 2025/2110 — Claim 1.
-/

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open BCIKS20.Claim510Kill BCIKS20.Claim510Supply
open ArkLib ArkLib.DecodedProximateRoot

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

namespace BCIKS20.Claim510Agreement

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
variable {x₀ : F} {R : F[X][X][Y]}

/-- **Per-place Hensel uniqueness (App-A §5.2.6, `π_z(γ) = P_z`).**  The canonical local
Hensel series equals the decoded proximate root: both root the specialized matching
polynomial, share the order-0 approximation, and the root is simple. -/
theorem localSeries_eq_aPDecoded (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    {w : F[X][Y]}
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbase : (w.eval (Polynomial.C x₀)).eval z = root.1)
    (hR : R.Separable) :
    localSeries hHyp z root hx = aPDecoded hHyp z root hx w := by
  set g := placeGeometry_of_localSeries hHyp hξ hlc z root hx
    (aPDecoded hHyp z root hx w)
    (Polynomial.dvd_iff_isRoot.mp (aPDecoded_dvd hHyp z root hx hdvd))
    (aPDecoded_cong hHyp z root hx hbase)
    (specialized_separable_of_R_separable hHyp z root hx hR) with hg
  exact ArkLib.IngredientC.specialization_eq_proximate_root_of_hensel
    g.f g.haβ_root g.haP_root g.haβ_cong g.haP_cong g.hderiv

/-- **The coefficient reading**: `π_z (aPre t)` is the `t`-th Taylor coefficient of the
decoded surface at the centre, read at the place. -/
theorem pi_z_aPre_eq_taylor_coeff (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    {w : F[X][Y]}
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbase : (w.eval (Polynomial.C x₀)).eval z = root.1)
    (hR : R.Separable) (t : ℕ) :
    π_z z root (aPre H x₀ R hHyp hlc t)
      = ((Polynomial.taylor (Polynomial.C x₀) w).coeff t).eval z := by
  have hcoeff : PowerSeries.coeff t (localSeries hHyp z root hx)
        * ((π_z z root) (ξ x₀ R H hHyp)) ^ (2 * t - 1)
      = (π_z z root) (βHensel H x₀ R hHyp t) :=
    coeff_localSeries_mul hHyp z root hx t
  rw [pi_z_pinning_of_monic H x₀ R hHyp hlc z root t] at hcoeff
  have hpow : ((π_z z root) (ξ x₀ R H hHyp)) ^ (2 * t - 1) ≠ 0 := pow_ne_zero _ hx
  have hread : PowerSeries.coeff t (localSeries hHyp z root hx)
      = π_z z root (aPre H x₀ R hHyp hlc t) := mul_right_cancel₀ hpow hcoeff
  rw [← hread, localSeries_eq_aPDecoded hHyp hξ hlc z root hx hdvd hbase hR,
    coeff_aPDecoded]

/-- **The value reading**: the weld's coefficient sum at the node `e = ω − x₀` equals the
surface value `w(ω)(z)`, provided the summation range covers the surface degree. -/
theorem aPre_sum_eq_surface_eval (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    {w : F[X][Y]}
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbase : (w.eval (Polynomial.C x₀)).eval z = root.1)
    (hR : R.Separable) {n : ℕ} (hn : w.natDegree < n) (ω : F) :
    (∑ t ∈ Finset.range n,
        π_z z root (aPre H x₀ R hHyp hlc t) * (ω - x₀) ^ t)
      = (w.eval (Polynomial.C ω)).eval z := by
  have hcoeffs : ∀ t, π_z z root (aPre H x₀ R hHyp hlc t)
      = ((Polynomial.taylor (Polynomial.C x₀) w).coeff t).eval z :=
    pi_z_aPre_eq_taylor_coeff hHyp hξ hlc z root hx hdvd hbase hR
  rw [Finset.sum_congr rfl fun t _ => by rw [hcoeffs t]]
  -- `∑_{t<n} (T.coeff t).eval z · (ω−x₀)^t = (T.eval (C (ω−x₀))).eval z` for `T` of
  -- `natDegree < n`, then `taylor_eval` recentres.
  set T : F[X][Y] := Polynomial.taylor (Polynomial.C x₀) w with hT
  have hTdeg : T.natDegree < n := by
    rw [hT, Polynomial.natDegree_taylor]
    exact hn
  have heval : T.eval (Polynomial.C (ω - x₀))
      = ∑ t ∈ Finset.range n, T.coeff t * (Polynomial.C (ω - x₀)) ^ t :=
    Polynomial.eval_eq_sum_range' hTdeg _
  have hz : (T.eval (Polynomial.C (ω - x₀))).eval z
      = ∑ t ∈ Finset.range n, (T.coeff t).eval z * (ω - x₀) ^ t := by
    rw [heval]
    rw [Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]
  rw [← hz, hT, Polynomial.taylor_eval]
  congr 2
  rw [← Polynomial.C_add]
  congr 1
  ring

/-- **The weld's `hagree` input, produced**: at every place of the matching set carrying the
decoded surface data and the proximity agreement `w(ω)(z) = u₀ + z·u₁`, the weld's
agreement hypothesis holds. -/
theorem agreement_of_decoded (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {w : F[X][Y]} {n : ℕ} (hn : w.natDegree < n)
    {matchingSet : Finset F}
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ matchingSet, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbase : ∀ z ∈ matchingSet, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hR : R.Separable)
    (ω : F) (a b : F)
    (hprox : ∀ z ∈ matchingSet, (w.eval (Polynomial.C ω)).eval z = a + z * b) :
    ∀ z ∈ matchingSet, ∃ r : rationalRoot (H_tilde' H) z,
      (∑ t ∈ Finset.range n,
        π_z z r (aPre H x₀ R hHyp hlc t) * (ω - x₀) ^ t) = a + z * b := by
  intro z hz
  refine ⟨root z, ?_⟩
  rw [aPre_sum_eq_surface_eval hHyp hξ hlc z (root z) (hx z hz) hdvd (hbase z hz) hR hn ω]
  exact hprox z hz

end BCIKS20.Claim510Agreement

/-! ## Axiom audit -/
#print axioms BCIKS20.Claim510Agreement.localSeries_eq_aPDecoded
#print axioms BCIKS20.Claim510Agreement.pi_z_aPre_eq_taylor_coeff
#print axioms BCIKS20.Claim510Agreement.aPre_sum_eq_surface_eval
#print axioms BCIKS20.Claim510Agreement.agreement_of_decoded
