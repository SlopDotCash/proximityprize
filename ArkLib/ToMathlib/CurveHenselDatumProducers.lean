/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.CurveFamilyGenuine
import ArkLib.ToMathlib.TruncatedLocalRoot
import ArkLib.ToMathlib.MatchingFactorLift

/-!
# Issue #304 — per-`z` root-geometry producers of the faithful `CurveHenselDatum`

`CurveFamilyHensel.CurveHenselDatum` is the per-`(u, P)` bundle of per-`z` Hensel root data on
the faithful curve surface: a matching polynomial `f z` over `F⟦X⟧`, a common approximation
`a₀ z`, root facts for the decoded `P z` AND for the curve specialization
`∑_{t<n} (z − x₀)^t • c_t`, the two mod-`X` congruences, and the unit derivative.  Its consumers
(`curveFamilyData_of_curveHenselDatum` → `δ_ε_correlatedAgreementCurves`) are already in-tree.
This file produces the datum's fields from in-tree GS machinery, in two lanes:

## Lane 1 — generic per-`z` bricks (the GS-interpolant coefficient ring)

* `isRoot_coe_of_matchesGraph` — **the `hProot`/`hQroot`-class fact from the GS divisibility
  route**: if `g` is a GS matching polynomial of the interpolant `Qz : F[X][Y]`
  (`MatchesGraph Qz g`, i.e. `Qz.eval g = 0`, equivalently `Y − C g ∣ Qz` — the exact output of
  `MatchingExtractor.matchingFactor_dvd_of_orderM_and_count`), then the coerced `↑g` is a root
  of the coerced interpolant over `F⟦X⟧`.
* `isRoot_coe_of_orderM_and_count` — the end-to-end form: GS order-`m` graph vanishing + the
  Johnson count ⟹ the power-series root fact, in one step.
* `coe_sub_C_mem_span_X_iff` / `coe_sub_C_coeff_zero_mem_span_X` — **the congruence fields are
  mechanical**: `↑p − C a ∈ (X)` iff `p.coeff 0 = a`; in particular the constant-coefficient
  choice `a₀ := C (p.coeff 0)` always works, and two polynomials share an approximation iff
  their constant terms agree.

## Lane 2 — the assembled producers

* `curveHenselDatum_of_matchesGraph` — **the GS-interpolant producer**: per good `z`, a
  *separable* interpolant `Q z : F[X][Y]` matching BOTH the decoded `P z` and the curve
  specialization (two `MatchesGraph` facts — the GS factorization cargo), plus equality of the
  two constant terms.  All seven `CurveHenselDatum` fields are discharged
  (`f z := (Q z).map coeToPowerSeries`, `a₀ z := C ((P z).coeff 0)`; the unit derivative comes
  from separability via `curveHenselDatum_of_separable`).
* `curveHenselDatum_of_orderM_and_count` — the same from raw GS multiplicity data: order-`m`
  vanishing of `Q z` on the graphs of both competitors over their agreement sets, under the
  Johnson counts.
* `curveHenselDatum_of_truncatedLocalRoot` — **the analytic producer at the constructed local
  series** (the `TruncatedLocalRoot` adapter): for the specialized matching polynomial
  `f z := (R.map coeffHom_loc).map (π̂_z)`, the curve-side root fact `hQroot` is DERIVED from
  `trunc_localSeries_isRoot_of_alphaFromBeta_vanishing` (tail vanishing of `αFromBeta` makes
  `localSeries` equal its truncation, which IS the curve specialization by the base-rational
  reading `htrunc`); the curve-side congruence `hQapprox` is DERIVED from
  `constantCoeff_localSeries` (no extra input); the decoded-side facts arrive in the exact
  `mpFin_of_localSeries` GS-cargo shapes (`hdvd`, order-0 congruence `hcong`); the unit
  derivative from `R.Separable`.
* `curveFamilyData_of_*` — the compositions into the faithful `CurveFamilyData` (whose in-tree
  consumers reach the §5 keystone `δ_ε_correlatedAgreementCurves`).

## The honest remaining inputs after this file

For lane 2's analytic producer: the per-`z` base-rational reading `htrunc` (the §5
rational-section content: the truncated local series IS the curve specialization — supplied by
the `gammaGenuine` base-rationality lane), the tail vanishing `hvanish` (supplied on `[k, T]` by
`αGenuine_eq_zero_on_range_of_matching_monic` and beyond `T` by the algebraic-degree lane), and
the decoded-side GS cargo (`hdvd`/`hcong` — the matching-factor divisibility at the decoded
polynomial, `MatchingFactorLift`).  For the GS-interpolant producer: separability of the
interpolant and the matching facts for the two competitors.  None of these is the keystone goal;
each is a recognized BCIKS20 §5/§6.2 ingredient with its own production lane.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (Prop. 5.5, the GS matching factor), §6.2 (Hensel uniqueness `π_z(γ) = P_z`), Appendix A.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open ProximityGap Code NNReal Finset Function
open ProximityPrize.BCIKS20.GammaGenuine BCIKS20.HenselNumerator
open scoped BigOperators ENNReal

namespace ArkLib

namespace FaithfulCurveExtraction

/-! ## Lane 1 — generic per-`z` root and congruence bricks -/

section Bricks

variable {F : Type} [Field F]

/-- **The `hProot`/`hQroot`-class root fact from the GS divisibility route.**  If `g` is a GS
matching polynomial of the interpolant `Qz : F[X][Y]` (`MatchesGraph Qz g`, i.e.
`Qz.eval g = 0`), then the coerced `↑g : F⟦X⟧` is a root of the coerced interpolant
`Qz.map coeToPowerSeries.ringHom : (F⟦X⟧)[Y]` — the exact root-field shape of
`CurveHenselDatum` at the interpolant-coercion matching polynomial. -/
theorem isRoot_coe_of_matchesGraph {Qz : F[X][Y]} {g : F[X]}
    (h : MatchingExtractor.MatchesGraph Qz g) :
    (Qz.map Polynomial.coeToPowerSeries.ringHom).IsRoot ((g : F[X]) : PowerSeries F) :=
  Polynomial.dvd_iff_isRoot.mp
    (MatchingFactorLift.matchingFactor_dvd_powerSeries_of_dvd
      ((MatchingExtractor.matchesGraph_iff_dvd Qz g).mp h))

/-- **End-to-end GS form of the root fact.**  From Guruswami–Sudan order-`m` vanishing of the
interpolant `Qz` on the graph of `g` over an agreement set `A`, under the Johnson count, the
coerced `↑g` is a root of the coerced interpolant over `F⟦X⟧`.  This is the full
multiplicity ⟹ root ⟹ divisibility ⟹ coefficient-ring-lift chain in one step. -/
theorem isRoot_coe_of_orderM_and_count {N : ℕ} (ωs : Fin N ↪ F) (Qz : F[X][Y]) (g : F[X])
    (m : ℕ) (A : Finset (Fin N))
    (hord : ∀ i ∈ A, GuruswamiSudan.HasOrderAt Qz (ωs i) (g.eval (ωs i)) m)
    (hcount : (Qz.eval g).natDegree < m * A.card) :
    (Qz.map Polynomial.coeToPowerSeries.ringHom).IsRoot ((g : F[X]) : PowerSeries F) :=
  isRoot_coe_of_matchesGraph
    (MatchingExtractor.eval_eq_zero_of_orderM_and_count ωs Qz g m A hord hcount)

/-- **The mod-`X` congruence is a constant-term fact:** `↑p − C a ∈ (X)` iff `p.coeff 0 = a`. -/
theorem coe_sub_C_mem_span_X_iff (p : F[X]) (a : F) :
    ((p : F[X]) : PowerSeries F) - PowerSeries.C a
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}
      ↔ p.coeff 0 = a := by
  rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub, PowerSeries.constantCoeff_C,
    sub_eq_zero, Polynomial.constantCoeff_coe]

/-- **The `hPapprox`-class congruence at the canonical approximation:** every coerced polynomial
reduces mod `X` to (the constant series of) its own constant coefficient. -/
theorem coe_sub_C_coeff_zero_mem_span_X (p : F[X]) :
    ((p : F[X]) : PowerSeries F) - PowerSeries.C (p.coeff 0)
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)} :=
  (coe_sub_C_mem_span_X_iff p (p.coeff 0)).mpr rfl

end Bricks

/-! ## Lane 2a — the GS-interpolant producer -/

section Interpolant

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **`CurveHenselDatum` from per-`z` GS matching data.**  At every good `z`, a *separable*
interpolant `Q z : F[X][Y]` matches BOTH the decoded `P z` and the curve specialization
(`MatchesGraph`, the GS factorization cargo of
`MatchingExtractor.matchingFactor_dvd_of_orderM_and_count`), and the two competitors share their
constant term.  All seven fields of the per-`(u, P)` curve-Hensel bundle are discharged:
`f z` is the coerced interpolant, `a₀ z := C ((P z).coeff 0)`, the roots come from
`isRoot_coe_of_matchesGraph`, the congruences from `coe_sub_C_mem_span_X_iff`, and the unit
derivative from separability via `curveHenselDatum_of_separable`. -/
noncomputable def curveHenselDatum_of_matchesGraph {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} {n : ℕ} {c : ℕ → F[X]}
    (Q : F → F[X][Y])
    (hsep : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Q z).Separable)
    (hP : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      MatchingExtractor.MatchesGraph (Q z) (P z))
    (hC : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      MatchingExtractor.MatchesGraph (Q z) (∑ t ∈ Finset.range n, (z - x₀) ^ t • c t))
    (h0 : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X]).coeff 0 = (P z).coeff 0) :
    CurveHenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P x₀ n c :=
  curveHenselDatum_of_separable
    (fun z => (Q z).map Polynomial.coeToPowerSeries.ringHom)
    (fun z => PowerSeries.C ((P z).coeff 0))
    (fun z hz => isRoot_coe_of_matchesGraph (hP z hz))
    (fun z hz => isRoot_coe_of_matchesGraph (hC z hz))
    (fun z _hz => coe_sub_C_coeff_zero_mem_span_X (P z))
    (fun z hz => (coe_sub_C_mem_span_X_iff _ _).mpr (h0 z hz))
    (fun z hz => (hsep z hz).map)

/-- **`CurveHenselDatum` from raw GS multiplicity data.**  The same producer with the matching
facts discharged from Guruswami–Sudan order-`m` graph vanishing of `Q z` at BOTH competitors
(the decoded `P z` over `AP z`, the curve specialization over `AC z`) under the Johnson
counts — the complete per-`z` root geometry from GS primitives. -/
noncomputable def curveHenselDatum_of_orderM_and_count {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} {n : ℕ} {c : ℕ → F[X]} {N : ℕ} (ωs : Fin N ↪ F)
    (Q : F → F[X][Y]) (m : ℕ) (AP AC : F → Finset (Fin N))
    (hsep : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Q z).Separable)
    (hordP : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ∀ i ∈ AP z, GuruswamiSudan.HasOrderAt (Q z) (ωs i) ((P z).eval (ωs i)) m)
    (hcountP : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ((Q z).eval (P z)).natDegree < m * (AP z).card)
    (hordC : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ∀ i ∈ AC z, GuruswamiSudan.HasOrderAt (Q z) (ωs i)
        ((∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X]).eval (ωs i)) m)
    (hcountC : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ((Q z).eval (∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X])).natDegree
        < m * (AC z).card)
    (h0 : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X]).coeff 0 = (P z).coeff 0) :
    CurveHenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P x₀ n c :=
  curveHenselDatum_of_matchesGraph Q hsep
    (fun z hz => MatchingExtractor.eval_eq_zero_of_orderM_and_count ωs (Q z) (P z) m (AP z)
      (hordP z hz) (hcountP z hz))
    (fun z hz => MatchingExtractor.eval_eq_zero_of_orderM_and_count ωs (Q z) _ m (AC z)
      (hordC z hz) (hcountC z hz))
    h0

/-- The GS-interpolant producer, composed into the faithful `CurveFamilyData`. -/
noncomputable def curveFamilyData_of_matchesGraph {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} {n : ℕ} {c : ℕ → F[X]} (hn : n < k + 2)
    (Q : F → F[X][Y])
    (hsep : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Q z).Separable)
    (hP : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      MatchingExtractor.MatchesGraph (Q z) (P z))
    (hC : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      MatchingExtractor.MatchesGraph (Q z) (∑ t ∈ Finset.range n, (z - x₀) ^ t • c t))
    (h0 : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (∑ t ∈ Finset.range n, (z - x₀) ^ t • c t : F[X]).coeff 0 = (P z).coeff 0) :
    CurveFamilyData (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  curveFamilyData_of_curveHenselDatum hn
    (curveHenselDatum_of_matchesGraph Q hsep hP hC h0)

end Interpolant

/-! ## Lane 2b — the analytic producer at the constructed local series -/

section LocalSeries

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **`CurveHenselDatum` from the constructed local series (the `TruncatedLocalRoot` adapter).**

The per-`z` matching polynomial is the specialized `f z := (R.map coeffHom_loc).map (π̂_z)` and
the approximation is the canonical `a₀ z := C (π_z(βHensel 0))`.  Field discharge:

* `hQroot` (the curve-side root) — DERIVED: `hvanish` (tail vanishing of `αFromBeta` from `n`
  on) makes `localSeries` equal its truncation
  (`trunc_localSeries_isRoot_of_alphaFromBeta_vanishing`), and the base-rational reading
  `htrunc` identifies that truncation with the curve specialization `∑_{t<n} (z − x₀)^t • c_t`.
* `hQapprox` (the curve-side congruence) — DERIVED with **no further input**: the truncation
  equals the local series as a power series, whose constant coefficient is `π_z(βHensel 0)`
  (`constantCoeff_localSeries`).
* `hProot`/`hPapprox` (the decoded side) — the exact `mpFin_of_localSeries` GS-cargo shapes:
  the matching-factor divisibility `hdvd` at `↑(P z)` and the order-0 congruence `hcong`.
* `hderiv` — from one global `R.Separable` via `specialized_separable_of_R_separable`. -/
noncomputable def curveHenselDatum_of_truncatedLocalRoot {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1) (hR : R.Separable)
    {n : ℕ} {c : ℕ → F[X]}
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    (hvanish : ∀ t, n ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t = 0)
    (htrunc : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (PowerSeries.trunc n (localSeries hHyp z (root z) (hx z hz)) : Polynomial F)
        = ∑ t ∈ Finset.range n, (z - x₀) ^ t • c t)
    (hdvd : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (Polynomial.X - Polynomial.C ((P z : F[X]) : PowerSeries F)) ∣
        ((R.map (coeffHom_loc x₀ hHyp)).map
          (PowerSeries.map (π_hat_z hHyp z (root z) (hx z hz)))))
    (hcong : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ((P z : F[X]) : PowerSeries F) - PowerSeries.C ((π_z z (root z))
          (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}) :
    CurveHenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P x₀ n c :=
  curveHenselDatum_of_separable
    (fun z =>
      if hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ then
        (R.map (coeffHom_loc x₀ hHyp)).map
          (PowerSeries.map (π_hat_z hHyp z (root z) (hx z hz)))
      else 0)
    (fun z => PowerSeries.C ((π_z z (root z))
      (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0)))
    (fun z hz => by
      dsimp only
      rw [dif_pos hz]
      exact Polynomial.dvd_iff_isRoot.mp (hdvd z hz))
    (fun z hz => by
      dsimp only
      rw [dif_pos hz, ← htrunc z hz]
      exact trunc_localSeries_isRoot_of_alphaFromBeta_vanishing hHyp hξ hlc z (root z)
        (hx z hz) hvanish)
    (fun z hz => hcong z hz)
    (fun z hz => by
      rw [← htrunc z hz,
        ← powerSeries_eq_coe_trunc_of_tail_zero (fun t ht =>
          coeff_localSeries_eq_zero_of_alphaFromBeta_eq_zero hHyp hξ z (root z) (hx z hz) t
            (hvanish t ht)),
        Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub,
        constantCoeff_localSeries hHyp z (root z) (hx z hz), PowerSeries.constantCoeff_C,
        sub_self])
    (fun z hz => by
      dsimp only
      rw [dif_pos hz]
      exact specialized_separable_of_R_separable hHyp z (root z) (hx z hz) hR)

/-- The analytic producer with the tail vanishing supplied at the **genuine** coefficients
(`αGenuine t = 0` for `t ≥ n` — the form `αGenuine_eq_zero_on_range_of_matching_monic`
produces), transported through the monic `BetaRecGenuineBridge` identification. -/
noncomputable def curveHenselDatum_of_truncatedLocalRoot_genuine {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1) (hR : R.Separable)
    {n : ℕ} {c : ℕ → F[X]}
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    (hvanish : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0)
    (htrunc : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (PowerSeries.trunc n (localSeries hHyp z (root z) (hx z hz)) : Polynomial F)
        = ∑ t ∈ Finset.range n, (z - x₀) ^ t • c t)
    (hdvd : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (Polynomial.X - Polynomial.C ((P z : F[X]) : PowerSeries F)) ∣
        ((R.map (coeffHom_loc x₀ hHyp)).map
          (PowerSeries.map (π_hat_z hHyp z (root z) (hx z hz)))))
    (hcong : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ((P z : F[X]) : PowerSeries F) - PowerSeries.C ((π_z z (root z))
          (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}) :
    CurveHenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P x₀ n c :=
  curveHenselDatum_of_truncatedLocalRoot hHyp hξ hlc hR root hx
    (fun t ht => by
      rw [BetaRecGenuineBridge.alphaFromBeta_BcoeffSigned_eq_αGenuine_of_monic x₀ R hHyp hlc t]
      exact hvanish t ht)
    htrunc hdvd hcong

/-- The analytic producer, composed into the faithful `CurveFamilyData`. -/
noncomputable def curveFamilyData_of_truncatedLocalRoot {k deg : ℕ} {domain : ι ↪ F}
    {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1) (hR : R.Separable)
    {n : ℕ} {c : ℕ → F[X]} (hn : n < k + 2)
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    (hvanish : ∀ t, n ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t = 0)
    (htrunc : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (PowerSeries.trunc n (localSeries hHyp z (root z) (hx z hz)) : Polynomial F)
        = ∑ t ∈ Finset.range n, (z - x₀) ^ t • c t)
    (hdvd : ∀ z (hz : z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ),
      (Polynomial.X - Polynomial.C ((P z : F[X]) : PowerSeries F)) ∣
        ((R.map (coeffHom_loc x₀ hHyp)).map
          (PowerSeries.map (π_hat_z hHyp z (root z) (hx z hz)))))
    (hcong : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ((P z : F[X]) : PowerSeries F) - PowerSeries.C ((π_z z (root z))
          (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}) :
    CurveFamilyData (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  curveFamilyData_of_curveHenselDatum hn
    (curveHenselDatum_of_truncatedLocalRoot hHyp hξ hlc hR root hx hvanish htrunc hdvd hcong)

end LocalSeries

end FaithfulCurveExtraction

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.FaithfulCurveExtraction.isRoot_coe_of_matchesGraph
#print axioms ArkLib.FaithfulCurveExtraction.isRoot_coe_of_orderM_and_count
#print axioms ArkLib.FaithfulCurveExtraction.coe_sub_C_mem_span_X_iff
#print axioms ArkLib.FaithfulCurveExtraction.coe_sub_C_coeff_zero_mem_span_X
#print axioms ArkLib.FaithfulCurveExtraction.curveHenselDatum_of_matchesGraph
#print axioms ArkLib.FaithfulCurveExtraction.curveHenselDatum_of_orderM_and_count
#print axioms ArkLib.FaithfulCurveExtraction.curveFamilyData_of_matchesGraph
#print axioms ArkLib.FaithfulCurveExtraction.curveHenselDatum_of_truncatedLocalRoot
#print axioms ArkLib.FaithfulCurveExtraction.curveHenselDatum_of_truncatedLocalRoot_genuine
#print axioms ArkLib.FaithfulCurveExtraction.curveFamilyData_of_truncatedLocalRoot
