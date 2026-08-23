/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.MatchingPointFromLocalSeries
import ArkLib.ToMathlib.HvanishSupply

/-!
# Issue #304 — the canonical decoded proximate root: `mpFin` from the GS surface factor

`matchingPoint_of_localSeries[_dvd]` fires the per-`(t,z)` `MatchingPoint` from four pieces of
per-place cargo: a proximate root `aP : F⟦X⟧`, its root fact at the place-mapped matching
polynomial, its order-0 congruence with `π_z(βHensel 0)`, and the index-`t` coefficient
vanishing.  This file supplies the **canonical** `aP` and derives all four facts from honest
§5 inputs:

* `aPDecoded w := PowerSeries.map π̂_z (coeffHom_loc x₀ w)` — the place image of the Prop-5.5
  decoded surface `w : F[X][Y]` (Taylor-recentred at the §5 centre `x₀`, coefficients read at
  the place `(z, t_z)`).
* `coeff_aPDecoded` — the coefficient formula: `coeff n (aPDecoded w) = ((taylor (C x₀) w).coeff
  n).eval z`.  Consequences: the constant coefficient is the **base-point value**
  `(w.eval (C x₀)).eval z` (`constantCoeff_aPDecoded`), and all coefficients above
  `w.natDegree` vanish (`coeff_aPDecoded_eq_zero` — the Prop-5.5 degree-`< k` truncation read at
  the place).
* `pi_z_βHensel_zero` — `π_z(βHensel 0) = t_z` (the recursion base reads off the branch value).
* `aPDecoded_dvd` — the matching-factor transport: the **global** GS surface divisibility
  `(Y′ − C w) ∣ R` maps through `coeffHom_loc` and `π̂_z` to the per-place divisibility
  `(Y′ − C (aPDecoded w)) ∣ f_z`.
* `matchingPoint_of_decoded` — the per-`(t,z)` `MatchingPoint` at the signed canonical
  coefficients from: the surface divisibility, the base-point fact
  `(w.eval (C x₀)).eval z = t_z`, the Prop-5.5 degree bound `w.natDegree < k`, and
  `R.Separable` — plus the standing nonvanishing `hξ`/`hx` and monicity.
* `mpFin_of_decoded` — the finite-range family in the exact `mpFin`/`mpPoint` shape of the
  §5 bundles (`Section5StrictDataOffcentreFin.mpFin`, `KeystoneAssembly`'s `mpPoint`, and
  `HvanishSupply.hvanish_of_mpPoint`'s input).
* `hvanish_of_decoded` / `gammaGenuine_eq_trunc_of_decoded` — the composed capstones: the
  `SβLargeAtFin` per-point vanishing, and the Claim 5.8′ truncation identity
  `gammaGenuine = trunc k gammaGenuine`, **end-to-end from the GS surface factor + the
  base-point geometry + discriminant counting** (via `GenuineTruncationFin`).

## The honest residual surface after this file

Per word, the `mpFin` lane needs exactly: (1) the GS surface factor `(Y′ − C w) ∣ R` with
`w.natDegree < k` (Prop 5.5 + matching content), (2) per-place branch roots with the base-point
values `(w.eval (C x₀)).eval z` (producible by `RationalRootSupply` from the factor structure),
(3) the per-place `ξ`-nonvanishing `hx` (one discriminant certificate,
`ConditionDiscProduct`/`PerPlaceSeparabilitySupply` lane), and (4) `R.Separable`.  Every input
is a named, finitely-checkable GS-side fact; no per-`t` cargo remains.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Prop 5.5, the matching surface), Appendix A.5.2.6 (the per-place Hensel
  congruence and proximate root).
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open PowerSeries

namespace ArkLib

namespace DecodedProximateRoot

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## The canonical proximate root -/

/-- **The canonical decoded proximate root**: the place image of the Prop-5.5 decoded surface
`w : F[X][Y]` — Taylor-recentred at the §5 centre `x₀` (inside `coeffHom_loc`), coefficients
evaluated at the place `(z, t_z)` through the localized place evaluation `π̂_z`. -/
noncomputable def aPDecoded {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) (w : F[X][Y]) : PowerSeries F :=
  PowerSeries.map (π_hat_z hHyp z root hx) (coeffHom_loc x₀ hHyp w)

/-- The coefficient formula: the `n`-th coefficient of the canonical proximate root is the
`n`-th Taylor coefficient of the surface at the centre, read at the curve parameter `z`. -/
theorem coeff_aPDecoded {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) (w : F[X][Y]) (n : ℕ) :
    PowerSeries.coeff n (aPDecoded hHyp z root hx w)
      = ((Polynomial.taylor (Polynomial.C x₀) w).coeff n).eval z := by
  rw [aPDecoded, PowerSeries.coeff_map, coeff_coeffHom_loc]
  -- `locLift q = algebraMap (mk (C q))`, so `π̂_z ∘ locLift = π_z ∘ mk ∘ C = eval at (z, t_z)`.
  rw [locLift, RingHom.comp_apply, RingHom.comp_apply, π_hat_z_comp, π_z_mk]
  exact Polynomial.evalEval_C _ _ _

/-- The constant coefficient of the canonical proximate root is the **base-point value**
`w(x₀, z)` (the surface evaluated at the centre, read at the curve parameter). -/
theorem constantCoeff_aPDecoded {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) (w : F[X][Y]) :
    PowerSeries.constantCoeff (aPDecoded hHyp z root hx w)
      = (w.eval (Polynomial.C x₀)).eval z := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_aPDecoded,
    Polynomial.taylor_coeff_zero]

/-- **The Prop-5.5 truncation, read at the place**: coefficients of the canonical proximate
root vanish above the surface degree. -/
theorem coeff_aPDecoded_eq_zero {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) {w : F[X][Y]} {n : ℕ}
    (hn : w.natDegree < n) :
    PowerSeries.coeff n (aPDecoded hHyp z root hx w) = 0 := by
  rw [coeff_aPDecoded]
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [Polynomial.natDegree_taylor])]
  exact Polynomial.eval_zero

/-! ## The recursion base reads off the branch value -/

/-- `π_z(βHensel 0) = t_z`: the recursion base (`T mod H̃′`) reads off the branch value at the
place. -/
theorem pi_z_βHensel_zero {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z) :
    (π_z z root) (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0) = root.1 := by
  rw [BCIKS20.HenselNumerator.βHensel_zero, π_z_mk]
  -- `evalEval z t_z X = t_z` (the outer variable reads the branch value).
  simp [Polynomial.evalEval]

/-- **The order-0 congruence from the base-point fact**: if the surface's centre value at `z`
is the branch value `t_z`, the canonical proximate root reduces mod `X` to
`π_z(βHensel 0)`. -/
theorem aPDecoded_cong {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) {w : F[X][Y]}
    (hbase : (w.eval (Polynomial.C x₀)).eval z = root.1) :
    aPDecoded hHyp z root hx w
        - PowerSeries.C ((π_z z root) (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
      ∈ Ideal.span {(PowerSeries.X : PowerSeries F)} := by
  rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub,
    constantCoeff_aPDecoded, PowerSeries.constantCoeff_C,
    pi_z_βHensel_zero hHyp z root, hbase, sub_self]

/-! ## The matching-factor transport -/

/-- **The matching-factor transport**: the global GS surface divisibility `(Y′ − C w) ∣ R`
maps through `coeffHom_loc` and `π̂_z` to the per-place divisibility by the canonical
proximate root. -/
theorem aPDecoded_dvd {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) {w : F[X][Y]}
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R) :
    (Polynomial.X - Polynomial.C (aPDecoded hHyp z root hx w)) ∣
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z root hx))) := by
  have h1 : (Polynomial.X - Polynomial.C w).map (coeffHom_loc x₀ hHyp)
      ∣ R.map (coeffHom_loc x₀ hHyp) := Polynomial.map_dvd _ hdvd
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at h1
  have h2 := Polynomial.map_dvd (PowerSeries.map (π_hat_z hHyp z root hx)) h1
  rwa [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at h2

/-! ## The per-`(t,z)` capstone -/

/-- **The per-`(t,z)` `MatchingPoint` from the GS surface factor.**  All per-place cargo of
`matchingPoint_of_localSeries_dvd` is supplied by the canonical proximate root: the root fact
by the matching-factor transport, the congruence by the base-point fact, the index-`t`
vanishing by the Prop-5.5 degree bound, separability from `R.Separable`. -/
noncomputable def matchingPoint_of_decoded {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    {w : F[X][Y]} {k : ℕ} (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbase : (w.eval (Polynomial.C x₀)).eval z = root.1)
    (hR : R.Separable)
    (t : ℕ) (hkt : k ≤ t) :
    BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
      (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t z root :=
  matchingPoint_of_localSeries_dvd hHyp hξ hlc z root hx
    (aPDecoded hHyp z root hx w)
    (aPDecoded_dvd hHyp z root hx hdvd)
    (aPDecoded_cong hHyp z root hx hbase)
    (specialized_separable_of_R_separable hHyp z root hx hR)
    t (coeff_aPDecoded_eq_zero hHyp z root hx (lt_of_lt_of_le hdeg hkt))

/-! ## The finite-range family and the composed capstones -/

section Family

variable [Fintype F] [DecidableEq F]

/-- **The `mpFin` family from the GS surface factor** — the exact `mpFin`/`mpPoint` shape the
§5 bundles and `HvanishSupply.hvanish_of_mpPoint` consume.  Per-place inputs quantified over
the matching set; the surface data is global. -/
noncomputable def mpFin_of_decoded {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {matchingSet : Finset F}
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ matchingSet, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    {w : F[X][Y]} {k : ℕ} (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbase : ∀ z ∈ matchingSet, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hR : R.Separable) (T : ℕ) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t z (root z) :=
  fun t hkt _ z hz =>
    matchingPoint_of_decoded hHyp hξ hlc z (root z) (hx z hz) hdeg hdvd
      (hbase z hz) hR t hkt

omit [Fintype F] [DecidableEq F] in
/-- **The `hvanish` capstone from the GS surface factor**: the per-point vanishing
`∃ r, π_z r (βHensel t) = 0` consumed by `GenuineTruncationFin.SβLargeAtFin_of_graded_disc`,
end-to-end from the surface divisibility + base-point geometry. -/
theorem hvanish_of_decoded {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {matchingSet : Finset F}
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ matchingSet, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    {w : F[X][Y]} {k : ℕ} (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbase : ∀ z ∈ matchingSet, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hR : R.Separable) (T : ℕ) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      ∃ r : rationalRoot (H_tilde' H) z,
        (π_z z r) (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp t) = 0 :=
  HvanishSupply.hvanish_of_mpPoint H
    (mpFin_of_decoded hHyp hξ hlc root hx hdeg hdvd hbase hR T)

/-- **Claim 5.8′ from the GS surface factor (the composed truncation capstone).**
`gammaGenuine = trunc k gammaGenuine`, end-to-end from: the surface divisibility
`(Y′ − C w) ∣ R` with `w.natDegree < k`, the per-place base-point roots, the per-place
`ξ`-nonvanishing, `R.Separable`, the genuine Prop-5.5 representative, the §6 discriminant
counting, and the graded side conditions.  Every hypothesis is a named finite GS-side fact. -/
theorem gammaGenuine_eq_trunc_of_decoded {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {Ppoly : F[X][Y]}
    (hrepG : polyToPowerSeries𝕃 H Ppoly
      = ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp)
    {matchingSet : Finset F}
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ matchingSet, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    {w : F[X][Y]} (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbase : ∀ z ∈ matchingSet, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hR : R.Separable)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F) :
    ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp))
          : PowerSeries (𝕃 H)) :=
  GenuineTruncationFin.gammaGenuine_eq_trunc_of_graded_disc H hHyp hD hH hmonic hd2 hdHD
    hD_Rx0 hRgrade hrepG
    (hvanish_of_decoded hHyp hξ hmonic.leadingCoeff root hx hdeg hdvd hbase hR
      Ppoly.natDegree)
    hdisc hcover hbig

end Family

end DecodedProximateRoot

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.DecodedProximateRoot.aPDecoded
#print axioms ArkLib.DecodedProximateRoot.coeff_aPDecoded
#print axioms ArkLib.DecodedProximateRoot.constantCoeff_aPDecoded
#print axioms ArkLib.DecodedProximateRoot.coeff_aPDecoded_eq_zero
#print axioms ArkLib.DecodedProximateRoot.pi_z_βHensel_zero
#print axioms ArkLib.DecodedProximateRoot.aPDecoded_cong
#print axioms ArkLib.DecodedProximateRoot.aPDecoded_dvd
#print axioms ArkLib.DecodedProximateRoot.matchingPoint_of_decoded
#print axioms ArkLib.DecodedProximateRoot.mpFin_of_decoded
#print axioms ArkLib.DecodedProximateRoot.hvanish_of_decoded
#print axioms ArkLib.DecodedProximateRoot.gammaGenuine_eq_trunc_of_decoded
