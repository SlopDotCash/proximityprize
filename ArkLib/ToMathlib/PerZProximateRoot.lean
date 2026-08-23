/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.CentreVanishingSupply
import ArkLib.ToMathlib.MatchingPointFromLocalSeries
import ArkLib.ToMathlib.DecodedProximateRoot

/-!
# Issue #304 — the per-`z` proximate root: `MatchingPoint` families from the per-place
decoded data (no global surface)

The F7/F8-evading matching lane (`BranchValuePigeonhole` + `CentreVanishingSupply`) produces
the matching set, branch roots, and base-point values from **per-place** decoded data.  This
file produces the remaining per-`(t,z)` `MatchingPoint` cargo from the same per-place data —
replacing `DecodedProximateRoot`'s global-surface route (whose surface factor is F7/F8-gated)
with the per-`z` decoded polynomial:

* `taylorCoerce x₀ : F[X] →+* F⟦X⟧` — Taylor-recentre at the RS point `x₀`, read as a power
  series: the per-`z` proximate root is `aPTaylor x₀ (P z) := taylorCoerce x₀ (P z)`.
* `placeHom_eq_taylorCoerce` — **the place/centre swap (hom level)**: reading the matching
  polynomial's coefficients through `coeffHom_loc x₀` then the place `π̂_z` equals specializing
  `Z := z` first, then Taylor-recentring at `x₀` and coercing.  Hence
  `fz_eq_specialized_taylorCoerce`: the matching polynomial `f_z` IS the `taylorCoerce`-image
  of the specialized interpolant `Q₀|_{Z:=z}`.
* `aPTaylor_dvd` — the per-`z` matching divisibility `(Y − C (P z)) ∣ Q₀|_{Z:=z}` (the
  S10-converse output) transports to `(Y − C (aPTaylor x₀ (P z))) ∣ f_z` — the proximate-root
  fact.
* `constantCoeff_aPTaylor` / `coeff_aPTaylor_eq_zero` — the order-0 value is `(P z).eval x₀`
  (the decoded branch value — tying the congruence to the pigeonhole root), and the
  coefficients vanish past `deg (P z) < k` (the RS degree bound — the `haP_coeff` cargo, free
  from decoding).
* `matchingPoint_of_perz_dvd` — the per-`(t,z)` `MatchingPoint` at the signed canonical
  coefficients from: the per-`z` divisibility, the decoded degree bound, the branch root with
  the decoded value, `ξ`-nonvanishing, monicity, and `R.Separable`.
* `mpFin_of_pigeonhole_supply` — **the composed family capstone**: the finite-range
  `MatchingPoint` family over a pigeonhole matching set (`BranchValuePigeonhole` incidence
  output), with the roots `incidenceRootFn` and all cargo per-place.

With this file, the per-`(t,z)` `MatchingPoint` production is complete from: per-`z` GS
matching divisibilities + decoded degree bounds + per-`z` H-incidence (pigeonhole) +
`ξ`-nonvanishing + `R.Separable` + monic `H` — all per-place or global named facts; **no
global surface object remains anywhere on the lane**.

## References
* [BCIKS20] §5.2.6 (the per-place Hensel matching), §6; the F-series ledger on issue #304.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open PowerSeries

namespace ArkLib

namespace PerZProximateRoot

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## The Taylor-coercion hom and the per-`z` proximate root -/

/-- Taylor-recentre at the RS point `x₀`, then read as a power series. -/
noncomputable def taylorCoerce (x₀ : F) : F[X] →+* PowerSeries F :=
  (Polynomial.coeToPowerSeries.ringHom).comp (Polynomial.taylorAlgHom x₀).toRingHom

/-- The coefficient formula for `taylorCoerce`. -/
theorem coeff_taylorCoerce (x₀ : F) (P : F[X]) (n : ℕ) :
    PowerSeries.coeff n (taylorCoerce x₀ P) = (Polynomial.taylor x₀ P).coeff n := by
  rw [taylorCoerce, RingHom.comp_apply]
  simp [Polynomial.taylorAlgHom_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coeff_coe]

/-- **The per-`z` proximate root**: the decoded polynomial's Taylor expansion at `x₀`. -/
noncomputable def aPTaylor (x₀ : F) (P : F[X]) : PowerSeries F := taylorCoerce x₀ P

/-- The order-0 value of the proximate root is the decoded branch value `(P).eval x₀`. -/
theorem constantCoeff_aPTaylor (x₀ : F) (P : F[X]) :
    PowerSeries.constantCoeff (aPTaylor x₀ P) = P.eval x₀ := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, aPTaylor, coeff_taylorCoerce,
    Polynomial.taylor_coeff_zero]

/-- The `haP_coeff` cargo: coefficients vanish past the decoded degree. -/
theorem coeff_aPTaylor_eq_zero (x₀ : F) {P : F[X]} {t : ℕ} (hdeg : P.natDegree < t) :
    PowerSeries.coeff t (aPTaylor x₀ P) = 0 := by
  rw [aPTaylor, coeff_taylorCoerce]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [Polynomial.natDegree_taylor])

/-! ## The place/centre swap -/

/-- **The place/centre swap (hom level).**  Reading a matching-polynomial coefficient through
`coeffHom_loc x₀` then the place `π̂_z` equals specializing `Z := z` first, then
Taylor-recentring at `x₀` and coercing. -/
theorem placeHom_eq_taylorCoerce {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) :
    (PowerSeries.map (π_hat_z hHyp z root hx)).comp (coeffHom_loc x₀ hHyp)
      = (taylorCoerce x₀).comp (Polynomial.mapRingHom (Polynomial.evalRingHom z)) := by
  refine RingHom.ext fun q => PowerSeries.ext fun n => ?_
  rw [RingHom.comp_apply, RingHom.comp_apply]
  -- LHS: π̂ ∘ locLift reading = the Taylor coefficient evaluated at z
  rw [PowerSeries.coeff_map, coeff_coeffHom_loc]
  rw [locLift, RingHom.comp_apply, RingHom.comp_apply, π_hat_z_comp, π_z_mk]
  -- RHS: the z-specialized Taylor coefficient
  rw [coeff_taylorCoerce]
  rw [Polynomial.coe_mapRingHom]
  -- `taylor x₀ (q.map f) = (taylor (C x₀) q).map f` with `f := evalRingHom z`
  have hswap : Polynomial.taylor x₀ (q.map (Polynomial.evalRingHom z))
      = (Polynomial.taylor (Polynomial.C x₀) q).map (Polynomial.evalRingHom z) := by
    have h := Polynomial.map_taylor q (Polynomial.C x₀) (Polynomial.evalRingHom z)
    rw [Polynomial.coe_evalRingHom, Polynomial.eval_C] at h
    exact h.symm
  rw [hswap, Polynomial.coeff_map, Polynomial.coe_evalRingHom]
  exact Polynomial.evalEval_C _ _ _

/-- **The matching polynomial is the `taylorCoerce`-image of the specialized interpolant**:
`f_z = (Q₀|_{Z:=z}).map (taylorCoerce x₀)`. -/
theorem fz_eq_specialized_taylorCoerce {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) :
    (R.map (coeffHom_loc x₀ hHyp)).map (PowerSeries.map (π_hat_z hHyp z root hx))
      = (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).map
          (taylorCoerce x₀) := by
  rw [Polynomial.map_map, Polynomial.map_map, placeHom_eq_taylorCoerce]

/-! ## The proximate-root divisibility -/

/-- **The per-`z` proximate-root fact.**  The per-`z` matching divisibility (the S10-converse
output shape) transports to the matching polynomial: `(Y − C (aPTaylor x₀ P)) ∣ f_z`. -/
theorem aPTaylor_dvd {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) {P : F[X]}
    (hdvd : Polynomial.X - Polynomial.C P ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) :
    (Polynomial.X - Polynomial.C (aPTaylor x₀ P)) ∣
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z root hx))) := by
  have h := Polynomial.map_dvd (taylorCoerce x₀) hdvd
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at h
  rwa [fz_eq_specialized_taylorCoerce hHyp z root hx]

/-! ## The order-0 congruence at the pigeonhole root -/

/-- **The order-0 congruence**: when the branch root carries the decoded value
`(P).eval x₀` (the pigeonhole root, monic case), the proximate root reduces mod `X` to
`π_z(βHensel 0)`. -/
theorem aPTaylor_cong {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z) {P : F[X]}
    (hval : (P.eval x₀ : F) = root.1) :
    aPTaylor x₀ P
        - PowerSeries.C ((π_z z root) (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp 0))
      ∈ Ideal.span {(PowerSeries.X : PowerSeries F)} := by
  rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub,
    constantCoeff_aPTaylor, PowerSeries.constantCoeff_C,
    DecodedProximateRoot.pi_z_βHensel_zero hHyp z root, hval, sub_self]

/-! ## The per-`(t,z)` capstone -/

/-- **The per-`(t,z)` `MatchingPoint` from per-place decoded data.**  All cargo of
`matchingPoint_of_localSeries_dvd` supplied: the proximate-root divisibility from the per-`z`
S10-converse output, the congruence from the decoded branch value at the root, the index-`t`
vanishing from the RS degree bound, separability from `R.Separable`. -/
noncomputable def matchingPoint_of_perz_dvd {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    {P : F[X]} {k : ℕ} (hdeg : P.natDegree < k)
    (hdvd : Polynomial.X - Polynomial.C P ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : (P.eval x₀ : F) = root.1)
    (hR : R.Separable)
    (t : ℕ) (hkt : k ≤ t) :
    BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
      (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t z root :=
  matchingPoint_of_localSeries_dvd hHyp hξ hlc z root hx
    (aPTaylor x₀ P)
    (aPTaylor_dvd hHyp z root hx hdvd)
    (aPTaylor_cong hHyp z root hval)
    (specialized_separable_of_R_separable hHyp z root hx hR)
    t (coeff_aPTaylor_eq_zero x₀ (lt_of_lt_of_le hdeg hkt))

/-! ## The composed family capstone over the pigeonhole supply -/

/-- **The `mpFin` family over a pigeonhole matching set.**  From: per-place H-incidence at the
decoded values (`BranchValuePigeonhole` output), per-place specialized matching
divisibilities (S10-converse outputs), decoded degree bounds, `ξ`-nonvanishing at the
incidence roots, monicity, and `R.Separable` — the finite-range `MatchingPoint` family at the
incidence roots.  **No global surface object anywhere.** -/
noncomputable def mpFin_of_pigeonhole_supply {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {matchingSet : Finset F} {Pz : F → F[X]} {k : ℕ}
    (hinc : ∀ z ∈ matchingSet, Polynomial.evalEval z ((Pz z).eval x₀) H = 0)
    (hdvd : ∀ z ∈ matchingSet, Polynomial.X - Polynomial.C (Pz z) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hdeg : ∀ z ∈ matchingSet, (Pz z).natDegree < k)
    (hx : ∀ z (hz : z ∈ matchingSet),
      (π_z z (BranchValuePigeonhole.incidenceRootFn (H := H) (hinc z hz)))
        (ξ x₀ R H hHyp) ≠ 0)
    (hR : R.Separable) (T : ℕ) :
    ∀ t, k ≤ t → t ≤ T → ∀ z, ∀ hz : z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t z
        (BranchValuePigeonhole.incidenceRootFn (H := H) (hinc z hz)) :=
  fun t hkt _ z hz =>
    matchingPoint_of_perz_dvd hHyp hξ hlc z
      (BranchValuePigeonhole.incidenceRootFn (H := H) (hinc z hz))
      (hx z hz) (hdeg z hz) (hdvd z hz)
      (BranchValuePigeonhole.incidenceRootFn_val_monic hlc (hinc z hz))
      hR t hkt

end PerZProximateRoot

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.PerZProximateRoot.taylorCoerce
#print axioms ArkLib.PerZProximateRoot.coeff_taylorCoerce
#print axioms ArkLib.PerZProximateRoot.aPTaylor
#print axioms ArkLib.PerZProximateRoot.constantCoeff_aPTaylor
#print axioms ArkLib.PerZProximateRoot.coeff_aPTaylor_eq_zero
#print axioms ArkLib.PerZProximateRoot.placeHom_eq_taylorCoerce
#print axioms ArkLib.PerZProximateRoot.fz_eq_specialized_taylorCoerce
#print axioms ArkLib.PerZProximateRoot.aPTaylor_dvd
#print axioms ArkLib.PerZProximateRoot.aPTaylor_cong
#print axioms ArkLib.PerZProximateRoot.matchingPoint_of_perz_dvd
#print axioms ArkLib.PerZProximateRoot.mpFin_of_pigeonhole_supply
