/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SectionNewtonWindow

/-!
# The GS-data instantiation of the section-Newton iteration (#304)

The bridge from the Guruswami–Sudan trivariate `R : F[Z][X][T]` to the Newton data the
cleared filtration and the window consume:

* `thetaHom` — the coefficient map `F[Z][X] →+* (Localization.Away ξ̄)⟦X⟧`: recentre the
  domain variable at `x₀` (`X ↦ X + C x₀`), push the curve-parameter coefficients into the
  localization, coerce to power series.  `gsNewtonData R := R.map thetaHom`.
* `placeMap_comp_thetaHom` — **the place commutation**: evaluating the localized data at a
  place `z` (with `ξ̄(z) ≠ 0`) is the same as specializing the trivariate at `z` first and
  then recentring/coercing over `F`.  One `Polynomial.ringHom_ext'` (twice).
* `eval_taylorSeries_gsNewtonData_specialized` — **the per-place root transport**: the §5
  divisibility `(T − C (P z)) ∣ R(z)` makes the recentred-coerced decoded polynomial an exact
  power-series root of the specialized Newton data — the input shape of the window.
* `Q₀_gsNewtonData` — the order-`0` reduction of the Newton data is the localized `x₀`-slice
  of the trivariate, so the derivative response is the localized `ξ̄` of `SectionNewtonXiSupply`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5, Appendix A.
-/

set_option linter.style.longLine false

namespace ArkLib.SectionNewtonCleared

open PowerSeries ProximityPrize.HenselSeriesCoeff

variable {F : Type*} [Field F] (ξ : Polynomial F)

local notation "𝔞" => algebraMap (Polynomial F) (Localization.Away ξ)

/-! ## The coefficient maps -/

/-- The recentring `X ↦ X + C x₀` on the domain variable, as a ring homomorphism on
`F[Z][X]`. -/
noncomputable def recentreHom (x₀ : F) :
    Polynomial (Polynomial F) →+* Polynomial (Polynomial F) :=
  Polynomial.eval₂RingHom (Polynomial.C : Polynomial F →+* Polynomial (Polynomial F))
    (Polynomial.X + Polynomial.C (Polynomial.C x₀))

/-- The recentring-then-coerce map over the base field. -/
noncomputable def taylorCoeHom (x₀ : F) : Polynomial F →+* PowerSeries F :=
  (Polynomial.coeToPowerSeries.ringHom).comp
    (Polynomial.eval₂RingHom (Polynomial.C : F →+* Polynomial F) (Polynomial.X + Polynomial.C x₀))

/-- **The Newton coefficient map**: recentre the domain variable at `x₀`, localize the
curve-parameter coefficients, coerce to power series. -/
noncomputable def thetaHom (x₀ : F) :
    Polynomial (Polynomial F) →+* PowerSeries (Localization.Away ξ) :=
  ((Polynomial.coeToPowerSeries.ringHom).comp (Polynomial.mapRingHom 𝔞)).comp
    (recentreHom x₀)

/-- **The Newton data of a GS trivariate**: `R : F[Z][X][T]` with the `T`-coefficients
pushed through `thetaHom`. -/
noncomputable def gsNewtonData (x₀ : F) (R : Polynomial (Polynomial (Polynomial F))) :
    Polynomial (PowerSeries (Localization.Away ξ)) :=
  R.map (thetaHom ξ x₀)

/-! ## The place commutation -/

/-- Mapping a coerced polynomial is coercing the mapped polynomial. -/
theorem powerSeriesMap_coe {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (q : Polynomial R) :
    (PowerSeries.map f) (q : PowerSeries R) = ((q.map f : Polynomial S) : PowerSeries S) := by
  ext n
  rw [PowerSeries.coeff_map, Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_map]

/-- **THE PLACE COMMUTATION**: evaluating the localized Newton coefficients at a place
(`ξ̄(z) ≠ 0`) is specializing the trivariate coefficients at `z` first, then
recentring/coercing over `F`. -/
theorem placeMap_comp_thetaHom (x₀ : F) {z : F} (hz : ξ.eval z ≠ 0) :
    (PowerSeries.map (placeMap ξ hz)).comp (thetaHom ξ x₀)
      = (taylorCoeHom x₀).comp (Polynomial.mapRingHom (Polynomial.evalRingHom z)) := by
  apply Polynomial.ringHom_ext'
  · -- agreement on curve-parameter coefficients (an `F[Z]`-indexed family)
    apply Polynomial.ringHom_ext'
    · ext a
      simp only [RingHom.coe_comp, Function.comp_apply, thetaHom, recentreHom, taylorCoeHom,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.coe_mapRingHom,
        Polynomial.map_C, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
        PowerSeries.map_C, Polynomial.eval_C]
      congr 1
      simpa using placeMap_algebraMap ξ hz (Polynomial.C a)
    · simp only [RingHom.coe_comp, Function.comp_apply, thetaHom, recentreHom, taylorCoeHom,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.coe_mapRingHom,
        Polynomial.map_C, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
        PowerSeries.map_C, Polynomial.eval_X]
      congr 1
      simpa using placeMap_algebraMap ξ hz Polynomial.X
  · -- agreement on the domain variable
    simp only [RingHom.coe_comp, Function.comp_apply, thetaHom, recentreHom, taylorCoeHom,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.coe_mapRingHom,
      Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_add, Polynomial.coe_X,
      Polynomial.coe_C, map_add, PowerSeries.map_X, PowerSeries.map_C]
    congr 2
    simpa using placeMap_algebraMap ξ hz (Polynomial.C x₀)

/-! ## The per-place root transport -/

/-- **The per-place root transport**: the §5 divisibility at a place makes the
recentred-coerced decoded polynomial an exact root of the specialized Newton data — the
input shape of the window. -/
theorem eval_taylorCoe_gsNewtonData_specialized (x₀ : F)
    {R : Polynomial (Polynomial (Polynomial F))} {z : F} (hz : ξ.eval z ≠ 0)
    {p : Polynomial F}
    (hdvd : (Polynomial.X - Polynomial.C p) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) :
    Polynomial.eval (taylorCoeHom x₀ p)
      ((gsNewtonData ξ x₀ R).map (PowerSeries.map (placeMap ξ hz))) = 0 := by
  -- specialize-then-recentre, by the place commutation
  have hmap : (gsNewtonData ξ x₀ R).map (PowerSeries.map (placeMap ξ hz))
      = (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).map (taylorCoeHom x₀) := by
    rw [gsNewtonData, Polynomial.map_map, placeMap_comp_thetaHom ξ x₀ hz,
      ← Polynomial.map_map]
  rw [hmap]
  -- transport the linear factor along `taylorCoeHom` and evaluate at its root
  obtain ⟨G, hG⟩ := hdvd
  rw [hG, Polynomial.map_mul, Polynomial.eval_mul, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self,
    zero_mul]

/-! ## The order-`0` reduction is the localized slice -/

/-- `constantCoeff ∘ thetaHom` evaluates the domain variable at `x₀` and localizes. -/
theorem constantCoeff_comp_thetaHom (x₀ : F) :
    (PowerSeries.constantCoeff (R := Localization.Away ξ)).comp (thetaHom ξ x₀)
      = (algebraMap (Polynomial F) (Localization.Away ξ)).comp
          (Polynomial.evalRingHom (Polynomial.C x₀)) := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · ext a
      simp only [RingHom.coe_comp, Function.comp_apply, thetaHom, recentreHom,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.coe_mapRingHom,
        Polynomial.map_C, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
        PowerSeries.constantCoeff_C, Polynomial.coe_evalRingHom, Polynomial.eval_C]
    · simp only [RingHom.coe_comp, Function.comp_apply, thetaHom, recentreHom,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.coe_mapRingHom,
        Polynomial.map_C, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
        PowerSeries.constantCoeff_C, Polynomial.coe_evalRingHom, Polynomial.eval_C]
  · simp only [RingHom.coe_comp, Function.comp_apply, thetaHom, recentreHom,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.coe_mapRingHom,
      Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_add, Polynomial.coe_X,
      Polynomial.coe_C, map_add, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C,
      zero_add, Polynomial.coe_evalRingHom, Polynomial.eval_X]

/-- **The order-`0` reduction of the Newton data is the localized `x₀`-slice** — so the
derivative response is the localized slice derivative, connecting to the `ξ̄` of
`SectionNewtonXiSupply`. -/
theorem Q₀_gsNewtonData (x₀ : F) (R : Polynomial (Polynomial (Polynomial F))) :
    Q₀ (gsNewtonData ξ x₀ R)
      = (R.map (Polynomial.evalRingHom (Polynomial.C x₀))).map 𝔞 := by
  unfold Q₀ gsNewtonData
  rw [Polynomial.map_map, Polynomial.map_map, constantCoeff_comp_thetaHom]

end ArkLib.SectionNewtonCleared

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.SectionNewtonCleared.powerSeriesMap_coe
#print axioms ArkLib.SectionNewtonCleared.placeMap_comp_thetaHom
#print axioms ArkLib.SectionNewtonCleared.eval_taylorCoe_gsNewtonData_specialized
#print axioms ArkLib.SectionNewtonCleared.constantCoeff_comp_thetaHom
#print axioms ArkLib.SectionNewtonCleared.Q₀_gsNewtonData
