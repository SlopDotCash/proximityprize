/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SectionNewtonGSData
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Recentring supplies for the GS Newton data (#304)

The remaining window inputs for `gsNewtonData`, all mechanical:

* `taylorCoeHom_eq_coe_taylor` — the recentre-coerce map is the (coerced) Taylor expansion,
  so the Mathlib `taylor` API (degree preservation, base coefficient) applies to the
  per-place decoded polynomials.
* `natDegree_coeff_recentreHom_le` — **the `hQdeg` supply**: recentring the domain variable
  does not raise the curve-parameter degrees of the coefficients (the binomial mixing is
  `F`-linear), so the flat/sloped GS `Z`-budgets transport to the Newton data verbatim
  (`exists_coeff_gsNewtonData`).
* `eval_derivative_Q₀_gsNewtonData` — **the `hresp` supply**: the derivative response of the
  Newton data is the localized slice response `ξ̄ := (∂_T R)(x₀, v(Z), Z)`-style polynomial —
  the exact `ξ̄` of `SectionNewtonXiSupply`.
* `monic_gsNewtonData`, `natDegree_gsNewtonData` — monicity/degree transport.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5, Appendix A.
-/

set_option linter.style.longLine false

namespace ArkLib.SectionNewtonCleared

open PowerSeries ProximityPrize.HenselSeriesCoeff

variable {F : Type*} [Field F] (ξ : Polynomial F)

local notation "𝔞" => algebraMap (Polynomial F) (Localization.Away ξ)

/-! ## The recentre-coerce map is the Taylor expansion -/

/-- The recentring over the base field is the Taylor expansion. -/
theorem taylorCoeHom_eq_coe_taylor (x₀ : F) (p : Polynomial F) :
    taylorCoeHom x₀ p = ((Polynomial.taylor x₀ p : Polynomial F) : PowerSeries F) := by
  rw [taylorCoeHom, Polynomial.taylor_apply, Polynomial.comp]
  rfl

/-- The base coefficient of the recentred decoded polynomial is its value at the centre. -/
theorem constantCoeff_taylorCoeHom (x₀ : F) (p : Polynomial F) :
    constantCoeff (taylorCoeHom x₀ p) = p.eval x₀ := by
  rw [taylorCoeHom_eq_coe_taylor, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    Polynomial.coeff_coe, Polynomial.taylor_coeff_zero]

/-- Degree preservation for the recentred decoded polynomial. -/
theorem natDegree_taylor_eq (x₀ : F) (p : Polynomial F) :
    (Polynomial.taylor x₀ p).natDegree = p.natDegree :=
  Polynomial.natDegree_taylor p x₀

/-! ## The `hQdeg` supply -/

/-- The recentring shift is the constant-coefficient image of the base shift. -/
theorem X_add_C_C_eq_map (x₀ : F) :
    (Polynomial.X + Polynomial.C (Polynomial.C x₀) : Polynomial (Polynomial F))
      = (Polynomial.X + Polynomial.C x₀ : Polynomial F).map
          (Polynomial.C : F →+* Polynomial F) := by
  rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]

/-- **Recentring does not raise curve-parameter degrees**: every coefficient of
`recentreHom x₀ p` is an `F`-linear combination of the coefficients of `p`. -/
theorem natDegree_coeff_recentreHom_le (x₀ : F) {p : Polynomial (Polynomial F)} {D : ℕ}
    (hp : ∀ m, (p.coeff m).natDegree ≤ D) (j : ℕ) :
    ((recentreHom x₀ p).coeff j).natDegree ≤ D := by
  rw [recentreHom]
  simp only [Polynomial.coe_eval₂RingHom]
  rw [Polynomial.eval₂_eq_sum_range, Polynomial.finset_sum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m _
  rw [Polynomial.coeff_C_mul, X_add_C_C_eq_map, ← Polynomial.map_pow, Polynomial.coeff_map]
  calc (p.coeff m * Polynomial.C (((Polynomial.X + Polynomial.C x₀) ^ m).coeff j)).natDegree
      ≤ (p.coeff m).natDegree
        + (Polynomial.C (((Polynomial.X + Polynomial.C x₀) ^ m).coeff j)).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ D + 0 := Nat.add_le_add (hp m) (le_of_eq (Polynomial.natDegree_C _))
    _ = D := Nat.add_zero D

/-- **The `hQdeg` supply for the Newton data**: a flat curve-parameter budget on the GS
trivariate transports to the Newton data. -/
theorem exists_coeff_gsNewtonData (x₀ : F) {R : Polynomial (Polynomial (Polynomial F))}
    {DZ : ℕ} (hR : ∀ i m, ((R.coeff i).coeff m).natDegree ≤ DZ) (i j : ℕ) :
    ∃ q : Polynomial F, q.natDegree ≤ DZ ∧
      𝔞 q = coeff j ((gsNewtonData ξ x₀ R).coeff i) := by
  refine ⟨(recentreHom x₀ (R.coeff i)).coeff j,
    natDegree_coeff_recentreHom_le x₀ (hR i) j, ?_⟩
  rw [gsNewtonData, Polynomial.coeff_map, thetaHom]
  simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom,
    Polynomial.coeToPowerSeries.ringHom_apply]
  rw [Polynomial.coeff_coe, Polynomial.coeff_map]

/-! ## The `hresp` supply -/

/-- **The slice response**: the derivative of the `x₀`-slice of the trivariate, evaluated at
the section — the `ξ̄` of `SectionNewtonXiSupply`, as a base polynomial. -/
noncomputable def sliceResponse (x₀ : F) (R : Polynomial (Polynomial (Polynomial F)))
    (v : Polynomial F) : Polynomial F :=
  Polynomial.eval v (Polynomial.derivative
    (R.map (Polynomial.evalRingHom (Polynomial.C x₀))))

/-- **The `hresp` supply**: the derivative response of the Newton data at the localized seed
is the localized slice response. -/
theorem eval_derivative_Q₀_gsNewtonData (x₀ : F)
    (R : Polynomial (Polynomial (Polynomial F))) (v : Polynomial F) :
    Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ (gsNewtonData ξ x₀ R)))
      = 𝔞 (sliceResponse x₀ R v) := by
  rw [Q₀_gsNewtonData, Polynomial.derivative_map, Polynomial.eval_map, sliceResponse,
    Polynomial.eval₂_hom]

/-! ## Monicity and degree transport -/

/-- Monicity transports to the Newton data. -/
theorem monic_gsNewtonData (x₀ : F) {R : Polynomial (Polynomial (Polynomial F))}
    (hR : R.Monic) : (gsNewtonData ξ x₀ R).Monic :=
  hR.map _

/-- Degree transports to the Newton data (monic case, nonzero response). -/
theorem natDegree_gsNewtonData (hξ0 : ξ ≠ 0) (x₀ : F)
    {R : Polynomial (Polynomial (Polynomial F))}
    (hR : R.Monic) : (gsNewtonData ξ x₀ R).natDegree = R.natDegree := by
  haveI : Nontrivial (Localization.Away ξ) := by
    have hinj : Function.Injective 𝔞 :=
      IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hξ0)
    refine nontrivial_of_ne (𝔞 1) 0 fun h => one_ne_zero (hinj ?_)
    rw [h, map_zero]
  exact hR.natDegree_map _

end ArkLib.SectionNewtonCleared

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.SectionNewtonCleared.taylorCoeHom_eq_coe_taylor
#print axioms ArkLib.SectionNewtonCleared.constantCoeff_taylorCoeHom
#print axioms ArkLib.SectionNewtonCleared.natDegree_coeff_recentreHom_le
#print axioms ArkLib.SectionNewtonCleared.exists_coeff_gsNewtonData
#print axioms ArkLib.SectionNewtonCleared.eval_derivative_Q₀_gsNewtonData
#print axioms ArkLib.SectionNewtonCleared.monic_gsNewtonData
#print axioms ArkLib.SectionNewtonCleared.natDegree_gsNewtonData
