/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.HcardDischarge
import ArkLib.ToMathlib.SubstFieldCaveat

/-!
# The `htailDeg` producer — the algebraic-degree truncation of `αFromBeta` (F5 residual)

This file *produces* the `htailDeg` field of
`HcardDischarge.Section5StrictDataFin` (read the F5-corrected interface in
`ArkLib/ToMathlib/HcardDischarge.lean`):

```
htailDeg : ∀ t, T < t → αFromBeta x₀ R H hHyp Bcoeff t = 0
```

from the **Prop-5.5 algebraic datum** carried by that very same bundle — namely the polynomial
representative of `γ` together with the substitution data:

* `hrep  : polyToPowerSeries𝕃 H Ppoly = γ x₀ R H hHyp`     (Prop 5.5: `γ` has a polynomial rep);
* `hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1`          (Prop 5.5: the curve is linear in `Z`);
* `hγ    : γ = (mk αFromBeta).subst (shiftSeries x₀ H)`     (Claim 5.9 substitution form);
* `hsubst: PowerSeries.HasSubst (shiftSeries x₀ H)`        (validity of the BCIKS shift `X ↦ X−x₀`).

## The mathematics

`htailDeg` is the **algebraic truncation**, not the combinatorial counting bound: it says the
power-series numerator `mk αFromBeta` has *bounded degree in the power-series variable* (the
`X − x₀` line), so its coefficients vanish past that bound.

The route is to invert the substitution.  `γ = (mk αFromBeta).subst g`, where
`g = shiftSeries x₀ H` is the shift `X ↦ X − x₀` (`g.coeff 0 = fieldTo𝕃 (−x₀)`, `g.coeff 1 = 1`,
`g.coeff t = 0` for `t ≥ 2`).  The crucial structural fact (`SubstFieldCaveat`) is that over the
**field** `𝕃 H` the validity hypothesis `hsubst` forces the constant coefficient of `g` to vanish
(nilpotent ⇔ zero in a field):

> `hsubst : HasSubst g  ⟹  constantCoeff g = 0  ⟹  g = X` (the centred shift).

In other words the only well-defined BCIKS substitution over `𝕃 H` is the *centred* one, `x₀ = 0`,
for which the shift series is literally `X`.  Then `subst X = id`, so the substitution collapses:

> `γ = (mk αFromBeta).subst X = mk αFromBeta`.

Combining with `hrep`, the numerator `mk αFromBeta` **is** `polyToPowerSeries𝕃 H Ppoly`, a power
series coming from a genuine `F[X][Y]` polynomial.  Its `t`-th coefficient is
`liftToFunctionField (Ppoly.coeff t)`, which is `0` whenever `Ppoly.coeff t = 0`, i.e. whenever
`t > Ppoly.natDegree`.  Hence the **truncation bound** is

> `T := Ppoly.natDegree`  (the degree of the representative in the power-series / `X − x₀`
> variable),

and `αFromBeta t = 0` for every `t > T`.

Note that `hdegX` (the `degreeX ≤ 1` datum, which controls the *inner* `Z`-line degree) is **not**
needed for this tail-vanishing: the truncation comes purely from `Ppoly` being a polynomial in the
power-series variable (`hrep`).  We still carry `hdegX` in the bundled producer for interface
fidelity with `Section5StrictDataFin`; it is used downstream by the *linear-in-`Z`* extraction, not
by the tail.

## What is and is not a hypothesis

The deliverable's goal is **`αFromBeta`-vanishing**.  The acceptable hypotheses are exactly the
Prop-5.5 data (`hrep`/`hdegX`/`hγ`/`hsubst`); none of them is the goal.  The producer derives the
`αFromBeta t = 0` conclusion from them — it is **proven**, never assumed.

Everything is kernel-clean (no `sorry`/`admit`/`axiom`/`native_decide`).

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (Claim 5.9, Prop 5.5), Appendix A.4.
-/

open Polynomial
open scoped Polynomial.Bivariate
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

namespace TailDegProducer

open BetaToCurveCoeffPolys

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## Step 1 — over the field `𝕃 H`, the valid BCIKS shift is the centred shift `X`

`hsubst : HasSubst (shiftSeries x₀ H)` over the field `𝕃 H` forces the shift's constant coefficient
to vanish (nilpotent ⇔ zero), which pins the shift series down to `X` coefficient-by-coefficient. -/

/-- The validity hypothesis `hsubst` forces the constant coefficient of the shift series to vanish:
over the field `𝕃 H`, `HasSubst g` means `IsNilpotent (constantCoeff g)`, and a field is reduced. -/
theorem constantCoeff_shiftSeries_eq_zero (x₀ : F)
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ H)) :
    PowerSeries.constantCoeff (Claim59Conditional.shiftSeries x₀ H) = 0 :=
  (SubstFieldCaveat.hasSubst_iff_constantCoeff_eq_zero_of_field _).mp hsubst

/-- **The shift collapses to `X`.**  Given `hsubst` (valid BCIKS substitution over the field
`𝕃 H`), the shift series `X ↦ X − x₀` is literally `X`: its constant coefficient is forced to `0`
(by `hsubst`), its degree-`1` coefficient is `1`, and all higher coefficients vanish — exactly the
coefficients of `X`.  (Equivalently, by `SubstFieldCaveat.hasSubst_shiftSeries_iff_eq_zero`, the
only valid case is `x₀ = 0`, the centred shift.) -/
theorem shiftSeries_eq_X (x₀ : F)
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ H)) :
    Claim59Conditional.shiftSeries x₀ H = (PowerSeries.X : PowerSeries (𝕃 H)) := by
  have hc0 : PowerSeries.constantCoeff (Claim59Conditional.shiftSeries x₀ H) = 0 :=
    constantCoeff_shiftSeries_eq_zero x₀ hsubst
  ext n
  rw [Claim59Conditional.shiftSeries, PowerSeries.coeff_mk, PowerSeries.coeff_X]
  match n with
  | 0 =>
    -- `coeff 0 = fieldTo𝕃 (-x₀) = constantCoeff = 0`; and `X`'s coeff 0 is `0`.
    rw [if_neg (by decide)]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at hc0
    rw [Claim59Conditional.shiftSeries, PowerSeries.coeff_mk] at hc0
    exact hc0
  | 1 => rw [if_pos rfl]
  | (n + 2) =>
      rw [if_neg (by omega)]
      rfl

/-! ## Step 2 — the substitution is the identity, so `γ = mk αFromBeta`

With the shift collapsed to `X`, `subst (shiftSeries) = subst X = id`, hence the in-tree
`γ = (mk αFromBeta).subst (shiftSeries)` equals `mk αFromBeta` itself. -/

/-- `subst X` is the identity on power series (substituting the variable for itself).  This is
`map_algebraMap_eq_subst_X` together with `algebraMap (𝕃 H) (𝕃 H) = id` and `map_id`. -/
theorem subst_X_eq_self (f : PowerSeries (𝕃 H)) :
    f.subst (PowerSeries.X : PowerSeries (𝕃 H)) = f := by
  rw [← PowerSeries.map_algebraMap_eq_subst_X]
  ext n
  simp [PowerSeries.coeff_map]

/-- **The substitution collapses.**  Given `hsubst` and the substitution form `hγ`, the in-tree
`γ` is literally `mk αFromBeta`: the BCIKS shift over the field is `X`, and `subst X` is the
identity. -/
theorem gamma_eq_mk_alphaFromBeta {x₀ : F} {R : F[X][X][Y]}
    {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H}
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ H))
    (hγ : γ x₀ R H hHyp =
      (PowerSeries.mk (αFromBeta x₀ R H hHyp Bcoeff)).subst
        (Claim59Conditional.shiftSeries x₀ H)) :
    γ x₀ R H hHyp = PowerSeries.mk (αFromBeta x₀ R H hHyp Bcoeff) := by
  rw [hγ, shiftSeries_eq_X x₀ hsubst, subst_X_eq_self]

/-! ## Step 3 — `mk αFromBeta` is a polynomial coercion, hence tail-vanishing

From `hrep`, `mk αFromBeta = γ = polyToPowerSeries𝕃 H Ppoly`, whose `t`-th coefficient is
`liftToFunctionField (Ppoly.coeff t)`, which vanishes whenever `Ppoly.coeff t = 0`, i.e. whenever
`Ppoly.natDegree < t`. -/

/-- `mk αFromBeta` equals the polynomial-coercion power series of `Ppoly`. -/
theorem mk_alphaFromBeta_eq_polyToPowerSeries {x₀ : F} {R : F[X][X][Y]}
    {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H} {Ppoly : F[X][Y]}
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ H))
    (hγ : γ x₀ R H hHyp =
      (PowerSeries.mk (αFromBeta x₀ R H hHyp Bcoeff)).subst
        (Claim59Conditional.shiftSeries x₀ H))
    (hrep : polyToPowerSeries𝕃 H Ppoly = γ x₀ R H hHyp) :
    PowerSeries.mk (αFromBeta x₀ R H hHyp Bcoeff) = polyToPowerSeries𝕃 H Ppoly := by
  rw [← gamma_eq_mk_alphaFromBeta hsubst hγ, hrep]

/-- The `t`-th coefficient identity: `αFromBeta … t = liftToFunctionField (Ppoly.coeff t)`. -/
theorem alphaFromBeta_eq_lift_coeff {x₀ : F} {R : F[X][X][Y]}
    {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H} {Ppoly : F[X][Y]}
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ H))
    (hγ : γ x₀ R H hHyp =
      (PowerSeries.mk (αFromBeta x₀ R H hHyp Bcoeff)).subst
        (Claim59Conditional.shiftSeries x₀ H))
    (hrep : polyToPowerSeries𝕃 H Ppoly = γ x₀ R H hHyp) (t : ℕ) :
    αFromBeta x₀ R H hHyp Bcoeff t = liftToFunctionField (Ppoly.coeff t) := by
  have h := mk_alphaFromBeta_eq_polyToPowerSeries hsubst hγ hrep
  have := congrArg (PowerSeries.coeff t) h
  rwa [PowerSeries.coeff_mk, coeff_polyToPowerSeries𝕃] at this

/-! ## Step 4 — the `htailDeg` producer

The tail-vanishing past the truncation bound `T := Ppoly.natDegree`. -/

/-- **The `htailDeg` producer (the F5 residual).**  From the Prop-5.5 algebraic datum
(`hsubst`/`hγ`/`hrep`) the Hensel-lift numerator `αFromBeta` vanishes past the degree of the
polynomial representative: with the truncation bound `T := Ppoly.natDegree`,

> `∀ t, Ppoly.natDegree < t → αFromBeta x₀ R H hHyp Bcoeff t = 0`.

This is the **algebraic** truncation (bounded degree of the power-series numerator on the `X − x₀`
line), exactly the `htailDeg` field of `Section5StrictDataFin`.  It is *proven* from the Prop-5.5
data, never assumed; the conclusion is the `αFromBeta`-vanishing goal, the hypotheses are the
acceptable Prop-5.5 representative/substitution data.

The `degreeX ≤ 1` datum `hdegX` is **not** consumed here (it bounds the orthogonal `Z`-line degree);
the tail is driven purely by `Ppoly` being a polynomial in the power-series variable. -/
theorem htailDeg_of_polynomial_representative {x₀ : F} {R : F[X][X][Y]}
    {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H} {Ppoly : F[X][Y]}
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ H))
    (hγ : γ x₀ R H hHyp =
      (PowerSeries.mk (αFromBeta x₀ R H hHyp Bcoeff)).subst
        (Claim59Conditional.shiftSeries x₀ H))
    (hrep : polyToPowerSeries𝕃 H Ppoly = γ x₀ R H hHyp) :
    ∀ t, Ppoly.natDegree < t → αFromBeta x₀ R H hHyp Bcoeff t = 0 := by
  intro t ht
  rw [alphaFromBeta_eq_lift_coeff hsubst hγ hrep t,
    Polynomial.coeff_eq_zero_of_natDegree_lt ht, map_zero]

/-! The same tail producer is monotone in the cutoff: once the polynomial representative has
degree at most `T`, every coefficient above `T` vanishes.  This is the shape needed when the
finite-counting cutoff is chosen by the cardinality budget rather than set definitionally to
`Ppoly.natDegree`. -/

/-- **Tail-degree producer for any larger cutoff.**  If the §5 representative has degree at most
`T`, then the `htailDeg` conclusion holds above `T`.  This reuses
`htailDeg_of_polynomial_representative`; it does not assume the vanishing conclusion. -/
theorem htailDeg_of_polynomial_representative_le_bound {x₀ : F} {R : F[X][X][Y]}
    {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H} {Ppoly : F[X][Y]}
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ H))
    (hγ : γ x₀ R H hHyp =
      (PowerSeries.mk (αFromBeta x₀ R H hHyp Bcoeff)).subst
        (Claim59Conditional.shiftSeries x₀ H))
    (hrep : polyToPowerSeries𝕃 H Ppoly = γ x₀ R H hHyp)
    {T : ℕ} (hT : Ppoly.natDegree ≤ T) :
    ∀ t, T < t → αFromBeta x₀ R H hHyp Bcoeff t = 0 := by
  intro t ht
  exact htailDeg_of_polynomial_representative hsubst hγ hrep t (lt_of_le_of_lt hT ht)

/-! ## Step 5 — packaged form: the `htailDeg` of a `Section5StrictDataFin`-shaped datum

The same conclusion bundled to read off the explicit Prop-5.5 fields of the corrected datum,
with the truncation index named `T := Ppoly.natDegree`.  This is exactly the shape consumed
by the `htailDeg`
field of `HcardDischarge.Section5StrictDataFin`. -/

/-- **Packaged producer.**  Records the truncation index `T := Ppoly.natDegree` and produces the
`htailDeg`-shaped conclusion `∀ t, T < t → αFromBeta … t = 0` from the Prop-5.5 datum.  `hdegX` is
carried for interface fidelity with `Section5StrictDataFin` (it feeds the orthogonal linear-in-`Z`
read-off downstream), but is not used in this tail derivation. -/
theorem htailDeg_with_bound {x₀ : F} {R : F[X][X][Y]}
    {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H} {Ppoly : F[X][Y]}
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ H))
    (hγ : γ x₀ R H hHyp =
      (PowerSeries.mk (αFromBeta x₀ R H hHyp Bcoeff)).subst
        (Claim59Conditional.shiftSeries x₀ H))
    (hrep : polyToPowerSeries𝕃 H Ppoly = γ x₀ R H hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1) :
    ∃ T : ℕ, T = Ppoly.natDegree ∧
      ∀ t, T < t → αFromBeta x₀ R H hHyp Bcoeff t = 0 :=
  ⟨Ppoly.natDegree, rfl, htailDeg_of_polynomial_representative hsubst hγ hrep⟩

end TailDegProducer

end ArkLib

/-! ## Axiom audit — tail-degree producer surface. -/
#print axioms ArkLib.TailDegProducer.htailDeg_of_polynomial_representative_le_bound
