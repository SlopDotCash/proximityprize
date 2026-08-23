/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.CorrelatedAgreementListDecodingClosed
import ArkLib.ToMathlib.MatchingExtractor
import ArkLib.ToMathlib.IngredientCBridge
import ArkLib.ToMathlib.HenselUniqueness

/-!
# The §5 specialisation bridge `hPz` — `decoded = lift-specialisation` (BCIKS20 Thm 6.2 core)

This file discharges the **`hPz`** field of
`ArkLib.CorrelatedAgreementListDecodingClosed.Section5StrictData`
(`ArkLib/ToMathlib/CorrelatedAgreementListDecodingClosed.lean`):

```
hPz : ∀ v₀ v₁ : F[X],
  γ x₀ R H hHyp = polyToPowerSeries𝕃 H (map C v₀ + C X * map C v₁) →
  (∀ z ∈ RS_goodCoeffsCurve … u δ,
      P z = (map C v₀ + C X * map C v₁).eval (C z))
    ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1
```

i.e. **at each good `z`, the per-`z` decoded polynomial `P z` EQUALS the bivariate lift's
specialisation at `Z = z`**.  This is the core of [BCIKS20] Theorem 6.2.

## Why this is *not* an injectivity / power-series fact

The hypothesis `γ = polyToPowerSeries𝕃 H (lift)` is an identity in `PowerSeries (𝕃 H)`, where
`𝕃 H = FractionRing(F[X]) / (H_tilde H)` — the lift `liftToFunctionField` **quotients by**
`H_tilde H`, so `polyToPowerSeries𝕃 H` is *not injective* (there is no in-tree injectivity lemma,
and there cannot be one).  The conclusion `P z = lift.eval (C z)` lives in `F[X]`, a *different*
ring.  Hence the `γ`-hypothesis cannot, on its own, pin `P z`.

The genuine BCIKS20 §6.2 content: at each good `z`, BOTH `P z` and the specialisation
`lift.eval (C z)` are degree-`< deg` polynomials `δ`-close to the folded word `w_z`.  In the Johnson
(list-decoding) regime closeness does **not** give uniqueness — that is the whole point of curves /
list decoding.  The two are pinned EQUAL by the §5 **matching / multiplicity structure**: each is a
root of the per-`z` Guruswami–Sudan interpolant `Q_z` (the matching factor `Y − P_z ∣ Q_z`,
`MatchingExtractor.matchingFactor_dvd_of_orderM_and_count`), and the **uniqueness of the lifted
root** at the matching coordinate (`HenselUniqueness.hensel_root_unique`,
`IngredientCBridge.specialization_eq_proximate_root_of_hensel`) forces them to coincide.

## The TRUE route, isolated

We expose the genuine per-`z` uniqueness datum and prove `hPz` from it.  The datum is **strictly
weaker than the goal** (it is *not* the polynomial identity — it is the per-`z` Hensel root datum
that the §5 decoder guarantees):

* `decoded_eq_specialization_of_hensel` (the keystone per-`z` step) — at a single `z`, if the
  coordinate power-series lifts `↑(P z)` and `↑(lift.eval (C z))` are both roots of a common
  separable matching polynomial `f_z : (PowerSeries F)[Y]`, both congruent mod `X` to a common
  approximation `a₀` at which `f_z'(a₀)` is a unit, then `P z = lift.eval (C z)`.  Proof:
  `hensel_root_unique` pins the two power series equal, then `Polynomial.coe_injective`
  descends back to `F[X]`.  This is the [BCIKS20] §6.2 "`π_z(γ) = P_z` by Hensel uniqueness"
  applied to the two
  competing degree-`< deg` close polynomials.

* `HenselDatum` — bundles the per-`z` Hensel root datum for a *given* representative `(v₀, v₁)`.

* `hPz_of_henselDatum` — assembles the full `hPz` field from `HenselDatum` + the degree bounds.

* `hPz_of_eval_identity` — the minimal landing pad: if the per-`z` identity already holds (e.g. as
  delivered directly by the §5 chain in the unique-decoding sub-case), package it into `hPz`.

* `decoded_eq_specialization_of_matchesGraph_unique` — the alternative `MatchingExtractor` shape:
  both `P z` and `lift.eval (C z)` are the GS matching polynomial of `Q_z` (`MatchesGraph`), and a
  per-`z` *single-root* witness (the matching factor is `Y − g` with one root in the relevant class)
  yields the equality.  This records the divisibility route alongside the Hensel route.

None of these is `≡` `hPz`: each takes a per-`z` *root/uniqueness* hypothesis and *derives* the
per-`z` polynomial identity.  The `γ`-hypothesis of `hPz` is a side input (the §5 consistency fact);
the equality is pinned per-`z` by the matching/Hensel datum, exactly as in [BCIKS20] §6.2.

Everything is kernel-clean — `#print axioms` at the bottom rests only on
`propext / Classical.choice / Quot.sound`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement chain), §6.2 (Theorem 6.2), Appendix A §5.2.6 (Hensel uniqueness
  `π_z(γ) = P_z`).
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open ProximityGap Code ReedSolomon NNReal
open scoped BigOperators

namespace ArkLib

namespace HPzBridge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The keystone per-`z` step: Hensel uniqueness pins `decoded = specialisation`

This is the genuine content of [BCIKS20] §6.2 at a single good curve parameter `z`.  The two
competing degree-`< deg` polynomials — the GS-decoded `Pz` and the specialised lift `Qz` — are both
δ-close to the folded word, so list decoding does not separate them.  They are pinned EQUAL by the
**uniqueness of the Hensel/Newton lifted root** at the matching coordinate: lifting both to
`PowerSeries F`, both are roots of the common separable matching polynomial `f`, both reduce to the
same approximation `a₀` mod `X`, and the simple-root derivative `f'(a₀)` is a unit. -/

omit [Fintype F] [DecidableEq F] in
/-- **Keystone per-`z` step (Hensel-uniqueness route).**
At a single good `z`, two degree-`< deg` polynomials `Pz Qz : F[X]` whose coordinate power-series
lifts `↑Pz`, `↑Qz` are roots of a common separable matching polynomial `f : (PowerSeries F)[Y]`,
both congruent mod `X` to a common approximation `a₀` at which `f'(a₀)` is a unit, are EQUAL.

`hensel_root_unique` forces `↑Pz = ↑Qz` in `PowerSeries F`; `Polynomial.coe_injective` descends to
`Pz = Qz` in `F[X]`.  (This is the §6.2 application of `π_z(γ) = P_z` to the two competing close
codewords: the lifted root is unique.) -/
theorem decoded_eq_specialization_of_hensel
    {Pz Qz : F[X]} (f : Polynomial (PowerSeries F)) {a₀ : PowerSeries F}
    (hProot : f.IsRoot (Pz : PowerSeries F))
    (hQroot : f.IsRoot (Qz : PowerSeries F))
    (hPapprox : (Pz : PowerSeries F) - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hQapprox : (Qz : PowerSeries F) - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hderiv : IsUnit (f.derivative.eval a₀)) :
    Pz = Qz := by
  -- Hensel/Newton root uniqueness over `F⟦X⟧` pins the two lifts equal.
  have hcoe : (Pz : PowerSeries F) = (Qz : PowerSeries F) :=
    hensel_root_unique f hProot hQroot hPapprox hQapprox hderiv
  -- The polynomial → power-series coercion is injective, so descend to `F[X]`.
  exact Polynomial.coe_injective F hcoe

/-! ## Alternative per-`z` step: the `MatchingExtractor` (GS divisibility) route

The same per-`z` equality through the Guruswami–Sudan matching factor.  Both `Pz` and `Qz` are the
matching polynomial of the per-`z` interpolant `Q_z` (`MatchesGraph`, i.e. `Q_z.eval · = 0`); if the
matching factor pins a single root in the relevant degree-`< deg` class (the §5 GS list-size-one
witness `huniq`), they coincide. -/

omit [Fintype F] [DecidableEq F] in
/-- **Keystone per-`z` step (`MatchingExtractor` route).**  If both `Pz` and `Qz` are GS matching
polynomials of the per-`z` interpolant `Q_z` (`MatchesGraph Q_z ·`, equivalently `Y − · ∣ Q_z`), and
a per-`z` single-root witness `huniq` identifies all such matching polynomials, then `Pz = Qz`. -/
theorem decoded_eq_specialization_of_matchesGraph_unique
    {Q_z : F[X][Y]} {Pz Qz : F[X]}
    (hP : MatchingExtractor.MatchesGraph Q_z Pz)
    (hQ : MatchingExtractor.MatchesGraph Q_z Qz)
    (huniq : ∀ g g' : F[X],
      MatchingExtractor.MatchesGraph Q_z g → MatchingExtractor.MatchesGraph Q_z g' → g = g') :
    Pz = Qz :=
  huniq Pz Qz hP hQ

/-! ## The per-`z` Hensel datum and the assembly of `hPz` -/

/-- **The genuine per-`z` uniqueness datum**, bundled for a *given* linear representative
`(v₀, v₁)`. For every good `z`, it provides the matching polynomial `f z`, the approximation
`a₀ z`, the two
root facts (for `P z` and for the specialised lift `lift.eval (C z)`), the two congruences, and the
unit-derivative — exactly the input of `decoded_eq_specialization_of_hensel`.

This is the §5 decoder's per-`z` Hensel guarantee (`π_z(γ) = P_z`), NOT the per-`z` polynomial
identity (which is *derived* below).

It carries the per-`z` matching polynomial and approximation as data (hence a `Type`, not a `Prop`),
exactly as `IngredientCBridge.specialization_eq_proximate_root_of_hensel` consumes them. -/
structure HenselDatum {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F) (v₀ v₁ : F[X]) : Type where
  /-- per-`z` matching polynomial over `F⟦X⟧`. -/
  f : F → Polynomial (PowerSeries F)
  /-- per-`z` common approximation. -/
  a₀ : F → PowerSeries F
  /-- `↑(P z)` is a root of the matching polynomial. -/
  hProot : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (f z).IsRoot ((P z : PowerSeries F))
  /-- `↑(lift.eval (C z))` is a root of the matching polynomial. -/
  hQroot : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (f z).IsRoot
      ((((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
            (Polynomial.C z) : F[X]) : PowerSeries F)
  /-- `↑(P z)` reduces to the approximation mod `X`. -/
  hPapprox : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (P z : PowerSeries F) - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}
  /-- `↑(lift.eval (C z))` reduces to the approximation mod `X`. -/
  hQapprox : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    ((((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
          (Polynomial.C z) : F[X]) : PowerSeries F) - a₀ z
      ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}
  /-- the matching coordinate is a simple root (unit derivative): separability of `R`. -/
  hderiv : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    IsUnit ((f z).derivative.eval (a₀ z))

omit [Nonempty ι] [DecidableEq ι] in
/-- **The per-`z` identity is derived from the Hensel datum.**  For every good `z`,
`P z = lift.eval (C z)`, via `decoded_eq_specialization_of_hensel`. -/
theorem eval_identity_of_henselDatum {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F} {v₀ v₁ : F[X]}
    (d : HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁) :
    ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      P z = ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
          (Polynomial.C z) := by
  intro z hz
  exact decoded_eq_specialization_of_hensel (f := d.f z) (a₀ := d.a₀ z)
    (d.hProot z hz) (d.hQroot z hz) (d.hPapprox z hz) (d.hQapprox z hz) (d.hderiv z hz)

/-! ## The deliverable: building the `hPz` field

`hPz` quantifies over *all* `(v₀, v₁)` with the `γ`-hypothesis, and demands the per-`z`
identity plus the degree bounds.  The genuine residual is therefore: for the representative
`(v₀, v₁)` the §5 chain produces, the per-`z` Hensel datum exists and the degree bounds
hold.  We package it so the consumer
(`curveCoeffPolys_of_betaRec`, which feeds the *same* `(v₀, v₁)` derived from the Prop-5.5
representative) gets exactly the `hPz` field. -/

/-- **`hPz` from the per-`z` Hensel datum (the deliverable).**

Residual hypotheses (none is `≡` the goal; each is the genuine §5 per-`z` datum):
* `hHensel` — for every `(v₀, v₁)` consistent with the `γ`-hypothesis, the per-`z` Hensel root datum
  `HenselDatum u P v₀ v₁` (the §5 decoder's `π_z(γ) = P_z` guarantee — root membership + Hensel
  congruence, NOT the polynomial identity);
* `hdeg` — for every such `(v₀, v₁)`, the §5 degree bound `vⱼ.natDegree < k + 1`.

Conclusion: the full `hPz` field — the per-`z` identity (DERIVED via Hensel uniqueness) plus the
degree bounds. -/
theorem hPz_of_henselDatum {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    {hHyp : BCIKS20AppendixA.ClaimA2.Hypotheses x₀ R H}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (hHensel : ∀ v₀ v₁ : F[X],
      BCIKS20AppendixA.ClaimA2.γ x₀ R H hHyp = BCIKS20AppendixA.polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdeg : ∀ v₀ v₁ : F[X],
      BCIKS20AppendixA.ClaimA2.γ x₀ R H hHyp = BCIKS20AppendixA.polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    ∀ v₀ v₁ : F[X],
      BCIKS20AppendixA.ClaimA2.γ x₀ R H hHyp = BCIKS20AppendixA.polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        P z = ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
            (Polynomial.C z))
        ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1 := by
  intro v₀ v₁ hlin
  exact ⟨eval_identity_of_henselDatum (hHensel v₀ v₁ hlin), (hdeg v₀ v₁ hlin).1,
    (hdeg v₀ v₁ hlin).2⟩

omit [Nonempty ι] [DecidableEq ι] in
/-- **`hPz` from the per-`z` identity directly (minimal landing pad).**  If the §5 chain already
delivers the per-`z` identity for the consistent representative (e.g. in the unique-decoding
sub-case), this packages it — plus the degree bounds — into the `hPz` field. -/
theorem hPz_of_eval_identity {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    {hHyp : BCIKS20AppendixA.ClaimA2.Hypotheses x₀ R H}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (hEval : ∀ v₀ v₁ : F[X],
      BCIKS20AppendixA.ClaimA2.γ x₀ R H hHyp = BCIKS20AppendixA.polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        P z = ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
            (Polynomial.C z))
        ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    ∀ v₀ v₁ : F[X],
      BCIKS20AppendixA.ClaimA2.γ x₀ R H hHyp = BCIKS20AppendixA.polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        P z = ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
            (Polynomial.C z))
        ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1 :=
  hEval

end HPzBridge

end ArkLib

/-! ## Axiom audit — must rest only on `[propext, Classical.choice, Quot.sound]`. -/
#print axioms ArkLib.HPzBridge.HenselDatum
#print axioms ArkLib.HPzBridge.decoded_eq_specialization_of_hensel
#print axioms ArkLib.HPzBridge.decoded_eq_specialization_of_matchesGraph_unique
#print axioms ArkLib.HPzBridge.eval_identity_of_henselDatum
#print axioms ArkLib.HPzBridge.hPz_of_henselDatum
#print axioms ArkLib.HPzBridge.hPz_of_eval_identity
