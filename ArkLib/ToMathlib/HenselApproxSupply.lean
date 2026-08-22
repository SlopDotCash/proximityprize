/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.HenselDatumProducer
import ArkLib.ToMathlib.CurveHenselDatumProducers

/-!
# Issue #304 — per-`z` approximation/congruence supply for `HPzBridge.HenselDatum`

`HPzBridge.HenselDatum` (cores 2+4 of the #304 frontier) demands, per good `z`, a common
approximation `a₀ z : F⟦X⟧` together with the two mod-`X` congruences `hPapprox`/`hQapprox`
for the decoded `P z` and the lift specialisation
`((map C v₀) + (C X) * (map C v₁)).eval (C z)`.  This file shows those two fields are
**mechanical**: they reduce to a single per-`z` order-0 agreement
`(P z).coeff 0 = (lift.eval (C z)).coeff 0`, via the canonical approximation
`a₀ z := C ((P z).coeff 0)`.

The underlying single-polynomial bricks are already in-tree
(`FaithfulCurveExtraction.coe_sub_C_mem_span_X_iff` /
`coe_sub_C_coeff_zero_mem_span_X`, `CurveHenselDatumProducers.lean`); here they are
packaged at the `HPzBridge`/`SepHenselInput` surface:

* `coe_sub_C_coeff_zero_pair` — the two-sided congruence: if `p.coeff 0 = q.coeff 0`,
  then with `a₀ := C (p.coeff 0)` BOTH `↑p − a₀` and `↑q − a₀` lie in `(X)`.
* `approx_supply_of_coeff_zero_agree` — the per-`z` family form for an abstract competitor
  family `Qz' : F → F[X]`: order-0 agreement on the good set yields the `hPapprox`- and
  `hQapprox`-shaped congruence families at `a₀ := fun z => C ((P z).coeff 0)`.
* `henselApprox_fields_of_lift_coeff_zero_agree` — the same, specialised at the lift family
  `Qz' z := ((map C v₀) + (C X) * (map C v₁)).eval (C z)`: the conclusions are *literally*
  the `hPapprox`/`hQapprox` fields of `HPzBridge.HenselDatum`.
* `sepHenselInput_of_roots_sep_coeff_zero` — the (d) glue: per-`z` root facts + separability
  + order-0 agreement assemble a full `HenselDatumProducer.SepHenselInput` (the congruence
  fields are discharged here; `hderiv` then comes from separability inside
  `henselDatum_of_sepInput`).
* `henselDatum_of_roots_sep_coeff_zero` — the composition into `HPzBridge.HenselDatum`
  itself (ready for `HPzBridge.hPz_of_henselDatum` / `hPz_of_sepHenselInput`).

## Honest residuals

Nothing here produces the *root* facts (`hProot`/`hQroot` — the GS matching cargo), the
separability of the matching polynomial, or the order-0 agreement itself; those remain the
genuine §5 inputs of the assembled producers (each with its own production lane:
`MatchingExtractor`/`MatchingFactorLift` for the roots, `PerPlaceSeparabilitySupply` for
`hsep`).  What this file removes from the frontier is the approximation/congruence pair:
it is *equivalent* to order-0 agreement, never an independent obligation.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Prop. 5.5), §6.2 (Hensel uniqueness `π_z(γ) = P_z`), Appendix A §5.2.6.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open ProximityGap Code ReedSolomon NNReal
open scoped BigOperators

namespace ArkLib

namespace HenselApproxSupply

/-! ## The two-sided congruence brick -/

section Bricks

variable {F : Type} [Field F]

/-- **The two-sided mod-`X` congruence at the canonical approximation.**  If two polynomials
share their constant coefficient, then with `a₀ := C (p.coeff 0)` BOTH coerced power series
`↑p − a₀` and `↑q − a₀` lie in `(X)` — exactly the `hPapprox`/`hQapprox` pair of
`HPzBridge.HenselDatum` at a single `z`.  (Single-sided bricks:
`FaithfulCurveExtraction.coe_sub_C_coeff_zero_mem_span_X` / `coe_sub_C_mem_span_X_iff`.) -/
theorem coe_sub_C_coeff_zero_pair (p q : F[X]) (h : p.coeff 0 = q.coeff 0) :
    (((p : F[X]) : PowerSeries F) - PowerSeries.C (p.coeff 0)
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    ∧ (((q : F[X]) : PowerSeries F) - PowerSeries.C (p.coeff 0)
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}) :=
  ⟨FaithfulCurveExtraction.coe_sub_C_coeff_zero_mem_span_X p,
    (FaithfulCurveExtraction.coe_sub_C_mem_span_X_iff q (p.coeff 0)).mpr h.symm⟩

end Bricks

/-! ## The per-`z` family supply on the good set -/

section Family

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Per-`z` approximation supply for an abstract competitor family.**  Given any per-`z`
family `Qz' : F → F[X]` whose constant coefficient agrees with the decoded `P z` at every
good `z`, the canonical approximation `a₀ := fun z => C ((P z).coeff 0)` satisfies BOTH
congruence families — the `hPapprox`/`hQapprox` field shapes of `HPzBridge.HenselDatum`
with `Qz'` in place of the lift specialisation. -/
theorem approx_supply_of_coeff_zero_agree {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} (P Qz' : F → Polynomial F)
    (h0 : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).coeff 0 = (Qz' z).coeff 0) :
    (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z : PowerSeries F) - PowerSeries.C ((P z).coeff 0)
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    ∧ (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ((Qz' z : F[X]) : PowerSeries F) - PowerSeries.C ((P z).coeff 0)
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}) :=
  ⟨fun z _hz => FaithfulCurveExtraction.coe_sub_C_coeff_zero_mem_span_X (P z),
    fun z hz =>
      (FaithfulCurveExtraction.coe_sub_C_mem_span_X_iff (Qz' z) ((P z).coeff 0)).mpr
        (h0 z hz).symm⟩

/-- **The `hPapprox`/`hQapprox` fields of `HPzBridge.HenselDatum`, verbatim.**  Specialising
the competitor family at the lift `Qz' z := ((map C v₀) + (C X) * (map C v₁)).eval (C z)`:
per-`z` order-0 agreement on the good set produces the two congruence fields at
`a₀ := fun z => C ((P z).coeff 0)`, in `HenselDatum`'s exact field shapes. -/
theorem henselApprox_fields_of_lift_coeff_zero_agree {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} (P : F → Polynomial F) (v₀ v₁ : F[X])
    (h0 : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).coeff 0
        = (((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
              (Polynomial.C z)).coeff 0) :
    (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z : PowerSeries F) - PowerSeries.C ((P z).coeff 0)
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    ∧ (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ((((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
            (Polynomial.C z) : F[X]) : PowerSeries F) - PowerSeries.C ((P z).coeff 0)
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)}) :=
  approx_supply_of_coeff_zero_agree P
    (fun z => ((Polynomial.map Polynomial.C v₀)
        + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
          (Polynomial.C z)) h0

/-! ## The glue: `SepHenselInput` and `HenselDatum` from roots + separability + order-0 -/

/-- **`SepHenselInput` from roots, separability, and order-0 agreement.**  The approximation
and both congruence fields are discharged by this file at `a₀ z := C ((P z).coeff 0)`; the
remaining inputs are the genuine §5 cargo: the per-`z` matching polynomial `f`, the two root
facts, separability, and the order-0 agreement `h0`. -/
noncomputable def sepHenselInput_of_roots_sep_coeff_zero
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F} {v₀ v₁ : F[X]}
    (f : F → Polynomial (PowerSeries F))
    (hProot : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (f z).IsRoot ((P z : PowerSeries F)))
    (hQroot : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (f z).IsRoot
        ((((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
              (Polynomial.C z) : F[X]) : PowerSeries F))
    (h0 : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).coeff 0
        = (((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
              (Polynomial.C z)).coeff 0)
    (hsep : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (f z).Separable) :
    HenselDatumProducer.SepHenselInput
      (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁ where
  f := f
  a₀ := fun z => PowerSeries.C ((P z).coeff 0)
  hProot := hProot
  hQroot := hQroot
  hPapprox := fun z hz =>
    (henselApprox_fields_of_lift_coeff_zero_agree P v₀ v₁ h0).1 z hz
  hQapprox := fun z hz =>
    (henselApprox_fields_of_lift_coeff_zero_agree P v₀ v₁ h0).2 z hz
  hsep := hsep

/-- **`HPzBridge.HenselDatum` from roots, separability, and order-0 agreement** — the (d)
composition through `henselDatum_of_sepInput` (which derives `hderiv` from separability via
`isUnit_derivative_of_separable_of_isRoot_of_congr`).  Ready for
`HPzBridge.hPz_of_henselDatum`. -/
noncomputable def henselDatum_of_roots_sep_coeff_zero
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F} {v₀ v₁ : F[X]}
    (f : F → Polynomial (PowerSeries F))
    (hProot : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (f z).IsRoot ((P z : PowerSeries F)))
    (hQroot : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (f z).IsRoot
        ((((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
              (Polynomial.C z) : F[X]) : PowerSeries F))
    (h0 : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).coeff 0
        = (((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
              (Polynomial.C z)).coeff 0)
    (hsep : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (f z).Separable) :
    HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁ :=
  HenselDatumProducer.henselDatum_of_sepInput
    (sepHenselInput_of_roots_sep_coeff_zero f hProot hQroot h0 hsep)

end Family

end HenselApproxSupply

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.HenselApproxSupply.coe_sub_C_coeff_zero_pair
#print axioms ArkLib.HenselApproxSupply.approx_supply_of_coeff_zero_agree
#print axioms ArkLib.HenselApproxSupply.henselApprox_fields_of_lift_coeff_zero_agree
#print axioms ArkLib.HenselApproxSupply.sepHenselInput_of_roots_sep_coeff_zero
#print axioms ArkLib.HenselApproxSupply.henselDatum_of_roots_sep_coeff_zero
