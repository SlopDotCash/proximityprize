/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.HenselApproxSupply

/-!
# Issue #304 — per-`z` matching-polynomial supply for `HPzBridge.HenselDatum`

`HPzBridge.HenselDatum` (cores 1+3 of the #304 frontier) demands, per good `z`, a matching
polynomial `f z : (F⟦X⟧)[Y]` together with the two root facts `hProot`/`hQroot` for the
decoded `P z` and the lift specialisation `((map C v₀) + (C X) * (map C v₁)).eval (C z)`.
The genuine §5 cargo, however, is produced over the **polynomial** coefficient ring: the
per-`z` Guruswami–Sudan interpolant is `Qz : F[X][Y]` and the GS extractor emits the matching
factor as a divisibility **in `F[X][Y]`**
(`MatchingExtractor.matchingFactor_dvd_of_orderM_and_count`).

This file supplies the missing per-`z` matching-polynomial lane: the matching polynomial is
the power-series lift of the specialized interpolant,

```
fSeries Qz := Qz.map Polynomial.coeToPowerSeries.ringHom : (F⟦X⟧)[Y]
```

and both root fields are transported from the `F[X][Y]`-level divisibilities.

* `fSeries` — the power-series lift of a specialized bivariate (coefficientwise `F[X] ↪ F⟦X⟧`
  along `Polynomial.coeToPowerSeries.ringHom`).
* `fSeries_dvd_of_dvd` — divisibility transport: `(Y − C v) ∣ Qz` over `F[X][Y]` pushes to
  `(Y − C ↑v) ∣ fSeries Qz` over `(F⟦X⟧)[Y]` (thin `fSeries`-shaped restatement of
  `MatchingFactorLift.matchingFactor_dvd_powerSeries_of_dvd`).
* `isRoot_fSeries_of_dvd` — root transport: from the `F[X][Y]` divisibility, `↑v : F⟦X⟧` is a
  root of `fSeries Qz` (via `Polynomial.dvd_iff_isRoot`).
* `fSeries_separable` — separability transport (`Polynomial.Separable.map`): the `hderiv`
  lane needs only `Qz.Separable` at the `F[X][Y]` level.
* `henselRoots_supply_of_dvd` — the per-`z` family supply for an **abstract** competitor
  family `Qz' : F → F[X]` (so it serves both the old eval-shaped `hPz` and the faithful
  curve-family surface): `F[X][Y]`-divisibilities on the good set yield both root-fact
  families at `f := fun z => fSeries (Q z)`.
* `henselRootFields_of_lift_dvd` — the same, specialised at the lift family
  `Qz' z := ((map C v₀) + (C X) * (map C v₁)).eval (C z)`: the conclusions are *literally*
  the `hProot`/`hQroot` fields of `HPzBridge.HenselDatum`.
* `InterpolantInput` — the `F[X][Y]`-level input bundle (interpolant family, the two GS
  divisibilities, order-0 agreement, separability): the polynomial-side analogue of
  `HenselDatumProducer.MatchingDvdInput`, one ring **below** it.
* `henselDatum_of_interpolant_dvd` / `henselDatum_of_interpolantInput` — the package: a full
  `HPzBridge.HenselDatum` from the `F[X][Y]`-level data (the congruence fields come from
  order-0 agreement via `HenselApproxSupply`, the unit derivative from separability via
  `henselDatum_of_sepInput`).
* `henselDatum_of_orderM_and_count` — the composed corollary consuming the **exact**
  conclusion shape of `MatchingExtractor.matchingFactor_dvd_of_orderM_and_count`: per-`z`
  GS order-`m` graph vanishing for BOTH competitors under the Johnson counts produces the
  datum directly from GS primitives.
* `hPz_of_interpolantInput` — the end-to-end landing: `hPz` from per-representative
  `InterpolantInput` + degree bounds (through `HPzBridge.hPz_of_henselDatum`).

## Honest residuals

Nothing here fabricates the §5 content.  The residual hypotheses of the assembled producers
are exactly the recognized BCIKS20 §5 ingredients, each with its own production lane:

* the per-`z` GS divisibilities (resp. the order-`m` vanishing + Johnson counts) for the two
  competitors — `MatchingExtractor`/`GSSpecializedConditions`;
* per-`z` separability of the specialized interpolant — `PerPlaceSeparabilitySupply`;
* the per-`z` order-0 agreement `(P z).coeff 0 = (lift.eval (C z)).coeff 0` — the §5
  common-approximation fact (`HenselApproxSupply`'s residual);
* for the `hPz` landing, the degree bounds for the consistent representative.

None of these is `≡` the goal: the per-`z` polynomial identity `P z = lift.eval (C z)` is
*derived* downstream by Hensel uniqueness (`HPzBridge.hPz_of_henselDatum`).

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Prop. 5.5, the GS matching factor), §6.2 (Hensel uniqueness `π_z(γ) = P_z`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open ProximityGap Code ReedSolomon NNReal
open scoped BigOperators

namespace ArkLib

namespace HenselMatchingPolySupply

/-! ## The per-`z` matching polynomial: the power-series lift of the interpolant -/

section Bricks

variable {F : Type} [Field F]

/-- **The power-series lift of the specialized GS interpolant.**  The per-`z` interpolant
`Qz : F[X][Y]` (inner variable = the RS variable `X`, outer = `Y`) read with its coefficients
embedded `F[X] ↪ F⟦X⟧` along the canonical `Polynomial.coeToPowerSeries.ringHom` — the
matching-polynomial shape `(F⟦X⟧)[Y]` that `HPzBridge.HenselDatum.f` demands. -/
noncomputable def fSeries (Qz : F[X][Y]) : Polynomial (PowerSeries F) :=
  Qz.map Polynomial.coeToPowerSeries.ringHom

/-- **Divisibility transport into the lift.**  If the GS matching factor `Y − C v` divides the
interpolant `Qz` over `F[X][Y]` (the exact conclusion of
`MatchingExtractor.matchingFactor_dvd_of_orderM_and_count`), the power-series matching factor
`Y − C ↑v` divides `fSeries Qz` over `(F⟦X⟧)[Y]`. -/
theorem fSeries_dvd_of_dvd {Qz : F[X][Y]} {v : F[X]}
    (hdvd : (Polynomial.X - Polynomial.C v) ∣ Qz) :
    (Polynomial.X - Polynomial.C ((v : F[X]) : PowerSeries F)) ∣ fSeries Qz :=
  MatchingFactorLift.matchingFactor_dvd_powerSeries_of_dvd hdvd

/-- **Root transport into the lift.**  From the `F[X][Y]`-level matching-factor divisibility,
the coerced `↑v : F⟦X⟧` is a root of the lifted interpolant `fSeries Qz` — the exact
`hProot`/`hQroot` field shape of `HPzBridge.HenselDatum` at `f z := fSeries (Q z)`. -/
theorem isRoot_fSeries_of_dvd {Qz : F[X][Y]} {v : F[X]}
    (hdvd : (Polynomial.X - Polynomial.C v) ∣ Qz) :
    (fSeries Qz).IsRoot ((v : F[X]) : PowerSeries F) :=
  Polynomial.dvd_iff_isRoot.mp (fSeries_dvd_of_dvd hdvd)

/-- **Separability transport into the lift.**  Separability of the specialized interpolant at
the `F[X][Y]` level pushes to the lift — the `hderiv` lane of the datum needs no separate
power-series input. -/
theorem fSeries_separable {Qz : F[X][Y]} (h : Qz.Separable) : (fSeries Qz).Separable :=
  h.map

end Bricks

/-! ## The per-`z` family supply on the good set -/

section Family

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Per-`z` root supply for an abstract competitor family.**  Given per-`z` interpolants
`Q : F → F[X][Y]` and the two matching-factor divisibilities over `F[X][Y]` — for the decoded
`P z` and for ANY second family `Qz' : F → F[X]` (instantiate `Qz'` at the lift
specialisation for the old eval-shaped `hPz`, or at the faithful curve-family decodings) —
both root-fact families hold at the lifted matching polynomial `f z := fSeries (Q z)`. -/
theorem henselRoots_supply_of_dvd {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} (Q : F → F[X][Y]) (P Qz' : F → Polynomial F)
    (hPdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C (P z)) ∣ Q z)
    (hQdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C (Qz' z)) ∣ Q z) :
    (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (fSeries (Q z)).IsRoot ((P z : F[X]) : PowerSeries F))
    ∧ (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (fSeries (Q z)).IsRoot ((Qz' z : F[X]) : PowerSeries F)) :=
  ⟨fun z hz => isRoot_fSeries_of_dvd (hPdvd z hz),
    fun z hz => isRoot_fSeries_of_dvd (hQdvd z hz)⟩

/-- **The `hProot`/`hQroot` fields of `HPzBridge.HenselDatum`, verbatim.**  Specialising the
competitor family at the lift `Qz' z := ((map C v₀) + (C X) * (map C v₁)).eval (C z)`:
the two `F[X][Y]`-level GS divisibilities on the good set produce the two root fields at
`f := fun z => fSeries (Q z)`, in `HenselDatum`'s exact field shapes. -/
theorem henselRootFields_of_lift_dvd {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} (Q : F → F[X][Y]) (P : F → Polynomial F) (v₀ v₁ : F[X])
    (hPdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C (P z)) ∣ Q z)
    (hQdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C
        (((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
              (Polynomial.C z))) ∣ Q z) :
    (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (fSeries (Q z)).IsRoot ((P z : F[X]) : PowerSeries F))
    ∧ (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (fSeries (Q z)).IsRoot
        ((((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
              (Polynomial.C z) : F[X]) : PowerSeries F)) :=
  ⟨fun z hz => isRoot_fSeries_of_dvd (hPdvd z hz),
    fun z hz => isRoot_fSeries_of_dvd (hQdvd z hz)⟩

/-! ## The `F[X][Y]`-level input bundle and the assembled producers -/

/-- **The `F[X][Y]`-level input bundle** — the polynomial-side analogue of
`HenselDatumProducer.MatchingDvdInput`, one coefficient ring *below* it: the per-`z` GS
interpolants live over `F[X]` and both matching-factor divisibilities are stated in
`F[X][Y]`, the exact output ring of `MatchingExtractor.matchingFactor_dvd_of_orderM_and_count`.
The matching polynomial of the datum is *constructed* (`f z := fSeries (Q z)`), not given. -/
structure InterpolantInput {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F) (v₀ v₁ : F[X]) : Type where
  /-- per-`z` specialized GS interpolant over the polynomial coefficient ring. -/
  Q : F → F[X][Y]
  /-- the decoded `P z` is a matching factor of the interpolant, in `F[X][Y]`. -/
  hPdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (Polynomial.X - Polynomial.C (P z)) ∣ Q z
  /-- the lift specialisation is a matching factor of the interpolant, in `F[X][Y]`. -/
  hQdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (Polynomial.X - Polynomial.C
      (((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
            (Polynomial.C z))) ∣ Q z
  /-- per-`z` order-0 agreement of the two competitors (the common-approximation fact). -/
  h0 : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (P z).coeff 0
      = (((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
            (Polynomial.C z)).coeff 0
  /-- per-`z` separability of the specialized interpolant, at the `F[X][Y]` level. -/
  hsep : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (Q z).Separable

/-- **`HPzBridge.HenselDatum` from the `F[X][Y]`-level interpolant data (the package).**
The matching polynomial is the lifted interpolant `f z := fSeries (Q z)`; the two root fields
come from the GS divisibility transport; the approximation/congruence fields from order-0
agreement (`HenselApproxSupply`, at `a₀ z := C ((P z).coeff 0)`); the unit derivative from
`F[X][Y]`-level separability through `Separable.map`. -/
noncomputable def henselDatum_of_interpolant_dvd {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F} {v₀ v₁ : F[X]}
    (Q : F → F[X][Y])
    (hPdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C (P z)) ∣ Q z)
    (hQdvd : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Polynomial.X - Polynomial.C
        (((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
              (Polynomial.C z))) ∣ Q z)
    (h0 : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).coeff 0
        = (((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
              (Polynomial.C z)).coeff 0)
    (hsep : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Q z).Separable) :
    HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁ :=
  HenselApproxSupply.henselDatum_of_roots_sep_coeff_zero
    (fun z => fSeries (Q z))
    (fun z hz => isRoot_fSeries_of_dvd (hPdvd z hz))
    (fun z hz => isRoot_fSeries_of_dvd (hQdvd z hz))
    h0
    (fun z hz => fSeries_separable (hsep z hz))

/-- **`HPzBridge.HenselDatum` from the bundled `F[X][Y]`-level input.** -/
noncomputable def henselDatum_of_interpolantInput {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F} {v₀ v₁ : F[X]}
    (d : InterpolantInput (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁) :
    HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁ :=
  henselDatum_of_interpolant_dvd d.Q d.hPdvd d.hQdvd d.h0 d.hsep

/-- **The composed corollary at the GS extractor's exact hypothesis shape.**  From per-`z`
Guruswami–Sudan order-`m` graph vanishing of the interpolant `Q z` at BOTH competitors — the
decoded `P z` over `AP z` and the lift specialisation over `AQ z` — under the Johnson counts
(the exact inputs of `MatchingExtractor.matchingFactor_dvd_of_orderM_and_count`), plus the
order-0 agreement and `F[X][Y]`-level separability, the full `HPzBridge.HenselDatum`. -/
noncomputable def henselDatum_of_orderM_and_count {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F} {v₀ v₁ : F[X]}
    {N : ℕ} (ωs : Fin N ↪ F) (Q : F → F[X][Y]) (m : ℕ) (AP AQ : F → Finset (Fin N))
    (hordP : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ∀ i ∈ AP z, GuruswamiSudan.HasOrderAt (Q z) (ωs i) ((P z).eval (ωs i)) m)
    (hcountP : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ((Q z).eval (P z)).natDegree < m * (AP z).card)
    (hordQ : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ∀ i ∈ AQ z, GuruswamiSudan.HasOrderAt (Q z) (ωs i)
        ((((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
              (Polynomial.C z)).eval (ωs i)) m)
    (hcountQ : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      ((Q z).eval
        (((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
              (Polynomial.C z))).natDegree < m * (AQ z).card)
    (h0 : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).coeff 0
        = (((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
              (Polynomial.C z)).coeff 0)
    (hsep : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (Q z).Separable) :
    HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁ :=
  henselDatum_of_interpolant_dvd Q
    (fun z hz => MatchingExtractor.matchingFactor_dvd_of_orderM_and_count
      ωs (Q z) (P z) m (AP z) (hordP z hz) (hcountP z hz))
    (fun z hz => MatchingExtractor.matchingFactor_dvd_of_orderM_and_count
      ωs (Q z) _ m (AQ z) (hordQ z hz) (hcountQ z hz))
    h0 hsep

end Family

end HenselMatchingPolySupply

/-! ## The end-to-end `hPz` landing -/

section HPz

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **`hPz` from per-representative `F[X][Y]`-level interpolant data.**  The residual
hypothesis is an `InterpolantInput` producer for every linear representative consistent with
`γ` (the §5 GS cargo: interpolant + two matching divisibilities + order-0 agreement +
separability), plus the usual degree bounds.  The per-`z` identity is DERIVED by Hensel
uniqueness through `HPzBridge.hPz_of_henselDatum`. -/
theorem hPz_of_interpolantInput {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    {hHyp : BCIKS20AppendixA.ClaimA2.Hypotheses x₀ R H}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (hInput : ∀ v₀ v₁ : F[X],
      BCIKS20AppendixA.ClaimA2.γ x₀ R H hHyp = BCIKS20AppendixA.polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HenselMatchingPolySupply.InterpolantInput
        (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
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
        ∧ v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1 :=
  HPzBridge.hPz_of_henselDatum
    (fun v₀ v₁ hlin =>
      HenselMatchingPolySupply.henselDatum_of_interpolantInput (hInput v₀ v₁ hlin)) hdeg

end HPz

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.HenselMatchingPolySupply.fSeries
#print axioms ArkLib.HenselMatchingPolySupply.fSeries_dvd_of_dvd
#print axioms ArkLib.HenselMatchingPolySupply.isRoot_fSeries_of_dvd
#print axioms ArkLib.HenselMatchingPolySupply.fSeries_separable
#print axioms ArkLib.HenselMatchingPolySupply.henselRoots_supply_of_dvd
#print axioms ArkLib.HenselMatchingPolySupply.henselRootFields_of_lift_dvd
#print axioms ArkLib.HenselMatchingPolySupply.InterpolantInput
#print axioms ArkLib.HenselMatchingPolySupply.henselDatum_of_interpolant_dvd
#print axioms ArkLib.HenselMatchingPolySupply.henselDatum_of_interpolantInput
#print axioms ArkLib.HenselMatchingPolySupply.henselDatum_of_orderM_and_count
#print axioms ArkLib.hPz_of_interpolantInput
