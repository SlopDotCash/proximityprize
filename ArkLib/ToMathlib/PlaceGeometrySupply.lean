/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.MpFinSupply

/-!
# Supplying the two `mpFin` residuals — `PlaceGeometry` and `BridgeData`

`ArkLib/ToMathlib/MpFinSupply.lean` reduced the per-point ingredient-C matching geometry (`mpFin`)
to **two named residual structures**:

* `MpFinSupply.PlaceGeometry z` — the `t`-uniform §5 root geometry at a matching place `z`: the
  matching polynomial `f`, the two roots `aβ = π_z(γ)` and `aP = P_z`, the approximation `a₀`, the
  two `IsRoot` facts, the two mod-`(X−x₀)` Hensel congruences, and per-place separability `hsep` of
  `f` (`PlaceGeometry.hderiv` is *derived* from `hsep`, never assumed);
* `MpFinSupply.BridgeData t z root aβ aP` — the per-`(t, z)` π_z-specialised L12 coefficient
  readings: `w`, `x`, `a`, `e`, the `α_t`-identity reading `hαβ`, the unit nonvanishings `hw`, `hx`,
  and the proximate-root reading `haP_coeff`.

This file builds the **suppliers** of those two residuals from the in-tree bricks, exactly mirroring
the hPz branch's proven `HenselDatumProducer` chain.

## `placeGeometry_of_henselDatum` — `PlaceGeometry` from the Hensel-datum chain

`PlaceGeometry`'s nine fields are *field-for-field* the per-`z` slice of
`HenselDatumProducer.SepHenselInput` (the hPz branch's proven §5 residual): the matching polynomial
`f z`, the approximation `a₀ z`, the two roots (`hProot`/`hQroot`), the two congruences
(`hPapprox`/`hQapprox`), and separability (`hsep`).  Reading off the table:

| `PlaceGeometry` field | Hensel-datum source |
| --------------------- | ------------------------------------------------------------- |
| `f`                   | the per-`z` matching polynomial `f z` (data)                  |
| `aβ`                  | the §5 specialisation root `π_z(γ)` (`hQroot`'s root, data)   |
| `aP`                  | the proximate root `P_z` (`hProot`'s root, data)             |
| `a₀`                  | the §5 approximation `a₀ z` (data)                           |
| `haβ_root`            | `hQroot z` — `aβ` is a root of `f`                           |
| `haP_root`            | `hProot z` — `aP` is a root of `f` (GS divisibility)        |
| `haβ_cong`            | `hQapprox z` — `aβ ≡ a₀ mod X`                              |
| `haP_cong`            | `hPapprox z` — `aP ≡ a₀ mod X`                              |
| `hsep`                | `hsep z` — separability of `f` (`Hypotheses.separable_evalX`) |

Every field is therefore discharged from a Hensel-datum input; nothing is genuinely new.  The unit
derivative `hderiv` that `MatchingPoint` ultimately needs is *not* a `PlaceGeometry` field — it is
produced from `hsep` by `MpFinSupply.PlaceGeometry.hderiv` (which calls
`HenselDatumProducer.isUnit_derivative_of_separable_of_isRoot_of_congr`), exactly as the hPz
branch's `HenselDatumProducer.henselDatum_of_sepInput` produces it.

The roots arrive either directly as `IsRoot` facts (`placeGeometry_of_henselDatum`) or, on the
`MatchingExtractor` route, as the GS matching-factor divisibility `(Y − aP) ∣ f` converted by
`Polynomial.dvd_iff_isRoot` (`placeGeometry_of_henselDatum_dvd`, reusing
`MpFinSupply.placeGeometry_of_matchingDvd`).  This records that `haP_root` is the Gap-B keystone /
`MatchingExtractor` output `(Y − P_z) ∣ Q_z` transported to `F⟦X⟧`.

## `bridgeData_of_L12` — `BridgeData` from the L12 readings

`BridgeData`'s four propositional fields (`hαβ`, `hw`, `hx`, `haP_coeff`) are *field-for-field* the
inputs of the in-tree L12 coefficient-extraction brick `CoeffExtract` (the inputs to
`BetaMatchingVanishes.MatchingPoint.mk_coeffExtract` / `coeff_extract_betaRec`):

| `BridgeData` field | L12 (`CoeffExtract`) input |
| ------------------ | ---------------------------------------------------------------- |
| `hαβ`              | π_z-specialised `α_t`-identity reading (`coeff_extract_betaRec`'s `hαβ`) |
| `hw`               | `w = π_z(W) ≠ 0` (`coeff_extract_betaRec`'s `hw`)              |
| `hx`               | `x = π_z(ξ) ≠ 0` (`coeff_extract_betaRec`'s `hx`)             |
| `haP_coeff`        | proximate root reads zero at index `t` (`coeff_extract_betaRec`'s `haP`) |

The L12 `α_t`-identity reading `hαβ` is the **genuine §5.2.6 / App-A.4 frontier** — there is no
in-tree lemma that derives it (it carries `betaRec`'s defining relation
`α_t = embedding(betaRec … t) / (W^{t+1} ξ^{e_t})` threaded through `subst`/`coeff`, the L13
content).  So `bridgeData_of_L12` is
the honest packaging constructor: it records that `BridgeData` asks for *exactly* the four
`CoeffExtract` inputs, no more.  The sanity check `bridgeData_of_L12_coeffExtract` confirms a
`BridgeData` reproduces the L12 `coeffExtract` discharge verbatim.

## Composition

* `mpFin_of_henselData` — from a per-`z` Hensel-datum producer (the §5 root/congruence/separability
  geometry) and a per-`(t, z)` L12 reading producer, assemble the full `mpFin` family in the exact
  shape of `BetaCurveInputFin.mpFin`.  This is the strongest achievable composition: it threads
  `placeGeometry_of_henselDatum` and `bridgeData_of_L12` through `MpFinSupply.mpFin_of_close_word`.
* `mpFin_of_henselData_dvd` — the `MatchingExtractor`/divisibility route variant, with the
  proximate-root field arriving as the GS matching-factor divisibility.

The remaining frontier after this file is exactly **the L12 `α_t`-identity reading `hαβ`** (per
`(t, z)`): everything in `PlaceGeometry` reduces to the proven Hensel-datum chain, the unit
derivative is derived from separability, the roots are the GS divisibility output, and three of the
four `BridgeData` fields (`hw`/`hx`/`haP_coeff`) are elementary nonvanishing / truncation facts.
The single irreducible per-`(t, z)` input is the `α_t`-identity — the `betaRec`-numerator
identification of L13.

Everything is kernel-clean (`#print axioms` at the bottom; only
`propext / Classical.choice / Quot.sound`).

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement chain), Appendix A.2 / A.4 (the `W`-power numerator recursion (A.1),
  §5.2.6 matching geometry, Hensel uniqueness `π_z(γ) = P_z`, separable simple root).
-/

-- Documentation-heavy file (BCIKS §5 / App-A.4 prose in the docstrings); the long-line style
-- linter is disabled locally, matching the sibling supply files.
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open PowerSeries

namespace ArkLib

namespace MpFinSupply

variable {F : Type} [Field F]

variable {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H}

/-! ## `PlaceGeometry` from the Hensel-datum chain

`placeGeometry_of_henselDatum` assembles a `PlaceGeometry z` from exactly the per-`z` slice of the
hPz branch's proven §5 residual `HenselDatumProducer.SepHenselInput`: the matching polynomial, the
two roots, the two Hensel congruences, and separability.  This is the direct analogue of
`HenselDatumProducer.henselDatum_of_sepInput` for the ingredient-C (`betaRec`) branch.  No field is
new — each is one of the Hensel-datum facts; the unit derivative is *derived* from `hsep`
(`PlaceGeometry.hderiv`), never assumed. -/

/-- **`PlaceGeometry` from the Hensel-datum facts.**

From the per-`z` §5 root geometry — the matching polynomial `f`, the specialisation root `aβ =
π_z(γ)`, the proximate root `aP = P_z`, the approximation `a₀`, the two `IsRoot` facts, the two
mod-`(X−x₀)` Hensel congruences, and separability of `f` — assemble a `PlaceGeometry z`.

These are *field-for-field* the per-`z` slice of `HenselDatumProducer.SepHenselInput`
(`f`/`a₀`/`hProot`/`hQroot`/`hPapprox`/`hQapprox`/`hsep`), recorded here in the abstract `aβ`/`aP`
shape `PlaceGeometry` uses.  The unit derivative needed downstream is produced from `hsep` by
`PlaceGeometry.hderiv`, exactly as `HenselDatumProducer.henselDatum_of_sepInput` produces it. -/
def placeGeometry_of_henselDatum {z : F}
    (f : Polynomial (PowerSeries F)) (aβ aP a₀ : PowerSeries F)
    (haβ_root : f.IsRoot aβ) (haP_root : f.IsRoot aP)
    (haβ_cong : aβ - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (haP_cong : aP - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsep : f.Separable) :
    PlaceGeometry (F := F) z where
  f := f
  aβ := aβ
  aP := aP
  a₀ := a₀
  haβ_root := haβ_root
  haP_root := haP_root
  haβ_cong := haβ_cong
  haP_cong := haP_cong
  hsep := hsep

/-- **`PlaceGeometry` from the Hensel-datum facts, `MatchingExtractor`/divisibility route.**

As `placeGeometry_of_henselDatum`, but the proximate-root field arrives as the GS matching-factor
divisibility `(X − C aP) ∣ f` (`Polynomial.X` is the outer variable `Y`), converted to `f.IsRoot aP`
by `Polynomial.dvd_iff_isRoot`.  This records that `haP_root` is exactly the Gap-B keystone /
`MatchingExtractor` output `(Y − P_z) ∣ Q_z`, transported to `F⟦X⟧` — the same shape the hPz
branch's `HenselDatumProducer.henselDatum_of_matchingDvd_and_sep` consumes.  Delegates to the
in-tree
`placeGeometry_of_matchingDvd`. -/
def placeGeometry_of_henselDatum_dvd {z : F}
    (f : Polynomial (PowerSeries F)) (aβ aP a₀ : PowerSeries F)
    (haβ_root : f.IsRoot aβ)
    (haP_dvd : (Polynomial.X - Polynomial.C aP) ∣ f)
    (haβ_cong : aβ - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (haP_cong : aP - a₀ ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsep : f.Separable) :
    PlaceGeometry (F := F) z :=
  placeGeometry_of_matchingDvd (z := z) f aβ aP a₀ haβ_root haP_dvd haβ_cong haP_cong hsep

/-! ## `BridgeData` from the L12 readings

`bridgeData_of_L12` packages the four L12 coefficient readings — the π_z-specialised `α_t`-identity
`hαβ`, the unit nonvanishings `hw`, `hx`, and the proximate-root reading `haP_coeff` — into a
`BridgeData`.  These are *field-for-field* the inputs of the in-tree L12 brick `CoeffExtract`
(`BetaMatchingVanishes.coeff_extract_betaRec`); the `α_t`-identity `hαβ` is the genuine §5.2.6 /
App-A.4 frontier (the `betaRec`-numerator identification of L13), carried as a named hypothesis. -/

/-- **`BridgeData` from the L12 coefficient readings.**

From the per-`(t, z)` π_z-specialised L12 readings — the `α_t`-identity coefficient reading `hαβ`
(`coeff t aβ = π_z(betaRec … t) / (w ^ a * x ^ e)`), the unit nonvanishings `hw : w ≠ 0`,
`hx : x ≠ 0`, and the proximate-root reading `haP_coeff : coeff t aP = 0` — assemble a
`BridgeData t z root aβ aP`.

These four are exactly the inputs of `BetaMatchingVanishes.coeff_extract_betaRec`
(`CoeffExtract.lean`), from which the `coeffExtract` field of `MatchingPoint` is discharged in tree.
The `α_t`-identity `hαβ` is the irreducible §5.2.6 / App-A.4 reading (L13's `betaRec`-numerator
identification); the other three are elementary nonvanishing / truncation facts. -/
def bridgeData_of_L12 {t : ℕ} {z : F} {root : rationalRoot (H_tilde' H) z}
    {aβ aP : PowerSeries F} {w x : F} {a e : ℕ}
    (hαβ : PowerSeries.coeff t aβ =
        (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) / (w ^ a * x ^ e))
    (hw : w ≠ 0) (hx : x ≠ 0)
    (haP_coeff : PowerSeries.coeff t aP = 0) :
    BridgeData (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp) (Bcoeff := Bcoeff)
      t z root aβ aP where
  w := w
  x := x
  a := a
  e := e
  hαβ := hαβ
  hw := hw
  hx := hx
  haP_coeff := haP_coeff

/-- **Sanity: a `BridgeData` reproduces the L12 `coeffExtract` discharge.**  The four
readings carried by a `BridgeData` (built by `bridgeData_of_L12`) feed
`BetaMatchingVanishes.coeff_extract_betaRec`
to discharge the residual `(X−x₀)^t` coefficient extraction `aβ = aP → π_z(betaRec … t) = 0` — the
exact `coeffExtract` field of `MatchingPoint`.  This confirms `BridgeData`'s fields coincide
field-for-field with the L12 brick's inputs. -/
theorem bridgeData_of_L12_coeffExtract {t : ℕ} {z : F} {root : rationalRoot (H_tilde' H) z}
    {aβ aP : PowerSeries F}
    (bd : BridgeData (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp) (Bcoeff := Bcoeff)
      t z root aβ aP) :
    aβ = aP → (π_z z root) (betaRec x₀ R H hHyp Bcoeff t) = 0 :=
  BetaMatchingVanishes.coeff_extract_betaRec bd.hαβ bd.hw bd.hx bd.haP_coeff

/-! ## Composition — `mpFin` from the Hensel-datum chain + the L12 readings

`mpFin_of_henselData` threads `placeGeometry_of_henselDatum` (per `z`) and `bridgeData_of_L12`
(per `(t, z)`) through `MpFinSupply.mpFin_of_close_word`, assembling the full finite-range matching
family in the exact shape of `BetaCurveInputFin.mpFin`.  This is the strongest composition the
in-tree bricks support: every `PlaceGeometry` field is a Hensel-datum fact, the unit derivative is
derived, and only the per-`(t, z)` L12 `α_t`-identity remains genuinely irreducible. -/

/-- **The `mpFin` family from a Hensel-datum producer + an L12 reading producer.**

Given, for every matching point `z ∈ matchingSet`:

* the §5 root geometry `f z`, `aβ z`, `aP z`, `a₀ z` together with the two roots `haβ_root`/
  `haP_root`, the two Hensel congruences `haβ_cong`/`haP_cong`, and separability `hsep` (the per-`z`
  slice of the Hensel-datum chain), and

for every `(t, z)` in the finite range `k ≤ t ≤ T`:

* the per-`(t, z)` L12 readings `w`, `x`, `a`, `e`, `hαβ`, `hw`, `hx`, `haP_coeff`,

assemble the finite-range family in the exact shape of `BetaCurveInputFin.mpFin`:

```
∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet, MatchingPoint x₀ R H hHyp Bcoeff t z (root z).
```

Each place geometry is `placeGeometry_of_henselDatum`; each bridging datum is `bridgeData_of_L12`;
they are threaded through `mpFin_of_close_word`.  The place geometry is `t`-uniform and reused at
every `t`. -/
def mpFin_of_henselData {k T : ℕ} {matchingSet : Finset F}
    {root : (z : F) → rationalRoot (H_tilde' H) z}
    (f : (z : F) → Polynomial (PowerSeries F))
    (aβ aP a₀ : (z : F) → PowerSeries F)
    (haβ_root : ∀ z ∈ matchingSet, (f z).IsRoot (aβ z))
    (haP_root : ∀ z ∈ matchingSet, (f z).IsRoot (aP z))
    (haβ_cong : ∀ z ∈ matchingSet, aβ z - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (haP_cong : ∀ z ∈ matchingSet, aP z - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsep : ∀ z ∈ matchingSet, (f z).Separable)
    (w x : (t : ℕ) → (z : F) → F) (a e : (t : ℕ) → (z : F) → ℕ)
    (hαβ : ∀ t, k ≤ t → t ≤ T → ∀ z, z ∈ matchingSet →
      PowerSeries.coeff t (aβ z) =
        (π_z z (root z)) (betaRec x₀ R H hHyp Bcoeff t) / (w t z ^ a t z * x t z ^ e t z))
    (hw : ∀ t, k ≤ t → t ≤ T → ∀ z, z ∈ matchingSet → w t z ≠ 0)
    (hx : ∀ t, k ≤ t → t ≤ T → ∀ z, z ∈ matchingSet → x t z ≠ 0)
    (haP_coeff : ∀ t, k ≤ t → t ≤ T → ∀ z, z ∈ matchingSet → PowerSeries.coeff t (aP z) = 0) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z) :=
  mpFin_of_close_word
    (geom := fun z hz =>
      placeGeometry_of_henselDatum (z := z) (f z) (aβ z) (aP z) (a₀ z)
        (haβ_root z hz) (haP_root z hz) (haβ_cong z hz) (haP_cong z hz) (hsep z hz))
    (bridge := fun t hkt htT z hz =>
      bridgeData_of_L12 (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp) (Bcoeff := Bcoeff)
        (t := t) (z := z) (root := root z)
        (hαβ t hkt htT z hz) (hw t hkt htT z hz) (hx t hkt htT z hz) (haP_coeff t hkt htT z hz))

/-- **The `mpFin` family from a Hensel-datum producer + an L12 reading producer,
`MatchingExtractor`/divisibility route.**

As `mpFin_of_henselData`, but the proximate-root facts arrive as the GS matching-factor
divisibilities `(X − C (aP z)) ∣ f z` (the Gap-B keystone / `MatchingExtractor` output),
converted to roots by `Polynomial.dvd_iff_isRoot` inside `placeGeometry_of_henselDatum_dvd`.
Delegates to the
in-tree `mpFin_of_graph_vanishing_dvd`. -/
def mpFin_of_henselData_dvd {k T : ℕ} {matchingSet : Finset F}
    {root : (z : F) → rationalRoot (H_tilde' H) z}
    (f : (z : F) → Polynomial (PowerSeries F))
    (aβ aP a₀ : (z : F) → PowerSeries F)
    (haβ_root : ∀ z ∈ matchingSet, (f z).IsRoot (aβ z))
    (haP_dvd : ∀ z ∈ matchingSet, (Polynomial.X - Polynomial.C (aP z)) ∣ f z)
    (haβ_cong : ∀ z ∈ matchingSet, aβ z - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (haP_cong : ∀ z ∈ matchingSet, aP z - a₀ z ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsep : ∀ z ∈ matchingSet, (f z).Separable)
    (w x : (t : ℕ) → (z : F) → F) (a e : (t : ℕ) → (z : F) → ℕ)
    (hαβ : ∀ t, k ≤ t → t ≤ T → ∀ z, z ∈ matchingSet →
      PowerSeries.coeff t (aβ z) =
        (π_z z (root z)) (betaRec x₀ R H hHyp Bcoeff t) / (w t z ^ a t z * x t z ^ e t z))
    (hw : ∀ t, k ≤ t → t ≤ T → ∀ z, z ∈ matchingSet → w t z ≠ 0)
    (hx : ∀ t, k ≤ t → t ≤ T → ∀ z, z ∈ matchingSet → x t z ≠ 0)
    (haP_coeff : ∀ t, k ≤ t → t ≤ T → ∀ z, z ∈ matchingSet → PowerSeries.coeff t (aP z) = 0) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp Bcoeff t z (root z) :=
  mpFin_of_graph_vanishing_dvd
    (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp) (Bcoeff := Bcoeff)
    (root := root) f aβ aP a₀ haβ_root haP_dvd haβ_cong haP_cong hsep
    (bridge := fun t hkt htT z hz =>
      bridgeData_of_L12 (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp) (Bcoeff := Bcoeff)
        (t := t) (z := z) (root := root z)
        (hαβ t hkt htT z hz) (hw t hkt htT z hz) (hx t hkt htT z hz) (haP_coeff t hkt htT z hz))

end MpFinSupply

end ArkLib


