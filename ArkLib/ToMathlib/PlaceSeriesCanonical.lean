/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.PlaceGeometrySupply
import ArkLib.ToMathlib.BetaRecGenuineBridge

/-!
# Issue #304 — the canonical per-place Hensel series (the `hαβ` slot, discharged by definition)

The `MpFinSupply.BridgeData` bundle carries the per-`(t, z)` L12 `α_t`-identity

```
hαβ : coeff t (aβ z) = π_z(betaRec … t) / (w ^ a * x ^ e)
```

as a *named hypothesis* relating an abstractly-given per-place series `aβ z` to the place-read
numerator.  But the §5 instantiation gets to *choose* `aβ z`: the honest canonical choice is the
series **defined** by the Claim-A.2 normalized place readings,

```
aBetaPlace … z root := mk (fun t => π_z(betaRec … t) / (π_z(W_𝒪)^{t+1} · π_z(ξ)^{e_t})),
```

for which `hαβ` holds **by definition** (`coeff_mk`).  This file pins that choice and rebuilds the
`BridgeData` constructor from it:

* `aBetaPlace` / `coeff_aBetaPlace` — the canonical per-place series and its definitional reading;
* `bridgeData_of_aBetaPlace` — `BridgeData` at the canonical series from just the two unit
  nonvanishings `hw`/`hx` and the proximate-root truncation `haP_coeff`: the `hαβ` slot is gone;
* `pi_z_W_eq_one_of_monic` / `bridgeData_of_aBetaPlace_monic` — for **monic** `H` the `W`-reading
  is literally `1` (`W_𝒪 = mk (C 1) = 1`, and `π_z` is a ring hom), so `hw` is free as well: the
  per-`(t, z)` input shrinks to `hx : π_z(ξ) ≠ 0` (a per-`z` discriminant-style condition) plus
  the uniform truncation reading.

## What this changes about the open problem

After this file, the mpPoint front no longer contains an `hαβ`-shaped residual at all: with
`aβ z := aBetaPlace … z (root z)`, the remaining genuine content of `MatchingPoint` production is
exactly the per-`z` `PlaceGeometry` for the canonical series — i.e. that `aBetaPlace` is a root of
the per-`z` matching polynomial congruent to the common approximation (`haβ_root`/`haβ_cong`).
In the monic case `betaRec (BcoeffSigned …) = βHensel` (`BetaRecGenuineBridge`), so those root
facts are place-images of the PROVEN genuine root relation `gammaGenuine_root` — the remaining
bridge being the coefficient-wise place map on the denominators-avoiding locus.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  Appendix A.4 (Claim A.2 normalization `α_t = β_t / (W^{t+1}·ξ^{e_t})`), §5.2.6 (place readings).
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

namespace PlaceSeriesCanonical

open MpFinSupply BetaRecGenuineBridge

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The canonical per-place Hensel series.**  At the place `(z, root)`, the series whose `t`-th
coefficient is the Claim-A.2 normalized place reading
`π_z(betaRec … t) / (π_z(W_𝒪)^{t+1} · π_z(ξ)^{e_t})`. -/
noncomputable def aBetaPlace (x₀ : F) (R : F[X][X][Y]) (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (z : F) (root : rationalRoot (H_tilde' H) z) : PowerSeries F :=
  PowerSeries.mk fun t =>
    (π_z z root) (betaRec x₀ R H hHyp Bcoeff t)
      / ((π_z z root) (W_𝒪 H) ^ (t + 1)
          * (π_z z root) (ξ x₀ R H hHyp) ^ henselDenominatorExponent t)

@[simp] theorem coeff_aBetaPlace (x₀ : F) (R : F[X][X][Y]) (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H)
    (z : F) (root : rationalRoot (H_tilde' H) z) (t : ℕ) :
    PowerSeries.coeff t (aBetaPlace x₀ R hHyp Bcoeff z root)
      = (π_z z root) (betaRec x₀ R H hHyp Bcoeff t)
          / ((π_z z root) (W_𝒪 H) ^ (t + 1)
              * (π_z z root) (ξ x₀ R H hHyp) ^ henselDenominatorExponent t) :=
  PowerSeries.coeff_mk t _

/-- **`BridgeData` at the canonical series — the `hαβ` slot is definitional.**  The per-`(t, z)`
inputs shrink to the two unit nonvanishings and the proximate-root truncation reading. -/
noncomputable def bridgeData_of_aBetaPlace {x₀ : F} {R : F[X][X][Y]}
    {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H}
    {t : ℕ} {z : F} {root : rationalRoot (H_tilde' H) z} {aP : PowerSeries F}
    (hw : (π_z z root) (W_𝒪 H) ≠ 0)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    (haP_coeff : PowerSeries.coeff t aP = 0) :
    BridgeData (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp) (Bcoeff := Bcoeff)
      t z root (aBetaPlace x₀ R hHyp Bcoeff z root) aP where
  w := (π_z z root) (W_𝒪 H)
  x := (π_z z root) (ξ x₀ R H hHyp)
  a := t + 1
  e := henselDenominatorExponent t
  hαβ := coeff_aBetaPlace x₀ R hHyp Bcoeff z root t
  hw := hw
  hx := hx
  haP_coeff := haP_coeff

/-! ## The monic case: the `W`-reading is literally `1` -/

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- For monic `H`, the integral `W`-element is `1`: `W_𝒪 = mk (C H.leadingCoeff) = mk (C 1) = 1`. -/
theorem W_O_eq_one_of_monic (hlc : H.leadingCoeff = 1) : W_𝒪 H = 1 := by
  rw [W_𝒪, hlc, Polynomial.C_1, map_one]

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- For monic `H`, the per-place `W`-reading is `1` (a ring hom sends `1` to `1`). -/
theorem pi_z_W_eq_one_of_monic (hlc : H.leadingCoeff = 1)
    {z : F} (root : rationalRoot (H_tilde' H) z) :
    (π_z z root) (W_𝒪 H) = 1 := by
  rw [W_O_eq_one_of_monic hlc, map_one]

/-- **`BridgeData` at the canonical series, monic case.**  `hw` is free
(`π_z(W_𝒪) = 1 ≠ 0`); the only remaining per-`z` unit input is the `ξ`-reading nonvanishing. -/
noncomputable def bridgeData_of_aBetaPlace_monic {x₀ : F} {R : F[X][X][Y]}
    {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H}
    {t : ℕ} {z : F} {root : rationalRoot (H_tilde' H) z} {aP : PowerSeries F}
    (hlc : H.leadingCoeff = 1)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    (haP_coeff : PowerSeries.coeff t aP = 0) :
    BridgeData (x₀ := x₀) (R := R) (H := H) (hHyp := hHyp) (Bcoeff := Bcoeff)
      t z root (aBetaPlace x₀ R hHyp Bcoeff z root) aP :=
  bridgeData_of_aBetaPlace
    (by rw [pi_z_W_eq_one_of_monic hlc root]; exact one_ne_zero) hx haP_coeff

/-! ## The monic canonical coefficients: the numerator reading is the `βHensel` reading -/

/-- At the signed canonical family, the canonical per-place series reads the genuine `(A.1)`
numerators: its `t`-th coefficient is `π_z(βHensel … t) / (π_z(W_𝒪)^{t+1} · π_z(ξ)^{e_t})`
(by `BetaRecGenuineBridge.betaRec_BcoeffSigned_eq_βHensel`). -/
theorem coeff_aBetaPlace_BcoeffSigned (x₀ : F) (R : F[X][X][Y]) (hHyp : Hypotheses x₀ R H)
    (z : F) (root : rationalRoot (H_tilde' H) z) (t : ℕ) :
    PowerSeries.coeff t (aBetaPlace x₀ R hHyp (BcoeffSigned H x₀ R) z root)
      = (π_z z root) (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp t)
          / ((π_z z root) (W_𝒪 H) ^ (t + 1)
              * (π_z z root) (ξ x₀ R H hHyp) ^ henselDenominatorExponent t) := by
  rw [coeff_aBetaPlace, betaRec_BcoeffSigned_eq_βHensel]

end PlaceSeriesCanonical

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.PlaceSeriesCanonical.aBetaPlace
#print axioms ArkLib.PlaceSeriesCanonical.coeff_aBetaPlace
#print axioms ArkLib.PlaceSeriesCanonical.bridgeData_of_aBetaPlace
#print axioms ArkLib.PlaceSeriesCanonical.W_O_eq_one_of_monic
#print axioms ArkLib.PlaceSeriesCanonical.pi_z_W_eq_one_of_monic
#print axioms ArkLib.PlaceSeriesCanonical.bridgeData_of_aBetaPlace_monic
#print axioms ArkLib.PlaceSeriesCanonical.coeff_aBetaPlace_BcoeffSigned
