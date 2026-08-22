/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.MatchingExtractor
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Lifting GS matching factors from `F[X][Y]` to `(F⟦X⟧)[Y]` (the §5 coefficient-ring bridge)

The Guruswami–Sudan matching-extractor (`ArkLib.MatchingExtractor`) produces the per-`z` matching
factor of the §5 interpolant as a divisibility statement **over `F[X][Y]`**:

```
(Polynomial.X - Polynomial.C Pz) ∣ Qz        -- in F[X][Y]
```

(`MatchingExtractor.matchingFactor_dvd_of_orderM_and_count`).  The Hensel-uniqueness route to the
`hPz` field, however, lives **over the power-series coefficient ring `F⟦X⟧`**:
`HenselDatumProducer.MatchingDvdInput` (and `HPzBridge.HenselDatum`) want the matching factor in
`(PowerSeries F)[Y]`:

```
(Polynomial.X - Polynomial.C ((Pz : PowerSeries F))) ∣ f z      -- in (PowerSeries F)[Y]
```

These are statements over *different* coefficient rings, so the GS extractor's `F[X][Y]` output is
**not directly consumable** by the matching-divisibility Hensel route.  This file supplies the missing
connective: the coefficient-ring pushforward along the canonical ring hom

```
Polynomial.coeToPowerSeries.ringHom : F[X] →+* PowerSeries F
```

(the `X`-adic embedding `F[X] ↪ F⟦X⟧`).  Concretely:

* `map_coeToPowerSeries` — `coeToPowerSeries.ringHom Pz = (Pz : PowerSeries F)` (the coercion
  used in `MatchingDvdInput`/`HenselDatum` is exactly this ring-hom map);
* `map_matchingFactor` — the matching factor's image: `(X − C Pz).map ↑
  = X − C (↑Pz)`;
* `matchingFactor_dvd_powerSeries_of_dvd` — divisibility transport: `(X − C Pz) ∣ Qz` over
  `F[X][Y]` ⟹ `(X − C ↑Pz) ∣ Qz.map ↑` over `(PowerSeries F)[Y]`;
* `matchingFactor_dvd_powerSeries_of_orderM_and_count` and
  `..._of_weightedDegree` — the end-to-end forms: from the GS order-`m` graph vanishing (resp. the
  `(1,k)`-weighted-degree Johnson budget), the lifted matching factor `Y − ↑Pz` divides the lifted
  interpolant `Qz.map (mapRingHom ↑)` directly in `(PowerSeries F)[Y]`, i.e. the exact
  `MatchingDvdInput.hPdvd`/`hQdvd` shape.

Nothing here is `≡` the `hPz` goal: it is a faithful divisibility transport (using
`Polynomial.map_dvd` and `Polynomial.coeff_coe`) that lets the genuine in-tree GS extractor output be
consumed by the Hensel-datum producer over `F⟦X⟧`.

Everything is kernel-clean — `#print axioms` at the bottom rests only on
`[propext, Classical.choice, Quot.sound]`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (the GS matching factor and the per-`z` Hensel lift over `F⟦X⟧`).
-/

open Polynomial Polynomial.Bivariate

namespace ArkLib

namespace MatchingFactorLift

variable {F : Type} [Field F] {n : ℕ}

/-- The coercion `(p : PowerSeries F)` used by `MatchingDvdInput`/`HenselDatum` is the image of the
canonical ring hom `Polynomial.coeToPowerSeries.ringHom : F[X] →+* PowerSeries F`. -/
theorem map_coeToPowerSeries (p : F[X]) :
    Polynomial.coeToPowerSeries.ringHom p = (p : PowerSeries F) := by
  exact Polynomial.coeToPowerSeries.ringHom_apply

/-- The image of the GS matching factor `Y − C Pz` under the coefficient-ring pushforward
`coeToPowerSeries.ringHom` is the power-series matching factor `Y − C (↑Pz)`. -/
theorem map_matchingFactor (Pz : F[X]) :
    (Polynomial.X - Polynomial.C Pz).map
        Polynomial.coeToPowerSeries.ringHom
      = Polynomial.X - Polynomial.C ((Pz : PowerSeries F)) := by
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_coeToPowerSeries]

/-- **The coefficient-ring divisibility transport.**  If the GS matching factor `Y − C Pz` divides
the interpolant `Qz` over `F[X][Y]`, then the power-series matching factor `Y − C (↑Pz)` divides the
pushforward `Qz.map (mapRingHom ↑)` over `(PowerSeries F)[Y]` — exactly the `MatchingDvdInput`
divisibility shape. -/
theorem matchingFactor_dvd_powerSeries_of_dvd {Qz : F[X][Y]} {Pz : F[X]}
    (hdvd : (Polynomial.X - Polynomial.C Pz) ∣ Qz) :
    (Polynomial.X - Polynomial.C ((Pz : PowerSeries F))) ∣
      Qz.map Polynomial.coeToPowerSeries.ringHom := by
  have h := Polynomial.map_dvd Polynomial.coeToPowerSeries.ringHom hdvd
  rwa [map_matchingFactor] at h

/-- **End-to-end (order-`m` form).**  From the Guruswami–Sudan order-`m` graph vanishing of the
interpolant `Qz` at the close-codeword graph of `Pz` over an agreement set `A`, under the Johnson
count `deg (Qz.eval Pz) < m · #A`, the lifted matching factor `Y − C (↑Pz)` divides the lifted
interpolant `Qz.map (mapRingHom ↑)` over `(PowerSeries F)[Y]`.  This delivers a
`MatchingDvdInput.hPdvd`/`hQdvd` field straight from the in-tree GS extractor. -/
theorem matchingFactor_dvd_powerSeries_of_orderM_and_count
    (ωs : Fin n ↪ F) (Qz : F[X][Y]) (Pz : F[X]) (m : ℕ) (A : Finset (Fin n))
    (hord : ∀ i ∈ A, GuruswamiSudan.HasOrderAt Qz (ωs i) (Pz.eval (ωs i)) m)
    (hcount : (Qz.eval Pz).natDegree < m * A.card) :
    (Polynomial.X - Polynomial.C ((Pz : PowerSeries F))) ∣
      Qz.map Polynomial.coeToPowerSeries.ringHom :=
  matchingFactor_dvd_powerSeries_of_dvd
    (MatchingExtractor.matchingFactor_dvd_of_orderM_and_count ωs Qz Pz m A hord hcount)

/-- **End-to-end (weighted-degree form).**  The common caller-facing variant: from `deg Pz ≤ k` and
the `(1,k)`-weighted degree of `Qz` below the Johnson budget `m · #A`, the lifted matching factor
`Y − C (↑Pz)` divides the lifted interpolant over `(PowerSeries F)[Y]`. -/
theorem matchingFactor_dvd_powerSeries_of_weightedDegree
    (ωs : Fin n ↪ F) (Qz : F[X][Y]) (Pz : F[X]) (m k : ℕ) (A : Finset (Fin n))
    (hPdeg : Pz.natDegree ≤ k)
    (hord : ∀ i ∈ A, GuruswamiSudan.HasOrderAt Qz (ωs i) (Pz.eval (ωs i)) m)
    (hwcount : natWeightedDegree Qz 1 k < m * A.card) :
    (Polynomial.X - Polynomial.C ((Pz : PowerSeries F))) ∣
      Qz.map Polynomial.coeToPowerSeries.ringHom :=
  matchingFactor_dvd_powerSeries_of_dvd
    (MatchingExtractor.matchingFactor_dvd_of_weightedDegree ωs Qz Pz m k A hPdeg hord hwcount)

end MatchingFactorLift

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.MatchingFactorLift.map_coeToPowerSeries
#print axioms ArkLib.MatchingFactorLift.map_matchingFactor
#print axioms ArkLib.MatchingFactorLift.matchingFactor_dvd_powerSeries_of_dvd
#print axioms ArkLib.MatchingFactorLift.matchingFactor_dvd_powerSeries_of_orderM_and_count
#print axioms ArkLib.MatchingFactorLift.matchingFactor_dvd_powerSeries_of_weightedDegree
