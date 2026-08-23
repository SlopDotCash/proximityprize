/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CoreA6deepGeomMinorSharp
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CoreA6deep_MinorTractability
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CoreA6_NovelInvariant

/-!
# Core A6deep CARDINALITY discharge - the geometric minor-degree sharpening, COMPOSED through the
# Bezout image bound, DISCHARGES `MinorImageLeBudget` for complete-homogeneous readouts (#444)

## The gap this file closes (the composition `_CoreA6deepGeomMinorSharp` named but never stated)

`_CoreA6deepGeomMinorSharp` proved the SHARP *degree* of the structured (complete-homogeneous /
geometric) determinantal minor:

  `geomMinor_natDegree` :  `deg (g_a g_{b-1} - g_{a-1} g_b) = b - 1`   ( `< D = b` ),

but ONLY as a standalone `F[X]` degree statement.  Its docstring CLAIMS this "discharges A6deep's
`MinorImageLeBudget` clause FOR the complete-homogeneous readout structure", yet the file never
states the *cardinality* theorem - it never plugs the sharpened degree back through
`_CoreA6deep_MinorTractability.forcedGammaImage_card_le_degree`
(`|forcedGammaImage| <= minorPoly.natDegree`).  That composition is the actual brick: it is what
turns "minor degree `b-1 < n`" into the image-count budget `|forcedGammaImage| <= b-1 <= n`, i.e.
the `Prop` `MinorImageLeBudget Wset α β nodes n` *holding outright* (not assumed as a hypothesis)
for the geometric readout structure.

The one missing link is the BRIDGE identifying the abstract `minorPoly` at the geometric readout
rows with the concrete `geomMinor`:

> **`minorPoly_geom_eq`** :  `minorPoly (g_a) (g_{a-1}) (g_b) (g_{b-1}) = X^a * g_{b-a-1}`,

which is immediate from `minorPoly`'s definition (`pα·pβm − pαm·pβ`) and `geomMinor_eq`.  With that
bridge the generic Bezout chain instantiates at the geometric rows, and the sharpened degree `b-1`
flows straight into the image cardinality.

## What is PROVEN here (axiom-clean, no `sorry`)

* **`minorPoly_geom_eq`** (BRIDGE) - the abstract univariate minor polynomial at the geometric
  readout rows `pα = g_a, pαm = g_{a-1}, pβ = g_b, pβm = g_{b-1}` equals the concrete geometric
  minor `X^a * g_{b-a-1}`.
* **`minorPoly_geom_natDegree`** - `deg (minorPoly (g_a) (g_{a-1}) (g_b) (g_{b-1})) = b - 1`, the
  sharpened degree carried to the *abstract* minor object (so it can feed the Bezout bound).
* **`minorPoly_geom_ne_zero`** - the geometric minor polynomial is `!= 0` (non-vacuity of the
  Bezout count).
* **`forcedGammaImage_card_le_geom`** (the SHARPENED A6deep bound) - under the (1-PARAM) structure
  with the readouts the geometric rows (`hΔ` factoring through `minorPoly (g_a) … (g_{b-1})`), the
  forced-γ image is bounded by the SHARP degree:

    `|forcedGammaImage| <= b - 1`,

  HALVING the generic `forcedGammaImage_card_le_two_mul_span`'s `2D` for the complete-homogeneous
  structure.
* **`minorImageLeBudget_geom`** (HEADLINE - the budget discharge) - whenever `b - 1 <= n` (the worst
  geometric row degree fits the prize budget `q*eps* ~ n`), the named `Prop`
  `MinorImageLeBudget Wset α β nodes n` **HOLDS** for the geometric readout structure.  Every prior
  site CONSUMED `MinorImageLeBudget` as an open hypothesis (`Dstar_le_budget_of_residual`); this is
  the FIRST theorem that PRODUCES it - for the structured (complete-homogeneous) readouts.
* **`Dstar_le_budget_geom`** - chained end-to-end: the depth-`(>= 2)` binding count `|Bad| <= n` is
  delivered *unconditionally* (no `MinorImageLeBudget` hypothesis) once the readouts are geometric
  and `b - 1 <= n`.

## Honest scope (rules 1,3,4,5,6 + ASYMPTOTIC GUARD)

EXTEND-PROVEN NON-MOMENT structural brick on the brief's named determinantal/Bezout lever.  It is
the COMPOSITION the sharpening file named but never stated: it carries the sharpened degree `b-1`
through the proven Bezout image bound to DISCHARGE the named budget `Prop` for the
complete-homogeneous readouts (the first PRODUCER of `MinorImageLeBudget`, vs every prior consumer).

It is NOT a closure of CORE.  It discharges the budget clause only for the GEOMETRIC readout
structure (a fixed monomial direction) and STILL inherits A6deep's open residual: the
**direction-uniformity** at the binding depth (`PerDirectionParam` / BCHKS 1.12 budget input - the
1-PARAM `hfac`/`hΔ` factoring is carried as a hypothesis, not proven for all binding directions),
which this file does not touch.  Field-universal `F[X]` algebra; thinness enters only via the
discrete-log structure that makes the readouts geometric.  NO capacity / beyond-Johnson / sub-linear
/ growth-law claim; the cliff-at-`n/2` (the delta*/incidence object) is UNTOUCHED.  CORE
`M(mu_n) <= C * sqrt(n * log(p/n))` stays **OPEN**.
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.CoreA6deep

open ArkLib.ProximityGap.CoreA6

variable {F : Type*} [Field F]

/-! ## 1. The bridge: the abstract minor polynomial at the geometric readout rows -/

/-- **BRIDGE - the abstract minor polynomial at the geometric readout rows.**  Instantiating
`_CoreA6deep_MinorTractability.minorPoly` (`= pα·pβm − pαm·pβ`) at the complete-homogeneous readouts
`pα = g_a`, `pαm = g_{a-1}`, `pβ = g_b`, `pβm = g_{b-1}` gives exactly the concrete geometric minor:

  `minorPoly (g_a) (g_{a-1}) (g_b) (g_{b-1}) = X^a * g_{b-a-1}`   (`1 <= a < b`).

So the generic Bezout chain, instantiated at the geometric rows, sees the sharpened single
monomial-times-geometric term. -/
theorem minorPoly_geom_eq {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    minorPoly (F := F) (geomPoly a) (geomPoly (a - 1)) (geomPoly b) (geomPoly (b - 1))
      = X ^ a * (geomPoly (b - a - 1)) := by
  unfold minorPoly
  exact geomMinor_eq ha hab

/-- **The sharpened degree carried to the abstract minor object.**  `1 <= a < b` ⟹
`deg (minorPoly (g_a) (g_{a-1}) (g_b) (g_{b-1})) = b - 1` - the same sharp `b-1` as
`geomMinor_natDegree`, now on the `minorPoly` form that feeds `forcedGammaImage_card_le_degree`. -/
theorem minorPoly_geom_natDegree {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    (minorPoly (F := F) (geomPoly a) (geomPoly (a - 1)) (geomPoly b)
      (geomPoly (b - 1))).natDegree = b - 1 := by
  unfold minorPoly
  exact geomMinor_natDegree ha hab

/-- **Non-vacuity of the abstract geometric minor.**  `1 <= a < b` ⟹
`minorPoly (g_a) (g_{a-1}) (g_b) (g_{b-1}) != 0`, so the Bezout root-count is a genuine finite
bound, not the vacuous `deg 0`. -/
theorem minorPoly_geom_ne_zero {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    minorPoly (F := F) (geomPoly a) (geomPoly (a - 1)) (geomPoly b) (geomPoly (b - 1)) ≠ 0 := by
  unfold minorPoly
  exact geomMinor_ne_zero ha hab

/-! ## 2. The sharpened forced-γ image bound (`<= b - 1`, halving the generic `2D`) -/

variable {ι : Type*} [DecidableEq ι]

/-- **The SHARPENED A6deep image bound for geometric readouts: `|forcedGammaImage| <= b - 1`.**
Under the (1-PARAM) structure with the readouts the complete-homogeneous rows - forced-γ a function
of the parameter (`hfac`) and the minor an evaluation of `minorPoly (g_a) (g_{a-1}) (g_b) (g_{b-1})`
(`hΔ`) - the forced-γ image satisfies

  `|forcedGammaImage| <= b - 1`,

via `_CoreA6deep_MinorTractability.forcedGammaImage_card_le_degree` plugged with the sharp degree
`minorPoly_geom_natDegree`.  This HALVES the generic `forcedGammaImage_card_le_two_mul_span`'s `2D`
budget (and lands strictly below `D = b`) for the complete-homogeneous readout structure. -/
theorem forcedGammaImage_card_le_geom [DecidableEq F]
    (Wset : Finset ι) (α β : ℕ) (nodes : ι → List F) (param : ι → F)
    (γfun : F → F) {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hfac : ∀ w ∈ minorLocus Wset α β nodes,
      forcedGammaOf α β nodes w = γfun (param w))
    (hΔ : ∀ w ∈ minorLocus Wset α β nodes,
      plueckerMinor α β (nodes w)
        = (minorPoly (geomPoly a) (geomPoly (a - 1)) (geomPoly b)
            (geomPoly (b - 1))).eval (param w)) :
    (forcedGammaImage Wset α β nodes).card ≤ b - 1 := by
  have hbound := forcedGammaImage_card_le_degree Wset α β nodes param γfun
    (geomPoly a) (geomPoly (a - 1)) (geomPoly b) (geomPoly (b - 1))
    hfac hΔ (minorPoly_geom_ne_zero ha hab)
  rwa [minorPoly_geom_natDegree ha hab] at hbound

/-! ## 3. HEADLINE - the budget discharge: `MinorImageLeBudget` HOLDS for geometric readouts -/

/-- **HEADLINE - the budget `Prop` discharge.**  For the geometric readout structure, whenever the
worst row degree fits the prize budget (`b - 1 <= n`, i.e. the span `D = b <= n + 1`, prize budget
`q*eps* ~ n`), the named `Prop`

  `MinorImageLeBudget Wset α β nodes n`   (`= |forcedGammaImage| <= n`)

**HOLDS** - it is no longer an open hypothesis.  Every prior site (`Dstar_le_budget_of_residual`)
CONSUMED `MinorImageLeBudget` as a black-box residual; this is the FIRST theorem that PRODUCES it,
for the complete-homogeneous readouts, by composing the sharpened geometric minor degree `b-1`
through the proven Bezout image bound. -/
theorem minorImageLeBudget_geom [DecidableEq F]
    (Wset : Finset ι) (α β : ℕ) (nodes : ι → List F) (param : ι → F)
    (γfun : F → F) {a b n : ℕ} (ha : 1 ≤ a) (hab : a < b) (hbn : b - 1 ≤ n)
    (hfac : ∀ w ∈ minorLocus Wset α β nodes,
      forcedGammaOf α β nodes w = γfun (param w))
    (hΔ : ∀ w ∈ minorLocus Wset α β nodes,
      plueckerMinor α β (nodes w)
        = (minorPoly (geomPoly a) (geomPoly (a - 1)) (geomPoly b)
            (geomPoly (b - 1))).eval (param w)) :
    MinorImageLeBudget Wset α β nodes n :=
  le_trans (forcedGammaImage_card_le_geom Wset α β nodes param γfun ha hab hfac hΔ) hbn

/-- **End-to-end: the depth-`(>= 2)` binding count `<= n` delivered UNCONDITIONALLY.**  Chaining the
discharged budget (`minorImageLeBudget_geom`) into
`_CoreA6_NovelInvariant.Dstar_le_budget_of_residual`:
for the geometric readout structure with `b - 1 <= n`, the depth-`(>= 2)` bad set satisfies
`|Bad| <= n` with NO `MinorImageLeBudget` hypothesis assumed - it is produced internally from the
geometric minor sharpening. -/
theorem Dstar_le_budget_geom [DecidableEq F]
    (Bad : Finset F) (Wset : Finset ι) (α β : ℕ) (nodes : ι → List F) (param : ι → F)
    (γfun : F → F) {a b n : ℕ} (ha : 1 ≤ a) (hab : a < b) (hbn : b - 1 ≤ n)
    (wit : F → ι)
    (hwit_locus : ∀ γ ∈ Bad, wit γ ∈ minorLocus Wset α β nodes)
    (hwit_eq : ∀ γ ∈ Bad, γ = forcedGammaOf α β nodes (wit γ))
    (hfac : ∀ w ∈ minorLocus Wset α β nodes,
      forcedGammaOf α β nodes w = γfun (param w))
    (hΔ : ∀ w ∈ minorLocus Wset α β nodes,
      plueckerMinor α β (nodes w)
        = (minorPoly (geomPoly a) (geomPoly (a - 1)) (geomPoly b)
            (geomPoly (b - 1))).eval (param w)) :
    Bad.card ≤ n :=
  Dstar_le_budget_of_residual Bad Wset α β nodes n wit hwit_locus hwit_eq
    (minorImageLeBudget_geom Wset α β nodes param γfun ha hab hbn hfac hΔ)

/-! ## 4. Non-vacuity / sanity -/

/-- **Sanity (the bridge at a cascade scale).**  At `a = 3, b = 8` over `ℚ` the abstract minor
polynomial at the geometric rows is `X^3 * g_4`, of degree `7 = b - 1`. -/
example :
    (minorPoly (F := ℚ) (geomPoly 3) (geomPoly 2) (geomPoly 8) (geomPoly 7)).natDegree = 7 := by
  have := minorPoly_geom_natDegree (F := ℚ) (a := 3) (b := 8) (by omega) (by omega)
  simpa using this

end ArkLib.ProximityGap.CoreA6deep

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.CoreA6deep.minorPoly_geom_eq
#print axioms ArkLib.ProximityGap.CoreA6deep.minorPoly_geom_natDegree
#print axioms ArkLib.ProximityGap.CoreA6deep.forcedGammaImage_card_le_geom
#print axioms ArkLib.ProximityGap.CoreA6deep.minorImageLeBudget_geom
#print axioms ArkLib.ProximityGap.CoreA6deep.Dstar_le_budget_geom
