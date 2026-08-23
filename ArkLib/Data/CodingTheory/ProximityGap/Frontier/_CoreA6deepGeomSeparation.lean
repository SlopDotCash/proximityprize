/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CoreA6deepGeomMinorBudget
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CoreA6deep_BezoutBeatsAllDepths

/-!
# Core A6deep SHARPENED depth-uniform separation - the geometric image bound `b-1` undercuts the
# trivial `(k+2)`-subset count at EVERY binding depth, with HALF the generic `2D` margin (#444)

## What this sharpens

`_CoreA6deep_BezoutBeatsAllDepths.Dstar_two_mul_span_lt_trivial_count` proves the GENERIC A6deep
image bound undercuts the trivial witness count at every binding over-determination order:

  `|forcedGammaImage| <= 2*n < C(n, k+2)`   (`n >= 6`, `0 <= k <= n - 4`).

But for the structured (complete-homogeneous / geometric) readout rows, `_CoreA6deepGeomMinorBudget`
sharpened the image bound from `2n` to `b - 1` (`forcedGammaImage_card_le_geom`, the halving of the
determinantal minor degree from the generic `2D`).  Composing that sharper bound with the SAME
unimodal-envelope separation gives the SHARPENED depth-uniform statement:

> **`Dstar_geom_lt_trivial_count`** :  `|forcedGammaImage| <= b - 1 < C(n, k+2)`   for the geometric
> readouts (`1 <= a < b <= n`, `n >= 6`, `0 <= k <= n - 4`),

with the binding margin `b - 1 <= n - 1`, i.e. STRICTLY BELOW the generic `2n` and below `n` itself
-- the geometric image undercuts the trivial count with HALF (or less) the generic determinantal
margin, depth-uniformly.

## What is PROVEN here (axiom-clean, no `sorry`)

* **`Dstar_geom_lt_trivial_count`** (HEADLINE) - the sharpened depth-uniform separation: under the
  (1-PARAM) geometric structure (`hΔ` factoring through `minorPoly (g_a) (g_{a-1}) (g_b) (g_{b-1})`)
  with `1 <= a < b <= n`, the forced-γ image is `<= b - 1 < C(n, k+2)` at every binding depth.  The
  margin `b - 1 < n <= 2n` is sharper than the generic `Dstar_two_mul_span_lt_trivial_count`.
* **`geom_image_lt_two_mul_span`** - the explicit gain statement: the geometric image bound `b - 1`
  is `< 2 * n` (strictly below the generic determinantal budget) whenever `b <= n` and `1 <= n`,
  certifying the halving as a standalone inequality.

## Honest scope (rules 1,3,4,5,6 + ASYMPTOTIC GUARD)

EXTEND-PROVEN composition: it carries the O209 geometric image bound `b-1` through the SAME proven
unimodal-binomial separation engine, sharpening the generic `2n` margin to `b-1 < n`.  It is NOT a
closure: like every A6deep statement it is per-direction (the geometric readout structure, a fixed
monomial direction) and STILL inherits the open `PerDirectionParam` 1-PARAM / direction-uniformity
residual (carried as `hfac`/`hΔ`).  Field-universal `F[X]` + `Nat` arithmetic.  NO capacity /
beyond-Johnson / sub-linear / growth-law claim; cliff-at-`n/2` (the delta*/incidence object)
UNTOUCHED.  CORE `M(mu_n) <= C * sqrt(n * log(p/n))` stays **OPEN**.
-/

open Finset Nat Polynomial

namespace ArkLib.ProximityGap.CoreA6deep

open ArkLib.ProximityGap.CoreA6

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]

/-- **The halving as a standalone inequality.**  For `1 <= n` and `b <= n`, the geometric image
bound `b - 1` is strictly below the generic determinantal budget `2 * n`: `b - 1 < 2 * n`.  This is
the explicit gain over `forcedGammaImage_card_le_two_mul_span`'s `2n`. -/
theorem geom_image_lt_two_mul_span {b n : ℕ} (hn : 1 ≤ n) (hbn : b ≤ n) : b - 1 < 2 * n := by
  omega

/-- **HEADLINE - the SHARPENED depth-uniform separation for geometric readouts.**  Granting the
A6deep one-parameter structure with the readouts the complete-homogeneous rows `g_a, g_{a-1}, g_b,
g_{b-1}` (`1 <= a < b <= n`), the forced-γ image is strictly below the trivial `(k+2)`-subset
witness count at every binding over-determination order (`n >= 6`, `0 <= k <= n - 4`):

  `|forcedGammaImage| <= b - 1 < C(n, k + 2)`.

The binding margin `b - 1 <= n - 1` is sharper than the generic
`Dstar_two_mul_span_lt_trivial_count`'s `2n` - the geometric image undercuts the trivial count with
HALF (or less) the generic determinantal margin, depth-uniformly.  Composes the O209 geometric image
bound (`forcedGammaImage_card_le_geom`) with the unimodal-envelope separation
(`bezout_span_beats_choose_at_overdet`), bridged by `b - 1 < n <= 2n`.  (The direction-uniform
binding count and `PerDirectionParam` 1-PARAM discharge remain the open plateau / BCHKS input.) -/
theorem Dstar_geom_lt_trivial_count [DecidableEq F]
    (Wset : Finset ι) (α β k : ℕ) (nodes : ι → List F) (param : ι → F)
    (γfun : F → F) {a b n : ℕ} (ha : 1 ≤ a) (hab : a < b) (hbn : b ≤ n)
    (hfac : ∀ w ∈ minorLocus Wset α β nodes,
      forcedGammaOf α β nodes w = γfun (param w))
    (hΔ : ∀ w ∈ minorLocus Wset α β nodes,
      plueckerMinor α β (nodes w)
        = (minorPoly (geomPoly a) (geomPoly (a - 1)) (geomPoly b)
            (geomPoly (b - 1))).eval (param w))
    (hn : 6 ≤ n) (hk : k ≤ n - 4) :
    (forcedGammaImage Wset α β nodes).card < choose n (k + 2) := by
  -- geometric image bound: |forcedGammaImage| <= b - 1
  have himg : (forcedGammaImage Wset α β nodes).card ≤ b - 1 :=
    forcedGammaImage_card_le_geom Wset α β nodes param γfun ha hab hfac hΔ
  -- the sharpened margin b - 1 < 2n, and the unimodal-envelope separation 2n < C(n,k+2)
  have hmargin : b - 1 < 2 * n := geom_image_lt_two_mul_span (by omega) hbn
  have hsep : 2 * n < choose n (k + 2) := bezout_span_beats_choose_at_overdet hn hk
  exact lt_of_le_of_lt himg (lt_trans hmargin hsep)

/-! ## Non-vacuity / sanity -/

/-- **Sanity (the sharpened margin at a cascade scale).**  At `n = 32`, geometric span `b = 32`
(worst row degree), the image bound `b - 1 = 31` is below the generic `2n = 64` and below
`C(32, 6)` (binding depth `k = 4`). -/
example : (32 - 1 : ℕ) < 2 * 32 ∧ (32 - 1 : ℕ) < Nat.choose 32 6 := by
  refine ⟨by omega, ?_⟩
  decide

end ArkLib.ProximityGap.CoreA6deep

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.CoreA6deep.geom_image_lt_two_mul_span
#print axioms ArkLib.ProximityGap.CoreA6deep.Dstar_geom_lt_trivial_count
