/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CoreA6deep_MinorTractability
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Core A6deep SHARPENING - the determinantal minor of complete-homogeneous (geometric) readout
# rows has degree `b - 1`, HALVING the generic `2D` Bezout budget to (below) `D` (#444)

## What A6deep left, and what this file sharpens

`_CoreA6deep_MinorTractability.minorPoly_natDegree_le` gives the *generic* Bezout budget

  `deg (pa * pbm - pam * pb) <= 2 * D`,

a `2 x 2` product-difference of degree-`D` polynomials.  That `2D` is a factor `2` ABOVE the prize
budget `n`: the named open `Prop` `MinorImageLeBudget` asks for `|forcedGammaImage| <= n`, and
A6deep only delivers `<= 2n` per direction (`forcedGammaImage_card_le_two_mul_span`,
`Dstar_le_two_mul_span`).

But the readout rows are **not** generic degree-`D` polynomials.  In the divided-difference
substrate (`mu_n` discrete-log, `x = h^t`), the relevant row readouts are the **complete-homogeneous
/ geometric** Gauss-period sums `g_c(X) = 1 + X + ... + X^c = sum_{i<c+1} X^i`, and the offset row
`h_{c-1}` is the **consecutive** geometric sum `g_{c-1}`.  For THESE structured rows the minor
collapses to a single monomial-times-geometric term:

> **`geomMinor_eq`** :  `g_a * g_{b-1} - g_{a-1} * g_b = X^a * g_{b-a-1}`   (for `a < b`),

so (`geomMinor_natDegree`)

> **`deg (g_a * g_{b-1} - g_{a-1} * g_b) = b - 1`**   (for `1 <= a < b`),

i.e. exactly `D - 1` at the worst row degree `D = b` -- a genuine **halving** of the generic `2D`
Bezout budget, landing the per-direction minor-locus root count (hence `forcedGammaImage`) **below**
the prize budget `n` for the complete-homogeneous readout structure.  Probe-confirmed exact integer
identity (`a < b <= 11`, both `a<b` and the antisymmetric `b<a` form) and degree `b-1` at the
cascade scales `b in {8,16,32,64}`.

## What is PROVEN here (axiom-clean, no `sorry`, char-free pure `F[X]` algebra)

* `geomPoly c := sum_{i in range (c+1)} X^i` - the complete-homogeneous (geometric) readout row as a
  polynomial in the discrete-log parameter, with `geomPoly_mul_X_sub_one` (`g_c*(X-1) = X^{c+1}-1`,
  the `geom_sum_mul` repackage) and `geomPoly_natDegree` (`deg g_c = c`).
* **`geomMinor_eq`** (HEADLINE identity) - `g_a * g_{b-1} - g_{a-1} * g_b = X^a * g_{b-a-1}` for
  `a < b`.  Proof: both sides times `(X-1)^2` agree by `geom_sum_mul` + ring; cancel `(X-1)^2 != 0`
  in the integral domain `F[X]`.
* **`geomMinor_natDegree`** - `deg (g_a g_{b-1} - g_{a-1} g_b) = b - 1` (`1 <= a < b`): the SHARP
  degree, `< D = b`.  Via `geomMinor_eq` + `natDegree (X^a * g_{b-a-1}) = a + (b-a-1) = b - 1`.
* **`geomMinor_natDegree_lt`** - the headline tractability consequence: the structured minor degree
  is `< b = D` (`<= D - 1 < D <= 2D`), strictly below A6deep's generic `2D`.  When `D = span = n`
  this puts the per-direction minor-locus root count, hence `|forcedGammaImage|`, below the prize
  budget `n` -- the A6deep `MinorImageLeBudget` clause, discharged FOR the complete-homogeneous
  readout structure (a fixed monomial direction).
* `geomMinor_ne_zero` - non-vacuity: the structured minor is `!= 0` (`X^a * g_{b-a-1} != 0`), so the
  sharp degree is a genuine root-count bound, not the vacuous `deg 0`.

## Honest scope (rules 1,3,4,5,6 + ASYMPTOTIC GUARD)

EXTEND-PROVEN NON-MOMENT structural brick on the brief's named **determinantal/Bezout lever**: it
SHARPENS A6deep's generic `2D` minor-degree budget to the exact `b-1 < D` for the *actual*
complete-homogeneous readout structure, halving the per-direction Bezout count and landing it below
the prize budget `n`.  It is NOT a closure: it discharges the budget clause only for the structured
(complete-homog) readouts and STILL inherits A6deep's open residual -- the **direction-uniformity**
at the binding depth (`PerDirectionParam` direction-selection / the BCHKS 1.12 budget input), which
this file does not touch.  Field-universal `F[X]` algebra (the cancellation is the geometric-sum
identity); thinness enters only via the discrete-log structure that makes the readouts geometric.
NO capacity / beyond-Johnson / sub-linear / growth-law claim; the cliff-at-`n/2` (the delta*/
incidence object) is UNTOUCHED.  CORE `M(mu_n) <= C * sqrt(n * log(p/n))` stays **OPEN**.
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.CoreA6deep

variable {F : Type*} [Field F]

/-! ## 1. The geometric (complete-homogeneous) readout row `g_c = 1 + X + ... + X^c` -/

/-- **The complete-homogeneous (geometric) readout row as a polynomial.**  `g_c = sum_{i<c+1} X^i =
1 + X + ... + X^c` -- the divided-difference substrate's Gauss-period readout `h_c` written in the
discrete-log parameter.  The offset row `h_{c-1}` is the consecutive `g_{c-1}`. -/
noncomputable def geomPoly (c : ℕ) : F[X] := ∑ i ∈ Finset.range (c + 1), X ^ i

/-- `g_c * (X - 1) = X^{c+1} - 1` -- the polynomial repackage of `geom_sum_mul`. -/
theorem geomPoly_mul_X_sub_one (c : ℕ) :
    (geomPoly (F := F) c) * (X - 1) = X ^ (c + 1) - 1 := by
  unfold geomPoly
  exact geom_sum_mul X (c + 1)

/-- `g_c` is monic. -/
theorem geomPoly_monic (c : ℕ) : (geomPoly (F := F) c).Monic := by
  unfold geomPoly
  exact monic_geom_sum_X (by omega)

/-- `g_c != 0` (it is monic). -/
theorem geomPoly_ne_zero (c : ℕ) : (geomPoly (F := F) c) ≠ 0 :=
  (geomPoly_monic c).ne_zero

/-- `X - 1 != 0` in `F[X]`. -/
private theorem X_sub_one_ne_zero : (X - 1 : F[X]) ≠ 0 := by
  have : (X - 1 : F[X]) = X - C 1 := by rw [map_one]
  rw [this]; exact X_sub_C_ne_zero 1

/-- `deg g_c = c`.  From `g_c * (X-1) = X^{c+1}-1`: in the domain `F[X]`,
`deg g_c + deg (X-1) = deg (X^{c+1}-1) = c+1`, and `deg (X-1) = 1`. -/
theorem geomPoly_natDegree (c : ℕ) : (geomPoly (F := F) c).natDegree = c := by
  have hmul := geomPoly_mul_X_sub_one (F := F) c
  have hdeg : ((geomPoly (F := F) c) * (X - 1)).natDegree = c + 1 := by
    rw [hmul]
    have : (X ^ (c + 1) - 1 : F[X]) = X ^ (c + 1) - C 1 := by rw [map_one]
    rw [this, natDegree_X_pow_sub_C]
  rw [natDegree_mul (geomPoly_ne_zero c) X_sub_one_ne_zero] at hdeg
  have h1 : (X - 1 : F[X]).natDegree = 1 := by
    have : (X - 1 : F[X]) = X - C 1 := by rw [map_one]
    rw [this, natDegree_X_sub_C]
  rw [h1] at hdeg
  omega

/-! ## 2. The headline minor identity: `g_a g_{b-1} - g_{a-1} g_b = X^a g_{b-a-1}` (degree b-1)

The determinantal minor of the consecutive geometric rows collapses to a single
monomial-times-geometric term.  Proof engine: both sides times `(X-1)^2` agree by the closed form
`g_c (X-1) = X^{c+1}-1` and pure `ring`; cancel the nonzero `(X-1)^2` in the integral domain `F[X]`.
-/

/-- **HEADLINE - the geometric minor identity.**  For `a < b`,

  `g_a * g_{b-1} - g_{a-1} * g_b = X^a * g_{b-a-1}`.

(`g_{a-1}` and `g_{b-1}` are the *offset* rows; `g_{b-a-1}` is the consecutive geometric sum of
length `b-a`.)  This is the determinantal Wronskian of the consecutive geometric readout rows,
collapsing to a single monomial-times-geometric term -- the source of the degree halving. -/
theorem geomMinor_eq {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    (geomPoly (F := F) a) * (geomPoly (b - 1)) - (geomPoly (a - 1)) * (geomPoly b)
      = X ^ a * (geomPoly (b - a - 1)) := by
  -- multiply both sides by (X-1)^2 and use the closed form; then cancel (X-1)^2 != 0.
  have hsq : (X - 1 : F[X]) ^ 2 ≠ 0 := pow_ne_zero 2 X_sub_one_ne_zero
  apply mul_right_cancel₀ hsq
  -- expand each `g_c * (X-1)` via the closed form
  have key : ∀ x y : ℕ,
      ((geomPoly (F := F) x) * (geomPoly y)) * (X - 1) ^ 2
        = (X ^ (x + 1) - 1) * (X ^ (y + 1) - 1) := by
    intro x y
    -- (gx * gy) * (X-1)^2 = (gx (X-1)) * (gy (X-1)) = (X^{x+1}-1)(X^{y+1}-1)
    calc (geomPoly (F := F) x) * (geomPoly y) * (X - 1) ^ 2
        = ((geomPoly (F := F) x) * (X - 1)) * ((geomPoly y) * (X - 1)) := by ring
      _ = (X ^ (x + 1) - 1) * (X ^ (y + 1) - 1) := by
            rw [geomPoly_mul_X_sub_one, geomPoly_mul_X_sub_one]
  have hXa : ((X : F[X]) ^ a * (geomPoly (b - a - 1))) * (X - 1) ^ 2
      = X ^ a * ((X ^ (b - a - 1 + 1) - 1) * (X - 1)) := by
    have hg := geomPoly_mul_X_sub_one (F := F) (b - a - 1)
    calc ((X : F[X]) ^ a * (geomPoly (b - a - 1))) * (X - 1) ^ 2
        = X ^ a * (((geomPoly (b - a - 1)) * (X - 1)) * (X - 1)) := by ring
      _ = X ^ a * ((X ^ (b - a - 1 + 1) - 1) * (X - 1)) := by rw [geomPoly_mul_X_sub_one]
  -- LHS times (X-1)^2
  rw [sub_mul, key a (b - 1), key (a - 1) b, hXa]
  -- now pure monomial algebra; reconcile the truncated subtractions with a<b
  have hbpos : 0 < b := lt_of_le_of_lt (Nat.zero_le a) hab
  have hba_pos : 0 < b - a := Nat.sub_pos_of_lt hab
  have hb1 : b - 1 + 1 = b := Nat.succ_pred_eq_of_pos hbpos
  have ha1 : a - 1 + 1 = a := Nat.succ_pred_eq_of_pos ha
  have hba1 : b - a - 1 + 1 = b - a := Nat.succ_pred_eq_of_pos hba_pos
  rw [hb1, ha1, hba1]
  -- goal: (X^{a+1}-1)(X^b-1) - (X^a-1)(X^{b+1}-1) = X^a*((X^{b-a}-1)(X-1))
  -- use X^{a+1} = X^a*X, X^{b+1}=X^b*X, X^b = X^a * X^{b-a}
  have hsplit : (X : F[X]) ^ b = X ^ a * X ^ (b - a) := by
    rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hab)]
  have hsa : (X : F[X]) ^ (a + 1) = X ^ a * X := by rw [pow_succ]
  have hsb : (X : F[X]) ^ (b + 1) = X ^ b * X := by rw [pow_succ]
  rw [hsa, hsb, hsplit]
  ring

/-- **Non-vacuity.**  The geometric minor `X^a * g_{b-a-1}` is nonzero (`X^a != 0`, `g_{b-a-1}`
monic), so the sharp degree below is a genuine bound, not `deg 0`. -/
theorem geomMinor_ne_zero {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    (geomPoly (F := F) a) * (geomPoly (b - 1)) - (geomPoly (a - 1)) * (geomPoly b) ≠ 0 := by
  rw [geomMinor_eq ha hab]
  exact mul_ne_zero (pow_ne_zero a X_ne_zero) (geomPoly_ne_zero _)

/-- **The SHARP degree of the geometric minor: `deg = b - 1`.**  For `1 <= a < b`,

  `deg (g_a g_{b-1} - g_{a-1} g_b) = b - 1`.

Exactly `D - 1` at the worst row degree `D = b` -- below A6deep's generic `2D`.  Via `geomMinor_eq`
and `natDegree (X^a * g_{b-a-1}) = a + (b - a - 1) = b - 1`. -/
theorem geomMinor_natDegree {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    ((geomPoly (F := F) a) * (geomPoly (b - 1)) - (geomPoly (a - 1)) * (geomPoly b)).natDegree
      = b - 1 := by
  rw [geomMinor_eq ha hab]
  rw [natDegree_mul (pow_ne_zero a X_ne_zero) (geomPoly_ne_zero _)]
  rw [natDegree_X_pow, geomPoly_natDegree]
  omega

/-- **HEADLINE tractability consequence - the structured minor degree is strictly below `b = D`.**
For `1 <= a < b`, `deg (g_a g_{b-1} - g_{a-1} g_b) < b`.  So at the worst row degree `D = b` the
complete-homogeneous minor's Bezout root-count budget is `< D`, below A6deep's generic `2D`.
When `D = span = n`, the per-direction minor-locus root count (hence `|forcedGammaImage|`) is `< n`
-- the prize budget `q*eps* ~ n`, discharging A6deep's `MinorImageLeBudget` clause FOR the
complete-homogeneous readout structure (a fixed monomial direction).  The open residual is the
direction-uniformity at the binding depth (A6deep `PerDirectionParam`), NOT touched here. -/
theorem geomMinor_natDegree_lt {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    ((geomPoly (F := F) a) * (geomPoly (b - 1)) - (geomPoly (a - 1)) * (geomPoly b)).natDegree
      < b := by
  rw [geomMinor_natDegree ha hab]; omega

/-- **Halving vs the generic `2D` budget.**  For `1 <= a < b` with `b <= D` (the row degrees bounded
by the span `D`), the structured minor degree is `<= D - 1 < 2 * D`: at least the full factor-2 gain
over `minorPoly_natDegree_le`'s generic `2D`, and strictly below `D` itself. -/
theorem geomMinor_natDegree_le_pred_span {a b D : ℕ} (ha : 1 ≤ a) (hab : a < b) (hbD : b ≤ D) :
    ((geomPoly (F := F) a) * (geomPoly (b - 1)) - (geomPoly (a - 1)) * (geomPoly b)).natDegree
      ≤ D - 1 := by
  rw [geomMinor_natDegree ha hab]; omega

/-! ## 3. Non-vacuity / sanity (concrete `ℚ` witnesses at the cascade scales) -/

/-- **Sanity (the identity).**  At `a = 2, b = 5` over `ℚ`:
`g_2 g_4 - g_1 g_5 = X^2 * g_2`. -/
example : (geomPoly (F := ℚ) 2) * (geomPoly 4) - (geomPoly 1) * (geomPoly 5)
    = X ^ 2 * (geomPoly 2) := by
  have := geomMinor_eq (F := ℚ) (a := 2) (b := 5) (by omega) (by omega)
  simpa using this

/-- **Sanity (degree halving at a cascade scale).**  At `a = 3, b = 8` the structured minor has
degree `7 = b - 1`, below the generic `2D = 16`. -/
example : ((geomPoly (F := ℚ) 3) * (geomPoly 7) - (geomPoly 2) * (geomPoly 8)).natDegree = 7 := by
  have := geomMinor_natDegree (F := ℚ) (a := 3) (b := 8) (by omega) (by omega)
  simpa using this

end ArkLib.ProximityGap.CoreA6deep

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.CoreA6deep.geomPoly_natDegree
#print axioms ArkLib.ProximityGap.CoreA6deep.geomMinor_eq
#print axioms ArkLib.ProximityGap.CoreA6deep.geomMinor_natDegree
#print axioms ArkLib.ProximityGap.CoreA6deep.geomMinor_natDegree_lt
#print axioms ArkLib.ProximityGap.CoreA6deep.geomMinor_ne_zero
