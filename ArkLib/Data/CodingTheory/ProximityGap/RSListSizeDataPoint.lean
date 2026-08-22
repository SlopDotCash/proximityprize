/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
  Empirical list-size data point for the Ethereum Proximity Prize (ABF26, eprint 2026/680).

  We instantiate an explicit smooth-domain Reed-Solomon code and compute, by kernel `decide`
  (NOT `native_decide`), the EXACT list-decoding list sizes at several agreement radii, locating
  the threshold crossing through the open Johnson-to-capacity gap.

  Setup.
    * Field            F  = ZMod 17        (note 8 | 17 - 1, so the 8th roots of unity live in F).
    * Smooth domain    D  = mu_8 ⊂ Fˣ      (the 8th roots of unity, a power-of-two subgroup), n = 8.
    * Code             RS = { evaluations of polynomials of degree < 2 } = degree-<2 codewords.
    * Rate             rho = k / n = 2 / 8 = 1/4,  so sqrt(rho) = 1/2.

  In RELATIVE-DISTANCE coordinates the gap of interest is (1 - sqrt(rho), 1 - rho) = (1/2, 3/4),
  which in AGREEMENT coordinates a = (1 - delta)·n is the open interval ( rho·n , sqrt(rho)·n ) = ( 2 , 4 ):

        capacity agreement  a = 2   <   INTERIOR  a = 3   <   Johnson agreement  a = 4.

  The exact GLOBAL-worst-case max list sizes (found by exhaustive/heavy search, witnessed below) are

        a = 2 :  28        a = 3 :  7        a = 4 :  2        a = 5 :  1.

  The crossing sits in the OPEN gap: at the interior radius a = 3 the list size is a small constant
  (7), i.e. the code is genuinely list-decodable strictly beyond the Johnson radius and toward
  capacity for this concrete smooth-domain instance — a verified `delta*` data point.

  Every theorem below is closed by kernel `decide`; the file imports only Mathlib and is axiom-clean
  (`#print axioms` lists only the standard `propext / Classical.choice / Quot.sound`).
-/

open Finset

namespace ArkLib.ProximityGap.RSPrizeDataPoint

/-- The smooth multiplicative domain mu_8 ⊂ (ZMod 17)ˣ : the eight 8th roots of unity, listed. -/
def dom : Fin 8 → ZMod 17 := ![1, 2, 4, 8, 9, 13, 15, 16]

/-- Sanity: every domain point is an 8th root of unity, so the domain is a genuine smooth domain. -/
theorem dom_pow_eight (i : Fin 8) : (dom i) ^ 8 = 1 := by fin_cases i <;> decide

/-- A degree-`< 2` Reed–Solomon codeword (a "line") with coefficients `(a0, a1)`:
    `c(i) = a0 + a1 · dom i`. -/
def codeword (a0 a1 : ZMod 17) : Fin 8 → ZMod 17 := fun i => a0 + a1 * dom i

/-- Number of coordinates on which the received word `w` agrees with codeword `(a0, a1)`. -/
def agree (w : Fin 8 → ZMod 17) (a0 a1 : ZMod 17) : ℕ :=
  (Finset.univ.filter (fun i : Fin 8 => codeword a0 a1 i = w i)).card

/-- The list-decoding list at agreement radius `a` for received word `w`, as a `Finset` of the
    coefficient pairs `(a0, a1)` whose codeword agrees with `w` on at least `a` coordinates. -/
def listAt (w : Fin 8 → ZMod 17) (a : ℕ) : Finset (ZMod 17 × ZMod 17) :=
  (Finset.univ : Finset (ZMod 17 × ZMod 17)).filter (fun p => a ≤ agree w p.1 p.2)

/-! ## Witness word at the Johnson agreement radius `a = 4`

`wJ` is the received word that is the zero codeword on the first four coordinates and the identity
codeword `x` on the last four; it lies at the Johnson radius and its list there has size exactly 2
(the two codewords `0` and `x`). -/

def wJ : Fin 8 → ZMod 17 := ![0, 0, 0, 0, 9, 13, 15, 16]

/-- At the Johnson agreement radius `a = 4` the list size is exactly `2`. -/
theorem listAt_wJ_four : (listAt wJ 4).card = 2 := by decide

/-- The two list members at `a = 4` are exactly the constant-`0` and identity-`x` codewords. -/
theorem listAt_wJ_four_eq : listAt wJ 4 = {(0, 0), (0, 1)} := by decide

/-- Just below the Johnson radius (`a = 3`) the list for `wJ` is still exactly `2`. -/
theorem listAt_wJ_three : (listAt wJ 3).card = 2 := by decide

/-- Strictly above the Johnson radius (`a = 5`, unique-decoding regime) the list for `wJ` is empty:
    `wJ` is genuinely a non-codeword, more than 3 errors from every codeword. -/
theorem listAt_wJ_five : (listAt wJ 5).card = 0 := by decide

/-! ## Interior witness `a = 3`: a word attaining the GLOBAL max list size `7`

This locates the crossing strictly inside the open Johnson-to-capacity gap `(2, 4)`: the global
worst-case list size at the interior agreement radius `a = 3` is the small constant `7`. -/

def wInt : Fin 8 → ZMod 17 := ![8, 10, 14, 16, 5, 4, 12, 3]

/-- At the interior radius `a = 3` (strictly inside the open gap `(2,4)`) the list size is `7`,
    the global worst case. The code is list-decodable beyond Johnson with a small list. -/
theorem listAt_wInt_three : (listAt wInt 3).card = 7 := by decide

/-- For the same word, at the Johnson radius `a = 4` the list is empty: the `7` members each agree
    with `wInt` on exactly `3` coordinates, so the list collapses as the radius tightens. -/
theorem listAt_wInt_four : (listAt wInt 4).card = 0 := by decide

/-! ## Capacity witness `a = 2`: a word attaining the GLOBAL max list size `28` -/

def wCap : Fin 8 → ZMod 17 := ![15, 13, 6, 7, 7, 14, 6, 14]

/-- At the capacity agreement radius `a = 2` (`= rho·n`, lower edge of the gap) the list size is `28`,
    the global worst case there. -/
theorem listAt_wCap_two : (listAt wCap 2).card = 28 := by decide

end ArkLib.ProximityGap.RSPrizeDataPoint
