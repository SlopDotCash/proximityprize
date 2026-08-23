/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G261WickCeilingExceedsDCFloor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G63PrimitiveCensusPinnedAtDCFloor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30Second

/-!
# G262: the two sponsor primes cross from Wick-above-DC at rank five to forced
characteristic-p super-Wick mass at rank six

G261 proves the exact identity

`Wick_r / DCfloor_r = (2r−1)‼ · q / n^r`

and its thin-regime consequence under the explicit premise `n^r ≤ q`.  At the prize parameters
that premise does not hold uniformly over the two live ranks.  For `n=2^30` and both certified
sponsor primes `P1,P2`, one has

`n^5 < Pi < n^6`.

Thus rank five is on G261's thin side, while rank six is on the opposite, characteristic-p
wraparound side.  The exact division-free margins are much stronger:

* at rank five, `Wick/DC > 241920` for P1 and `> 483840` for P2;
* at rank six, `DC/Wick > 400` for P1 and `> 200` for P2.

Combining the second pair with G63's unconditional Parseval floor shows that every actual
primitive/wraparound collision census at rank six is strictly larger than `400·Wick` at P1 and
`200·Wick` at P2.  Consequently the characteristic-zero Wick value cannot be an upper ceiling for
the rank-six sponsor census.  This is the exact arithmetic mechanism behind G64's forced FS15–FS18
exception at depth six.

This is a sponsor-facing scope correction and route no-go, not a Jacobi estimate and not prize
closure.  The direct row-labelled rank-five/rank-six covariance remains open / on-BGK.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace ArkLib.ProximityGap.Frontier.G262SponsorRankCrossover

open scoped Nat

open ArkLib.ProximityGap.Frontier.G261WickCeilingExceedsDCFloor
  (wickTerm dcFloorNum dcFloor)
open ArkLib.ProximityGap.Frontier.G63PrimitiveCensusPinnedAtDCFloor
  (census census_ge_dcFloor_div)

/-- The smooth subgroup order at both sponsor primes. -/
abbrev n : ℕ := 2 ^ 30

/-- The first certified sponsor prime. -/
abbrev p1 : ℕ := ArkLib.ProximityGap.PrizeShapePrimeP30.P

/-- The second certified sponsor prime. -/
abbrev p2 : ℕ := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P

local instance p1PrimeFact : Fact (Nat.Prime p1) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

local instance p2PrimeFact : Fact (Nat.Prime p2) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- **General reverse-regime lemma.**  If `(2r−1)‼·q < n^r`, then the Wick term is strictly
below the DC floor.  This is the converse side of G261's thin-regime comparison. -/
theorem wick_lt_dcFloor_of_doubleFactorial_mul_q_lt_pow {q n r : ℕ}
    (hn : 0 < n) (hq : 0 < q) (hthick : (2 * r - 1)‼ * q < n ^ r) :
    (wickTerm n r : ℝ) < dcFloor q n r := by
  have hnR : (0 : ℝ) < (n : ℝ) ^ r := pow_pos (by exact_mod_cast hn) r
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hthickR : (((2 * r - 1)‼ * q : ℕ) : ℝ) < ((n ^ r : ℕ) : ℝ) := by
    exact_mod_cast hthick
  have hwick : (wickTerm n r : ℝ) = ((2 * r - 1)‼ : ℝ) * (n : ℝ) ^ r := by
    unfold wickTerm
    push_cast
    ring
  have hdc : dcFloor q n r = (n : ℝ) ^ r * (n : ℝ) ^ r / (q : ℝ) := by
    unfold dcFloor dcFloorNum
    push_cast
    rw [show 2 * r = r + r by omega, pow_add]
  rw [hwick, hdc, lt_div_iff₀ hqR]
  push_cast at hthickR
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (mul_lt_mul_of_pos_right hthickR hnR)

/-- Any quantity above the DC floor is strictly above Wick in the reverse regime.  G63 supplies
exactly this premise for the primitive/wraparound census. -/
theorem wick_lt_of_dcFloor_le {q n r : ℕ} {C : ℝ}
    (hn : 0 < n) (hq : 0 < q) (hthick : (2 * r - 1)‼ * q < n ^ r)
    (hDC : dcFloor q n r ≤ C) :
    (wickTerm n r : ℝ) < C :=
  lt_of_lt_of_le (wick_lt_dcFloor_of_doubleFactorial_mul_q_lt_pow hn hq hthick) hDC

/-- P1 lies strictly between the fifth and sixth powers of the subgroup order. -/
theorem p1_between_rank_five_and_six : n ^ 5 < p1 ∧ p1 < n ^ 6 := by
  norm_num [n, p1]

/-- P2 lies strictly between the fifth and sixth powers of the subgroup order. -/
theorem p2_between_rank_five_and_six : n ^ 5 < p2 ∧ p2 < n ^ 6 := by
  norm_num [n, p2]

/-- At P1, rank-five Wick exceeds the DC floor by a factor strictly larger than `241920`. -/
theorem p1_rank_five_wick_gt_241920_mul_dcFloor :
    (241920 : ℝ) * dcFloor p1 n 5 < (wickTerm n 5 : ℝ) := by
  norm_num [n, p1, wickTerm, dcFloor, dcFloorNum, Nat.doubleFactorial]

/-- At P2, rank-five Wick exceeds the DC floor by a factor strictly larger than `483840`. -/
theorem p2_rank_five_wick_gt_483840_mul_dcFloor :
    (483840 : ℝ) * dcFloor p2 n 5 < (wickTerm n 5 : ℝ) := by
  norm_num [n, p2, wickTerm, dcFloor, dcFloorNum, Nat.doubleFactorial]

/-- At P1, the rank-six DC floor exceeds `400` Wick terms. -/
theorem p1_rank_six_dcFloor_gt_400_mul_wick :
    (400 : ℝ) * (wickTerm n 6 : ℝ) < dcFloor p1 n 6 := by
  norm_num [n, p1, wickTerm, dcFloor, dcFloorNum, Nat.doubleFactorial]

/-- At P2, the rank-six DC floor exceeds `200` Wick terms. -/
theorem p2_rank_six_dcFloor_gt_200_mul_wick :
    (200 : ℝ) * (wickTerm n 6 : ℝ) < dcFloor p2 n 6 := by
  norm_num [n, p2, wickTerm, dcFloor, dcFloorNum, Nat.doubleFactorial]

/-- At P1, every rank-six quantity that contains the DC mass is more than `400` times Wick. -/
theorem p1_rank_six_superWick_of_dcFloor_le {C : ℝ} (hDC : dcFloor p1 n 6 ≤ C) :
    (400 : ℝ) * (wickTerm n 6 : ℝ) < C :=
  lt_of_lt_of_le p1_rank_six_dcFloor_gt_400_mul_wick hDC

/-- At P2, every rank-six quantity that contains the DC mass is more than `200` times Wick. -/
theorem p2_rank_six_superWick_of_dcFloor_le {C : ℝ} (hDC : dcFloor p2 n 6 ≤ C) :
    (200 : ℝ) * (wickTerm n 6 : ℝ) < C :=
  lt_of_lt_of_le p2_rank_six_dcFloor_gt_200_mul_wick hDC

/-- **P1 characteristic-p census consequence.**  G63's primitive/wraparound census at rank six
is strictly more than `400` times the characteristic-zero Wick value. -/
theorem p1_rank_six_census_gt_400_mul_wick {ζ : ZMod p1}
    (hprim : IsPrimitiveRoot ζ n) {ψ : AddChar (ZMod p1) ℂ} (hψ : ψ.IsPrimitive) :
    (400 : ℝ) * (wickTerm n 6 : ℝ) < (census ζ (2 ^ 29) 6 : ℝ) := by
  have hDC := census_ge_dcFloor_div (F := ZMod p1) (ζ := ζ) (m := 2 ^ 29) (r := 6)
    (by positivity) (by simpa [n] using hprim) hψ (by positivity)
  have hn_eq : 2 * 2 ^ 29 = n := by norm_num [n]
  rw [ZMod.card p1, hn_eq] at hDC
  have hfloor : dcFloor p1 n 6 = (n : ℝ) ^ (2 * 6) / (p1 : ℝ) := by
    unfold dcFloor dcFloorNum
    push_cast
    rfl
  have hDC' : dcFloor p1 n 6 ≤ (census ζ (2 ^ 29) 6 : ℝ) := by
    rw [hfloor]
    exact hDC
  exact p1_rank_six_superWick_of_dcFloor_le hDC'

/-- **P2 characteristic-p census consequence.**  G63's primitive/wraparound census at rank six
is strictly more than `200` times the characteristic-zero Wick value. -/
theorem p2_rank_six_census_gt_200_mul_wick {ζ : ZMod p2}
    (hprim : IsPrimitiveRoot ζ n) {ψ : AddChar (ZMod p2) ℂ} (hψ : ψ.IsPrimitive) :
    (200 : ℝ) * (wickTerm n 6 : ℝ) < (census ζ (2 ^ 29) 6 : ℝ) := by
  have hDC := census_ge_dcFloor_div (F := ZMod p2) (ζ := ζ) (m := 2 ^ 29) (r := 6)
    (by positivity) (by simpa [n] using hprim) hψ (by positivity)
  have hn_eq : 2 * 2 ^ 29 = n := by norm_num [n]
  rw [ZMod.card p2, hn_eq] at hDC
  have hfloor : dcFloor p2 n 6 = (n : ℝ) ^ (2 * 6) / (p2 : ℝ) := by
    unfold dcFloor dcFloorNum
    push_cast
    rfl
  have hDC' : dcFloor p2 n 6 ≤ (census ζ (2 ^ 29) 6 : ℝ) := by
    rw [hfloor]
    exact hDC
  exact p2_rank_six_superWick_of_dcFloor_le hDC'

/-- Honest scope marker: this is a sponsor-rank route correction, not prize closure. -/
def isPrizeClosure : Bool := false

theorem not_prizeClosure : isPrizeClosure = false := rfl

#print axioms wick_lt_dcFloor_of_doubleFactorial_mul_q_lt_pow
#print axioms wick_lt_of_dcFloor_le
#print axioms p1_between_rank_five_and_six
#print axioms p2_between_rank_five_and_six
#print axioms p1_rank_five_wick_gt_241920_mul_dcFloor
#print axioms p2_rank_five_wick_gt_483840_mul_dcFloor
#print axioms p1_rank_six_dcFloor_gt_400_mul_wick
#print axioms p2_rank_six_dcFloor_gt_200_mul_wick
#print axioms p1_rank_six_census_gt_400_mul_wick
#print axioms p2_rank_six_census_gt_200_mul_wick
#print axioms not_prizeClosure

end ArkLib.ProximityGap.Frontier.G262SponsorRankCrossover
