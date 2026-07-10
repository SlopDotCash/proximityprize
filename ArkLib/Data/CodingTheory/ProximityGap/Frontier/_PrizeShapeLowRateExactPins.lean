/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R382HalfRadiusPinConnector
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30Second
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-!
# Literal bad-count connectors for the prize-shaped low-rate pins

This file contains no incidence hypothesis hidden behind a named predicate.  Its generic
connectors take the literal uniform `mcaEvent`-filter bound produced by the rich-point theorem,
turn it into an `epsMCA` bound, and feed it to the operational `mcaDeltaStar` ledger.

There are two prize-shaped arithmetic branches.

* For `P₁ / 2^128 = 2^30`, a predecessor count at most `n` combines with the overlap-packing
  bad point at `1/2` and pins the threshold exactly at `1/2`.
* For `P₂ / 2^128 = 2^31 = 2n`, a count at most `2n` at `17/32` proves the strict lower pin
  `mcaDeltaStar >= 17/32 > 1/2`.

The concrete corollaries presently expose the corresponding literal count as a theorem
hypothesis.  Once the rate-`1/16` and rate-`1/8` rich-point capstones are imported, their
unconditional specializations are one-line applications of these corollaries.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger Code
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.PackingBudgetFirstJump
open ArkLib.ProximityGap.Frontier.R382HalfRadiusPinConnector

namespace ArkLib.ProximityGap.Frontier.PrizeShapeLowRateExactPins

attribute [local instance] Classical.propDecidable

local instance firstPrimeFact :
    Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

local instance secondPrimeFact :
    Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- A finite count budget `E * Q <= p` is exactly the normalized inequality
`E/p <= Q⁻¹` used by the prize ledger. -/
theorem natCast_div_le_inv_of_mul_le {E Q p : ℕ}
    (hQ : 0 < Q) (hp : 0 < p) (hbudget : E * Q ≤ p) :
    (E : ℝ≥0∞) / (p : ℝ≥0∞) ≤ ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hpTop : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  rw [ENNReal.div_le_iff hp0 hpTop]
  have hQ0 : (Q : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hQTop : (Q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top Q
  calc
    (E : ℝ≥0∞) ≤ (E : ℝ≥0∞) * Q * (Q : ℝ≥0∞)⁻¹ := by
      rw [mul_assoc, ENNReal.mul_inv_cancel hQ0 hQTop, mul_one]
    _ ≤ (p : ℝ≥0∞) * (Q : ℝ≥0∞)⁻¹ := by
      gcongr
      exact_mod_cast hbudget
    _ = (Q : ℝ≥0∞)⁻¹ * (p : ℝ≥0∞) := mul_comm _ _

open Classical in
/-- A literal uniform bad-scalar count gives an operational lower bracket at any radius. -/
theorem radius_le_mcaDeltaStar_of_badCount_le
    {ι F : Type} [Fintype ι] [Nonempty ι]
    [Field F] [Fintype F]
    (C : Set (ι → F)) (delta : ℝ≥0) (E : ℕ) (epsilonStar : ℝ≥0∞)
    (hdelta : delta ≤ 1)
    (hcount : ∀ u : WordStack F (Fin 2) ι,
      (Finset.univ.filter fun gamma : F =>
        mcaEvent C delta (u 0) (u 1) gamma).card ≤ E)
    (hbudget : (E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ epsilonStar) :
    delta ≤ mcaDeltaStar (F := F) (A := F) C epsilonStar := by
  apply le_mcaDeltaStar_of_good (F := F) (A := F) C epsilonStar hdelta
  exact le_trans (epsMCA_le_of_badCount_le C delta E hcount) hbudget

/-- **Generic exact-half connector.**  At the tight quotient `p/Q=n`, a literal bound of
`n` bad scalars at the half predecessor supplies the good side.  The existing overlap packing
supplies the bad point at `1/2`; lattice constancy closes the interval between them. -/
theorem evalCode_deltaStar_eq_half_of_predecessor_badCount_le
    {p n k Q : ℕ} [Fact p.Prime] [NeZero n]
    {g : ZMod p} (hg : orderOf g = n)
    (hQ : 0 < Q) (hk : 2 ≤ k) (hnEven : n % 2 = 0)
    (hfloor : p / Q = n) (hkquarter : k ≤ n / 4)
    (hsupply : 4 ≤ p - n)
    (hcount : ∀ u : WordStack (ZMod p) (Fin 2) (Fin n),
      (Finset.univ.filter fun gamma : ZMod p =>
        mcaEvent (evalCode g n (k - 1)) (halfPredecessorRadius n)
          (u 0) (u 1) gamma).card ≤ n) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n (k - 1))
        ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) = (1 / 2 : ℝ≥0) := by
  have hn2 : 2 ≤ n := by omega
  have hp : 0 < p := (Fact.out (p := p.Prime)).pos
  have hmul : n * Q ≤ p := by
    have h := Nat.mul_div_le p Q
    simpa [hfloor, Nat.mul_comm] using h
  have hbudget : (n : ℝ≥0∞) / (Fintype.card (ZMod p) : ℝ≥0∞) ≤
      ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) := by
    rw [ZMod.card]
    exact natCast_div_le_inv_of_mul_le hQ hp hmul
  have hprev : epsMCA (F := ZMod p) (A := ZMod p)
      (evalCode g n (k - 1)) (halfPredecessorRadius n) ≤
        ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) :=
    le_trans
      (epsMCA_le_of_badCount_le (evalCode g n (k - 1))
        (halfPredecessorRadius n) n hcount)
      hbudget
  have hlower : (1 / 2 : ℝ≥0) ≤
      mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n (k - 1))
        ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) :=
    half_le_mcaDeltaStar_of_predecessor_good hnEven hn2
      (evalCode g n (k - 1)) ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) hprev
  have hupper :
      mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n (k - 1))
          ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤ (1 / 2 : ℝ≥0) :=
    mcaDeltaStar_le_half_of_floor_eq_length hg hQ hk hnEven hfloor hkquarter hsupply
  exact le_antisymm hupper hlower

/-! ## Concrete prize-shaped arithmetic specializations -/

/-- At the first certified prize-shaped prime, the literal rate-`1/16` predecessor count
immediately pins the operational threshold to `1/2`. -/
theorem firstPrime_rateSixteenth_deltaStar_eq_half_of_badCount
    (hcount : ∀ u : WordStack
      (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P) (Fin 2) (Fin (2 ^ 30)),
      (Finset.univ.filter fun gamma : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P =>
        mcaEvent
          (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 26 - 1))
          (halfPredecessorRadius (2 ^ 30)) (u 0) (u 1) gamma).card ≤ 2 ^ 30) :
    mcaDeltaStar
      (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
      (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
      (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 26 - 1))
      (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) = (1 / 2 : ℝ≥0) := by
  letI : Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30.P) :=
    ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩
  letI : NeZero (2 ^ 30 : ℕ) := ⟨by norm_num⟩
  exact evalCode_deltaStar_eq_half_of_predecessor_badCount_le
    ArkLib.ProximityGap.PrizeShapePrimeP30.orderOf_g
    (by norm_num) (by norm_num) (by norm_num)
    ArkLib.ProximityGap.PrizeShapePrimeP30.P_div_two_pow_128
    (by norm_num) (by norm_num) hcount

/-- At the second certified prime, a literal `2n` bad-count bound at `17/32` gives a
strictly-beyond-half operational lower pin. -/
theorem secondPrime_rateSixteenth_seventeenThirtyTwo_le_deltaStar_of_badCount
    (hcount : ∀ u : WordStack
      (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) (Fin 2) (Fin (2 ^ 30)),
      (Finset.univ.filter fun gamma : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P =>
        mcaEvent
          (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
            (2 ^ 30) (2 ^ 26 - 1))
          (17 / 32 : ℝ≥0) (u 0) (u 1) gamma).card ≤ 2 ^ 31) :
    (17 / 32 : ℝ≥0) ≤
      mcaDeltaStar
        (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
        (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
        (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
          (2 ^ 30) (2 ^ 26 - 1))
        (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) := by
  letI : Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) :=
    ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩
  have hp : 0 < ArkLib.ProximityGap.PrizeShapePrimeP30Second.P :=
    ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P.pos
  have hmul : (2 ^ 31 : ℕ) * 2 ^ 128 ≤
      ArkLib.ProximityGap.PrizeShapePrimeP30Second.P := by norm_num
  have hbudget : ((2 ^ 31 : ℕ) : ℝ≥0∞) /
      (Fintype.card (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) : ℝ≥0∞) ≤
        (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) := by
    rw [ZMod.card]
    exact natCast_div_le_inv_of_mul_le (by norm_num) hp hmul
  exact radius_le_mcaDeltaStar_of_badCount_le
    (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
      (2 ^ 30) (2 ^ 26 - 1))
    (17 / 32 : ℝ≥0) (2 ^ 31)
    (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞)
    (by rw [div_le_one (by norm_num : (0 : ℝ≥0) < 32)]; norm_num) hcount hbudget

/-- The second-prime conclusion is genuinely separated from the first-prime half pin. -/
theorem secondPrime_rateSixteenth_half_lt_deltaStar_of_badCount
    (hcount : ∀ u : WordStack
      (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) (Fin 2) (Fin (2 ^ 30)),
      (Finset.univ.filter fun gamma : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P =>
        mcaEvent
          (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
            (2 ^ 30) (2 ^ 26 - 1))
          (17 / 32 : ℝ≥0) (u 0) (u 1) gamma).card ≤ 2 ^ 31) :
    (1 / 2 : ℝ≥0) <
      mcaDeltaStar
        (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
        (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
        (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
          (2 ^ 30) (2 ^ 26 - 1))
        (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) := by
  exact lt_of_lt_of_le (by norm_num)
    (secondPrime_rateSixteenth_seventeenThirtyTwo_le_deltaStar_of_badCount hcount)

end ArkLib.ProximityGap.Frontier.PrizeShapeLowRateExactPins

/-! ## Axiom audit -/

namespace ArkLib.ProximityGap.Frontier.PrizeShapeLowRateExactPins

#print axioms evalCode_deltaStar_eq_half_of_predecessor_badCount_le
#print axioms firstPrime_rateSixteenth_deltaStar_eq_half_of_badCount
#print axioms secondPrime_rateSixteenth_half_lt_deltaStar_of_badCount

end ArkLib.ProximityGap.Frontier.PrizeShapeLowRateExactPins
