/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PackingBudgetFirstJump
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateEighthFullWiring
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateSixteenthFullWiring
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SeventeenThirtyTwoFullWiring
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30Second
import ArkLib.Data.CodingTheory.ProximityGap.KKH26RegimeSplit
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

The generic connectors expose the corresponding literal count as a theorem hypothesis.  The
rate-`1/8` and rate-`1/16` incidence capstones discharge it for the first certified field, and
the rate-`1/16` `17/32` capstone gives the separated lower pin for the second field.  All of
the resulting concrete conclusions are unconditional.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

open Finset
open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger Code
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.PackingBudgetFirstJump

namespace ArkLib.ProximityGap.Frontier.PrizeShapeLowRateExactPins

attribute [local instance] Classical.propDecidable

/-- The last Hamming lattice radius below `1/2` at even length.  This local definition keeps
the literal-count connector independent of the heavier projective R382 stack. -/
noncomputable def halfPredecessorRadius (n : ℕ) : ℝ≥0 :=
  ((n / 2 - 1 : ℕ) : ℝ≥0) / (n : ℝ≥0)

/-- A good half predecessor fills the whole open interval below `1/2`, because `epsMCA`
depends only on `floor(delta*n)`. -/
theorem half_le_mcaDeltaStar_of_predecessor_good
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} [NeZero n] (hnEven : n % 2 = 0) (hn2 : 2 ≤ n)
    (C : Set (Fin n → F)) (epsilonStar : ℝ≥0∞)
    (hprev : epsMCA (F := F) (A := F) C (halfPredecessorRadius n) ≤ epsilonStar) :
    (1 / 2 : ℝ≥0) ≤ mcaDeltaStar (F := F) (A := F) C epsilonStar := by
  let w : ℕ := n / 2 - 1
  let deltaPrev : ℝ≥0 := halfPredecessorRadius n
  have hnpos : 0 < n := by omega
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hnHalf : n = 2 * (n / 2) := by omega
  have hprevMul : deltaPrev * (n : ℝ≥0) = (w : ℝ≥0) := by
    dsimp only [deltaPrev, halfPredecessorRadius, w]
    exact div_mul_cancel₀ _ hn0
  have hhalfMul : (1 / 2 : ℝ≥0) * (n : ℝ≥0) = ((n / 2 : ℕ) : ℝ≥0) := by
    have hncast : (n : ℝ≥0) = 2 * ((n / 2 : ℕ) : ℝ≥0) := by
      exact_mod_cast hnHalf
    rw [hncast]
    field_simp
  have hgood : ∀ delta : ℝ≥0, delta < (1 / 2 : ℝ≥0) →
      epsMCA (F := F) (A := F) C delta ≤ epsilonStar := by
    intro delta hdelta
    by_cases hle : delta ≤ deltaPrev
    · exact le_trans (epsMCA_mono C hle) hprev
    · have hprevDelta : deltaPrev < delta := lt_of_not_ge hle
      have hlowerFloor : (w : ℝ≥0) ≤ delta * (n : ℝ≥0) := by
        have hm := mul_lt_mul_of_pos_right hprevDelta (by positivity)
        rw [hprevMul] at hm
        exact hm.le
      have hupperFloor : delta * (n : ℝ≥0) < ((n / 2 : ℕ) : ℝ≥0) := by
        have hm := mul_lt_mul_of_pos_right hdelta (by positivity)
        rwa [hhalfMul] at hm
      have hfloorDelta :
          Nat.floor (delta * (Fintype.card (Fin n) : ℝ≥0)) = w := by
        rw [Fintype.card_fin, Nat.floor_eq_iff (zero_le _)]
        constructor
        · exact hlowerFloor
        · dsimp only [w]
          have hsucc : n / 2 - 1 + 1 = n / 2 := by omega
          have hcast : (((n / 2 - 1 : ℕ) : ℝ≥0) + 1) =
              ((n / 2 : ℕ) : ℝ≥0) := by
            exact_mod_cast hsucc
          rw [hcast]
          exact hupperFloor
      have hfloorPrev :
          Nat.floor (deltaPrev * (Fintype.card (Fin n) : ℝ≥0)) = w := by
        rw [Fintype.card_fin, hprevMul, Nat.floor_natCast]
      rw [ProximityGap.epsMCA_eq_of_floor_eq (F := F) (A := F) C
        (hfloorDelta.trans hfloorPrev.symm)]
      exact hprev
  by_contra hnot
  rw [not_le] at hnot
  obtain ⟨delta, hstarDelta, hdeltaHalf⟩ := exists_between hnot
  have hdeltaLe := le_mcaDeltaStar_of_good (F := F) (A := F) C epsilonStar
    (le_trans hdeltaHalf.le (by norm_num)) (hgood delta hdeltaHalf)
  exact (not_lt_of_ge hdeltaLe) hstarDelta

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

/-- A literal uniform bad-scalar count gives an operational lower bracket at any radius. -/
theorem radius_le_mcaDeltaStar_of_badCount_le
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
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

local instance firstPrimeFact :
    Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

local instance secondPrimeFact :
    Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

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
  letI : NeZero (2 ^ 30 : ℕ) := ⟨by norm_num⟩
  exact evalCode_deltaStar_eq_half_of_predecessor_badCount_le
    ArkLib.ProximityGap.PrizeShapePrimeP30.orderOf_g
    (by norm_num) (by norm_num) (by norm_num)
    ArkLib.ProximityGap.PrizeShapePrimeP30.P_div_two_pow_128
    (by norm_num) (by norm_num) hcount

/-- **Unconditional first-prime rate-`1/16` pin.**  The fully assembled rich-point
incidence theorem supplies the literal predecessor count, so the prize-shaped operational
threshold is exactly `1/2` with no named geometric residual. -/
theorem firstPrime_rateSixteenth_deltaStar_eq_half :
    mcaDeltaStar
      (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
      (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
      (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 26 - 1))
      (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) = (1 / 2 : ℝ≥0) := by
  apply firstPrime_rateSixteenth_deltaStar_eq_half_of_badCount
  intro u
  letI : NeZero (2 ^ 30 : ℕ) := ⟨by norm_num⟩
  have hg0 : ArkLib.ProximityGap.PrizeShapePrimeP30.g ≠ 0 :=
    ProximityGap.KKH26RegimeSplit.ne_zero_of_orderOf_eq
      ArkLib.ProximityGap.PrizeShapePrimeP30.orderOf_g
  let dom : Fin (2 ^ 30) ↪ ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P :=
    ProximityGap.KKH26RegimeSplit.powDomain
      ArkLib.ProximityGap.PrizeShapePrimeP30.g
      ArkLib.ProximityGap.PrizeShapePrimeP30.orderOf_g hg0
  have hcount :=
    ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenthFullWiring.halfPredecessor_badScalar_filter_card_le_length
        (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
        (n := 2 ^ 30) (h := 2 ^ 29) (k := 2 ^ 26)
        dom (by norm_num) (by norm_num) (by norm_num) u
  have hcode :
      evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g
          (2 ^ 30) (2 ^ 26 - 1) =
        (ReedSolomon.code dom (2 ^ 26) :
          Set (Fin (2 ^ 30) → ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)) := by
    simpa only [dom, Nat.sub_add_cancel (by norm_num : 1 ≤ 2 ^ 26)] using
      (ProximityGap.KKH26RegimeSplit.evalCode_eq_reedSolomon
        ArkLib.ProximityGap.PrizeShapePrimeP30.g
        ArkLib.ProximityGap.PrizeShapePrimeP30.orderOf_g hg0
        (2 ^ 26 - 1))
  rw [← hcode] at hcount
  simpa only [halfPredecessorRadius,
    ArkLib.ProximityGap.Frontier.R382HalfRadiusPinConnector.halfPredecessorRadius]
    using hcount

/-- **Unconditional first-prime rate-`1/8` pin.**  The complete exceptional-line
pruning and third-moment incidence theorem bounds the literal predecessor bad-scalar
set by the code length, so the operational threshold is exactly `1/2`. -/
theorem firstPrime_rateEighth_deltaStar_eq_half :
    mcaDeltaStar
      (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
      (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
      (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 27 - 1))
      (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) = (1 / 2 : ℝ≥0) := by
  letI : NeZero (2 ^ 30 : ℕ) := ⟨by norm_num⟩
  apply evalCode_deltaStar_eq_half_of_predecessor_badCount_le
    ArkLib.ProximityGap.PrizeShapePrimeP30.orderOf_g
    (by norm_num) (by norm_num) (by norm_num)
    ArkLib.ProximityGap.PrizeShapePrimeP30.P_div_two_pow_128
    (by norm_num) (by norm_num)
  intro u
  have hg0 : ArkLib.ProximityGap.PrizeShapePrimeP30.g ≠ 0 :=
    ProximityGap.KKH26RegimeSplit.ne_zero_of_orderOf_eq
      ArkLib.ProximityGap.PrizeShapePrimeP30.orderOf_g
  let dom : Fin (2 ^ 30) ↪ ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P :=
    ProximityGap.KKH26RegimeSplit.powDomain
      ArkLib.ProximityGap.PrizeShapePrimeP30.g
      ArkLib.ProximityGap.PrizeShapePrimeP30.orderOf_g hg0
  have hcount :=
    ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthFullWiring.halfPredecessor_badScalar_filter_card_le_two_pow_thirty
      (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
      (k := 2 ^ 27) dom (by norm_num) (by norm_num) u
  have hcode :
      evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g
          (2 ^ 30) (2 ^ 27 - 1) =
        (ReedSolomon.code dom (2 ^ 27) :
          Set (Fin (2 ^ 30) → ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)) := by
    simpa only [dom, Nat.sub_add_cancel (by norm_num : 1 ≤ 2 ^ 27)] using
      (ProximityGap.KKH26RegimeSplit.evalCode_eq_reedSolomon
        ArkLib.ProximityGap.PrizeShapePrimeP30.g
        ArkLib.ProximityGap.PrizeShapePrimeP30.orderOf_g hg0
        (2 ^ 27 - 1))
  rw [← hcode] at hcount
  simpa only [halfPredecessorRadius,
    ArkLib.ProximityGap.Frontier.R382HalfRadiusPinConnector.halfPredecessorRadius]
    using hcount

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
    (by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 32)]
      norm_num) hcount hbudget

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

/-- **Unconditional second-prime rate-`1/16` lower pin.**  The assembled
`17/32` incidence theorem supplies the literal `2n` scalar budget. -/
theorem secondPrime_rateSixteenth_seventeenThirtyTwo_le_deltaStar :
    (17 / 32 : ℝ≥0) ≤
      mcaDeltaStar
        (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
        (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
        (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
          (2 ^ 30) (2 ^ 26 - 1))
        (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) := by
  apply secondPrime_rateSixteenth_seventeenThirtyTwo_le_deltaStar_of_badCount
  intro u
  letI : NeZero (2 ^ 30 : ℕ) := ⟨by norm_num⟩
  have hg0 : ArkLib.ProximityGap.PrizeShapePrimeP30Second.g ≠ 0 :=
    ProximityGap.KKH26RegimeSplit.ne_zero_of_orderOf_eq
      ArkLib.ProximityGap.PrizeShapePrimeP30Second.orderOf_g
  let dom : Fin (2 ^ 30) ↪ ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P :=
    ProximityGap.KKH26RegimeSplit.powDomain
      ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
      ArkLib.ProximityGap.PrizeShapePrimeP30Second.orderOf_g hg0
  have hcount :=
    ArkLib.ProximityGap.Frontier.SeventeenThirtyTwoFullWiring.seventeenThirtyTwo_badScalar_filter_card_le_two_mul_length
      (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
      (n := 2 ^ 30) (m := 2 ^ 25) (k := 2 ^ 26)
      dom (by norm_num) (by norm_num) (by norm_num) u
  have hcode :
      evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
          (2 ^ 30) (2 ^ 26 - 1) =
        (ReedSolomon.code dom (2 ^ 26) :
          Set (Fin (2 ^ 30) → ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)) := by
    simpa only [dom, Nat.sub_add_cancel (by norm_num : 1 ≤ 2 ^ 26)] using
      (ProximityGap.KKH26RegimeSplit.evalCode_eq_reedSolomon
        ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
        ArkLib.ProximityGap.PrizeShapePrimeP30Second.orderOf_g hg0
        (2 ^ 26 - 1))
  rw [← hcode] at hcount
  simpa only [show 2 * 2 ^ 30 = 2 ^ 31 by norm_num] using hcount

/-- The two certified prize-shaped fields have genuinely different operational
rate-`1/16` thresholds: the second lies strictly above the first field's exact half pin. -/
theorem secondPrime_rateSixteenth_half_lt_deltaStar :
    (1 / 2 : ℝ≥0) <
      mcaDeltaStar
        (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
        (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
        (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
          (2 ^ 30) (2 ^ 26 - 1))
        (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) :=
  lt_of_lt_of_le (by norm_num)
    secondPrime_rateSixteenth_seventeenThirtyTwo_le_deltaStar

end ArkLib.ProximityGap.Frontier.PrizeShapeLowRateExactPins

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.PrizeShapeLowRateExactPins.evalCode_deltaStar_eq_half_of_predecessor_badCount_le
#print axioms
  ArkLib.ProximityGap.Frontier.PrizeShapeLowRateExactPins.firstPrime_rateSixteenth_deltaStar_eq_half_of_badCount
#print axioms
  ArkLib.ProximityGap.Frontier.PrizeShapeLowRateExactPins.firstPrime_rateSixteenth_deltaStar_eq_half
#print axioms
  ArkLib.ProximityGap.Frontier.PrizeShapeLowRateExactPins.firstPrime_rateEighth_deltaStar_eq_half
#print axioms
  ArkLib.ProximityGap.Frontier.PrizeShapeLowRateExactPins.secondPrime_rateSixteenth_half_lt_deltaStar_of_badCount
#print axioms
  ArkLib.ProximityGap.Frontier.PrizeShapeLowRateExactPins.secondPrime_rateSixteenth_half_lt_deltaStar
