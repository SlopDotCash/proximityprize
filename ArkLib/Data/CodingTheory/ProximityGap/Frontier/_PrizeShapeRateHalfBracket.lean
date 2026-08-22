/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Frontier._GenericQuotientInterpolationSpread
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SecondMomentUniformFieldWindow
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30Second
import ArkLib.Data.CodingTheory.ProximityGap.ProductionRegimeBracket

/-!
# A concrete prize-shaped bracket at exact rate one half

The uniform quotient-field wrapper uses enough support for every field below `2^256`,
and therefore starts at quotient size `256`.  For either certified `n = 2^30`
prize-shaped field, the exact quotient `p / 2^128` is only `n` or `2n`.  Retaining that
field-normalized value in the second-moment argument makes quotient size `64` sufficient.

For exact rate `1/2`, the quotient parameters are

`s = 64`, `r = 33`, `m = 2^24`,

so the bad radius is `1 - r/s = 31/64` and the code dimension is
`(r-1)m = 2^29`, exactly half of `n`.  This yields unconditional operational ceilings
at `31/64` for both certified fields.  The ordinary RS staircase supplies the current
unconditional good-side floor

`((2^29)/3 + 1) / 2^30 = 178956971 / 2^30`.

The file also isolates the exact remaining one-rung residual for the first field: a
literal `n`-point bad-scalar cap at the predecessor of `31/64` would pin the operational
threshold to `31/64`.  In contrast, the analogous cap at the predecessor of `1/2` is
formally refuted by the quotient construction.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

open Finset
open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger Code
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket

open ArkLib.ProximityGap.Frontier.GenericQuotientInterpolationSpread
open ArkLib.ProximityGap.Frontier.SecondMomentUniformFieldWindow

attribute [local instance] Classical.propDecidable

/-! ## Generic arithmetic and lattice connectors -/

/-- A finite count budget `E * Q <= p` gives the normalized bound `E/p <= Q^-1`. -/
theorem natCast_div_le_inv_of_mul_le {E Q p : Nat}
    (hQ : 0 < Q) (hp : 0 < p) (hbudget : E * Q <= p) :
    (E : ENNReal) / (p : ENNReal) <= ((Q : ENNReal)⁻¹ : ENNReal) := by
  have hp0 : (p : ENNReal) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hpTop : (p : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top p
  rw [ENNReal.div_le_iff hp0 hpTop]
  have hQ0 : (Q : ENNReal) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hQTop : (Q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top Q
  calc
    (E : ENNReal) <= (E : ENNReal) * Q * (Q : ENNReal)⁻¹ := by
      rw [mul_assoc, ENNReal.mul_inv_cancel hQ0 hQTop, mul_one]
    _ <= (p : ENNReal) * (Q : ENNReal)⁻¹ := by
      gcongr
      exact_mod_cast hbudget
    _ = (Q : ENNReal)⁻¹ * (p : ENNReal) := mul_comm _ _

/-- The canonical prize error, coerced to `ENNReal`, is the inverse of the natural
power `2^128`. -/
theorem epsStar_coe_eq_natCast_inv :
    (ProximityGap.epsStar : ENNReal) = (((2 ^ 128 : Nat) : ENNReal)⁻¹ : ENNReal) := by
  rw [ProximityGap.epsStar]
  norm_num [one_div]

/-- The lattice point immediately before `a/n`. -/
noncomputable def predecessorRadius (n a : Nat) : NNReal :=
  ((a - 1 : Nat) : NNReal) / (n : NNReal)

/-- A good predecessor fills the entire open real interval below the next Hamming
lattice point.  This is the general form of the half-predecessor connector. -/
theorem latticeBoundary_le_mcaDeltaStar_of_predecessor_good
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n a : Nat} [NeZero n] (ha1 : 1 <= a) (han : a <= n)
    (C : Set (Fin n -> F)) (epsilonStar : ENNReal)
    (hprev : epsMCA (F := F) (A := F) C (predecessorRadius n a) <= epsilonStar) :
    (a : NNReal) / (n : NNReal) <=
      mcaDeltaStar (F := F) (A := F) C epsilonStar := by
  let w : Nat := a - 1
  let deltaPrev : NNReal := predecessorRadius n a
  let deltaBoundary : NNReal := (a : NNReal) / (n : NNReal)
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn0 : (n : NNReal) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hwa : w + 1 = a := by
    dsimp only [w]
    omega
  have hprevMul : deltaPrev * (n : NNReal) = (w : NNReal) := by
    dsimp only [deltaPrev, predecessorRadius, w]
    exact div_mul_cancel₀ _ hn0
  have hboundaryMul : deltaBoundary * (n : NNReal) = (a : NNReal) := by
    dsimp only [deltaBoundary]
    exact div_mul_cancel₀ _ hn0
  have hboundaryLeOne : deltaBoundary <= 1 := by
    dsimp only [deltaBoundary]
    rw [div_le_one (by positivity)]
    exact_mod_cast han
  have hgood : forall delta : NNReal, delta < deltaBoundary ->
      epsMCA (F := F) (A := F) C delta <= epsilonStar := by
    intro delta hdelta
    by_cases hle : delta <= deltaPrev
    · exact le_trans (epsMCA_mono C hle) hprev
    · have hprevDelta : deltaPrev < delta := lt_of_not_ge hle
      have hlowerFloor : (w : NNReal) <= delta * (n : NNReal) := by
        have hm := mul_lt_mul_of_pos_right hprevDelta (by positivity)
        rw [hprevMul] at hm
        exact hm.le
      have hupperFloor : delta * (n : NNReal) < (a : NNReal) := by
        have hm := mul_lt_mul_of_pos_right hdelta (by positivity)
        rwa [hboundaryMul] at hm
      have hfloorDelta :
          Nat.floor (delta * (Fintype.card (Fin n) : NNReal)) = w := by
        rw [Fintype.card_fin, Nat.floor_eq_iff (zero_le _)]
        constructor
        · exact hlowerFloor
        · have hcast : ((w : NNReal) + 1) = (a : NNReal) := by
            exact_mod_cast hwa
          rw [hcast]
          exact hupperFloor
      have hfloorPrev :
          Nat.floor (deltaPrev * (Fintype.card (Fin n) : NNReal)) = w := by
        rw [Fintype.card_fin, hprevMul, Nat.floor_natCast]
      rw [ProximityGap.epsMCA_eq_of_floor_eq (F := F) (A := F) C
        (hfloorDelta.trans hfloorPrev.symm)]
      exact hprev
  change deltaBoundary <= mcaDeltaStar (F := F) (A := F) C epsilonStar
  by_contra hnot
  rw [not_le] at hnot
  obtain ⟨delta, hstarDelta, hdeltaBoundary⟩ := exists_between hnot
  have hdeltaLe := le_mcaDeltaStar_of_good (F := F) (A := F) C epsilonStar
    (le_trans hdeltaBoundary.le hboundaryLeOne) (hgood delta hdeltaBoundary)
  exact (not_lt_of_ge hdeltaLe) hstarDelta

/-! ## Field-normalized quotient spread -/

/-- The rounded quotient second-moment construction, retaining the actual field quotient
instead of replacing it by the uniform worst-case bound `2^128+2`. -/
theorem epsStar_lt_epsMCA_of_exact_rounded_quotient_supply
    {p s m r : Nat} [Fact p.Prime] [NeZero s] [NeZero m]
    (hpLo : 2 ^ 128 <= p) (hpHi : p < 2 ^ 256)
    (hs : 1 <= s) (hm : 1 <= m) (hr2 : 2 <= r) (hr : r <= s)
    {g : ZMod p} (hg : orderOf g = s * m)
    (hSupply : p / 2 ^ 128 + 3 <= Nat.choose s r) :
    (ProximityGap.epsStar : ENNReal) <
      epsMCA (F := ZMod p) (evalCode g (s * m) ((r - 1) * m - 1))
        (1 - (r : NNReal) / (s : NNReal)) := by
  let M : Nat := p / 2 ^ 128 + 3
  have hMle : M * M <= M * p := by
    simpa only [M, pow_two] using
      (rounded_family_sq_le_mul_field (Q := 2 ^ 128) (p := p) (by norm_num) hpLo)
  have hNum : p * p < 2 ^ 128 * (M * p - M * M) := by
    simpa only [M, pow_two] using prize_field_sq_lt_secondMoment_numerator hpLo hpHi
  have hStrict : (ProximityGap.epsStar : ENNReal) <
      (((M : ENNReal) - (M * M : ENNReal) / (p : ENNReal)) / (p : ENNReal)) :=
    ProximityGap.epsStar_lt_second_moment_value (by omega) hMle hNum
  exact hStrict.trans_le
    (genericQuotient_epsMCA_lower_bound_secondMoment hs hm hr2 hr hg M
      (by simpa only [M] using hSupply))

/-- Operational ceiling from the exact field-normalized rounded supply. -/
theorem mcaDeltaStar_le_of_exact_rounded_quotient_supply
    {p s m r : Nat} [Fact p.Prime] [NeZero s] [NeZero m]
    (hpLo : 2 ^ 128 <= p) (hpHi : p < 2 ^ 256)
    (hs : 1 <= s) (hm : 1 <= m) (hr2 : 2 <= r) (hr : r <= s)
    {g : ZMod p} (hg : orderOf g = s * m)
    (hSupply : p / 2 ^ 128 + 3 <= Nat.choose s r) :
    mcaDeltaStar (F := ZMod p)
        (evalCode g (s * m) ((r - 1) * m - 1))
        (ProximityGap.epsStar : ENNReal) <=
      1 - (r : NNReal) / (s : NNReal) :=
  mcaDeltaStar_le_of_bad _ _
    (epsStar_lt_epsMCA_of_exact_rounded_quotient_supply
      hpLo hpHi hs hm hr2 hr hg hSupply)

/-! ## Concrete exact-rate-half instances -/

local instance firstPrimeFact :
    Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

local instance secondPrimeFact :
    Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- The immediately preceding dyadic quotient has too few central supports even for the
smaller first-field rounded target. -/
theorem firstPrime_rateHalf_s32_supply_short :
    Nat.choose 32 17 <
      ArkLib.ProximityGap.PrizeShapePrimeP30.P / 2 ^ 128 + 3 := by
  rw [ArkLib.ProximityGap.PrizeShapePrimeP30.P_div_two_pow_128]
  norm_num [Nat.choose]

/-- The size-`32` quotient is also too short for the larger second-field budget. -/
theorem secondPrime_rateHalf_s32_supply_short :
    Nat.choose 32 17 <
      ArkLib.ProximityGap.PrizeShapePrimeP30Second.P / 2 ^ 128 + 3 := by
  rw [ArkLib.ProximityGap.PrizeShapePrimeP30Second.P_div_two_pow_128]
  norm_num [Nat.choose]

/-- Quotient size `64` has ample supply for the first certified field. -/
theorem firstPrime_rateHalf_s64_supply :
    ArkLib.ProximityGap.PrizeShapePrimeP30.P / 2 ^ 128 + 3 <= Nat.choose 64 33 := by
  rw [ArkLib.ProximityGap.PrizeShapePrimeP30.P_div_two_pow_128]
  norm_num [Nat.choose]

/-- Quotient size `64` also has ample supply for the second certified field. -/
theorem secondPrime_rateHalf_s64_supply :
    ArkLib.ProximityGap.PrizeShapePrimeP30Second.P / 2 ^ 128 + 3 <=
      Nat.choose 64 33 := by
  rw [ArkLib.ProximityGap.PrizeShapePrimeP30Second.P_div_two_pow_128]
  norm_num [Nat.choose]

/-- Strict badness at `31/64` for the first exact-rate-half prize-shaped code. -/
theorem firstPrime_rateHalf_epsStar_lt_epsMCA_thirtyOneSixtyFour :
    (ProximityGap.epsStar : ENNReal) <
      epsMCA (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
        (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g
          (2 ^ 30) (2 ^ 29 - 1)) (31 / 64 : NNReal) := by
  letI : NeZero (64 : Nat) := ⟨by norm_num⟩
  letI : NeZero (2 ^ 24 : Nat) := ⟨by norm_num⟩
  have h := epsStar_lt_epsMCA_of_exact_rounded_quotient_supply
    (p := ArkLib.ProximityGap.PrizeShapePrimeP30.P)
    (s := 64) (m := 2 ^ 24) (r := 33)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    ArkLib.ProximityGap.PrizeShapePrimeP30.orderOf_g
    firstPrime_rateHalf_s64_supply
  have hn : 64 * 2 ^ 24 = 2 ^ 30 := by norm_num
  have hd : (33 - 1) * 2 ^ 24 - 1 = 2 ^ 29 - 1 := by norm_num
  have hradius : (1 : NNReal) - ((33 : Nat) : NNReal) / ((64 : Nat) : NNReal) =
      31 / 64 := by
    have hfrac : (((33 : Nat) : NNReal) / ((64 : Nat) : NNReal)) <= 1 := by
      rw [div_le_one (by positivity)]
      norm_num
    rw [tsub_eq_iff_eq_add_of_le hfrac]
    apply NNReal.eq
    norm_num
  rw [hn, hd, hradius] at h
  exact h

/-- **First-field exact-rate-half ceiling:** `deltaStar <= 31/64`. -/
theorem firstPrime_rateHalf_mcaDeltaStar_le_thirtyOneSixtyFour :
    mcaDeltaStar
      (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
      (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
      (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g
        (2 ^ 30) (2 ^ 29 - 1))
      (ProximityGap.epsStar : ENNReal) <= (31 / 64 : NNReal) :=
  mcaDeltaStar_le_of_bad _ _ firstPrime_rateHalf_epsStar_lt_epsMCA_thirtyOneSixtyFour

/-- **Second-field exact-rate-half ceiling:** `deltaStar <= 31/64`. -/
theorem secondPrime_rateHalf_mcaDeltaStar_le_thirtyOneSixtyFour :
    mcaDeltaStar
      (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
      (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
      (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
        (2 ^ 30) (2 ^ 29 - 1))
      (ProximityGap.epsStar : ENNReal) <= (31 / 64 : NNReal) := by
  letI : NeZero (64 : Nat) := ⟨by norm_num⟩
  letI : NeZero (2 ^ 24 : Nat) := ⟨by norm_num⟩
  have h := mcaDeltaStar_le_of_exact_rounded_quotient_supply
    (p := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
    (s := 64) (m := 2 ^ 24) (r := 33)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    ArkLib.ProximityGap.PrizeShapePrimeP30Second.orderOf_g
    secondPrime_rateHalf_s64_supply
  have hn : 64 * 2 ^ 24 = 2 ^ 30 := by norm_num
  have hd : (33 - 1) * 2 ^ 24 - 1 = 2 ^ 29 - 1 := by norm_num
  have hradius : (1 : NNReal) - ((33 : Nat) : NNReal) / ((64 : Nat) : NNReal) =
      31 / 64 := by
    have hfrac : (((33 : Nat) : NNReal) / ((64 : Nat) : NNReal)) <= 1 := by
      rw [div_le_one (by positivity)]
      norm_num
    rw [tsub_eq_iff_eq_add_of_le hfrac]
    apply NNReal.eq
    norm_num
  rw [hn, hd, hradius] at h
  exact h

/-- The production staircase reaches `178956971 / 2^30` unconditionally in the first field. -/
theorem firstPrime_rateHalf_ladder_floor :
    (178956971 : NNReal) / (2 ^ 30 : NNReal) <=
      mcaDeltaStar
        (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
        (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
        (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g
          (2 ^ 30) (2 ^ 29 - 1))
        (ProximityGap.epsStar : ENNReal) := by
  letI : NeZero (2 ^ 30 : Nat) := ⟨by norm_num⟩
  let dom : Fin (2 ^ 30) ↪ ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P :=
    ProximityGap.Ownership.smoothDom ArkLib.ProximityGap.PrizeShapePrimeP30.g
      (2 ^ 30) ArkLib.ProximityGap.PrizeShapePrimeP30.orderOf_g
  have hbudget : ((2 ^ 30 : Nat) : ENNReal) /
      (Fintype.card (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P) : ENNReal) <=
        (ProximityGap.epsStar : ENNReal) := by
    rw [ZMod.card]
    have h := natCast_div_le_inv_of_mul_le
      (E := 2 ^ 30) (Q := 2 ^ 128)
      (p := ArkLib.ProximityGap.PrizeShapePrimeP30.P)
      (by norm_num) ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P.pos (by norm_num)
    rwa [epsStar_coe_eq_natCast_inv]
  have hlower := ProximityGap.ProductionRegime.production_good_ladder_reach
    (dom := dom) (k := 2 ^ 29) (by norm_num) hbudget
  have hcode :
      evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g
          (2 ^ 30) (2 ^ 29 - 1) =
        ((ProximityGap.SpikeFloor.rsCode dom (2 ^ 29) :
          Submodule (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
            (Fin (2 ^ 30) -> ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)) :
          Set (Fin (2 ^ 30) -> ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)) := by
    simpa only [dom, Nat.sub_add_cancel (by norm_num : 1 <= 2 ^ 29)] using
      (ProximityGap.Ownership.evalCode_eq_rsCode
        ArkLib.ProximityGap.PrizeShapePrimeP30.orderOf_g (2 ^ 29 - 1))
  rw [← hcode] at hlower
  convert hlower using 1 <;> norm_num

/-- The same unconditional staircase floor in the second certified field. -/
theorem secondPrime_rateHalf_ladder_floor :
    (178956971 : NNReal) / (2 ^ 30 : NNReal) <=
      mcaDeltaStar
        (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
        (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
        (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
          (2 ^ 30) (2 ^ 29 - 1))
        (ProximityGap.epsStar : ENNReal) := by
  letI : NeZero (2 ^ 30 : Nat) := ⟨by norm_num⟩
  let dom : Fin (2 ^ 30) ↪ ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P :=
    ProximityGap.Ownership.smoothDom ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
      (2 ^ 30) ArkLib.ProximityGap.PrizeShapePrimeP30Second.orderOf_g
  have hbudget : ((2 ^ 30 : Nat) : ENNReal) /
      (Fintype.card (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) : ENNReal) <=
        (ProximityGap.epsStar : ENNReal) := by
    rw [ZMod.card]
    have h := natCast_div_le_inv_of_mul_le
      (E := 2 ^ 30) (Q := 2 ^ 128)
      (p := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
      (by norm_num) ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P.pos (by norm_num)
    rwa [epsStar_coe_eq_natCast_inv]
  have hlower := ProximityGap.ProductionRegime.production_good_ladder_reach
    (dom := dom) (k := 2 ^ 29) (by norm_num) hbudget
  have hcode :
      evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
          (2 ^ 30) (2 ^ 29 - 1) =
        ((ProximityGap.SpikeFloor.rsCode dom (2 ^ 29) :
          Submodule (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
            (Fin (2 ^ 30) -> ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)) :
          Set (Fin (2 ^ 30) -> ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)) := by
    simpa only [dom, Nat.sub_add_cancel (by norm_num : 1 <= 2 ^ 29)] using
      (ProximityGap.Ownership.evalCode_eq_rsCode
        ArkLib.ProximityGap.PrizeShapePrimeP30Second.orderOf_g (2 ^ 29 - 1))
  rw [← hcode] at hlower
  convert hlower using 1 <;> norm_num

/-- The strongest presently unconditional concrete bracket supplied by the landed
good- and bad-side mechanisms in the first field. -/
theorem firstPrime_rateHalf_deltaStar_bracket :
    (178956971 : NNReal) / (2 ^ 30 : NNReal) <=
        mcaDeltaStar
          (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
          (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
          (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g
            (2 ^ 30) (2 ^ 29 - 1))
          (ProximityGap.epsStar : ENNReal) ∧
      mcaDeltaStar
          (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
          (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
          (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g
            (2 ^ 30) (2 ^ 29 - 1))
          (ProximityGap.epsStar : ENNReal) <= (31 / 64 : NNReal) :=
  ⟨firstPrime_rateHalf_ladder_floor,
    firstPrime_rateHalf_mcaDeltaStar_le_thirtyOneSixtyFour⟩

/-- The corresponding unconditional concrete bracket in the second certified field. -/
theorem secondPrime_rateHalf_deltaStar_bracket :
    (178956971 : NNReal) / (2 ^ 30 : NNReal) <=
        mcaDeltaStar
          (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
          (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
          (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
            (2 ^ 30) (2 ^ 29 - 1))
          (ProximityGap.epsStar : ENNReal) ∧
      mcaDeltaStar
          (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
          (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
          (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
            (2 ^ 30) (2 ^ 29 - 1))
          (ProximityGap.epsStar : ENNReal) <= (31 / 64 : NNReal) :=
  ⟨secondPrime_rateHalf_ladder_floor,
    secondPrime_rateHalf_mcaDeltaStar_le_thirtyOneSixtyFour⟩

/-! ## The exact residual and the half-predecessor refutation -/

/-- A literal `n`-scalar cap at the predecessor of `31/64` would make the quotient
ceiling exact.  This is the smallest one-rung all-stack residual left by the bracket. -/
theorem firstPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count
    (hcount : forall u : WordStack
      (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P) (Fin 2) (Fin (2 ^ 30)),
      (Finset.univ.filter fun gamma : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P =>
        mcaEvent
          (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g
            (2 ^ 30) (2 ^ 29 - 1))
          (predecessorRadius (2 ^ 30) (31 * 2 ^ 24))
          (u 0) (u 1) gamma).card <= 2 ^ 30) :
    mcaDeltaStar
      (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
      (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
      (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g
        (2 ^ 30) (2 ^ 29 - 1))
      (ProximityGap.epsStar : ENNReal) = (31 / 64 : NNReal) := by
  letI : NeZero (2 ^ 30 : Nat) := ⟨by norm_num⟩
  have hbudget : ((2 ^ 30 : Nat) : ENNReal) /
      (Fintype.card (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P) : ENNReal) <=
        (ProximityGap.epsStar : ENNReal) := by
    rw [ZMod.card]
    have h := natCast_div_le_inv_of_mul_le
      (E := 2 ^ 30) (Q := 2 ^ 128)
      (p := ArkLib.ProximityGap.PrizeShapePrimeP30.P)
      (by norm_num) ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P.pos (by norm_num)
    rwa [epsStar_coe_eq_natCast_inv]
  have hprev : epsMCA
      (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
      (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
      (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g
        (2 ^ 30) (2 ^ 29 - 1))
      (predecessorRadius (2 ^ 30) (31 * 2 ^ 24)) <=
        (ProximityGap.epsStar : ENNReal) :=
    le_trans
      (epsMCA_le_of_badCount_le
        (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g
          (2 ^ 30) (2 ^ 29 - 1))
        (predecessorRadius (2 ^ 30) (31 * 2 ^ 24)) (2 ^ 30) hcount)
      hbudget
  have hlower := latticeBoundary_le_mcaDeltaStar_of_predecessor_good
    (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
    (n := 2 ^ 30) (a := 31 * 2 ^ 24)
    (by norm_num) (by norm_num)
    (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g
      (2 ^ 30) (2 ^ 29 - 1))
    (ProximityGap.epsStar : ENNReal) hprev
  have hlower' : (31 / 64 : NNReal) <=
      mcaDeltaStar
        (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
        (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
        (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g
          (2 ^ 30) (2 ^ 29 - 1))
        (ProximityGap.epsStar : ENNReal) := by
    convert hlower using 1 <;> norm_num
  exact le_antisymm firstPrime_rateHalf_mcaDeltaStar_le_thirtyOneSixtyFour hlower'

/-- In the second certified field the exact normalized budget is twice the block
length.  Thus a `2n`-scalar cap at the same predecessor pins the same quotient
ceiling exactly. -/
theorem secondPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count
    (hcount : forall u : WordStack
      (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) (Fin 2) (Fin (2 ^ 30)),
      (Finset.univ.filter fun gamma : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P =>
        mcaEvent
          (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
            (2 ^ 30) (2 ^ 29 - 1))
          (predecessorRadius (2 ^ 30) (31 * 2 ^ 24))
          (u 0) (u 1) gamma).card <= 2 ^ 31) :
    mcaDeltaStar
      (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
      (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
      (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
        (2 ^ 30) (2 ^ 29 - 1))
      (ProximityGap.epsStar : ENNReal) = (31 / 64 : NNReal) := by
  letI : NeZero (2 ^ 30 : Nat) := ⟨by norm_num⟩
  have hbudget : ((2 ^ 31 : Nat) : ENNReal) /
      (Fintype.card (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) : ENNReal) <=
        (ProximityGap.epsStar : ENNReal) := by
    rw [ZMod.card]
    have h := natCast_div_le_inv_of_mul_le
      (E := 2 ^ 31) (Q := 2 ^ 128)
      (p := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
      (by norm_num) ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P.pos (by norm_num)
    rwa [epsStar_coe_eq_natCast_inv]
  have hprev : epsMCA
      (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
      (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
      (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
        (2 ^ 30) (2 ^ 29 - 1))
      (predecessorRadius (2 ^ 30) (31 * 2 ^ 24)) <=
        (ProximityGap.epsStar : ENNReal) :=
    le_trans
      (epsMCA_le_of_badCount_le
        (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
          (2 ^ 30) (2 ^ 29 - 1))
        (predecessorRadius (2 ^ 30) (31 * 2 ^ 24)) (2 ^ 31) hcount)
      hbudget
  have hlower := latticeBoundary_le_mcaDeltaStar_of_predecessor_good
    (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
    (n := 2 ^ 30) (a := 31 * 2 ^ 24)
    (by norm_num) (by norm_num)
    (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
      (2 ^ 30) (2 ^ 29 - 1))
    (ProximityGap.epsStar : ENNReal) hprev
  have hlower' : (31 / 64 : NNReal) <=
      mcaDeltaStar
        (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
        (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
        (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
          (2 ^ 30) (2 ^ 29 - 1))
        (ProximityGap.epsStar : ENNReal) := by
    convert hlower using 1 <;> norm_num
  exact le_antisymm secondPrime_rateHalf_mcaDeltaStar_le_thirtyOneSixtyFour hlower'

/-- **Naive half-predecessor refutation at exact rate `1/2`.**  There cannot be an
all-stack `n`-scalar bound at the last lattice point below `1/2`: monotonicity would make
`31/64` good, contradicting the unconditional quotient-spread bad witness there. -/
theorem firstPrime_rateHalf_not_halfPredecessor_badCount_le_length :
    ¬ (forall u : WordStack
      (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P) (Fin 2) (Fin (2 ^ 30)),
      (Finset.univ.filter fun gamma : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P =>
        mcaEvent
          (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g
            (2 ^ 30) (2 ^ 29 - 1))
          (((2 ^ 29 - 1 : Nat) : NNReal) / (2 ^ 30 : NNReal))
          (u 0) (u 1) gamma).card <= 2 ^ 30) := by
  intro hcount
  have hbudget : ((2 ^ 30 : Nat) : ENNReal) /
      (Fintype.card (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P) : ENNReal) <=
        (ProximityGap.epsStar : ENNReal) := by
    rw [ZMod.card]
    have h := natCast_div_le_inv_of_mul_le
      (E := 2 ^ 30) (Q := 2 ^ 128)
      (p := ArkLib.ProximityGap.PrizeShapePrimeP30.P)
      (by norm_num) ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P.pos (by norm_num)
    rwa [epsStar_coe_eq_natCast_inv]
  have hhalfGood : epsMCA
      (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
      (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
      (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g
        (2 ^ 30) (2 ^ 29 - 1))
      (((2 ^ 29 - 1 : Nat) : NNReal) / (2 ^ 30 : NNReal)) <=
        (ProximityGap.epsStar : ENNReal) :=
    le_trans
      (epsMCA_le_of_badCount_le
        (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g
          (2 ^ 30) (2 ^ 29 - 1))
        (((2 ^ 29 - 1 : Nat) : NNReal) / (2 ^ 30 : NNReal))
        (2 ^ 30) hcount)
      hbudget
  have hmono := epsMCA_mono
    (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
    (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
    (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30.g
      (2 ^ 30) (2 ^ 29 - 1))
    (show (31 / 64 : NNReal) <=
      ((2 ^ 29 - 1 : Nat) : NNReal) / (2 ^ 30 : NNReal) by
        rw [le_div_iff₀ (by positivity : (0 : NNReal) < 2 ^ 30)]
        norm_num)
  have hle := le_trans hmono hhalfGood
  exact (not_lt_of_ge hle) firstPrime_rateHalf_epsStar_lt_epsMCA_thirtyOneSixtyFour

end ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket.latticeBoundary_le_mcaDeltaStar_of_predecessor_good
#print axioms
  ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket.epsStar_lt_epsMCA_of_exact_rounded_quotient_supply
#print axioms
  ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket.firstPrime_rateHalf_deltaStar_bracket
#print axioms
  ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket.secondPrime_rateHalf_deltaStar_bracket
#print axioms
  ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket.firstPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count
#print axioms
  ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket.secondPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count
#print axioms
  ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket.firstPrime_rateHalf_not_halfPredecessor_badCount_le_length
