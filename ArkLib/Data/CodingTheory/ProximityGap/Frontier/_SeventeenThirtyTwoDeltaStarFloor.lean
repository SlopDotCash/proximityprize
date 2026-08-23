/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SeventeenThirtyTwoFullWiring
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._GenericQuotientInterpolationSpread
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30Second
import ArkLib.Data.CodingTheory.ProximityGap.KKH26RegimeSplit
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# Operational delta-star floor from the rate-`1/16` `17/32` incidence theorem

`_SeventeenThirtyTwoFullWiring` proves a literal bad-scalar count of `2n` at radius
`17/32`.  This file supplies the reusable operational composition:

* `reedSolomon_epsMCA_seventeenThirtyTwo_le` turns the count into
  `epsMCA <= 2n / |F|`;
* `evalCode_seventeenThirtyTwo_le_mcaDeltaStar` turns the normalized budget
  `2n Q <= p` into `17/32 <= mcaDeltaStar` for a smooth evaluation code;
* `not_two_mul_length_budget_of_floor_eq_length` records that this particular
  route cannot fire on the tight quotient branch `p / Q = n`.
* the final two arithmetic lemmas show why the existing overlap-packing and
  near-capacity upper bounds cannot meet this `2n`-budget floor.

For the certified second prize-shaped field, the independent collision-free
generic-quotient ceiling does apply.  The final theorem combines the two routes into
the unconditional bracket `17/32 <= mcaDeltaStar <= 119/128`.

Thus the new good point is a genuine stronger lower bracket when the normalized
field budget reaches `2n`, but it does not strengthen the exact half pin on the
tight `n`-budget branch.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal
open _root_.ProximityGap Code
open _root_.ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.SeventeenThirtyTwoFullWiring
open ArkLib.ProximityGap.Frontier.GenericQuotientInterpolationSpread

namespace ArkLib.ProximityGap.Frontier.SeventeenThirtyTwoDeltaStarFloor

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
/-- The literal `2n` count from the incidence theorem, normalized as an
`epsMCA` bound over an arbitrary finite field. -/
theorem reedSolomon_epsMCA_seventeenThirtyTwo_le
    {n m k : ℕ} [NeZero n] (dom : Fin n ↪ F)
    (hn : n = 32 * m) (hk : 1 ≤ k) (hrate : 16 * k ≤ n) :
    epsMCA (F := F) (A := F)
        (ReedSolomon.code dom k : Set (Fin n → F)) (17 / 32 : ℝ≥0)
      ≤ ((2 * n : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  apply epsMCA_le_of_badCount_le
  intro u
  classical
  exact seventeenThirtyTwo_badScalar_filter_card_le_two_mul_length
    dom hn hk hrate u

/-- Clearing the two finite denominators in the operational budget comparison. -/
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

/-- Strict companion to `natCast_div_le_inv_of_mul_le`, used by explicit
bad-family upper brackets. -/
theorem inv_natCast_lt_natCast_div {Q p W : ℕ}
    (hQ : 0 < Q) (hp : 0 < p) (hsmall : p < Q * W) :
    ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) < (W : ℝ≥0∞) / (p : ℝ≥0∞) := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hpTop : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hp0) (Or.inl hpTop)]
  have hQ0 : (Q : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hQTop : (Q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top Q
  rw [← ENNReal.div_eq_inv_mul,
    ENNReal.div_lt_iff (Or.inl hQ0) (Or.inl hQTop)]
  exact_mod_cast (by simpa [Nat.mul_comm] using hsmall)

/-- **Generic beyond-half operational floor.**  For a length divisible by `32`,
rate at most `1/16`, and field budget `2n Q <= p`, the smooth-domain evaluation
code is good at `17/32`, hence its operational threshold is at least `17/32`. -/
theorem evalCode_seventeenThirtyTwo_le_mcaDeltaStar
    {p n m k Q : ℕ} [Fact p.Prime] [NeZero n]
    {g : ZMod p} (hg : orderOf g = n)
    (hn : n = 32 * m) (hk : 1 ≤ k) (hrate : 16 * k ≤ n)
    (hQ : 0 < Q) (hbudget : (2 * n) * Q ≤ p) :
    (17 / 32 : ℝ≥0) ≤
      mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (evalCode g n (k - 1)) ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) := by
  have hp : 0 < p := (Fact.out (p := p.Prime)).pos
  have hg0 : g ≠ 0 :=
    ProximityGap.KKH26RegimeSplit.ne_zero_of_orderOf_eq hg
  let dom : Fin n ↪ ZMod p :=
    ProximityGap.KKH26RegimeSplit.powDomain g hg hg0
  have hepsRS := reedSolomon_epsMCA_seventeenThirtyTwo_le
    (F := ZMod p) (n := n) (m := m) (k := k) dom hn hk hrate
  have hcode :
      evalCode g n (k - 1) =
        (ReedSolomon.code dom k : Set (Fin n → ZMod p)) := by
    simpa only [dom, Nat.sub_add_cancel hk] using
      (ProximityGap.KKH26RegimeSplit.evalCode_eq_reedSolomon
        g hg hg0 (k - 1))
  have heps :
      epsMCA (F := ZMod p) (A := ZMod p)
          (evalCode g n (k - 1)) (17 / 32 : ℝ≥0)
        ≤ ((2 * n : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) := by
    rw [hcode]
    simpa only [ZMod.card] using hepsRS
  have hnormalized :
      ((2 * n : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)
        ≤ ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) :=
    natCast_div_le_inv_of_mul_le hQ hp hbudget
  exact le_mcaDeltaStar_of_good
    (F := ZMod p) (A := ZMod p) (evalCode g n (k - 1))
    ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞)
    (by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 32)]
      norm_num)
    (heps.trans hnormalized)

/-- The `2n` budget required by the `17/32` count is incompatible with the
tight quotient `p / Q = n`.  This is the exact arithmetic reason the new good
point does not improve the already exact half pin on that branch. -/
theorem not_two_mul_length_budget_of_floor_eq_length
    {p n Q : ℕ} (hn : 0 < n) (hQ : 0 < Q) (hfloor : p / Q = n) :
    ¬ (2 * n) * Q ≤ p := by
  intro hbudget
  have hpLt : p < Q * (n + 1) := by
    simpa [hfloor] using Nat.lt_mul_div_succ p hQ
  have hstep : Q * (n + 1) ≤ (2 * n) * Q := by
    rw [Nat.mul_comm (2 * n) Q]
    exact Nat.mul_le_mul_left Q (by omega)
  omega

/-- In the legal overlap-packing range `e + k + 1 <= n`, its `2e+2`
bad scalars are strictly fewer than `2n` as soon as the code has positive
dimension.  Consequently that family cannot cross the normalized budget
used by the `17/32` floor. -/
theorem overlap_packing_count_lt_two_mul_length
    {n k e : ℕ} (hk : 1 ≤ k) (hecap : e + k + 1 ≤ n) :
    2 * e + 2 < 2 * n := by
  omega

/-- A field large enough to normalize a `2n` bad-count bound is not in the
small-field window `p < (n-k)Q` used by the standard near-capacity upper
bracket. -/
theorem not_nearCapacity_smallField_of_two_mul_length_budget
    {p n k Q : ℕ} (hkn : k ≤ n) (hbudget : (2 * n) * Q ≤ p) :
    ¬ p < (n - k) * Q := by
  intro hpSmall
  have hnk : n - k ≤ 2 * n := by omega
  have hmul : (n - k) * Q ≤ (2 * n) * Q :=
    Nat.mul_le_mul_right Q hnk
  omega

/-! ## The certified second-field bracket -/

local instance secondPrimeFact :
    Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- **A strictly stronger two-sided prize-field bracket.**  For the certified
prime with normalized quotient `2n`, the `17/32` incidence theorem supplies the
lower side.  The independent `s=128`, `r=9` generic-quotient family is
collision-free over this field and has mass above `2^-128`, supplying the upper
side `119/128`.  The endpoints do not coincide, so this is not an
exact pin. -/
theorem secondPrime_rateSixteenth_deltaStar_bracket :
    (17 / 32 : ℝ≥0) ≤
        mcaDeltaStar
          (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
          (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
          (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
            (2 ^ 30) (2 ^ 26 - 1))
          (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞)
      ∧
    mcaDeltaStar
          (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
          (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
          (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
            (2 ^ 30) (2 ^ 26 - 1))
          (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞)
      ≤ (119 / 128 : ℝ≥0) := by
  constructor
  · letI : NeZero (2 ^ 30 : ℕ) := ⟨by norm_num⟩
    exact evalCode_seventeenThirtyTwo_le_mcaDeltaStar
      (p := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
      (n := 2 ^ 30) (m := 2 ^ 25) (k := 2 ^ 26) (Q := 2 ^ 128)
      ArkLib.ProximityGap.PrizeShapePrimeP30Second.orderOf_g
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · letI : NeZero (2 ^ 23 : ℕ) := ⟨by norm_num⟩
    have hord : orderOf ArkLib.ProximityGap.PrizeShapePrimeP30Second.g =
        128 * 2 ^ 23 := by
      simpa only [show 128 * 2 ^ 23 = 2 ^ 30 by norm_num] using
        ArkLib.ProximityGap.PrizeShapePrimeP30Second.orderOf_g
    have heps : (ProximityGap.epsStar : ℝ≥0∞) =
        (((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) := by
      rw [ProximityGap.epsStar]
      push_cast
      rw [one_div]
      norm_num
    have hchoose : Nat.choose 128 9 = 19062702032000 := by
      norm_num [Nat.choose]
    have hcollision : (Nat.choose 128 9).choose 2 <
        ArkLib.ProximityGap.PrizeShapePrimeP30Second.P := by
      rw [hchoose, Nat.choose_two_right]
      norm_num
    have hfieldMass : ArkLib.ProximityGap.PrizeShapePrimeP30Second.P <
        2 ^ 128 * Nat.choose 128 9 := by
      norm_num [Nat.choose]
    have hmass : (ProximityGap.epsStar : ℝ≥0∞) <
        (Nat.choose 128 9 : ℝ≥0∞) /
          (ArkLib.ProximityGap.PrizeShapePrimeP30Second.P : ℝ≥0∞) := by
      rw [heps]
      exact inv_natCast_lt_natCast_div
        (by norm_num) ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P.pos
        hfieldMass
    have hupper :=
      genericQuotient_mcaDeltaStar_le
        (p := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
        (s := 128) (m := 2 ^ 23) (r := 9)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (g := ArkLib.ProximityGap.PrizeShapePrimeP30Second.g) hord
        hcollision (ProximityGap.epsStar : ℝ≥0∞) hmass
    have hradius : (1 : ℝ≥0) -
        ((9 : ℕ) : ℝ≥0) / ((128 : ℕ) : ℝ≥0) = 119 / 128 := by
      have hle : ((9 : ℕ) : ℝ≥0) / ((128 : ℕ) : ℝ≥0) ≤ 1 := by
        apply (div_le_iff₀ (by
          norm_num : (0 : ℝ≥0) < ((128 : ℕ) : ℝ≥0))).2
        norm_num
      rw [tsub_eq_iff_eq_add_of_le hle]
      norm_num
    rw [show 128 * 2 ^ 23 = 2 ^ 30 by norm_num,
      show (9 - 1) * 2 ^ 23 - 1 = 2 ^ 26 - 1 by norm_num,
      heps, hradius] at hupper
    exact hupper

end ArkLib.ProximityGap.Frontier.SeventeenThirtyTwoDeltaStarFloor

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.SeventeenThirtyTwoDeltaStarFloor

#print axioms reedSolomon_epsMCA_seventeenThirtyTwo_le
#print axioms evalCode_seventeenThirtyTwo_le_mcaDeltaStar
#print axioms not_two_mul_length_budget_of_floor_eq_length
#print axioms overlap_packing_count_lt_two_mul_length
#print axioms not_nearCapacity_smallField_of_two_mul_length_budget
#print axioms secondPrime_rateSixteenth_deltaStar_bracket
