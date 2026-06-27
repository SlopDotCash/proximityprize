/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ThornerZamanPNTStatement
import ArkLib.Data.CodingTheory.ProximityGap.KKH26TightCeiling

/-!
# Generic KKH26 tight square bridge from the Thorner-Zaman PNT statement

`_ThornerZamanPNTStatement.lean` intentionally stops at the lightweight reduction
`ThornerZamanPNT -> TZPrimeSupply`.  `KKH26TightCeiling.lean` now exposes the generic tight
square-budget KKH26 consumer in normalized form:

  `A^2 * (2^(mu-1) * log(2r)) / log(n^beta) < supply`.

This file composes those two pieces without specializing to `s = 128`.  The only unproved
mathematical input remains the named analytic proposition `ThornerZamanPNT`; the bridge itself is
  just the cardinality reduction plus the already-proven KKH26 tight ceiling.

The canonical floor-supply wrappers remove the auxiliary `supply` parameter entirely: callers
can compare the normalized KKH26 budget directly against the integer floor of the TZ density.
-/

open scoped NNReal ENNReal Nat

namespace ProximityGap.Frontier.KKH26ThornerZamanTightBridge

open ProximityGap.Frontier.ThornerZamanPNTStatement
  (ThornerZamanPNT tzDensityLB tzPrimeSupply_of_thornerZamanPNT
    tzPrimeSupply_of_thornerZamanPNT_natFloor)
open ArkLib.ProximityGap.KKH26
  (TZPrimeSupply evalCode kkh26_mcaDeltaStar_le_of_TZ_tight_square_bound_log
    tightResultantLogRatio_nonneg tightResultantLog_eq)

/-- If a nonnegative real budget is strictly below `floor(x)`, then `x` was nonnegative.

This removes the separate density-nonnegativity side condition from floor-supply wrappers whose
left-hand side is already known to be nonnegative. -/
lemma real_nonneg_of_nonneg_lt_natFloor {x budget : ℝ}
    (hbudget_nonneg : 0 ≤ budget) (hbudget_lt : budget < ((⌊x⌋₊ : ℕ) : ℝ)) :
    0 ≤ x := by
  have hfloor_pos : 0 < ⌊x⌋₊ := by
    by_contra hnot
    have hfloor0 : ⌊x⌋₊ = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hfloor0, Nat.cast_zero] at hbudget_lt
    exact not_lt_of_ge hbudget_nonneg hbudget_lt
  have hx_one : (1 : ℝ) ≤ x := Nat.floor_pos.mp hfloor_pos
  exact le_trans (by norm_num : (0 : ℝ) ≤ 1) hx_one

/-- **Generic Thorner-Zaman -> KKH26 tight ceiling bridge.**

If the named TZ density statement supplies enough primes in the progression `1 mod n`, and that
integer supply beats the normalized tight KKH26 square budget, then the polynomial-field-size
KKH26 `mcaDeltaStar` ceiling follows for arbitrary `mu`. -/
theorem kkh26_ceiling_of_thornerZamanPNT_tight_square_bound_log
    {n : ℕ} {beta eps : ℝ} {supply : ℕ} [NeZero n]
    (hTZ : ThornerZamanPNT n beta eps) {mu m r : ℕ}
    (hmu : 1 ≤ mu) (hm : 1 ≤ m) (hn : n = 2 ^ mu * m)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (mu - 1))
    (hx : 2 ≤ (n : ℝ) ^ beta)
    (hpl : (((2 : ℕ) ^ mu : ℕ) : ℝ) < (n : ℝ) ^ beta)
    (hsupply : (supply : ℝ) ≤ tzDensityLB n beta eps)
    (hcount : (((2 ^ r * (2 ^ (mu - 1)).choose r) ^ 2 : ℕ) : ℝ) *
        ((((2 ^ (mu - 1) : ℕ) : ℝ) * Real.log (((2 * r : ℕ) : ℝ))) /
          Real.log ((n : ℝ) ^ beta))
      < (supply : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧
      (n : ℝ) ^ beta ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ beta ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = n ∧
        ∀ epsStar : ℝ≥0∞,
          epsStar < ((2 ^ r * (2 ^ (mu - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g n ((r - 2) * m)) epsStar
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ mu) := by
  have hSupply : TZPrimeSupply n beta supply :=
    tzPrimeSupply_of_thornerZamanPNT hTZ hsupply
  exact kkh26_mcaDeltaStar_le_of_TZ_tight_square_bound_log
    (n := n) (β := beta) (supply := supply) (μ := mu) (m := m) (r := r)
    hSupply hmu hm hn hr2 hr hx hpl hcount

/-- **Natural-floor form of the generic bridge.**

This variant replaces the real side condition `supply <= tzDensityLB` by the checkable integer
condition `supply <= floor(tzDensityLB)`. -/
theorem kkh26_ceiling_of_thornerZamanPNT_natFloor_tight_square_bound_log
    {n : ℕ} {beta eps : ℝ} {supply : ℕ} [NeZero n]
    (hTZ : ThornerZamanPNT n beta eps) {mu m r : ℕ}
    (hmu : 1 ≤ mu) (hm : 1 ≤ m) (hn : n = 2 ^ mu * m)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (mu - 1))
    (hx : 2 ≤ (n : ℝ) ^ beta)
    (hpl : (((2 : ℕ) ^ mu : ℕ) : ℝ) < (n : ℝ) ^ beta)
    (hpos : 0 ≤ tzDensityLB n beta eps)
    (hsupply : supply ≤ ⌊tzDensityLB n beta eps⌋₊)
    (hcount : (((2 ^ r * (2 ^ (mu - 1)).choose r) ^ 2 : ℕ) : ℝ) *
        ((((2 ^ (mu - 1) : ℕ) : ℝ) * Real.log (((2 * r : ℕ) : ℝ))) /
          Real.log ((n : ℝ) ^ beta))
      < (supply : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧
      (n : ℝ) ^ beta ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ beta ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = n ∧
        ∀ epsStar : ℝ≥0∞,
          epsStar < ((2 ^ r * (2 ^ (mu - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g n ((r - 2) * m)) epsStar
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ mu) := by
  have hSupply : TZPrimeSupply n beta supply :=
    tzPrimeSupply_of_thornerZamanPNT_natFloor hTZ hpos hsupply
  exact kkh26_mcaDeltaStar_le_of_TZ_tight_square_bound_log
    (n := n) (β := beta) (supply := supply) (μ := mu) (m := m) (r := r)
    hSupply hmu hm hn hr2 hr hx hpl hcount

/-- **Canonical floor-supply form of the generic bridge.**

This is the most direct paper-facing version: the requested prime supply is exactly
`floor(tzDensityLB n beta eps)`, so callers only need a nonnegativity proof for the density and
the normalized tight KKH26 budget comparison against that floor. -/
theorem kkh26_ceiling_of_thornerZamanPNT_floor_tight_square_bound_log
    {n : ℕ} {beta eps : ℝ} [NeZero n]
    (hTZ : ThornerZamanPNT n beta eps) {mu m r : ℕ}
    (hmu : 1 ≤ mu) (hm : 1 ≤ m) (hn : n = 2 ^ mu * m)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (mu - 1))
    (hx : 2 ≤ (n : ℝ) ^ beta)
    (hpl : (((2 : ℕ) ^ mu : ℕ) : ℝ) < (n : ℝ) ^ beta)
    (hpos : 0 ≤ tzDensityLB n beta eps)
    (hcount : (((2 ^ r * (2 ^ (mu - 1)).choose r) ^ 2 : ℕ) : ℝ) *
        ((((2 ^ (mu - 1) : ℕ) : ℝ) * Real.log (((2 * r : ℕ) : ℝ))) /
          Real.log ((n : ℝ) ^ beta))
      < ((⌊tzDensityLB n beta eps⌋₊ : ℕ) : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧
      (n : ℝ) ^ beta ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ beta ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = n ∧
        ∀ epsStar : ℝ≥0∞,
          epsStar < ((2 ^ r * (2 ^ (mu - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g n ((r - 2) * m)) epsStar
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ mu) := by
  exact kkh26_ceiling_of_thornerZamanPNT_natFloor_tight_square_bound_log
    (supply := ⌊tzDensityLB n beta eps⌋₊) hTZ hmu hm hn hr2 hr hx hpl hpos le_rfl
    hcount

/-- **Canonical floor-supply form with automatic density nonnegativity.**

The normalized tight KKH26 budget is nonnegative under `r ≥ 2` and `n^beta ≥ 2`.  Therefore a
strict comparison of that budget against `floor(tzDensityLB n beta eps)` already implies
`0 ≤ tzDensityLB n beta eps`; callers no longer need to provide that side condition separately. -/
theorem kkh26_ceiling_of_thornerZamanPNT_floor_tight_square_bound_log_auto_nonneg
    {n : ℕ} {beta eps : ℝ} [NeZero n]
    (hTZ : ThornerZamanPNT n beta eps) {mu m r : ℕ}
    (hmu : 1 ≤ mu) (hm : 1 ≤ m) (hn : n = 2 ^ mu * m)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (mu - 1))
    (hx : 2 ≤ (n : ℝ) ^ beta)
    (hpl : (((2 : ℕ) ^ mu : ℕ) : ℝ) < (n : ℝ) ^ beta)
    (hcount : (((2 ^ r * (2 ^ (mu - 1)).choose r) ^ 2 : ℕ) : ℝ) *
        ((((2 ^ (mu - 1) : ℕ) : ℝ) * Real.log (((2 * r : ℕ) : ℝ))) /
          Real.log ((n : ℝ) ^ beta))
      < ((⌊tzDensityLB n beta eps⌋₊ : ℕ) : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧
      (n : ℝ) ^ beta ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ beta ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = n ∧
        ∀ epsStar : ℝ≥0∞,
          epsStar < ((2 ^ r * (2 ^ (mu - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g n ((r - 2) * m)) epsStar
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ mu) := by
  have hratio_nonneg :
      0 ≤ ((((2 ^ (mu - 1) : ℕ) : ℝ) * Real.log (((2 * r : ℕ) : ℝ))) /
          Real.log ((n : ℝ) ^ beta)) := by
    simpa [tightResultantLog_eq] using
      (tightResultantLogRatio_nonneg (n := n) (β := beta) mu r (by omega) hx)
  have hbudget_nonneg :
      0 ≤ (((2 ^ r * (2 ^ (mu - 1)).choose r) ^ 2 : ℕ) : ℝ) *
        ((((2 ^ (mu - 1) : ℕ) : ℝ) * Real.log (((2 * r : ℕ) : ℝ))) /
          Real.log ((n : ℝ) ^ beta)) := by
    exact mul_nonneg (by positivity) hratio_nonneg
  have hpos : 0 ≤ tzDensityLB n beta eps :=
    real_nonneg_of_nonneg_lt_natFloor hbudget_nonneg hcount
  exact kkh26_ceiling_of_thornerZamanPNT_floor_tight_square_bound_log
    hTZ hmu hm hn hr2 hr hx hpl hpos hcount

end ProximityGap.Frontier.KKH26ThornerZamanTightBridge

/-! ## Axiom audit (expected: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`) -/
open ProximityGap.Frontier.KKH26ThornerZamanTightBridge in
#print axioms kkh26_ceiling_of_thornerZamanPNT_tight_square_bound_log
open ProximityGap.Frontier.KKH26ThornerZamanTightBridge in
#print axioms kkh26_ceiling_of_thornerZamanPNT_natFloor_tight_square_bound_log
open ProximityGap.Frontier.KKH26ThornerZamanTightBridge in
#print axioms kkh26_ceiling_of_thornerZamanPNT_floor_tight_square_bound_log
open ProximityGap.Frontier.KKH26ThornerZamanTightBridge in
#print axioms kkh26_ceiling_of_thornerZamanPNT_floor_tight_square_bound_log_auto_nonneg
