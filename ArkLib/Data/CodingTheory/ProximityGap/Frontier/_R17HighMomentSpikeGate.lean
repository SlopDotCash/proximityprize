/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MomentTailRateGate
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R17TchiMomentIdentities
import Mathlib.Data.Nat.Factorial.DoubleFactorial

set_option linter.style.longLine false

/-!
# Round 17: high-moment spike gate for Wick-shaped budgets

The high-moment probe for the shifted character sums `T_χ` shows the operational issue behind the
deep-rung wall: a shallow Wick-shaped average moment can still pay for one full-size atom.  This
file records that arithmetic as a tiny, axiom-clean consumer of `_MomentTailRateGate`.

For scores on `N` atoms, a Wick-shaped `2r`-moment budget

`A = (2r-1)‼ * n^r`

does not exclude a single atom of size `n` unless

`N * A < n^(2r)`.

Equivalently, if `n^(2r) ≤ N * A`, then there is a one-spike score vector satisfying the same
average-moment budget while violating any proposed threshold `T < n`.

This is not a no-go against the prize: at the saddle depth the desired moment budget is meant to
beat exactly this finite-atom rate.  It is a bookkeeping guardrail for R17/R18: any proposed
high-moment closure must show the Markov rate has crossed the one-spike threshold, not merely that
some fixed shallow moment is Wick-shaped.
-/

set_option autoImplicit false

open Finset
open ArkLib.ProximityGap.Frontier.R16LegendreCosetFace (shiftedCharSum)

namespace ArkLib.ProximityGap.Frontier.R17HighMomentSpikeGate

open ArkLib.ProximityGap.Frontier.MomentTailRateGate

variable {α : Type} [Fintype α]

/-- Wick-shaped average moment budget at depth `r`, normalized as a `2r`-th power score budget. -/
noncomputable def wickAverageBudget (n : ℝ) (r : ℕ) : ℝ :=
  (Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ r

/-- Local size bound for the Wick double factorial: `(2r-1)‼ ≤ (2r)^r`.  Kept local so this
small gate does not import the larger incidence-moment tower just for the same arithmetic atom. -/
theorem doubleFactorial_two_sub_one_le (r : ℕ) :
    (Nat.doubleFactorial (2 * r - 1) : ℝ) ≤ (2 * r : ℝ) ^ r := by
  have hclosed : Nat.doubleFactorial (2 * r - 1) = ∏ i ∈ Finset.range r, (2 * i + 1) := by
    cases r with
    | zero => simp
    | succ m =>
      have h2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
      rw [h2, Nat.doubleFactorial_eq_prod_odd m]
      rw [Finset.prod_range_succ']
      simp
  have hcast : (Nat.doubleFactorial (2 * r - 1) : ℝ)
      = ∏ i ∈ Finset.range r, ((2 * i + 1 : ℕ) : ℝ) := by
    rw [hclosed]; push_cast; rfl
  rw [hcast]
  calc ∏ i ∈ Finset.range r, ((2 * i + 1 : ℕ) : ℝ)
      ≤ ∏ _i ∈ Finset.range r, (2 * r : ℝ) := by
        apply Finset.prod_le_prod
        · intro i _; positivity
        · intro i hi
          have hir : i + 1 ≤ r := Finset.mem_range.mp hi
          have : (i : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hir
          push_cast
          nlinarith [this]
    _ = (2 * r : ℝ) ^ r := by rw [Finset.prod_const, Finset.card_range]

/-- **Consumer side.**  A Wick-shaped average `2r`-moment budget proves the hard threshold `T`
once the finite atom-count rate crosses:

`#α * (2r-1)‼ * n^r ≤ T^(2r)`.

This is the exact Markov last mile used by the moment method. -/
theorem forall_le_of_wickAverageBudget_rate [Nonempty α]
    {X : α → ℝ} {n T : ℝ} {r : ℕ}
    (hX : ∀ a : α, 0 ≤ X a) (hT : 0 ≤ T) (hr : 1 ≤ r)
    (havg : powMomentAverage X (2 * r) ≤ wickAverageBudget n r)
    (hrate : (Fintype.card α : ℝ) * wickAverageBudget n r ≤ T ^ (2 * r)) :
    ∀ a : α, X a ≤ T := by
  exact forall_le_of_averageMoment_card_mul_le_threshold
    hX hT (by omega) havg hrate

/-- **Spike obstruction side.**  If the same Wick-shaped average `2r`-moment budget can pay for one
full-size atom `n`, then for every threshold `T < n` there is a nonnegative one-spike score vector
whose average `2r`-moment is within the Wick budget but whose supremum exceeds `T`.

The arithmetic condition is exactly

`n^(2r) ≤ #α * (2r-1)‼ * n^r`.

Thus a shallow Wick moment is value-useless for the worst-case supremum until this inequality is
reversed. -/
theorem wickAverageBudget_allows_full_spike [Nonempty α] [DecidableEq α]
    {n T : ℝ} {r : ℕ} (hr : 1 ≤ r) (hn : 0 ≤ n) (hTn : T < n)
    (hbudget : n ^ (2 * r) ≤ (Fintype.card α : ℝ) * wickAverageBudget n r) :
    ∃ X : α → ℝ,
      (∀ a : α, 0 ≤ X a) ∧
      powMomentAverage X (2 * r) ≤ wickAverageBudget n r ∧
      ∃ a : α, T < X a := by
  exact averageMoment_budget_allows_single_spike_of_pow_le_card_mul
    (α := α) (k := 2 * r) (T := T) (S := n) (A := wickAverageBudget n r)
    (by omega) hn hTn hbudget

/-- Canceled obstruction condition.  If
`n^r ≤ #α * (2r-1)‼`, then the Wick-shaped average budget can still pay for a single full-size
atom, so every proposed threshold `T < n` is compatible with a one-spike countermodel. -/
theorem wickAverageBudget_allows_full_spike_of_pow_le_card_mul_df
    [Nonempty α] [DecidableEq α]
    {n T : ℝ} {r : ℕ} (hr : 1 ≤ r) (hn : 0 ≤ n) (hTn : T < n)
    (hbudget :
      n ^ r ≤ (Fintype.card α : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)) :
    ∃ X : α → ℝ,
      (∀ a : α, 0 ≤ X a) ∧
      powMomentAverage X (2 * r) ≤ wickAverageBudget n r ∧
      ∃ a : α, T < X a := by
  apply wickAverageBudget_allows_full_spike (α := α) hr hn hTn
  unfold wickAverageBudget
  have hnpow : 0 ≤ n ^ r := pow_nonneg hn r
  calc n ^ (2 * r)
      = n ^ r * n ^ r := by
        have htwo : 2 * r = r + r := by omega
        rw [htwo, pow_add]
    _ ≤ ((Fintype.card α : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)) * n ^ r := by
        exact mul_le_mul_of_nonneg_right hbudget hnpow
    _ = (Fintype.card α : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ r) := by
        ring

/-- Strict form of the crossed-rate condition: if
`#α * (2r-1)‼ * n^r < n^(2r)`, then the Wick-shaped budget excludes full-size atoms. -/
theorem no_full_spike_of_wickAverageBudget_rate_lt [Nonempty α]
    {X : α → ℝ} {n : ℝ} {r : ℕ}
    (hX : ∀ a : α, 0 ≤ X a) (hn : 0 ≤ n) (hr : 1 ≤ r)
    (havg : powMomentAverage X (2 * r) ≤ wickAverageBudget n r)
    (hrate : (Fintype.card α : ℝ) * wickAverageBudget n r < n ^ (2 * r)) :
    ∀ a : α, X a ≤ n := by
  exact forall_le_of_averageMoment_card_mul_lt_threshold
    hX hn (by omega) havg hrate

/-- Coarse rate upper bound for a Wick-shaped budget:
`#α * (2r-1)‼ * n^r ≤ #α * (2r)^r * n^r`. -/
theorem card_mul_wickAverageBudget_le_card_mul_pow
    {n : ℝ} {r : ℕ} (hn : 0 ≤ n) :
    (Fintype.card α : ℝ) * wickAverageBudget n r
      ≤ (Fintype.card α : ℝ) * (2 * r : ℝ) ^ r * n ^ r := by
  unfold wickAverageBudget
  have hdf := doubleFactorial_two_sub_one_le r
  have hnpow : 0 ≤ n ^ r := by positivity
  have hcard : 0 ≤ (Fintype.card α : ℝ) := by positivity
  calc (Fintype.card α : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ r)
      ≤ (Fintype.card α : ℝ) * (((2 * r : ℝ) ^ r) * n ^ r) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hdf hnpow) hcard
    _ = (Fintype.card α : ℝ) * (2 * r : ℝ) ^ r * n ^ r := by ring

/-- Easy-to-check sufficient crossing condition.  If the coarser rate
`#α * (2r)^r * n^r < n^(2r)` holds, then the exact Wick-shaped budget excludes full-size atoms. -/
theorem no_full_spike_of_coarse_wick_rate_lt [Nonempty α]
    {X : α → ℝ} {n : ℝ} {r : ℕ}
    (hX : ∀ a : α, 0 ≤ X a) (hn : 0 ≤ n) (hr : 1 ≤ r)
    (havg : powMomentAverage X (2 * r) ≤ wickAverageBudget n r)
    (hrate : (Fintype.card α : ℝ) * (2 * r : ℝ) ^ r * n ^ r < n ^ (2 * r)) :
    ∀ a : α, X a ≤ n := by
  exact no_full_spike_of_wickAverageBudget_rate_lt hX hn hr havg
    ((card_mul_wickAverageBudget_le_card_mul_pow (α := α) hn).trans_lt hrate)

/-- Canceled coarse crossing condition.  For positive `n`, the easy sufficient condition
`#α * (2r)^r < n^r` is exactly what is needed to make the coarse Wick rate
`#α * (2r)^r * n^r < n^(2r)`. -/
theorem no_full_spike_of_card_mul_pow_lt [Nonempty α]
    {X : α → ℝ} {n : ℝ} {r : ℕ}
    (hX : ∀ a : α, 0 ≤ X a) (hn : 0 < n) (hr : 1 ≤ r)
    (havg : powMomentAverage X (2 * r) ≤ wickAverageBudget n r)
    (hrate : (Fintype.card α : ℝ) * (2 * r : ℝ) ^ r < n ^ r) :
    ∀ a : α, X a ≤ n := by
  have hn0 : 0 ≤ n := le_of_lt hn
  have hnpow : 0 < n ^ r := pow_pos hn r
  apply no_full_spike_of_coarse_wick_rate_lt hX hn0 hr havg
  calc (Fintype.card α : ℝ) * (2 * r : ℝ) ^ r * n ^ r
      < n ^ r * n ^ r := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          mul_lt_mul_of_pos_right hrate hnpow
    _ = n ^ (2 * r) := by
      have htwo : 2 * r = r + r := by omega
      rw [htwo, pow_add]

section ShiftedCharacterConsumer

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Direct shifted-character consumer: once the corrected-away Wick budget has crossed the finite
rate threshold, every non-deleted offset is bounded by `T`.  This is the concrete Tχ version of the
Markov last mile, with the field size `q` already present in `ShiftedCharAwayWickAt`. -/
theorem shiftedCharSum_le_of_awayWickAt_rate
    (χ : MulChar F ℂ) (G D : Finset F) (r : ℕ) {T : ℝ}
    (hT : 0 ≤ T) (hr : 1 ≤ r)
    (hwick :
      ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ G D r)
    (hrate :
      (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
        ≤ T ^ (2 * r))
    {s₀ : F} (hs₀ : s₀ ∉ D) :
    ‖shiftedCharSum χ G s₀‖ ≤ T := by
  by_contra hnot
  have hgt : T < ‖shiftedCharSum χ G s₀‖ := lt_of_not_ge hnot
  have hk0 : 2 * r ≠ 0 := by omega
  have hpow_gt :
      T ^ (2 * r) < ‖shiftedCharSum χ G s₀‖ ^ (2 * r) :=
    pow_lt_pow_left₀ hgt hT hk0
  have hpow_le :
      ‖shiftedCharSum χ G s₀‖ ^ (2 * r)
        ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ)
            * (G.card : ℝ) ^ r :=
    ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.shiftedCharSum_pow_le_of_awayWickAt
      χ G D r hwick hs₀
  exact (not_lt_of_ge hrate) (lt_of_lt_of_le hpow_gt hpow_le)

/-- Coarse sufficient shifted-character consumer using `(2r-1)‼ ≤ (2r)^r`. -/
theorem shiftedCharSum_le_of_coarse_awayWickAt_rate
    (χ : MulChar F ℂ) (G D : Finset F) (r : ℕ) {T : ℝ}
    (hT : 0 ≤ T) (hr : 1 ≤ r)
    (hwick :
      ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.ShiftedCharAwayWickAt χ G D r)
    (hrate :
      (Fintype.card F : ℝ) * (2 * r : ℝ) ^ r * (G.card : ℝ) ^ r
        ≤ T ^ (2 * r))
    {s₀ : F} (hs₀ : s₀ ∉ D) :
    ‖shiftedCharSum χ G s₀‖ ≤ T := by
  refine shiftedCharSum_le_of_awayWickAt_rate χ G D r hT hr hwick ?_ hs₀
  have hdf := doubleFactorial_two_sub_one_le r
  have hcard : 0 ≤ (Fintype.card F : ℝ) := by positivity
  have hGpow : 0 ≤ (G.card : ℝ) ^ r := by positivity
  calc (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
      ≤ (Fintype.card F : ℝ) * (2 * r : ℝ) ^ r * (G.card : ℝ) ^ r := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdf hcard) hGpow
    _ = (Fintype.card F : ℝ) * (2 * r : ℝ) ^ r * (G.card : ℝ) ^ r := by ring
    _ ≤ T ^ (2 * r) := hrate

end ShiftedCharacterConsumer

end ArkLib.ProximityGap.Frontier.R17HighMomentSpikeGate

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R17HighMomentSpikeGate.doubleFactorial_two_sub_one_le
#print axioms ArkLib.ProximityGap.Frontier.R17HighMomentSpikeGate.forall_le_of_wickAverageBudget_rate
#print axioms ArkLib.ProximityGap.Frontier.R17HighMomentSpikeGate.wickAverageBudget_allows_full_spike
#print axioms ArkLib.ProximityGap.Frontier.R17HighMomentSpikeGate.wickAverageBudget_allows_full_spike_of_pow_le_card_mul_df
#print axioms ArkLib.ProximityGap.Frontier.R17HighMomentSpikeGate.no_full_spike_of_wickAverageBudget_rate_lt
#print axioms ArkLib.ProximityGap.Frontier.R17HighMomentSpikeGate.card_mul_wickAverageBudget_le_card_mul_pow
#print axioms ArkLib.ProximityGap.Frontier.R17HighMomentSpikeGate.no_full_spike_of_coarse_wick_rate_lt
#print axioms ArkLib.ProximityGap.Frontier.R17HighMomentSpikeGate.no_full_spike_of_card_mul_pow_lt
#print axioms ArkLib.ProximityGap.Frontier.R17HighMomentSpikeGate.shiftedCharSum_le_of_awayWickAt_rate
#print axioms ArkLib.ProximityGap.Frontier.R17HighMomentSpikeGate.shiftedCharSum_le_of_coarse_awayWickAt_rate
