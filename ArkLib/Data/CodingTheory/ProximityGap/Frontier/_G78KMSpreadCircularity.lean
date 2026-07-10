/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# G78: Kelley–Meka spread technology is loss-class-compatible but rank-one circular

The Kelley–Meka engine (strong 3-progression bounds, 2023; Bloom–Sisask refinement) is the
first additive-combinatorics technology whose per-step losses live in the prize-tolerable
class: Croot–Sisask `L^{2k}` sampling at depth `k ~ log(1/α)` loses `(1/α)^{1/k} = e^{O(1)}`
per step, i.e. total `C^r` at convolution depth `r` — and the prize target
`A_r ≤ K^r (2r−1)‼ n^r` tolerates any constant base `K` (`M ≤ √(2eK)·√(n ln q)` at
`r ≈ ln q`).  Every previously walked engine (BGK/Burgess/iterated-Shkredov/…) loses a
factor `n^ε` per step and is exponent-floored; KM is NOT. This file isolates a necessary
rank-one spreadness check that becomes circular at the Fourier scale.

**The obstruction is the hypothesis, not the loss class.**  KM's flatness conclusions hold
for SPREAD sets: no relative density increment on structured cells (rank-one Bohr sets /
arcs are the base case). This file proves an abstract increment-extraction lemma relevant to
that comparison:

* a biased phase-weighted cell sum forces an `L¹` cell-mass deviation
  (`l1_deviation_of_phase_bias`), hence a single cell with deviation `≥ (bias − slack)/K`
  (`exists_cell_deviation_of_phase_bias`);
* when separately instantiated with cells = the `K` arcs of the `b`-dilated value partition
  and suitable phase/oscillation estimates, it is intended to turn a large `‖η_b‖` into an
  arc-density increment. Those arc definitions and estimates are not formalized here, so this
  file does not itself identify the full Kelley–Meka hypothesis with the prize bound.
  (Probe `probe_g77_km_spread_circularity.py`: dev/(M/n) ∈ [3.1, 6.9] across
  n = 8/16/32, twelve primes — the two-sided equivalence is real at rank one.)

The composite map (spreadness ⟹ KM flatness ⟹ moment bound ⟹ sup bound ⟹ spreadness)
is a loop of constant-loss arrows with no contraction — the same fixed-point shape as the
closed `_DyadicDoublingNoContraction` route, now for the KM operator.  The non-circular
unconditional input the loop would need — anti-concentration of a geometric progression in
arcs WITHOUT Fourier — is exactly the BGK/Cilleruelo–Garaev frontier, exponent-floored.

HONEST SCOPE. This is an abstract extraction lemma and loss-class computation, not a formal
instantiation of Kelley–Meka and not a closure. It does not prove that no non-Fourier spreadness
certificate can exist. CORE remains OPEN / ON-BGK.

Issue #466.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.G78KMSpreadCircularity

open Finset

/-- **L¹ increment extraction.**  If phase-weighted cell masses show bias `A` while the raw
phases nearly cancel (`‖Σ c_T‖ ≤ B`), then the cell masses deviate from any reference level
`w` by at least `A − w·B` in `L¹`.  (Cells with unit-bounded phases; triangle inequality.) -/
theorem l1_deviation_of_phase_bias
    {S : Type*} (s : Finset S) (nT : S → ℝ) (c : S → ℂ) (w A B : ℝ)
    (hw : 0 ≤ w)
    (hc : ∀ T ∈ s, ‖c T‖ ≤ 1)
    (hbias : A ≤ ‖∑ T ∈ s, ((nT T : ℝ) : ℂ) * c T‖)
    (hcancel : ‖∑ T ∈ s, c T‖ ≤ B) :
    A - w * B ≤ ∑ T ∈ s, |nT T - w| := by
  have hsplit :
      (∑ T ∈ s, ((nT T - w : ℝ) : ℂ) * c T) =
        (∑ T ∈ s, ((nT T : ℝ) : ℂ) * c T) - ((w : ℝ) : ℂ) * ∑ T ∈ s, c T := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun T _ => ?_
    push_cast
    ring
  have h2 : ‖((w : ℝ) : ℂ) * ∑ T ∈ s, c T‖ ≤ w * B := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]
    exact mul_le_mul_of_nonneg_left hcancel hw
  have hlower :
      A - w * B ≤ ‖∑ T ∈ s, ((nT T - w : ℝ) : ℂ) * c T‖ := by
    rw [hsplit]
    have h1 : ‖(∑ T ∈ s, ((nT T : ℝ) : ℂ) * c T)‖ - ‖((w : ℝ) : ℂ) * ∑ T ∈ s, c T‖ ≤
        ‖(∑ T ∈ s, ((nT T : ℝ) : ℂ) * c T) - ((w : ℝ) : ℂ) * ∑ T ∈ s, c T‖ :=
      norm_sub_norm_le _ _
    linarith
  have hupper :
      ‖∑ T ∈ s, ((nT T - w : ℝ) : ℂ) * c T‖ ≤ ∑ T ∈ s, |nT T - w| := by
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun T hT => ?_
    have hterm : ‖((nT T - w : ℝ) : ℂ) * c T‖ = |nT T - w| * ‖c T‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hterm]
    have h1 : |nT T - w| * ‖c T‖ ≤ |nT T - w| * 1 :=
      mul_le_mul_of_nonneg_left (hc T hT) (abs_nonneg _)
    simpa using h1
  linarith

/-- **Single-cell extraction.**  Some cell carries deviation `≥ (A − w·B)/K` where `K` is
the number of cells: a biased phase sum certifies a density increment on one cell. -/
theorem exists_cell_deviation_of_phase_bias
    {S : Type*} (s : Finset S) (hs : s.Nonempty)
    (nT : S → ℝ) (c : S → ℂ) (w A B : ℝ)
    (hw : 0 ≤ w)
    (hc : ∀ T ∈ s, ‖c T‖ ≤ 1)
    (hbias : A ≤ ‖∑ T ∈ s, ((nT T : ℝ) : ℂ) * c T‖)
    (hcancel : ‖∑ T ∈ s, c T‖ ≤ B) :
    ∃ T ∈ s, (A - w * B) / (s.card : ℝ) ≤ |nT T - w| := by
  by_contra hcon
  push_neg at hcon
  have hsum : ∑ T ∈ s, |nT T - w| < (s.card : ℝ) * ((A - w * B) / (s.card : ℝ)) := by
    have hcard : (0 : ℝ) < (s.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hs
    calc ∑ T ∈ s, |nT T - w|
        < ∑ _T ∈ s, (A - w * B) / (s.card : ℝ) := by
          refine Finset.sum_lt_sum_of_nonempty hs fun T hT => hcon T hT
      _ = (s.card : ℝ) * ((A - w * B) / (s.card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hl1 := l1_deviation_of_phase_bias s nT c w A B hw hc hbias hcancel
  have hcard : (0 : ℝ) < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  rw [mul_div_cancel₀ _ (ne_of_gt hcard)] at hsum
  linarith

/-- **The loss-class computation.**  At sampling depth `k = log(1/α)`, the Croot–Sisask
per-step loss `(1/α)^{1/k}` is exactly `e`: the KM engine's loss lives in the constant-base
class `C^r`, which the prize tolerates.  (Stated for any `α ∈ (0,1)` via
`rpow`: `(1/α)^{1/log(1/α)} = e`.) -/
theorem km_per_step_loss_is_e (α : ℝ) (h0 : 0 < α) (h1 : α < 1) :
    (1 / α) ^ (1 / Real.log (1 / α)) = Real.exp 1 := by
  have hgt : 1 < 1 / α := by
    rw [one_div]
    first
      | exact (one_lt_inv₀ h0).mpr h1
      | exact one_lt_inv_of_lt h0 h1
      | exact one_lt_inv h0 h1
  have hlogpos : 0 < Real.log (1 / α) := Real.log_pos hgt
  have hpos : (0 : ℝ) < 1 / α := by positivity
  rw [Real.rpow_def_of_pos hpos, mul_one_div, div_self (ne_of_gt hlogpos)]

end ArkLib.ProximityGap.Frontier.G78KMSpreadCircularity

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G78KMSpreadCircularity.l1_deviation_of_phase_bias
#print axioms
  ArkLib.ProximityGap.Frontier.G78KMSpreadCircularity.exists_cell_deviation_of_phase_bias
#print axioms
  ArkLib.ProximityGap.Frontier.G78KMSpreadCircularity.km_per_step_loss_is_e
