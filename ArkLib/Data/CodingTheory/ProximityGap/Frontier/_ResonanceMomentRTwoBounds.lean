/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceMomentRTwo

/-!
# Two-sided bracket on the `r = 2` resonance rung (#407 / #444)

Extends `_ResonanceMomentRTwo`, which supplies:
* `phaseSum_two`: `phaseSum u 2 c = ∑_{a≠0, c-a≠0} u(a) u(c-a)` (the off-diagonal convolution);
* `phaseSum_two_zero_of_conjSymm`: `phaseSum u 2 0 = m - 1` (the diagonal peak);
* `resonanceMoment_two_ge_of_conjSymm`: `T 2 ≥ (m-1)²` (the diagonal LOWER bound).

This file supplies the matching UPPER companions, for a **unit-phase** vector (`‖u l‖ = 1`,
the Gauss-sum normalisation `u_l = τ(χ^l)/√p`):

* `phaseSum_two_norm_le` — the per-frequency L∞ ceiling
  `‖phaseSum u 2 c‖ ≤ m - 1`  for every `c`,
  proved by the triangle inequality on the off-diagonal convolution: at most `m-1` unit terms.
  This is TIGHT: at `c = 0` the diagonal value is exactly `m-1` (the conjugate-symmetric peak),
  so the L∞ bound is attained and cannot be improved by a constant.

* `resonanceMoment_two_le` — the aggregate L² ceiling
  `T 2 = resonanceMoment u 2 ≤ m · (m-1)²`,
  by squaring the per-frequency ceiling and summing over the `m` frequencies.

## Honest scope — a BRACKET, not a closure

Together with the proven lower bound this BRACKETS the `r = 2` rung in kernel-checked Lean:

> `(m - 1)² ≤ T 2 ≤ m · (m - 1)²`   (conjugate-symmetric unit phases).

The multiplicative gap is exactly `m` (the number of frequencies). The probe-measured truth is
`T 2 = Θ(m²)` (≈ `2.4·(m-1)²`), sitting at the LOWER end of this bracket: the off-diagonal phase
sums exhibit `√m`-cancellation (worst off-diagonal `‖phaseSum u 2 c‖ ≈ √m · O(1)`, not the trivial
`m-1`), so the true `T 2` is far below the `m·(m-1)²` ceiling. Closing that `√m`-vs-`m-1` gap per
frequency is the SAME L²→L∞ deviation question as the prize sup-norm wall; this file does NOT close
it. The `(2 m log m)²` `ResonanceConjecture` ceiling is consistent with both ends of the bracket but
is NOT proved here.

NO CORE / cancellation / completion / moment-saving / anti-concentration / capacity claim.
CORE `M(μ_n) ≤ C √(n log m)` UNCHANGED / OPEN. Axiom-clean (`propext, Classical.choice, Quot.sound`).
Issues #407, #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators Classical
open Finset

variable {m : ℕ} [NeZero m]

/-- **Per-frequency L∞ ceiling: `‖phaseSum u 2 c‖ ≤ m - 1`.** For a unit-phase vector
(`‖u l‖ = 1`) the depth-2 phase-sum at any frequency `c` is the off-diagonal convolution of at
most `m - 1` unit terms, so its norm is at most `m - 1`. This is TIGHT — the diagonal value at
`c = 0` is exactly `m - 1` for conjugate-symmetric phases (`phaseSum_two_zero_of_conjSymm`). -/
theorem phaseSum_two_norm_le (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (c : ZMod m) :
    ‖phaseSum u 2 c‖ ≤ ((m : ℝ) - 1) := by
  classical
  rw [phaseSum_two]
  -- triangle inequality: ‖∑ ...‖ ≤ ∑ ‖...‖, each term has norm 1
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ a ∈ Finset.univ.filter (fun a : ZMod m => a ≠ 0 ∧ c - a ≠ 0),
      ‖u a * u (c - a)‖ = 1 := by
    intro a _
    rw [norm_mul, hu a, hu (c - a)]; norm_num
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- the filtered set has card ≤ card {a ≠ 0} = m - 1
  have hsub : (Finset.univ.filter (fun a : ZMod m => a ≠ 0 ∧ c - a ≠ 0)) ⊆
      (Finset.univ.filter (fun a : ZMod m => a ≠ 0)) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, ha.2.1⟩
  have hcardle : (Finset.univ.filter (fun a : ZMod m => a ≠ 0 ∧ c - a ≠ 0)).card ≤
      (Finset.univ.filter (fun a : ZMod m => a ≠ 0)).card := Finset.card_le_card hsub
  have hcard0 : (Finset.univ.filter (fun a : ZMod m => a ≠ 0)).card = m - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0),
      Finset.card_univ, ZMod.card]
  have hle : (Finset.univ.filter (fun a : ZMod m => a ≠ 0 ∧ c - a ≠ 0)).card ≤ m - 1 := by
    rw [← hcard0]; exact hcardle
  have hm : 1 ≤ m := NeZero.one_le
  calc ((Finset.univ.filter (fun a : ZMod m => a ≠ 0 ∧ c - a ≠ 0)).card : ℝ)
      ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hle
    _ = ((m : ℝ) - 1) := by push_cast [Nat.cast_sub hm]; ring

/-- **Aggregate L² ceiling: `T 2 = resonanceMoment u 2 ≤ m · (m-1)²`.** Squaring the per-frequency
ceiling `‖phaseSum u 2 c‖ ≤ m-1` and summing over the `m` frequencies. Paired with the proven
lower bound `(m-1)² ≤ T 2`, this BRACKETS the `r = 2` rung: `(m-1)² ≤ T 2 ≤ m·(m-1)²`. -/
theorem resonanceMoment_two_le (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) :
    resonanceMoment u 2 ≤ (m : ℝ) * ((m : ℝ) - 1) ^ 2 := by
  classical
  unfold resonanceMoment
  have hm : 1 ≤ m := NeZero.one_le
  have hm1 : (0 : ℝ) ≤ (m : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  -- each squared norm is ≤ (m-1)²
  have hbd : ∀ c : ZMod m, ‖phaseSum u 2 c‖ ^ 2 ≤ ((m : ℝ) - 1) ^ 2 := by
    intro c
    have h1 := phaseSum_two_norm_le u hu c
    have h0 : (0 : ℝ) ≤ ‖phaseSum u 2 c‖ := norm_nonneg _
    exact pow_le_pow_left₀ h0 h1 2
  calc ∑ c : ZMod m, ‖phaseSum u 2 c‖ ^ 2
      ≤ ∑ _c : ZMod m, ((m : ℝ) - 1) ^ 2 := Finset.sum_le_sum (fun c _ => hbd c)
    _ = (Finset.univ.card : ℝ) * ((m : ℝ) - 1) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (m : ℝ) * ((m : ℝ) - 1) ^ 2 := by
        rw [Finset.card_univ, ZMod.card]

/-- **Conditional `r = 2` conjecture discharge from the trivial ceiling.** If the trivial upper bound
`m·(m-1)²` already fits under the `ResonanceConjecture` ceiling `(2 m log m)²` — i.e. when
`m·(m-1)² ≤ (2 m log m)²` — then `ResonanceConjecture u 2` holds UNCONDITIONALLY for unit phases.
Probe truth: the hypothesis holds for small `m` (≲ 80) and FAILS for large `m` (the trivial ceiling
overshoots the conjecture by a factor `~ m / (4 log² m) → ∞`). So this is an HONEST regime-limited
discharge: the triangle/L¹ route reaches the conjecture ONLY in the small-`m` regime; closing it for
large `m` requires the off-diagonal `√m`-cancellation (the prize sup-norm wall), NOT the triangle
bound. A door-(i)-style "L¹/triangle is insufficient asymptotically" constraint at the resonance level. -/
theorem resonanceConjecture_two_of_trivCeil_le (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hfit : (m : ℝ) * ((m : ℝ) - 1) ^ 2 ≤ (2 * (m : ℝ) * Real.log m) ^ 2) :
    ResonanceConjecture u 2 := by
  unfold ResonanceConjecture
  exact le_trans (resonanceMoment_two_le u hu) hfit

/-- **The `r = 2` two-sided bracket** (conjugate-symmetric unit phases):
`(m-1)² ≤ T 2 ≤ m·(m-1)²`. The lower bound is the diagonal mass; the upper bound is the trivial
per-frequency ceiling summed. The probe truth `T 2 = Θ(m²)` sits at the LOWER end (`√m`-cancellation
in the off-diagonal). Closing the per-frequency `√m`-vs-`m` gap is the open prize sup-norm wall. -/
theorem resonanceMoment_two_bracket (u : ZMod m → ℂ)
    (hu : ∀ l : ZMod m, ‖u l‖ = 1) (hsymm : ∀ a : ZMod m, u (-a) = (starRingEnd ℂ) (u a)) :
    ((m : ℝ) - 1) ^ 2 ≤ resonanceMoment u 2 ∧
      resonanceMoment u 2 ≤ (m : ℝ) * ((m : ℝ) - 1) ^ 2 :=
  ⟨resonanceMoment_two_ge_of_conjSymm u hu hsymm, resonanceMoment_two_le u hu⟩

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.phaseSum_two_norm_le
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_two_le
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_two_bracket
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceConjecture_two_of_trivCeil_le
