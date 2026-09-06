/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPhaseResonance

/-!
# The base case `r = 1` of the resonance moment (#407 / #444)

Extends `GaussPhaseResonance` (the named `sqrt p`-free free variable of the prize). That file
defines the phase-sum `phaseSum u r c`, the deep resonance moment `T r = resonanceMoment u r`,
proves `T r >= 0` and the vanishing criterion, and states the open `ResonanceConjecture`. It does
NOT pin a single value of `T r`.

This file supplies the EXACT base case `r = 1`:

> `phaseSum u 1 c = if c = 0 then 0 else u c`,  hence  `T 1 = sum_{c != 0} ‖u c‖^2`.

For a unit-phase vector `u` (`‖u l‖ = 1`, the Gauss-sum unit phases `u_l = tau(chi^l)/sqrt p`,
the actual object after the `sqrt p`-cancellation), this is exactly

> `resonanceMoment u 1 = m - 1`.

This is the `sqrt p`-free core of the Salem-Zygmund / Parseval L2-mass `sum_j |tau(chi^j)|^2 / m^2
= (m-1) p / m^2` (the verified `avg |eta_b|^2 ~ n` second-moment fact) with the `p` divided out.
It also discharges the `ResonanceConjecture` at depth `r = 1` UNCONDITIONALLY for `m >= 2`
(`m - 1 <= 2 m log m`).

## Honest scope

This is the BASE CASE only. The prize binds at depth `r ~ log m` (the deep resonance moment),
where the conjecture is the recognized open Gauss-period / BGK content. `r = 1` is the trivial
Parseval rung, FAR below binding. NO capacity / beyond-Johnson / sub-linear / closure claim;
CORE `M(mu_n) <= C sqrt(n log m)` UNCHANGED / OPEN.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #407, #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators Classical
open Finset

variable {m : ℕ} [NeZero m]

/-- The `r = 1` filter `{X : Fin 1 -> ZMod m | (forall i, X i != 0) and sum X = c}` is the
singleton `{fun _ => c}` when `c != 0`, and empty when `c = 0`. We package the membership
criterion: `X` is in the filter iff `c != 0` and `X = fun _ => c`. -/
theorem mem_phaseSum_one_filter (c : ZMod m) (X : Fin 1 → ZMod m) :
    (X ∈ (Finset.univ.filter (fun X : Fin 1 → ZMod m =>
        (∀ i, X i ≠ 0) ∧ (∑ i, X i) = c))) ↔ (c ≠ 0 ∧ X = fun _ => c) := by
  classical
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, hsum⟩
    have hX0 : X 0 = c := by simpa [Fin.sum_univ_one] using hsum
    refine ⟨?_, ?_⟩
    · rw [← hX0]; exact hne 0
    · funext i
      have : i = 0 := Subsingleton.elim i 0
      rw [this, hX0]
  · rintro ⟨hc, rfl⟩
    refine ⟨fun i => ?_, ?_⟩
    · exact hc
    · simp

/-- **`phaseSum u 1 c = if c = 0 then 0 else u c`.** The depth-1 phase-sum collapses to the single
phase at `c` (and vanishes at `c = 0`). -/
theorem phaseSum_one (u : ZMod m → ℂ) (c : ZMod m) :
    phaseSum u 1 c = if c = 0 then 0 else u c := by
  classical
  unfold phaseSum
  by_cases hc : c = 0
  · subst hc
    rw [if_pos rfl]
    apply Finset.sum_eq_zero
    intro X hX
    rw [mem_phaseSum_one_filter] at hX
    exact absurd rfl hX.1
  · rw [if_neg hc]
    have hfilter : (Finset.univ.filter (fun X : Fin 1 → ZMod m =>
        (∀ i, X i ≠ 0) ∧ (∑ i, X i) = c)) = {fun _ => c} := by
      ext X
      rw [mem_phaseSum_one_filter, Finset.mem_singleton]
      exact ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩
    rw [hfilter, Finset.sum_singleton]
    simp

/-- **`resonanceMoment u 1 = sum_{c != 0} ‖u c‖^2`.** The depth-1 resonance moment is the
L2-mass of the unit-phase vector off the zero residue. -/
theorem resonanceMoment_one (u : ZMod m → ℂ) :
    resonanceMoment u 1 = ∑ c ∈ Finset.univ.filter (fun c : ZMod m => c ≠ 0), ‖u c‖ ^ 2 := by
  classical
  unfold resonanceMoment
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun c : ZMod m => c ≠ 0)]
  have hzero : (∑ c ∈ Finset.univ.filter (fun c : ZMod m => ¬ c ≠ 0),
      ‖phaseSum u 1 c‖ ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    rw [Finset.mem_filter] at hc
    have : c = 0 := by simpa using hc.2
    rw [this, phaseSum_one, if_pos rfl, norm_zero]
    simp
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  rw [Finset.mem_filter] at hc
  rw [phaseSum_one, if_neg hc.2]

/-- **`resonanceMoment u 1 = m - 1`** for a unit-phase vector `u` (`‖u l‖ = 1`). This is the exact
base-case value of the prize's free variable: the `sqrt p`-free Salem-Zygmund / Parseval L2-mass. -/
theorem resonanceMoment_one_of_unit (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) :
    resonanceMoment u 1 = (m : ℝ) - 1 := by
  classical
  rw [resonanceMoment_one]
  have hterm : ∀ c ∈ Finset.univ.filter (fun c : ZMod m => c ≠ 0), ‖u c‖ ^ 2 = (1 : ℝ) := by
    intro c _
    rw [hu c]; norm_num
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (Finset.univ.filter (fun c : ZMod m => c ≠ 0)).card = m - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0),
      Finset.card_univ, ZMod.card]
  rw [hcard]
  have hm : 1 ≤ m := NeZero.one_le
  rw [Nat.cast_sub hm, Nat.cast_one]

/-- **The `ResonanceConjecture` holds UNCONDITIONALLY at depth `r = 1`** for a unit-phase vector,
provided `m >= 2`: `m - 1 <= 2 m log m`. (The base rung of the prize, far below the binding depth
`r ~ log m` where the conjecture is open.) -/
theorem resonanceConjecture_one_of_unit (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hm : 2 ≤ m) :
    ResonanceConjecture u 1 := by
  unfold ResonanceConjecture
  rw [resonanceMoment_one_of_unit u hu]
  rw [pow_one]
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog : Real.log 2 ≤ Real.log m :=
    Real.log_le_log (by norm_num) hmR
  have hlog2 : (0.6931471 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  -- 2 m log m >= 2 m log 2 >= 2 m * 0.6931 = 1.3862 m >= m >= m - 1
  have h1 : (2 : ℝ) * (m : ℝ) * Real.log 2 ≤ 2 * (m : ℝ) * Real.log m := by
    have : (0 : ℝ) ≤ 2 * (m : ℝ) := by linarith
    nlinarith [hlog, hmpos]
  have h2 : (m : ℝ) ≤ 2 * (m : ℝ) * Real.log 2 := by
    nlinarith [hlog2, hmpos]
  linarith

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.phaseSum_one
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_one
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_one_of_unit
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceConjecture_one_of_unit
