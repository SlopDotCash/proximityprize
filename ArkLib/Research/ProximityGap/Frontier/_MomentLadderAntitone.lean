/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The moment ladder is antitone: deeper even moments give tighter sup-norm bounds (#407)

The meta-theorem's claim "the *only* route below `√S` is high moments, and depth `≈ log m` is needed"
has two halves: (i) any *single* moment is capped at `√S` (the spike, `_MetaTheoremSecondOrderFloor`),
and (ii) within the moment route, **deeper is strictly better** — the ladder
`r ↦ (∑_i a_i^{2r})^{1/(2r)}` is *antitone*, decreasing toward `max_i a_i` as `r → ∞`. This file
proves (ii), so the prize floor `√(n log(q/n))` is reachable only at large depth (the issue's
`r ≈ log m`), never at small `r` — the structural reason the open input lives at depth `≈ ln q`.

* `sum_rpow_le_rpow_sum` — the superadditivity backbone `∑_i f_i^p ≤ (∑_i f_i)^p` for `p ≥ 1`
  (`ℝ≥0`), proved by induction from `NNReal.add_rpow_le_rpow_add`. (Mathlib packages only the reverse
  `rpow_sum_le_const_mul_sum_rpow`; this Finset form is the missing companion.)
* `ladder_antitone` — `(∑_i a_i^{2(r+1)})^{1/(2(r+1))} ≤ (∑_i a_i^{2r})^{1/(2r)}`: the ladder
  decreases in depth.

Axiom target: `[propext, Classical.choice, Quot.sound]`. Issue #407.
-/

open Finset NNReal

namespace ProximityGap.Frontier.MomentLadderAntitone

/-- **Finset rpow superadditivity.** For `p ≥ 1` and nonnegative `f`, `∑_i f_i^p ≤ (∑_i f_i)^p`.
Proved by induction from the two-term `NNReal.add_rpow_le_rpow_add`. -/
theorem sum_rpow_le_rpow_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
    ∑ i ∈ s, (f i) ^ p ≤ (∑ i ∈ s, f i) ^ p := by
  classical
  induction s using Finset.induction with
  | empty => simp [NNReal.zero_rpow (ne_of_gt (show (0:ℝ) < p by linarith))]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    calc (f a) ^ p + ∑ i ∈ s, (f i) ^ p
        ≤ (f a) ^ p + (∑ i ∈ s, f i) ^ p := by gcongr
      _ ≤ (f a + ∑ i ∈ s, f i) ^ p := NNReal.add_rpow_le_rpow_add _ _ hp

/-- **The moment ladder is antitone in depth.** For a nonnegative family `a` over a finite index, the
even-moment root `(∑_i a_i^{2r})^{1/(2r)}` decreases as `r` grows: depth `r+1` is at most depth `r`.
So deeper moments give tighter sup-norm bounds — the prize floor needs large depth. -/
theorem ladder_antitone {ι : Type*} [Fintype ι] (a : ι → ℝ≥0) {r : ℕ} (hr : 1 ≤ r) :
    (∑ i, (a i) ^ (2 * (r + 1))) ^ ((1 : ℝ) / (2 * (r + 1)))
      ≤ (∑ i, (a i) ^ (2 * r)) ^ ((1 : ℝ) / (2 * r)) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (r : ℝ) + 1 ≠ 0 := by positivity
  set p : ℝ := ((r : ℝ) + 1) / r with hpdef
  have hp1 : 1 ≤ p := by rw [hpdef, le_div_iff₀ hr0]; linarith
  -- superadditivity applied to `b i = a i ^ (2r)` at exponent `p = (r+1)/r`
  have hkey : ∑ i, ((a i) ^ (2 * r) : ℝ≥0) ^ p ≤ (∑ i, (a i) ^ (2 * r)) ^ p :=
    sum_rpow_le_rpow_sum (Finset.univ) (fun i => (a i) ^ (2 * r)) hp1
  -- rewrite the LHS summand `(a i ^ (2r))^p = a i ^ (2(r+1))`
  have hterm : ∀ i, ((a i) ^ (2 * r) : ℝ≥0) ^ p = (a i) ^ (2 * (r + 1)) := by
    intro i
    rw [← NNReal.rpow_natCast (a i) (2 * r), ← NNReal.rpow_natCast (a i) (2 * (r + 1)),
      ← NNReal.rpow_mul]
    congr 1
    rw [hpdef]; push_cast; field_simp [hr0.ne', hr1]
  simp_rw [hterm] at hkey
  -- raise both sides to `1/(2(r+1))`, then collapse the iterated exponent on the RHS
  have hmono := NNReal.rpow_le_rpow hkey (by positivity : (0:ℝ) ≤ (1 : ℝ) / (2 * (r + 1)))
  rw [← NNReal.rpow_mul] at hmono
  have hR : p * ((1 : ℝ) / (2 * (r + 1))) = (1 : ℝ) / (2 * r) := by
    rw [hpdef]; push_cast; field_simp [hr0.ne', hr1]
  rw [hR] at hmono
  exact hmono

end ProximityGap.Frontier.MomentLadderAntitone

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.MomentLadderAntitone.sum_rpow_le_rpow_sum
#print axioms ProximityGap.Frontier.MomentLadderAntitone.ladder_antitone
