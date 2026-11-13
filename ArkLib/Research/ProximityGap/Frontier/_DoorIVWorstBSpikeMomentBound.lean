/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Door IV: the worst-`b` is an ISOLATED large-deviation spike, so a b-side count bound is
# moment-equivalent (routes back to the second moment = BGK), not a new door

This file records the axiom-clean kernel behind the probe
`scripts/probes/probe_dooriv_worstb_plateau.py`.

## The probed object

Over all `(p-1)/n` multiplicative-coset representatives `b`, look at the distribution of the period
modulus `|η_b|`. A door-(iv) "b-side anti-concentration" hope: bound the sup `M = max_b |η_b|` by
controlling *how many* `b` achieve near-`M` (if few, exploit the arithmetic selecting them).

## The probe verdict (reproducible, proper `μ_n`, p ≫ n³, never n = q−1, over ALL coset reps)

The sup is a **sharp isolated large-deviation spike**, not a broad plateau:

* `frac{ b : |η_b| ≥ 0.9 M } → 0` (measured 7e-4, 1e-4, 2e-4, 6e-4, 3e-4 at n = 16,32,64,16,32):
  a negligible fraction of cosets reach within 90 % of the max.
* mean/M ≈ 0.20–0.23 and `(M − mean)/σ ≈ 4.5 → 5.0 → 5.3` (GROWING with n): the sup sits ~5
  standard deviations above the bulk, deepening with `n`.

A deep, isolated, σ-growing spike is exactly the **extreme-value / equidistribution** profile that
Shaw's tetrachotomy marks as door (iii) = BGK (proven dead). So the worst-`b` does **not** open a new
door: its isolation routes the sup back through the second moment of the `|η_b|` family.

## The formalizable kernel (this file): one-sided Chebyshev is moment-equivalent

A b-side count bound cannot beat the second moment. The clean discrete fact: for a finite family of
reals with mean `μ` and any threshold `μ + d` (`d > 0`), the count of indices exceeding the threshold
times `d²` is at most the centered second moment `Σ (xᵢ − μ)²`. Equivalently the EXCESS of the max
over the mean is controlled by the second moment and the (small) above-threshold count — i.e. an
isolated spike is *consistent with* a small second moment and carries no information beyond it. Any
sup bound through the spike count therefore passes through `Σ (xᵢ − μ)²`, the additive-energy /
moment object = the BGK wall. This proves nothing about CORE and uses no completion; it pins the
b-side count route as moment-equivalent.
-/

namespace ProximityGap.Frontier.DoorIVWorstBSpikeMomentBound

open Finset

variable {ι : Type*}

/-- One-sided Chebyshev / Cantelli count bound (discrete, exact). For a finite family `x : ι → ℝ`
indexed by `s`, with mean parameter `μ`, the number of indices whose value exceeds `μ + d` (with
`d > 0`), scaled by `d²`, is at most the centered second moment `Σ (xᵢ − μ)²`.

This is the kernel obstruction: a high threshold (`d` large, e.g. the spike at `≈ 5σ`) forces the
above-threshold COUNT to be small **only because** the second moment is small — the count is governed
by `Σ (xᵢ − μ)²`, the moment/energy object. A b-side count bound is thus moment-equivalent. -/
theorem threshold_count_mul_sq_le_centered_sndMoment
    (x : ι → ℝ) (s : Finset ι) (μ d : ℝ) (hd : 0 < d) :
    ((s.filter (fun i => μ + d ≤ x i)).card : ℝ) * d ^ 2
      ≤ ∑ i ∈ s, (x i - μ) ^ 2 := by
  classical
  set T := s.filter (fun i => μ + d ≤ x i) with hT
  have hsub : T ⊆ s := Finset.filter_subset _ _
  -- card * d² = ∑_{T} d²
  have hcard : ((T.card : ℝ)) * d ^ 2 = ∑ _i ∈ T, d ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  -- each term on T dominates d²
  have hblock : ∑ _i ∈ T, d ^ 2 ≤ ∑ i ∈ T, (x i - μ) ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have hxi : μ + d ≤ x i := (Finset.mem_filter.mp hi).2
    have hge : d ≤ x i - μ := by linarith
    have hdle : d ^ 2 ≤ (x i - μ) ^ 2 := by
      have h0 : (0 : ℝ) ≤ d := le_of_lt hd
      exact pow_le_pow_left₀ h0 hge 2
    exact hdle
  -- extend the lower block to the full sum (nonneg terms)
  have hext : ∑ i ∈ T, (x i - μ) ^ 2 ≤ ∑ i ∈ s, (x i - μ) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro i _ _
    positivity
  calc ((T.card : ℝ)) * d ^ 2 = ∑ _i ∈ T, d ^ 2 := hcard
    _ ≤ ∑ i ∈ T, (x i - μ) ^ 2 := hblock
    _ ≤ ∑ i ∈ s, (x i - μ) ^ 2 := hext

/-- Moment-equivalence corollary (the door-(iv) constraint): the above-threshold COUNT is bounded
by the centered second moment divided by `d²`. An isolated spike (small count at large `d`) is thus
*explained by* a small second moment `Σ (xᵢ − μ)²` — the additive-energy / moment object. Bounding
the sup via the spike count therefore passes through the second moment, i.e. it is moment-equivalent
and offers no escape from the BGK wall. -/
theorem threshold_count_le_sndMoment_div
    (x : ι → ℝ) (s : Finset ι) (μ d : ℝ) (hd : 0 < d) :
    ((s.filter (fun i => μ + d ≤ x i)).card : ℝ)
      ≤ (∑ i ∈ s, (x i - μ) ^ 2) / d ^ 2 := by
  have hsq : (0 : ℝ) < d ^ 2 := by positivity
  rw [le_div_iff₀ hsq]
  exact threshold_count_mul_sq_le_centered_sndMoment x s μ d hd

/-- Spike-floor form of the same obstruction: the moment cost is already paid once a single index
reaches the threshold `μ + d`.  Thus a proof strategy that first finds or isolates one adversarial
worst-`b` spike has not escaped moments: the mere existence of that spike forces the centered second
moment to be at least `d²`.  Count information can only strengthen this by the integer multiplicity
factor in `threshold_count_mul_sq_le_centered_sndMoment`. -/
theorem sndMoment_ge_sq_of_exists_threshold
    (x : ι → ℝ) (s : Finset ι) (μ d : ℝ) (hd : 0 < d)
    (hex : ∃ i ∈ s, μ + d ≤ x i) :
    d ^ 2 ≤ ∑ i ∈ s, (x i - μ) ^ 2 := by
  classical
  let T := s.filter (fun i => μ + d ≤ x i)
  have hTpos : 0 < T.card := by
    rcases hex with ⟨i, his, hix⟩
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨his, hix⟩⟩
  have hcard : (1 : ℝ) ≤ (T.card : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hTpos
  have hsq_nonneg : 0 ≤ d ^ 2 := by positivity
  have hmul : d ^ 2 ≤ (T.card : ℝ) * d ^ 2 := by
    nlinarith
  have hcheb : (T.card : ℝ) * d ^ 2 ≤ ∑ i ∈ s, (x i - μ) ^ 2 := by
    simpa [T] using threshold_count_mul_sq_le_centered_sndMoment x s μ d hd
  exact le_trans hmul hcheb


/-- Contrapositive spike-budget form: if the centered second moment budget is strictly below `d²`,
then there is **no** index at threshold `μ+d`.  This is the exact kernel guard against a b-side
"isolated spike for free" argument: even a single threshold hit already costs one full `d²` unit of
second moment, so any proof that permits such a hit has routed through the moment/BGK object. -/
theorem threshold_count_eq_zero_of_sndMoment_lt_sq
    (x : ι → ℝ) (s : Finset ι) (μ d : ℝ) (hd : 0 < d)
    (hsmall : (∑ i ∈ s, (x i - μ) ^ 2) < d ^ 2) :
    (s.filter (fun i => μ + d ≤ x i)).card = 0 := by
  classical
  by_contra hne
  have hpos : 0 < (s.filter (fun i => μ + d ≤ x i)).card := Nat.pos_of_ne_zero hne
  rcases Finset.card_pos.mp hpos with ⟨i, hiT⟩
  have hi : i ∈ s ∧ μ + d ≤ x i := Finset.mem_filter.mp hiT
  have hge : d ^ 2 ≤ ∑ i ∈ s, (x i - μ) ^ 2 :=
    sndMoment_ge_sq_of_exists_threshold x s μ d hd ⟨i, hi.1, hi.2⟩
  linarith

end ProximityGap.Frontier.DoorIVWorstBSpikeMomentBound

#print axioms ProximityGap.Frontier.DoorIVWorstBSpikeMomentBound.threshold_count_mul_sq_le_centered_sndMoment
#print axioms ProximityGap.Frontier.DoorIVWorstBSpikeMomentBound.threshold_count_le_sndMoment_div
#print axioms ProximityGap.Frontier.DoorIVWorstBSpikeMomentBound.sndMoment_ge_sq_of_exists_threshold
#print axioms ProximityGap.Frontier.DoorIVWorstBSpikeMomentBound.threshold_count_eq_zero_of_sndMoment_lt_sq
