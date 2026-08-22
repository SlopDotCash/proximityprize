/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# G252: global phase discrepancy does not pin the fixed-row weighted covariance (#466)

G251 closed the *aggregate* Cartesian discrepancy route and named the sole surviving target: a
theorem that controls **joint phase-row placement**, equivalently a fixed-row weighted
shifted-subgroup/Jacobi bound.  The natural repair hoped that the joint law of the phase axis
(`arg What(χ)`) and the rank-weight axis (`Rhat_r(χ)`) carries a *rigidity* — a phase co-rotation —
that a global-discrepancy-admissible rearrangement cannot break.

The G252 probes (`scripts/probes/g252_joint_phase_lock_probe.py`,
`scripts/probes/g252_signed_incidence_lock.py`) measure the actual joint law on exact sponsor-type
cells with the true signed incidence weight.  Two facts emerge, sharpening as `m → ∞`:

* the phase-lock strength `|Σ |W||R| e^{i(argW-argR)}| / Σ|W||R|` collapses toward `0`
  (`0.36` at `m=63` down to `0.0002` at `m=1001`): the two phases **decorrelate**; and
* in every cell a *balanced* sign split of the phase histogram (the only move that a global
  discrepancy budget permits, since it preserves the histogram) drives the real covariance to `≤ 0`.

This file records the exact finite invariant behind those numerics.  A "global phase discrepancy
budget" is, at its strongest, control of the phase *histogram*.  The sharpest such control is a
balanced sign vector (equal `+1`/`−1` counts, histogram-sum `0`).  We exhibit, for every `k`, a
fixed-row signed weight whose aligned (all-phases-`+1`) covariance is strictly positive, yet which a
balanced sign vector annihilates.  Hence histogram-level global phase control leaves the fixed-row
weighted covariance completely unpinned: the missing certificate cannot be produced by any global
phase-discrepancy input, only by a genuinely joint phase-row placement theorem.

This is a route no-go, not a Jacobi estimate and not a prize closure.  CORE remains OPEN / ON-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G252JointPhaseRowFreedom

open Finset

/-- The fixed-row weight on `2k` quotient cells: the uniform (all-ones) rank observable.
This is the extremal decorrelated weight isolated by the G252 probe as `m → ∞`. -/
def rowWeight (k : ℕ) : Fin (2 * k) → ℤ := fun _ => 1

/-- A balanced phase-sign vector: `+1` on the first `k` cells, `−1` on the last `k`.
This is the strongest global-discrepancy-admissible move — it preserves the phase histogram
(equal numbers of `+1` and `−1`). -/
def balancedSign (k : ℕ) : Fin (2 * k) → ℤ :=
  fun i => if (i : ℕ) < k then 1 else -1

/-- The aligned covariance: all phases set to `+1`.  This is the maximal (triangle) value. -/
def alignedCov (k : ℕ) : ℤ := ∑ i, rowWeight k i

/-- The split covariance under the balanced phase-sign vector. -/
def splitCov (k : ℕ) : ℤ := ∑ i, balancedSign k i * rowWeight k i

/-- The aligned covariance is exactly `2k`: the fixed-row weighted covariance is genuinely nonzero. -/
theorem alignedCov_eq (k : ℕ) : alignedCov k = 2 * k := by
  unfold alignedCov rowWeight
  simp

/-- The aligned covariance is strictly positive for every nonempty family. -/
theorem alignedCov_pos (k : ℕ) (hk : 0 < k) : 0 < alignedCov k := by
  rw [alignedCov_eq]
  positivity

/-- The phase histogram of `balancedSign` sums to `0`: it is a legitimate
global-discrepancy-preserving rearrangement (equal `+1` and `−1` mass). -/
theorem balancedSign_histogram (k : ℕ) : ∑ i, balancedSign k i = 0 := by
  unfold balancedSign
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, smul_eq_mul, mul_one, mul_neg]
  have hfilter : (Finset.univ.filter (fun i : Fin (2 * k) => (i : ℕ) < k)).card = k := by
    classical
    have hbij :
        (Finset.univ.filter (fun i : Fin (2 * k) => (i : ℕ) < k)).card
          = (Finset.range (2 * k) |>.filter (fun j => j < k)).card := by
      rw [Finset.card_filter, Finset.card_filter,
        Fin.sum_univ_eq_sum_range (fun j => if j < k then (1 : ℕ) else 0)]
    rw [hbij]
    have hk2 : k ≤ 2 * k := by omega
    have : (Finset.range (2 * k)).filter (fun j => j < k) = Finset.range k := by
      apply Finset.ext; intro j
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨_, hj⟩; exact hj
      · intro hj; exact ⟨lt_of_lt_of_le hj hk2, hj⟩
    rw [this, Finset.card_range]
  have hcompl :
      (Finset.univ.filter (fun i : Fin (2 * k) => ¬ (i : ℕ) < k)).card = k := by
    have htot : (Finset.univ : Finset (Fin (2 * k))).card = 2 * k := by simp
    have := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin (2 * k))))
      (p := fun i : Fin (2 * k) => (i : ℕ) < k)
    rw [hfilter, htot] at this
    omega
  rw [hfilter, hcompl]
  ring

/-- The split covariance under the balanced phase-sign vector is exactly `0`. -/
theorem splitCov_eq_zero (k : ℕ) : splitCov k = 0 := by
  unfold splitCov rowWeight
  simp only [mul_one]
  exact balancedSign_histogram k

/-- **The freedom invariant.**  For every nonempty fixed-row family, the aligned weighted
covariance is strictly positive, while a balanced (histogram-preserving) phase-sign vector drives
the same covariance to exactly `0`.  Global phase-histogram control therefore does not pin the
fixed-row weighted covariance: the gap between `alignedCov` and `splitCov` is the full aligned
value, achieved by an admissible global-discrepancy move. -/
theorem global_phase_control_does_not_pin_covariance (k : ℕ) (hk : 0 < k) :
    0 < alignedCov k ∧ splitCov k = 0 ∧ ∑ i, balancedSign k i = 0 :=
  ⟨alignedCov_pos k hk, splitCov_eq_zero k, balancedSign_histogram k⟩

/-- The pinning defect equals the full aligned covariance `2k`: histogram-level global phase
control loses the entire fixed-row signal. -/
theorem pinning_defect_eq_full (k : ℕ) : alignedCov k - splitCov k = 2 * k := by
  rw [alignedCov_eq, splitCov_eq_zero]; ring

/-- Honest scope marker: this is only a joint phase-row freedom no-go. -/
def isPrizeClosure : Bool := false

theorem not_prizeClosure : isPrizeClosure = false := rfl

#print axioms alignedCov_eq
#print axioms alignedCov_pos
#print axioms balancedSign_histogram
#print axioms splitCov_eq_zero
#print axioms global_phase_control_does_not_pin_covariance
#print axioms pinning_defect_eq_full
#print axioms not_prizeClosure

end ArkLib.ProximityGap.Frontier.G252JointPhaseRowFreedom
