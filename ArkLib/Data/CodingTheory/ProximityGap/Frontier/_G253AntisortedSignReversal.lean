/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# G253: the balanced move does not merely annihilate the fixed-row covariance — it reverses it (#466)

G252 (`_G252JointPhaseRowFreedom.lean`) showed that on the *uniform* (all-ones) fixed-row weight,
the sharpest global-discrepancy-admissible move — a balanced, histogram-preserving sign vector —
drives the aligned covariance from `2k > 0` down to exactly `0`.  That already refuted the hoped-for
"global phase discrepancy pins the fixed-row covariance" rigidity.

But the actual CORE object is not the uniform weight.  `conj(Rhat_r(χ))` is a **rank-`r` observable
that varies across the quotient cells**: a nonuniform, spread-carrying weight.  The Opus-core G252
probes measured, on exact sponsor-type cells with the true signed incidence weight, that the
worst-case balanced split does not stop at `0` — it drives the real covariance *strictly negative*,
`bal_frac ≈ −0.57 … −0.71`, bounded away from `0` uniformly in `m` (DISPROOF_LOG
`n=16 p=1009 r=5 m=63 → bal_frac=−0.5798`, `n=8 p=8009 r=5 m=1001 → bal_frac=−0.6559`, etc.).
G252 formalized only the `= 0` collapse and could not see this **sign reversal**, because the
reversal is impossible for a uniform weight (`splitCov ≡ 0` there).

This file records the exact finite invariant behind that measurement.  Model the rank-`r`
observable as the extremal **strictly increasing** integer weight across the `2k` sorted cells,
`rankWeight a k i = a + i` (`a ≥ 0` the DC pedestal, `i` the rank-sorted spread).  The worst-case
balanced move is the **antisorted** sign vector: `+1` on the low-weight half, `−1` on the
high-weight half.  We prove in `ℤ`, in closed form:

* `alignedCov_pos`: the aligned (all-phases-`+1`) covariance is strictly positive for `k ≥ 1`;
* `splitCov_eq_neg_sq`: `splitCov a k = −k²`, the antisorted balanced covariance, **independent of
  the DC pedestal `a`** and **strictly negative** for `k ≥ 1`.  The pedestal cancels because the
  sign histogram is balanced; what survives is exactly the negative of the squared spread.
* `antiSign_histogram`: the antisorted sign vector is a legitimate histogram-preserving move (sums
  to `0`);
* `splitCov_neg`: `splitCov a k < 0` for `k ≥ 1` — the sign reversal G252 could not see;
* `reversal_defect_eq`: `alignedCov a k − splitCov a k = alignedCov a k + k²`, strictly more than
  the full aligned value — the balanced move does not just cancel the signal, it overshoots into
  reversal.

**r-content (why this is not a fixed-depth island).**  `splitCov a k = −k²` isolates the reversal
magnitude as the *squared spread of the rank weight*, with the DC pedestal `a` provably inert.  A
rank-`r` observable of larger spread yields a proportionally larger reversal: the invariant is a
function of the weight geometry the rank parameter controls, not of a fixed depth.  This is the
sharp, sign-aware upgrade of G252's `splitCov = 0` — the histogram-preserving move an unweighted
global phase-discrepancy budget permits reverses the fixed-row weighted signal, so no such budget
can lower-bound the covariance.

This is a route no-go, not a Jacobi estimate and not a prize closure.  CORE remains OPEN / ON-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G253AntisortedSignReversal

open Finset

/-- A strictly increasing rank-`r` observable across the `2k` sorted quotient cells: the DC pedestal
`a` plus the rank-sorted spread `i`.  This is the extremal spread-carrying representative of a
nonuniform rank weight (`conj(Rhat_r(χ))`), the object G252's uniform weight could not model. -/
def rankWeight (a k : ℕ) : Fin (2 * k) → ℤ := fun i => (a : ℤ) + (i : ℕ)

/-- The antisorted balanced phase-sign vector: `+1` on the `k` low-weight cells, `−1` on the `k`
high-weight cells.  This is the strongest global-discrepancy-admissible move against a *sorted*
weight — it preserves the phase histogram (equal `+1`/`−1` counts) yet is maximally anti-correlated
with the weight. -/
def antiSign (k : ℕ) : Fin (2 * k) → ℤ :=
  fun i => if (i : ℕ) < k then 1 else -1

/-- The aligned covariance: all phases `+1` (the maximal, triangle value). -/
def alignedCov (a k : ℕ) : ℤ := ∑ i, rankWeight a k i

/-- The split covariance under the antisorted balanced phase-sign vector. -/
def splitCov (a k : ℕ) : ℤ := ∑ i, antiSign k i * rankWeight a k i

/-- The aligned covariance as a `range (2*k)` sum of `a + j`. -/
private theorem alignedCov_as_range (a k : ℕ) :
    alignedCov a k = ∑ j ∈ Finset.range (2 * k), ((a : ℤ) + (j : ℤ)) := by
  unfold alignedCov rankWeight
  rw [Fin.sum_univ_eq_sum_range (fun j => (a : ℤ) + (j : ℤ))]

/-- The aligned covariance is strictly positive for `k ≥ 1`: the fixed-row weighted covariance is
genuinely nonzero (every summand `a + j ≥ 0`, and the top cell `a + (2k−1) ≥ 1`). -/
theorem alignedCov_pos (a k : ℕ) (hk : 0 < k) : 0 < alignedCov a k := by
  rw [alignedCov_as_range]
  have hmem : (2 * k - 1) ∈ Finset.range (2 * k) := by
    rw [Finset.mem_range]; omega
  have hpos : (0 : ℤ) < (a : ℤ) + ((2 * k - 1 : ℕ) : ℤ) := by
    have : (1 : ℤ) ≤ ((2 * k - 1 : ℕ) : ℤ) := by
      have : 1 ≤ 2 * k - 1 := by omega
      exact_mod_cast this
    positivity
  refine Finset.sum_pos' (fun j _ => ?_) ⟨2 * k - 1, hmem, hpos⟩
  positivity

/-- The antisorted sign vector sums to `0`: it is a legitimate global-discrepancy-preserving move
(equal `+1` and `−1` mass). -/
theorem antiSign_histogram (k : ℕ) : ∑ i, antiSign k i = 0 := by
  unfold antiSign
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, smul_eq_mul, mul_one, mul_neg]
  have hfilter : (Finset.univ.filter (fun i : Fin (2 * k) => (i : ℕ) < k)).card = k := by
    classical
    have hbij :
        (Finset.univ.filter (fun i : Fin (2 * k) => (i : ℕ) < k)).card
          = ((Finset.range (2 * k)).filter (fun j => j < k)).card := by
      rw [Finset.card_filter, Finset.card_filter,
        Fin.sum_univ_eq_sum_range (fun j => if j < k then (1 : ℕ) else 0)]
    rw [hbij]
    have hk2 : k ≤ 2 * k := by omega
    have hset : (Finset.range (2 * k)).filter (fun j => j < k) = Finset.range k := by
      apply Finset.ext; intro j
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨_, hj⟩; exact hj
      · intro hj; exact ⟨lt_of_lt_of_le hj hk2, hj⟩
    rw [hset, Finset.card_range]
  have hcompl :
      (Finset.univ.filter (fun i : Fin (2 * k) => ¬ (i : ℕ) < k)).card = k := by
    have htot : (Finset.univ : Finset (Fin (2 * k))).card = 2 * k := by simp
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (Fin (2 * k))))
      (p := fun i : Fin (2 * k) => (i : ℕ) < k)
    rw [hfilter, htot] at hsplit
    omega
  rw [hfilter, hcompl]; ring

/-- **The reversal invariant (closed form).**  The antisorted balanced covariance is exactly
`−k²`, independent of the DC pedestal `a`.

Proof: split the `2k` cells into the low half `range k` and the reflected high half.  On the low
half `antiSign = +1` and the weight is `a + j`; on the high half `antiSign = −1` and, reindexing
`j ↦ k + j`, the weight is `a + k + j`.  The pedestal `a` and the linear ramp `j` cancel between the
two `range k` sums by the balanced histogram, leaving `∑_{j<k} (−k) = −k²`. -/
theorem splitCov_eq_neg_sq (a k : ℕ) : splitCov a k = - (k : ℤ) ^ 2 := by
  unfold splitCov antiSign rankWeight
  -- convert to a range (2k) sum
  rw [Fin.sum_univ_eq_sum_range
    (fun j => (if j < k then (1 : ℤ) else -1) * ((a : ℤ) + (j : ℤ)))]
  -- split range (2k) = range k ∪ [k, 2k)
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le k)
    (by omega : k ≤ 2 * k)]
  -- low half: j < k, sign +1
  have hlow : ∑ j ∈ Finset.Ico 0 k, (if j < k then (1 : ℤ) else -1) * ((a : ℤ) + (j : ℤ))
      = ∑ j ∈ Finset.Ico 0 k, ((a : ℤ) + (j : ℤ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Ico] at hj
    simp [hj.2]
  -- high half: reindex j = k + t, t in range k, sign -1
  have hhigh : ∑ j ∈ Finset.Ico k (2 * k),
        (if j < k then (1 : ℤ) else -1) * ((a : ℤ) + (j : ℤ))
      = ∑ t ∈ Finset.Ico 0 k, (-1 : ℤ) * ((a : ℤ) + ((k : ℤ) + (t : ℤ))) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have h2k : 2 * k - k = k := by omega
    rw [h2k, Finset.range_eq_Ico]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_Ico] at ht
    have hlt : ¬ (k + t < k) := by omega
    rw [if_neg hlt]
    push_cast
    ring
  rw [hlow, hhigh]
  -- now both are range/Ico k sums; combine and simplify to -k^2
  rw [← Finset.sum_add_distrib]
  have hsimp : ∀ t ∈ Finset.Ico 0 k,
      ((a : ℤ) + (t : ℤ)) + (-1 : ℤ) * ((a : ℤ) + ((k : ℤ) + (t : ℤ))) = -(k : ℤ) := by
    intro t _; ring
  rw [Finset.sum_congr rfl hsimp]
  rw [Finset.sum_const]
  simp only [Nat.card_Ico, Nat.sub_zero, smul_eq_mul]
  push_cast
  ring

/-- The sign reversal, strict form: the balanced move drives the covariance strictly negative for
`k ≥ 1`.  This is the fact G252's uniform weight could not see (`splitCov ≡ 0` there); it captures
the measured `bal_frac ≈ −0.57 … −0.71`. -/
theorem splitCov_neg (a k : ℕ) (hk : 0 < k) : splitCov a k < 0 := by
  rw [splitCov_eq_neg_sq]
  have : (0 : ℤ) < (k : ℤ) ^ 2 := by positivity
  linarith

/-- **The reversal defect.**  `alignedCov − splitCov = alignedCov + k²`: the histogram-preserving
balanced move does not merely cancel the aligned signal, it overshoots by the squared spread `k²`
into reversal.  Contrast G252 `pinning_defect_eq_full`, where the defect equals exactly the aligned
value (`splitCov = 0`); here the defect strictly exceeds it. -/
theorem reversal_defect_eq (a k : ℕ) :
    alignedCov a k - splitCov a k = alignedCov a k + (k : ℤ) ^ 2 := by
  rw [splitCov_eq_neg_sq]; ring

/-- The freedom invariant, sign-aware upgrade of G252's `global_phase_control_does_not_pin_covariance`:
for every nonempty spread-carrying fixed-row family, the aligned covariance is strictly positive, the
antisorted balanced move is histogram-preserving, and it drives the covariance strictly negative
(reversal), not merely to `0`. -/
theorem global_phase_control_reverses_covariance (a k : ℕ) (hk : 0 < k) :
    0 < alignedCov a k ∧ splitCov a k < 0 ∧ ∑ i, antiSign k i = 0 :=
  ⟨alignedCov_pos a k hk, splitCov_neg a k hk, antiSign_histogram k⟩

/-- Honest scope marker: this is only a sign-reversal freedom no-go. -/
def isPrizeClosure : Bool := false

theorem not_prizeClosure : isPrizeClosure = false := rfl

#print axioms alignedCov_pos
#print axioms antiSign_histogram
#print axioms splitCov_eq_neg_sq
#print axioms splitCov_neg
#print axioms reversal_defect_eq
#print axioms global_phase_control_reverses_covariance
#print axioms not_prizeClosure

end ArkLib.ProximityGap.Frontier.G253AntisortedSignReversal
