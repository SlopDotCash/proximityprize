/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G254ConjugatePairedPhaseFreedom

/-!
# G255: multiplier-sign imbalance does not bound the phase-measure discrepancy (#466)

G252/G253/G254 close the histogram-budget repairs of the global phase-discrepancy route: a balanced
(`∑ s = 0`), conjugation-preserving sign move annihilates and then reverses the fixed-row covariance.
The natural rescue for a *marginal* phase-discrepancy input then claims that such a balanced sign move
is admissible under the Lu–Zheng–Zheng marginal phase information, on the ground that its
**multiplier-sign histogram** is balanced to at most one atom (`|∑ s| ≤ 1`), hence — the argument
goes — the *complex phase* empirical measure of the rows is perturbed by only `1/(m-1)`.

That identification is false, and this file records the exact finite invariant that refutes it. A
sign `s = -1` on a row multiplies its normalized phase `z` by `-1`, i.e. **rotates it by `π`**.
Multiplying roughly half of the rows by `-1` — exactly what a balanced `∑ s = 0` move does — moves
that entire half of the phase atoms by `π`, so the empirical phase measure changes by a **fixed
fraction bounded away from `0`**, independent of the (zero) multiplier-sign imbalance. The
"one-atom" scale `1/(m-1)` measures only the imbalance of the `±1` multiplier histogram; it gives no
bound on the discrepancy of the actual phases.

## Model

Index `2*k` normalized phase atoms by `Fin (2*k)`.  Assign the low half `phaseClass = 0` (a first
real angle) and the high half `phaseClass = 1` (a distinct real angle); this is the two-class
extremal-decorrelated arrangement of G252.  The balanced move `phaseSign` gives `+1` to the low half
and `-1` to the high half: `∑ phaseSign = 0`, so it is *maximally* histogram-balanced — its
multiplier-sign imbalance is `0`, better than the "one atom" the rescue is allowed.

A `-1` sign rotates a phase by `π`: `movePhase` sends class `c` to `c + 2` (two fresh classes `2, 3`
distinct from both originals `0, 1`), modelling `z ↦ -z`.  The **phase-measure discrepancy** is
counted by `phaseChanged`, the number of atoms whose phase class actually moves under the signed
move.

We prove, in `ℤ`/`ℕ`, in closed form:

* `signImbalance_eq_zero`: `∑ phaseSign = 0` — the multiplier-sign histogram is exactly balanced,
  the strongest form of the "at most one atom" hypothesis the rescue invokes;
* `phaseChanged_card_eq`: **exactly `k` of the `2k` atoms change phase** under the balanced move —
  every high-half atom is rotated by `π`, every low-half atom is fixed;
* `phaseChanged_is_half`: `2 * (phaseChanged move).card = 2 * k` — the moved fraction is exactly
  one half, **independent of the vanishing multiplier-sign imbalance**;
* `sign_imbalance_does_not_bound_phase_discrepancy`: **the headline decoupling.** A move with zero
  multiplier-sign imbalance (`∑ phaseSign = 0`) changes the phase class of a full half of the atoms
  (`(phaseChanged …).card = k`).  So the multiplier-sign imbalance `1/(m-1)` and the phase-measure
  discrepancy `k/(2k) = 1/2` are different statistics: the former does not upper-bound the latter;
* `phaseDiscrepancy_ge_half`, `phaseDiscrepancy_gt_imbalanceScale`: at every `k ≥ 1` the phase
  discrepancy `2·changed ≥ 2k` (fraction `≥ 1/2`) strictly exceeds the one-atom imbalance scale
  `2·1 = 2` once `k ≥ 2`, and the gap `k` grows without bound — this is not a fixed-`k` accident.

## r-content and why this is not a fixed-depth island

The moved fraction is `k / (2k) = 1/2` for **every** `k`, and `k` is the family half-size the rank
parameter controls (it is G253's spread and G254's paired margin index).  So the decoupling
`phaseChanged = k` while `∑ sign = 0` is a `k`-uniform statement, not a fixed-`k` accident: for the
actual sponsor P1 the multiplier-sign imbalance is `2^{-128+o(1)}` but the phase-measure discrepancy
stays at `1/2`, exactly the three-orders-of-magnitude gap the G256 exact probe measured
(`circular_measure_change ≈ 0.56–0.68` versus one-atom scale `1/(m-1)`).  This closes the last
histogram-admissibility rescue of the marginal phase-discrepancy route: a balanced sign move is
**not** admissible under a marginal-phase input, because it changes the marginal phase measure by a
constant fraction.

This is a route-hygiene no-go (the exact discriminator refuting the "one-atom phase-histogram"
admissibility claim), not a Jacobi estimate and not a prize closure.  The live prize face is
unchanged: a genuinely joint, row-labelled sponsor-prime estimate for
`Re ∑_{χ≠1} What(χ) conj(Rhat_r(χ))` at `r = 5, 6`, which must NOT factor through any marginal phase
budget.  CORE remains OPEN / ON-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G255SignImbalancePhaseDecoupling

open Finset

/-- The low half `{i : Fin (2*k) | (i:ℕ) < k}` has exactly `k` elements. -/
theorem card_low_half (k : ℕ) :
    (Finset.univ.filter (fun i : Fin (2 * k) => (i : ℕ) < k)).card = k := by
  classical
  have hbridge : (Finset.univ.filter (fun i : Fin (2 * k) => (i : ℕ) < k))
      = (Finset.univ.filter (fun i : Fin (2 * k) => i < (k : ℕ))) := by
    apply Finset.filter_congr; intro i _; rfl
  rw [hbridge]
  rw [Fin.card_filter_val_lt]
  omega

/-- The phase class of atom `i` among `2*k` rows: the low half (`i < k`) sits at class `0`, the high
half (`k ≤ i`) sits at class `1`.  This is the two-class extremal-decorrelated arrangement. -/
def phaseClass (k : ℕ) (i : Fin (2 * k)) : ℕ := if (i : ℕ) < k then 0 else 1

/-- The balanced conjugation-preserving sign move: `+1` on the low half, `-1` on the high half.
Its multiplier-sign histogram is exactly balanced. -/
def phaseSign (k : ℕ) (i : Fin (2 * k)) : ℤ := if (i : ℕ) < k then 1 else -1

/-- A sign of `-1` rotates a phase by `π`: `movePhase` sends class `c` to `c + 2`, i.e. into the two
fresh classes `2, 3` distinct from both originals `0, 1`, modelling `z ↦ -z`.  A `+1` sign fixes the
phase. -/
def movedClass (k : ℕ) (i : Fin (2 * k)) : ℕ :=
  if phaseSign k i = 1 then phaseClass k i else phaseClass k i + 2

/-- The set of atoms whose phase class actually moves under the balanced signed move. -/
def phaseChanged (k : ℕ) : Finset (Fin (2 * k)) :=
  Finset.univ.filter (fun i => movedClass k i ≠ phaseClass k i)

/-- **Zero multiplier-sign imbalance.**  The balanced move's `±1` histogram is exactly balanced:
`k` atoms carry `+1`, `k` carry `-1`, so `∑ phaseSign = 0`.  This is the strongest form of the "at
most one atom" hypothesis the marginal-phase rescue invokes. -/
theorem signImbalance_eq_zero (k : ℕ) : ∑ i : Fin (2 * k), phaseSign k i = 0 := by
  classical
  have hlow : (Finset.univ.filter (fun i : Fin (2 * k) => (i : ℕ) < k)).card = k :=
    card_low_half k
  have hhigh : (Finset.univ.filter (fun i : Fin (2 * k) => ¬ (i : ℕ) < k)).card = k := by
    have htot := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (2 * k)))) (fun i => (i : ℕ) < k)
    rw [hlow, Finset.card_univ, Fintype.card_fin] at htot
    omega
  -- split the sum over the low half and its complement
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin (2 * k) => (i : ℕ) < k)]
  have hlowsum : (∑ i ∈ Finset.univ.filter (fun i : Fin (2 * k) => (i : ℕ) < k), phaseSign k i)
      = (k : ℤ) := by
    have : ∀ i ∈ Finset.univ.filter (fun i : Fin (2 * k) => (i : ℕ) < k), phaseSign k i = 1 := by
      intro i hi
      simp only [Finset.mem_filter] at hi
      simp [phaseSign, hi.2]
    rw [Finset.sum_congr rfl this, Finset.sum_const, hlow]; simp
  have hhighsum : (∑ i ∈ Finset.univ.filter (fun i : Fin (2 * k) => ¬ (i : ℕ) < k), phaseSign k i)
      = -(k : ℤ) := by
    have : ∀ i ∈ Finset.univ.filter (fun i : Fin (2 * k) => ¬ (i : ℕ) < k), phaseSign k i = -1 := by
      intro i hi
      simp only [Finset.mem_filter] at hi
      simp [phaseSign, hi.2]
    rw [Finset.sum_congr rfl this, Finset.sum_const, hhigh]; simp
  rw [hlowsum, hhighsum]; ring

/-- A low-half atom (`i < k`) carries sign `+1` and does not move. -/
theorem low_not_changed (k : ℕ) (i : Fin (2 * k)) (hi : (i : ℕ) < k) :
    movedClass k i = phaseClass k i := by
  unfold movedClass phaseSign
  simp [hi]

/-- A high-half atom (`k ≤ i`) carries sign `-1` and is rotated by `π`, so it moves. -/
theorem high_changed (k : ℕ) (i : Fin (2 * k)) (hi : ¬ (i : ℕ) < k) :
    movedClass k i ≠ phaseClass k i := by
  unfold movedClass phaseSign
  simp only [hi, if_false]
  have : ¬ ((-1 : ℤ) = 1) := by decide
  simp [this]

/-- The set of changed atoms is exactly the high half `{i | ¬ i < k}`. -/
theorem phaseChanged_eq_high (k : ℕ) :
    phaseChanged k = Finset.univ.filter (fun i : Fin (2 * k) => ¬ (i : ℕ) < k) := by
  unfold phaseChanged
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : (i : ℕ) < k
  · simp [low_not_changed k i hi, hi]
  · exact iff_of_true (high_changed k i hi) hi

/-- **Exactly `k` of the `2k` atoms change phase.**  Every high-half atom is rotated by `π`, every
low-half atom is fixed: the balanced move moves a full half of the phase atoms. -/
theorem phaseChanged_card_eq (k : ℕ) : (phaseChanged k).card = k := by
  classical
  rw [phaseChanged_eq_high]
  have htot := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (2 * k)))) (fun i => (i : ℕ) < k)
  rw [card_low_half, Finset.card_univ, Fintype.card_fin] at htot
  omega

/-- The moved fraction is exactly one half: `2 · changed = 2k`, independent of the (vanishing)
multiplier-sign imbalance. -/
theorem phaseChanged_is_half (k : ℕ) : 2 * (phaseChanged k).card = 2 * k := by
  rw [phaseChanged_card_eq]

/-- **Headline decoupling.**  A move with *zero* multiplier-sign imbalance (`∑ phaseSign = 0`) still
changes the phase class of a full **half** of the atoms (`(phaseChanged k).card = k`).  So the
multiplier-sign imbalance and the phase-measure discrepancy are different statistics: the former
(scale `1/(m-1)`) does not upper-bound the latter (`k/(2k) = 1/2`).  This refutes the "one-atom
phase-histogram" admissibility claim for the marginal phase-discrepancy route. -/
theorem sign_imbalance_does_not_bound_phase_discrepancy (k : ℕ) :
    (∑ i : Fin (2 * k), phaseSign k i = 0) ∧ (phaseChanged k).card = k :=
  ⟨signImbalance_eq_zero k, phaseChanged_card_eq k⟩

/-- The phase-measure discrepancy is at least half for every nonempty family: `2 · changed ≥ 2k`. -/
theorem phaseDiscrepancy_ge_half (k : ℕ) : 2 * k ≤ 2 * (phaseChanged k).card := by
  rw [phaseChanged_is_half]

/-- The phase discrepancy `k` strictly exceeds the one-atom multiplier scale (`1`) once `k ≥ 2`, and
the gap `k - 1` grows without bound.  The decoupling is `k`-uniform, not a fixed-`k` accident. -/
theorem phaseDiscrepancy_gt_imbalanceScale (k : ℕ) (hk : 2 ≤ k) :
    1 < (phaseChanged k).card := by
  rw [phaseChanged_card_eq]; omega

/-- Honest scope marker: a route-hygiene discriminator, not a prize closure. -/
def isPrizeClosure : Bool := false

theorem not_prizeClosure : isPrizeClosure = false := rfl

#print axioms signImbalance_eq_zero
#print axioms phaseChanged_eq_high
#print axioms phaseChanged_card_eq
#print axioms phaseChanged_is_half
#print axioms sign_imbalance_does_not_bound_phase_discrepancy
#print axioms phaseDiscrepancy_ge_half
#print axioms phaseDiscrepancy_gt_imbalanceScale
#print axioms not_prizeClosure

end ArkLib.ProximityGap.Frontier.G255SignImbalancePhaseDecoupling
