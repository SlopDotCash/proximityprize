/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Dyadic phase-chaining gate

This Frontier scratch file records the deterministic consumer for the live
phase-alignment route from the proximity-prize successor issue.

The intended prize instantiation is:

* `A N` is the worst dyadic Gaussian-period sup norm at tower height `N`;
* `inc N` is the certified phase-increment/entropy cost for the split
  `mu_{2^(N+1)} = mu_{2^N} union zeta * mu_{2^N}`;
* the hard mathematics is proving the `PhaseIncrementLaw` with
  `B = C * sqrt (n * log (p / n))`.

This file proves only the no-loss chaining implication.  It contains no
list-decoding vocabulary and no Johnson-bound reduction.

The newest #407 phase-alignment comment refines the live target to a local
square-descent law: for `M(n) = max_b |S_b(mu_n)|`, prove
`M(2n)^2 <= 2 * M(n)^2` up to a small drift.  The multiplicative gate below is
the deterministic telescope for that form.

The final child-submaximality bridge isolates the exact one-level algebra behind
that comment: if the aligned half-coset magnitudes are `x` and `y`, it is enough
to prove `x^2 + y^2 <= M(n)^2`; the elementary inequality
`(x + y)^2 <= 2 * (x^2 + y^2)` supplies the dyadic factor `2`.
-/

namespace ProximityGap.Frontier.DyadicPhaseChaining

open Finset
open scoped BigOperators

/-- The additive chaining budget accumulated along the first `N` dyadic levels. -/
def PhaseChainingBudget (A inc : ℕ → ℝ) (N : ℕ) : ℝ :=
  A 0 + ∑ i ∈ range N, inc i

/--
A phase-increment law consists of a levelwise recursion plus a global budget for
the accumulated increments.

This is intentionally abstract: the next mathematical step is to instantiate
`A` by dyadic Gaussian-period sup norms and `inc` by a phase-alignment defect or
metric-entropy increment.
-/
def PhaseIncrementLaw (A inc : ℕ → ℝ) (N : ℕ) (B : ℝ) : Prop :=
  (∀ i, i < N → A (i + 1) ≤ A i + inc i) ∧ PhaseChainingBudget A inc N ≤ B

/--
Deterministic chaining: a levelwise phase-increment recursion bounds the top
level by the accumulated chaining budget.
-/
theorem level_le_phaseChainingBudget {A inc : ℕ → ℝ} {N : ℕ}
    (hstep : ∀ i, i < N → A (i + 1) ≤ A i + inc i) :
    A N ≤ PhaseChainingBudget A inc N := by
  induction N with
  | zero =>
      simp [PhaseChainingBudget]
  | succ N ih =>
      have hstepN : ∀ i, i < N → A (i + 1) ≤ A i + inc i := by
        intro i hi
        exact hstep i (Nat.lt_trans hi (Nat.lt_succ_self N))
      have ihN : A N ≤ PhaseChainingBudget A inc N := ih hstepN
      have hN : A (N + 1) ≤ A N + inc N := hstep N (Nat.lt_succ_self N)
      calc
        A (N + 1) ≤ A N + inc N := hN
        _ ≤ PhaseChainingBudget A inc N + inc N := by linarith
        _ = PhaseChainingBudget A inc (N + 1) := by
          simp [PhaseChainingBudget, sum_range_succ, add_assoc, add_comm]

/-- A certified phase-increment law immediately bounds the top level. -/
theorem level_le_of_phaseIncrementLaw {A inc : ℕ → ℝ} {N : ℕ} {B : ℝ}
    (hlaw : PhaseIncrementLaw A inc N B) :
    A N ≤ B := by
  exact le_trans (level_le_phaseChainingBudget (A := A) (inc := inc) hlaw.1) hlaw.2

/--
Falsification form: a top-level counterexample above the proposed budget rules
out the phase-increment law.  This is the refutation loop for candidate
phase-defect budgets.
-/
theorem not_phaseIncrementLaw_of_budget_lt {A inc : ℕ → ℝ} {N : ℕ} {B : ℝ}
    (hbad : B < A N) :
    ¬ PhaseIncrementLaw A inc N B := by
  intro hlaw
  exact not_lt_of_ge (level_le_of_phaseIncrementLaw hlaw) hbad

/-- The multiplicative budget accumulated along the first `N` dyadic levels. -/
def MultiplicativeChainingBudget (Q step : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∏ i ∈ range N, step i) * Q 0

/--
The square-descent law requested by the #407 phase-alignment reduction.

In the intended instantiation, `Q i = M(2^i)^2` and `step i` is the certified
one-level loss, conjecturally `2 * (1 + o(1))`.
-/
def SquareDescentLaw (Q step : ℕ → ℝ) (N : ℕ) (B : ℝ) : Prop :=
  (∀ i, i < N → 0 ≤ step i) ∧
    (∀ i, i < N → Q (i + 1) ≤ step i * Q i) ∧
      MultiplicativeChainingBudget Q step N ≤ B

/--
Multiplicative chaining: a local square-descent recursion telescopes to the
product of the per-level losses.
-/
theorem level_le_multiplicativeChainingBudget {Q step : ℕ → ℝ} {N : ℕ}
    (hnonneg : ∀ i, i < N → 0 ≤ step i)
    (hstep : ∀ i, i < N → Q (i + 1) ≤ step i * Q i) :
    Q N ≤ MultiplicativeChainingBudget Q step N := by
  induction N with
  | zero =>
      simp [MultiplicativeChainingBudget]
  | succ N ih =>
      have hnonnegN : ∀ i, i < N → 0 ≤ step i := by
        intro i hi
        exact hnonneg i (Nat.lt_trans hi (Nat.lt_succ_self N))
      have hstepN : ∀ i, i < N → Q (i + 1) ≤ step i * Q i := by
        intro i hi
        exact hstep i (Nat.lt_trans hi (Nat.lt_succ_self N))
      have ihN : Q N ≤ MultiplicativeChainingBudget Q step N := ih hnonnegN hstepN
      have hN : Q (N + 1) ≤ step N * Q N := hstep N (Nat.lt_succ_self N)
      calc
        Q (N + 1) ≤ step N * Q N := hN
        _ ≤ step N * MultiplicativeChainingBudget Q step N := by
          exact mul_le_mul_of_nonneg_left ihN (hnonneg N (Nat.lt_succ_self N))
        _ = MultiplicativeChainingBudget Q step (N + 1) := by
          simp [MultiplicativeChainingBudget, prod_range_succ, mul_assoc, mul_comm]

/-- A certified square-descent law immediately bounds the top level. -/
theorem level_le_of_squareDescentLaw {Q step : ℕ → ℝ} {N : ℕ} {B : ℝ}
    (hlaw : SquareDescentLaw Q step N B) :
    Q N ≤ B := by
  exact le_trans
    (level_le_multiplicativeChainingBudget (Q := Q) (step := step) hlaw.1 hlaw.2.1)
    hlaw.2.2

/--
Falsification form for the square-descent gate.  Any observed top-level value
above the proposed product budget refutes the candidate local descent law.
-/
theorem not_squareDescentLaw_of_budget_lt {Q step : ℕ → ℝ} {N : ℕ} {B : ℝ}
    (hbad : B < Q N) :
    ¬ SquareDescentLaw Q step N B := by
  intro hlaw
  exact not_lt_of_ge (level_le_of_squareDescentLaw hlaw) hbad

/--
The #407 one-level shape, with an explicit drift term:

`Q (i + 1) <= 2 * (1 + drift i) * Q i`.

For the intended Gaussian-period application, `Q i = M(2^i)^2`, so the leading
factor `2` is the random-scale doubling and the drift product is the entire
excess over the target `sqrt (n * log (p / n))` envelope.
-/
def DyadicSquareDriftBudget (Q drift : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∏ i ∈ range N, (2 : ℝ) * (1 + drift i)) * Q 0

/--
`DyadicSquareDriftLaw` is the closed deterministic consumer for the live
phase-alignment conjecture.  It contains the exact local square-descent shape
from #407 and a fully explicit terminal budget.

The hard prize mathematics is to prove this law for the true dyadic
Gaussian-period envelope with a drift product of size `polylog (p / n)`.
-/
def DyadicSquareDriftLaw (Q drift : ℕ → ℝ) (N : ℕ) (B : ℝ) : Prop :=
  (∀ i, i < N → 0 ≤ (2 : ℝ) * (1 + drift i)) ∧
    (∀ i, i < N → Q (i + 1) ≤ ((2 : ℝ) * (1 + drift i)) * Q i) ∧
      DyadicSquareDriftBudget Q drift N ≤ B

/--
The drift-shaped #407 law is just a specialization of the multiplicative
square-descent telescope, with no additional analytic loss.
-/
theorem level_le_dyadicSquareDriftBudget {Q drift : ℕ → ℝ} {N : ℕ}
    (hnonneg : ∀ i, i < N → 0 ≤ (2 : ℝ) * (1 + drift i))
    (hstep : ∀ i, i < N → Q (i + 1) ≤ ((2 : ℝ) * (1 + drift i)) * Q i) :
    Q N ≤ DyadicSquareDriftBudget Q drift N := by
  exact level_le_multiplicativeChainingBudget
    (Q := Q) (step := fun i => (2 : ℝ) * (1 + drift i)) hnonneg hstep

/-- A certified dyadic drift law bounds the terminal squared envelope. -/
theorem level_le_of_dyadicSquareDriftLaw {Q drift : ℕ → ℝ} {N : ℕ} {B : ℝ}
    (hlaw : DyadicSquareDriftLaw Q drift N B) :
    Q N ≤ B := by
  exact le_trans
    (level_le_dyadicSquareDriftBudget (Q := Q) (drift := drift) hlaw.1 hlaw.2.1)
    hlaw.2.2

/--
Falsification form for the #407 drift law.  Any measured dyadic Gaussian-period
level above the drift product budget refutes the proposed local descent package.
-/
theorem not_dyadicSquareDriftLaw_of_budget_lt {Q drift : ℕ → ℝ} {N : ℕ} {B : ℝ}
    (hbad : B < Q N) :
    ¬ DyadicSquareDriftLaw Q drift N B := by
  intro hlaw
  exact not_lt_of_ge (level_le_of_dyadicSquareDriftLaw hlaw) hbad

/--
Recursive affine square-descent budget.

This is the exact deterministic consumer for the literal latest #407 local
shape `M(2n)^2 <= 2 * M(n)^2 + drift`: set `c = 2`,
`Q i = M(2^i)^2`, and `drift i` to the certified one-level additive error.
-/
def AffineSquareDescentBudget (c : ℝ) (Q0 : ℝ) (drift : ℕ → ℝ) : ℕ → ℝ
  | 0 => Q0
  | N + 1 => c * AffineSquareDescentBudget c Q0 drift N + drift N

/--
The affine local square-descent law with an explicit terminal budget.

The law is finite and falsifiable: all open math is in the one-step recurrence.
The recursive budget is intentionally used instead of a closed-form geometric
sum so this consumer stays definitionally small.
-/
def AffineSquareDescentLaw (Q drift : ℕ → ℝ) (c : ℝ) (N : ℕ) (B : ℝ) : Prop :=
  0 ≤ c ∧
    (∀ i, i < N → Q (i + 1) ≤ c * Q i + drift i) ∧
      AffineSquareDescentBudget c (Q 0) drift N ≤ B

/--
Affine square-descent chaining: a local recurrence
`Q(i+1) <= c * Q(i) + drift(i)` bounds the top level by the recursively
accumulated drift budget.
-/
theorem level_le_affineSquareDescentBudget {Q drift : ℕ → ℝ} {c : ℝ} {N : ℕ}
    (hc : 0 ≤ c) (hstep : ∀ i, i < N → Q (i + 1) ≤ c * Q i + drift i) :
    Q N ≤ AffineSquareDescentBudget c (Q 0) drift N := by
  induction N with
  | zero =>
      simp [AffineSquareDescentBudget]
  | succ N ih =>
      have hstepN : ∀ i, i < N → Q (i + 1) ≤ c * Q i + drift i := by
        intro i hi
        exact hstep i (Nat.lt_trans hi (Nat.lt_succ_self N))
      have ihN : Q N ≤ AffineSquareDescentBudget c (Q 0) drift N := ih hstepN
      have hN : Q (N + 1) ≤ c * Q N + drift N := hstep N (Nat.lt_succ_self N)
      calc
        Q (N + 1) ≤ c * Q N + drift N := hN
        _ ≤ c * AffineSquareDescentBudget c (Q 0) drift N + drift N := by
          nlinarith [mul_le_mul_of_nonneg_left ihN hc]
        _ = AffineSquareDescentBudget c (Q 0) drift (N + 1) := by
          simp [AffineSquareDescentBudget]

/-- A certified affine square-descent law immediately bounds the top level. -/
theorem level_le_of_affineSquareDescentLaw {Q drift : ℕ → ℝ} {c : ℝ} {N : ℕ} {B : ℝ}
    (hlaw : AffineSquareDescentLaw Q drift c N B) :
    Q N ≤ B := by
  exact le_trans
    (level_le_affineSquareDescentBudget (Q := Q) (drift := drift) hlaw.1 hlaw.2.1)
    hlaw.2.2

/-- The literal #407 square-descent target with the sharp dyadic factor `2`. -/
def TwoAdicAffineSquareDescentLaw (Q drift : ℕ → ℝ) (N : ℕ) (B : ℝ) : Prop :=
  AffineSquareDescentLaw Q drift (2 : ℝ) N B

/--
Consumer for `Q(i+1) <= 2 * Q(i) + drift(i)`: once the local additive
phase-error recurrence and terminal budget are certified, the top dyadic level
is bounded.
-/
theorem level_le_of_twoAdicAffineSquareDescentLaw {Q drift : ℕ → ℝ} {N : ℕ} {B : ℝ}
    (hlaw : TwoAdicAffineSquareDescentLaw Q drift N B) :
    Q N ≤ B :=
  level_le_of_affineSquareDescentLaw hlaw

/-- With zero additive drift, the affine budget is the pure geometric budget `c^N * Q0`. -/
theorem affineSquareDescentBudget_zero_drift (c Q0 : ℝ) (N : ℕ) :
    AffineSquareDescentBudget c Q0 (fun _ => (0 : ℝ)) N = c ^ N * Q0 := by
  induction N with
  | zero =>
      simp [AffineSquareDescentBudget]
  | succ N ih =>
      simp [AffineSquareDescentBudget, ih, pow_succ]
      ring

/-- The zero-drift two-adic affine budget is exactly `2^N * Q0`. -/
theorem twoAdicAffineSquareDescentBudget_zero_drift (Q0 : ℝ) (N : ℕ) :
    AffineSquareDescentBudget (2 : ℝ) Q0 (fun _ => (0 : ℝ)) N = (2 : ℝ) ^ N * Q0 := by
  exact affineSquareDescentBudget_zero_drift (2 : ℝ) Q0 N

/--
Zero-drift two-adic affine descent is the deterministic `Q N <= 2^N Q 0` bound.

This is the refutable pure-random-scale form of the phase-alignment route: any measured terminal
square envelope above `2^N Q0` forces a nonzero drift or a different mechanism.
-/
theorem level_le_of_twoAdicAffineSquareDescentLaw_zero_drift {Q : ℕ → ℝ} {N : ℕ} :
    TwoAdicAffineSquareDescentLaw Q (fun _ => (0 : ℝ)) N
      ((2 : ℝ) ^ N * Q 0) →
      Q N ≤ (2 : ℝ) ^ N * Q 0 := by
  intro hlaw
  exact level_le_of_twoAdicAffineSquareDescentLaw hlaw

/--
Direct refutation hook for the zero-drift dyadic phase route.

If the terminal square envelope exceeds the pure `2^N` budget, then no local recurrence
`Q(i+1) <= 2 * Q(i)` can hold through the whole window with that terminal budget.
-/
theorem not_twoAdicAffineSquareDescentLaw_zero_drift_of_budget_lt {Q : ℕ → ℝ} {N : ℕ}
    (hbad : (2 : ℝ) ^ N * Q 0 < Q N) :
    ¬ TwoAdicAffineSquareDescentLaw Q (fun _ => (0 : ℝ)) N ((2 : ℝ) ^ N * Q 0) := by
  intro hlaw
  exact not_lt_of_ge (level_le_of_twoAdicAffineSquareDescentLaw_zero_drift hlaw) hbad

/--
If the affine two-adic recurrence holds while the terminal square envelope exceeds the pure
`2^N Q0` budget, then the accumulated additive drift budget is genuinely above the pure budget.

This is the quantitative form of the #407 phase-route correction: finite-level excess cannot be
hidden in the telescope; it must appear as positive accumulated drift.
-/
theorem pure_budget_lt_affineBudget_of_level_gt_pure {Q drift : ℕ → ℝ} {N : ℕ}
    (hlaw :
      TwoAdicAffineSquareDescentLaw Q drift N
        (AffineSquareDescentBudget (2 : ℝ) (Q 0) drift N))
    (hbad : (2 : ℝ) ^ N * Q 0 < Q N) :
    (2 : ℝ) ^ N * Q 0 < AffineSquareDescentBudget (2 : ℝ) (Q 0) drift N := by
  exact hbad.trans_le (level_le_of_twoAdicAffineSquareDescentLaw hlaw)

/--
Falsification form for the affine square-descent law. A measured top-level
value above the proposed recursive budget refutes the candidate local drift
bound or its arithmetic budget.
-/
theorem not_affineSquareDescentLaw_of_budget_lt {Q drift : ℕ → ℝ} {c : ℝ} {N : ℕ}
    {B : ℝ}
    (hbad : B < Q N) :
    ¬ AffineSquareDescentLaw Q drift c N B := by
  intro hlaw
  exact not_lt_of_ge (level_le_of_affineSquareDescentLaw hlaw) hbad

/--
One-level algebra behind the #407 phase-alignment descent.  If the aligned
children have square mass at most `B`, then their aligned sum has square mass at
most `2 * B`.
-/
theorem aligned_sum_sq_le_two_mul_of_sq_add_sq_le {x y B : ℝ}
    (h : x ^ 2 + y ^ 2 ≤ B) :
    (x + y) ^ 2 ≤ 2 * B := by
  have hparallelogram : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (x - y)]
  nlinarith

/--
Local aligned-child submaximality for a dyadic tower envelope `M`.

At level `i`, the next worst value `M (i+1)` is represented as an aligned sum
`x + y` of two half-coset magnitudes, and those child magnitudes have square
mass at most the previous-level worst square.  This is the exact one-level
mathematical input suggested by #407.
-/
def LocalAlignedChildSubmaximality (M : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ i, i < N → ∃ x y : ℝ, M (i + 1) = x + y ∧ x ^ 2 + y ^ 2 ≤ M i ^ 2

/--
The local aligned-child submaximality statement implies the multiplicative
square-descent law with per-level loss exactly `2`.
-/
theorem squareDescentLaw_of_localAlignedChildSubmaximality {M : ℕ → ℝ} {N : ℕ}
    (hlocal : LocalAlignedChildSubmaximality M N) :
    SquareDescentLaw (fun i => M i ^ 2) (fun _ => (2 : ℝ)) N
      (MultiplicativeChainingBudget (fun i => M i ^ 2) (fun _ => (2 : ℝ)) N) := by
  refine ⟨?_, ?_, le_rfl⟩
  · intro i hi
    norm_num
  · intro i hi
    obtain ⟨x, y, hsum, hsq⟩ := hlocal i hi
    simpa [hsum] using aligned_sum_sq_le_two_mul_of_sq_add_sq_le hsq

/--
Direct falsification hook for the aligned-child route.

If a probe or theorem produces a terminal square mass above the exact `2`-per-level budget, then
the local aligned-child submaximality hypothesis cannot hold through that tower window.
-/
theorem not_localAlignedChildSubmaximality_of_budget_lt {M : ℕ → ℝ} {N : ℕ}
    (hbad :
      MultiplicativeChainingBudget (fun i => M i ^ 2) (fun _ => (2 : ℝ)) N < M N ^ 2) :
    ¬ LocalAlignedChildSubmaximality M N := by
  intro hlocal
  exact not_squareDescentLaw_of_budget_lt
    (Q := fun i => M i ^ 2) (step := fun _ => (2 : ℝ)) (N := N)
    (B := MultiplicativeChainingBudget (fun i => M i ^ 2) (fun _ => (2 : ℝ)) N) hbad
    (squareDescentLaw_of_localAlignedChildSubmaximality hlocal)

/-! ## Axiom audit -/

#print axioms level_le_phaseChainingBudget
#print axioms level_le_of_phaseIncrementLaw
#print axioms not_phaseIncrementLaw_of_budget_lt
#print axioms level_le_multiplicativeChainingBudget
#print axioms level_le_of_squareDescentLaw
#print axioms not_squareDescentLaw_of_budget_lt
#print axioms level_le_dyadicSquareDriftBudget
#print axioms level_le_of_dyadicSquareDriftLaw
#print axioms not_dyadicSquareDriftLaw_of_budget_lt
#print axioms level_le_affineSquareDescentBudget
#print axioms level_le_of_affineSquareDescentLaw
#print axioms level_le_of_twoAdicAffineSquareDescentLaw
#print axioms affineSquareDescentBudget_zero_drift
#print axioms twoAdicAffineSquareDescentBudget_zero_drift
#print axioms level_le_of_twoAdicAffineSquareDescentLaw_zero_drift
#print axioms not_twoAdicAffineSquareDescentLaw_zero_drift_of_budget_lt
#print axioms pure_budget_lt_affineBudget_of_level_gt_pure
#print axioms not_affineSquareDescentLaw_of_budget_lt
#print axioms aligned_sum_sq_le_two_mul_of_sq_add_sq_le
#print axioms squareDescentLaw_of_localAlignedChildSubmaximality
#print axioms not_localAlignedChildSubmaximality_of_budget_lt

end ProximityGap.Frontier.DyadicPhaseChaining
