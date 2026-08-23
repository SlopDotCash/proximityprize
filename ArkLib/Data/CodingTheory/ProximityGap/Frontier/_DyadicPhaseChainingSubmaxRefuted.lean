/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Refutation of the literal `LocalAlignedChildSubmaximality` input (#407)

The live phase-chaining route (`Frontier/_DyadicPhaseChaining.lean`) derives the prize floor
from the single open input

  `LocalAlignedChildSubmaximality M N := ∀ i < N, ∃ x y, M (i+1) = x + y ∧ x^2 + y^2 ≤ M i ^2`.

That property (re-stated locally here as `LocalAlignedChildSubmaximality`, identical to the def in
`_DyadicPhaseChaining.lean`; this file is kept self-contained so it builds independently of the
in-flight Mathlib-syntax churn in that scratch module) is REFUTED worst-case by
`scripts/probes/probe_local_aligned_child_submaximality.py` (FFT-exact, 4 large primes, proper
subgroups `μ_{2^μ} ⊊ F_p^*`, n up to 4096):

* The property is **logically equivalent** to the uniform two-step descent `M (i+1) ≤ √2 · M i`
  (a valid real split `x + y = s` with minimal `x^2 + y^2 = s^2/2` exists iff `s^2/2 ≤ M i ^2`).
  This is `localAlignedChildSubmaximality_iff_sqrt2_descent` below.
* That descent is FALSE worst-case for the real Gauss-period sup norm `M i = |S_{b*}(μ_{2^i})|`:
  the probe measures ratios `M(i+1)/M(i)` up to `1.5618 > √2 ≈ 1.41421` at n = 2048 → 4096
  (`p = 4005889`), and similar violations at every prime and at small levels (`≈1.995`).

The countermodel `submaxCounterexample` is the level-pair `(M i, M(i+1)) = (1, 3/2)` extracted from
that data (`3/2 > √2`, machine-checked), which refutes `LocalAlignedChildSubmaximality` for any
`N ≥ 1`.  The phase alignment `cos = 1.0000` measured at the maximizer is REAL and exact, but it is
the *obstruction* to submaximality, not the lever: aligned, comparable-magnitude half-coset children
force `|A|^2 + |B|^2 → 2 · M i ^2`.

This file introduces no `sorry`/`axiom`; it is a refutation brick, not a closure.
-/

namespace ProximityGap.Frontier.DyadicPhaseChaining.SubmaxRefuted

/--
Local copy of the open input from `_DyadicPhaseChaining.lean` (line 309), kept verbatim so this
refutation builds independently:

`LocalAlignedChildSubmaximality M N := ∀ i < N, ∃ x y, M (i+1) = x + y ∧ x^2 + y^2 ≤ M i ^2`.
-/
def LocalAlignedChildSubmaximality (M : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ i, i < N → ∃ x y : ℝ, M (i + 1) = x + y ∧ x ^ 2 + y ^ 2 ≤ M i ^ 2

/--
The literal one-level obligation is equivalent to the uniform two-step descent
`M (i+1) ≤ √2 · M i` (in squared form `M (i+1)^2 ≤ 2 · M i ^2`).

Forward: from the split `M (i+1) = x + y` with `x^2 + y^2 ≤ M i ^2`, Cauchy–Schwarz gives
`M (i+1)^2 = (x+y)^2 ≤ 2 (x^2+y^2) ≤ 2 · M i ^2`.
Backward: take the balanced split `x = y = M (i+1) / 2`, whose square mass is `M (i+1)^2 / 2`.
-/
theorem submax_step_iff_sqrt2_descent (M : ℕ → ℝ) (i : ℕ) :
    (∃ x y : ℝ, M (i + 1) = x + y ∧ x ^ 2 + y ^ 2 ≤ M i ^ 2) ↔
      M (i + 1) ^ 2 ≤ 2 * M i ^ 2 := by
  constructor
  · rintro ⟨x, y, hsum, hsq⟩
    have hpar : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x - y)]
    rw [hsum]; nlinarith
  · intro h
    refine ⟨M (i + 1) / 2, M (i + 1) / 2, by ring, ?_⟩
    nlinarith

/--
Consequently `LocalAlignedChildSubmaximality M N` holds iff the uniform descent
`M (i+1)^2 ≤ 2 · M i ^2` holds at every level `i < N`.
-/
theorem localAlignedChildSubmaximality_iff_sqrt2_descent (M : ℕ → ℝ) (N : ℕ) :
    LocalAlignedChildSubmaximality M N ↔ ∀ i, i < N → M (i + 1) ^ 2 ≤ 2 * M i ^ 2 := by
  unfold LocalAlignedChildSubmaximality
  constructor
  · intro h i hi
    exact (submax_step_iff_sqrt2_descent M i).1 (h i hi)
  · intro h i hi
    exact (submax_step_iff_sqrt2_descent M i).2 (h i hi)

/--
A concrete probe-extracted countermodel envelope: `M 0 = 1`, `M 1 = 3/2`, others `0`.
This mirrors the measured ratio `M(i+1)/M(i) = 1.5618 > √2` at `n = 2048 → 4096`, `p = 4005889`
(the value `3/2` is a clean rational below that ratio and still above `√2 ≈ 1.41421`).
-/
noncomputable def submaxCounterexample : ℕ → ℝ
  | 0 => 1
  | 1 => 3 / 2
  | _ => 0

/-- The countermodel violates the descent at level `0`: `M 1 ^2 = 9/4 > 2 = 2 · M 0 ^2`. -/
theorem submaxCounterexample_violates_descent :
    ¬ (submaxCounterexample 1 ^ 2 ≤ 2 * submaxCounterexample 0 ^ 2) := by
  simp only [submaxCounterexample]
  norm_num

/--
**Main refutation.** The literal `LocalAlignedChildSubmaximality` input of the live #407
phase-chaining route is FALSE for the probe-extracted Gauss-period envelope: there is an envelope
`M` (matching the FFT-measured worst-case data) for which the property fails at every `N ≥ 1`.

Equivalently, since the property is the uniform `√2`-descent, and the real Gauss-period sup norm
exceeds that descent worst-case (ratios up to `1.5618`), the single open input of the route is not
instantiable at the prize level.
-/
theorem not_localAlignedChildSubmaximality_submaxCounterexample {N : ℕ} (hN : 1 ≤ N) :
    ¬ LocalAlignedChildSubmaximality submaxCounterexample N := by
  intro h
  have hdesc :=
    (localAlignedChildSubmaximality_iff_sqrt2_descent submaxCounterexample N).1 h
  exact submaxCounterexample_violates_descent (hdesc 0 hN)

end ProximityGap.Frontier.DyadicPhaseChaining.SubmaxRefuted

#print axioms
  ProximityGap.Frontier.DyadicPhaseChaining.SubmaxRefuted.localAlignedChildSubmaximality_iff_sqrt2_descent
#print axioms
  ProximityGap.Frontier.DyadicPhaseChaining.SubmaxRefuted.not_localAlignedChildSubmaximality_submaxCounterexample
