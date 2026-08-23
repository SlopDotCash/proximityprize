/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Finite-prefix Jacobi turnover gate

The form-D/Jacobi route to issue #464 says the prize upper bound is equivalent to an early turnover
of the recurrence coefficients `b_k`: the global edge is controlled only when all relevant
coefficients satisfy the prize-scale ceiling.

This file isolates the finite last-mile obstruction.  Verifying the Hermite/Jacobi coefficient
bound on a prefix `k <= K` does not imply a global bound: a single coefficient at `K+1` can spike.
The exact finite consumer is:

`global bound = prefix bound + tail bound`.

For the real Gauss-period Jacobi matrix, the missing theorem is therefore not more low-depth
Hankel arithmetic by itself.  It is a tail/turnover theorem saying no coefficient beyond the
checked prefix can re-enter above the prize ceiling.  This is the form-D version of the same
L²-to-L∞ / deep-moment wall.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.JacobiFinitePrefixTurnoverGate

/-- Coefficients are bounded by `B` on the prefix `k <= K`. -/
def PrefixBound (b : ℕ -> ℝ) (K : ℕ) (B : ℝ) : Prop :=
  ∀ k : ℕ, k <= K -> b k <= B

/-- Coefficients are bounded by `B` strictly after the prefix. -/
def TailBound (b : ℕ -> ℝ) (K : ℕ) (B : ℝ) : Prop :=
  ∀ k : ℕ, K < k -> b k <= B

/-- Global coefficient ceiling. -/
def GlobalBound (b : ℕ -> ℝ) (B : ℝ) : Prop :=
  ∀ k : ℕ, b k <= B

/-- Prefix and tail bounds are exactly a global bound. -/
theorem globalBound_iff_prefix_and_tail (b : ℕ -> ℝ) (K : ℕ) (B : ℝ) :
    GlobalBound b B ↔ PrefixBound b K B ∧ TailBound b K B := by
  constructor
  · intro h
    exact ⟨fun k _hk => h k, fun k _hk => h k⟩
  · intro h k
    rcases h with ⟨hprefix, htail⟩
    by_cases hk : k <= K
    · exact hprefix k hk
    · exact htail k (Nat.lt_of_not_ge hk)

/-- The one-coefficient spike immediately after a checked prefix. -/
def prefixSpike (K : ℕ) (H : ℝ) : ℕ -> ℝ :=
  fun k : ℕ => if k <= K then 0 else H

/-- A prefix spike is zero on the checked prefix. -/
theorem prefixSpike_eq_zero_of_le {K k : ℕ} {H : ℝ} (hk : k <= K) :
    prefixSpike K H k = 0 := by
  simp [prefixSpike, hk]

/-- A prefix spike has height `H` at `K+1`. -/
theorem prefixSpike_succ (K : ℕ) (H : ℝ) :
    prefixSpike K H (K + 1) = H := by
  have hnot : ¬ K + 1 <= K := by omega
  simp [prefixSpike, hnot]

/-- The prefix spike obeys any nonnegative prefix budget. -/
theorem prefixBound_prefixSpike {K : ℕ} {B H : ℝ} (hB : 0 <= B) :
    PrefixBound (prefixSpike K H) K B := by
  intro k hk
  rw [prefixSpike_eq_zero_of_le hk]
  exact hB

/-- If the spike height is above `B`, the global bound fails. -/
theorem not_globalBound_prefixSpike {K : ℕ} {B H : ℝ} (hBH : B < H) :
    ¬ GlobalBound (prefixSpike K H) B := by
  intro hglobal
  have h := hglobal (K + 1)
  rw [prefixSpike_succ K H] at h
  exact (not_lt_of_ge h) hBH

/-- Prefix verification alone cannot force the global Jacobi turnover ceiling: for any checked
prefix and any larger height `H`, there is a coefficient profile that satisfies the prefix bound
but violates the global bound at the next index. -/
theorem prefixBound_not_force_global
    {K : ℕ} {B H : ℝ} (hB : 0 <= B) (hBH : B < H) :
    ∃ b : ℕ -> ℝ,
      PrefixBound b K B ∧ ¬ GlobalBound b B ∧ b (K + 1) = H := by
  refine ⟨prefixSpike K H, prefixBound_prefixSpike hB,
    not_globalBound_prefixSpike hBH, prefixSpike_succ K H⟩

/-- A tail bound is exactly the extra ingredient ruled out by the prefix-spike countermodel. -/
theorem tailBound_fails_for_prefixSpike {K : ℕ} {B H : ℝ} (hBH : B < H) :
    ¬ TailBound (prefixSpike K H) K B := by
  intro htail
  have h := htail (K + 1) (by omega : K < K + 1)
  rw [prefixSpike_succ K H] at h
  exact (not_lt_of_ge h) hBH

/-- Bundled finite gate: prefix-only evidence is refuted by a spike; prefix plus tail is equivalent
to the global turnover statement. -/
theorem finitePrefixTurnoverGate
    {K : ℕ} {B H : ℝ} (hB : 0 <= B) (hBH : B < H) :
    (GlobalBound (prefixSpike K H) B ↔
        PrefixBound (prefixSpike K H) K B ∧ TailBound (prefixSpike K H) K B)
      ∧ PrefixBound (prefixSpike K H) K B
      ∧ ¬ TailBound (prefixSpike K H) K B
      ∧ ¬ GlobalBound (prefixSpike K H) B := by
  exact ⟨globalBound_iff_prefix_and_tail (prefixSpike K H) K B,
    prefixBound_prefixSpike hB,
    tailBound_fails_for_prefixSpike hBH,
    not_globalBound_prefixSpike hBH⟩

#print axioms globalBound_iff_prefix_and_tail
#print axioms prefixSpike_eq_zero_of_le
#print axioms prefixSpike_succ
#print axioms prefixBound_prefixSpike
#print axioms not_globalBound_prefixSpike
#print axioms prefixBound_not_force_global
#print axioms tailBound_fails_for_prefixSpike
#print axioms finitePrefixTurnoverGate

end ArkLib.ProximityGap.Frontier.JacobiFinitePrefixTurnoverGate
