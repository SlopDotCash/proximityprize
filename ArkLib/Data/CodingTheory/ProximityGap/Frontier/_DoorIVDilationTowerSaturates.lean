/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVDilationDescentRecursion

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Door-(iv) Lane-3: the iterated dilation tower SATURATES the trivial ceiling (#444)

`_DoorIVDilationDescentRecursion` (`worstPeriod_union_le_two_mul_worstPeriod`) kernel-anchored the
single dilation step

> `M(μ_n) = M(H ∪ g·H) ≤ 2 · M(μ_{n/2})`.

Its docstring then argues, **in prose only**, that iterating this `a = log₂ n` times down the dyadic
tower `μ_{2^a} ⊃ μ_{2^{a-1}} ⊃ ... ⊃ μ_1` gives `M(μ_{2^a}) ≤ 2^a · M(μ_1) = n · M(μ_1)`, i.e. the
**trivial `M ≤ n` ceiling and NO √-saving whatsoever**.  This file LOCKS that iteration as a real
kernel-checked theorem, so the "the 2-adic factor-2 recursion is saving-free" constraint (the brief's
ASYMPTOTIC-CLAIM GUARD / Lane-3 refuted-lever lock) is backed by a proof, not a paragraph.

The content is a clean piece of real analysis, completely thinness-agnostic by design (it is a CONSTRAINT
on what iterating ANY factor-`c` descent can deliver, not a CORE bound):

* `descent_tower_le` : from `∀k, M (k+1) ≤ c · M k` (with `0 ≤ c`), conclude
  `M a ≤ c^a · M 0`.  Specialized to `c = 2` this is exactly the prose iteration.
* `dilation_tower_le_two_pow` : the factor-`2` specialization, `M a ≤ 2^a · M 0`.
* `dilation_tower_saturates_trivial` : with `M 0 = O(1)` (the base subgroup `μ_1 = {1}` has
  `M(μ_1) ≤ 1`), the iterated bound is `M a ≤ 2^a = n` — the trivial ceiling, reproduced by the
  recursion with no improvement.

## The no-√-saving lock (why iterating the recursion cannot reach the prize)

The prize CORE needs `M(μ_{2^a}) ≤ C·√(2^a · log) ≤ C·2^{a/2}·√(log)`.  Iterating a per-level factor `c`
gives `M a ≤ c^a · M 0`.  For the tower bound to even REACH the prize order `2^{a/2}` one needs
`c^a ≤ 2^{a/2}·poly`, i.e. `c ≤ √2` asymptotically.  But the probe `_DoorIVTwoDilateNoJointExtreme`
(`34bcd204d`) showed the per-level factor is **exactly `2`** at the worst frequency (the two dilates
co-ray, `ρ(b*) = 1`, `norm_eta_eq_two_dilate_of_coherent`), so the split inequality is an EQUALITY at
`b*` and the factor `2` cannot be shaved.  The two facts together — (this file) iterating `c` gives
`c^a`, and (the probe) `c = 2` is forced — are the precise reason the dilation route is dead:

* `tower_reaches_prizeScale_forces_c_le` : if `c^a · M 0 ≤ K · 2^(a/2)` for a fixed `K` and growing
  base mass, then `c ≤ √2` is forced in the limit sense captured by the per-`a` inequality
  `c^a ≤ (K · 2^(a/2)) / M 0`.  (Stated as the clean finite witness, no asymptotics asserted.)

This is a CONSTRAINT LEMMA only: no CORE bound, no cancellation, completion, moment, anti-concentration,
or capacity claim.  CORE `M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN; door (iv) stays the only live door.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVDilationTowerSaturates

open scoped NNReal

/-- **★ Abstract iterated descent.**  If a nonnegative real sequence `M` contracts by a fixed
nonnegative factor `c` at each step (`M (k+1) ≤ c · M k`), then after `a` steps it is bounded by
`c^a · M 0`.  This is the kernel-anchored form of the prose "iterate the factor-`2` recursion `log₂ n`
times" argument in `_DoorIVDilationDescentRecursion`. -/
theorem descent_tower_le {M : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hstep : ∀ k, M (k + 1) ≤ c * M k) :
    ∀ a, M a ≤ c ^ a * M 0 := by
  intro a
  induction a with
  | zero => simp
  | succ n ih =>
    calc M (n + 1) ≤ c * M n := hstep n
      _ ≤ c * (c ^ n * M 0) := by
            apply mul_le_mul_of_nonneg_left ih hc
      _ = c ^ (n + 1) * M 0 := by ring

/-- **The factor-`2` dilation specialization.**  Iterating the proven single dilation step
`M (k+1) ≤ 2 · M k` down the dyadic tower of depth `a` gives `M a ≤ 2^a · M 0`. -/
theorem dilation_tower_le_two_pow {M : ℕ → ℝ}
    (hstep : ∀ k, M (k + 1) ≤ 2 * M k) :
    ∀ a, M a ≤ 2 ^ a * M 0 := by
  intro a
  have := descent_tower_le (M := M) (c := 2) (by norm_num) hstep a
  simpa using this

/-- **The tower saturates the trivial ceiling.**  With the base subgroup mass `M 0 ≤ 1` (the singleton
`μ_1 = {1}` has worst period `≤ 1`), the iterated factor-`2` descent yields exactly `M a ≤ 2^a`, i.e.
the trivial `M(μ_n) ≤ n` ceiling reproduced with NO improvement — the precise no-√-saving content. -/
theorem dilation_tower_saturates_trivial {M : ℕ → ℝ}
    (hstep : ∀ k, M (k + 1) ≤ 2 * M k) (hbase : M 0 ≤ 1) :
    ∀ a, M a ≤ 2 ^ a := by
  intro a
  have h := dilation_tower_le_two_pow (M := M) hstep a
  have hpow : (0 : ℝ) ≤ 2 ^ a := by positivity
  calc M a ≤ 2 ^ a * M 0 := h
    _ ≤ 2 ^ a * 1 := by exact mul_le_mul_of_nonneg_left hbase hpow
    _ = 2 ^ a := by ring

/-- **No-√-saving lock (finite-witness form).**  Suppose a per-level descent factor `c` is good enough
that, against base mass `M 0`, the iterated bound `c^a · M 0` reaches the prize scale `K · 2^(a/2)` at
depth `a` (`c^a · M 0 ≤ K · 2^(a/2)`).  Then with positive base mass the per-level factor is constrained
by `c^a ≤ (K · 2^(a/2)) / M 0`.  Combined with the probed FACT that the dilation factor is forced to be
exactly `2` (`_DoorIVTwoDilateNoJointExtreme`, co-ray at `b*`), `2^a` cannot satisfy this for fixed `K`
once `a` is large — locking that the factor-2 recursion cannot reach the prize by iteration. -/
theorem tower_reaches_prizeScale_forces_c_le {c K M0 : ℝ} {a : ℕ}
    (hM0 : 0 < M0) (hreach : c ^ a * M0 ≤ K * 2 ^ (a / 2 : ℝ)) :
    c ^ a ≤ (K * 2 ^ (a / 2 : ℝ)) / M0 := by
  rw [le_div_iff₀ hM0]
  exact hreach

/-- **Contrapositive lock.**  If the forced per-level factor `c = 2` overshoots the prize budget at
depth `a` (`(K · 2^(a/2)) / M0 < 2^a`), then the iterated tower bound CANNOT reach the prize scale at
that depth: `K · 2^(a/2) < 2^a · M0`.  This is the honest "the factor-`2` recursion overshoots
`√(n)`" statement: `2^a = n` is the wrong order, `2^(a/2) = √n` is the target. -/
theorem dilation_tower_overshoots_prizeScale {K M0 : ℝ} {a : ℕ}
    (hM0 : 0 < M0) (hover : (K * 2 ^ (a / 2 : ℝ)) / M0 < 2 ^ a) :
    K * 2 ^ (a / 2 : ℝ) < 2 ^ a * M0 := by
  rw [div_lt_iff₀ hM0] at hover
  exact hover

end ArkLib.ProximityGap.Frontier.DoorIVDilationTowerSaturates
