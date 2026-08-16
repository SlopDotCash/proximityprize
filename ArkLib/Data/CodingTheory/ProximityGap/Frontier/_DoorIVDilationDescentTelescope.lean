/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVDilationDescentRecursion

/-!
# Door-(iv) Lane-3: dyadic-descent telescoping — the recursion gives ONLY the trivial `n`-ceiling (#444)

The dilation-descent recursion (`_DoorIVDilationDescentRecursion`, `a9e7c3f9b`) proved the per-level
inequality `M(μ_{2^{k+1}}) ≤ 2·M(μ_{2^k})`.  This file turns the "iterating it `a = log₂ n` times yields
only `M(μ_n) ≤ n·M(μ_1)`, no √-saving" remark from the recursion docstring into a kernel-checked
**telescoping theorem**, parametric over an abstract level-indexed worst-period sequence `M : ℕ → ℝ`.

> **`M_{k+1} ≤ 2·M_k` for all `k < a`  ⟹  `M_a ≤ 2^a · M_0`.**

Specialized to the dyadic tower (`M_k = M(μ_{2^k})`, `M_0 = M(μ_1) = 1` since `μ_1 = {1}` and
`‖ψ(b)‖ = 1`), this is `M(μ_{2^a}) ≤ 2^a = n`: the **exact trivial `M ≤ n` ceiling**, recovered with
NO cancellation.  This pins, as a theorem rather than prose, the precise statement of *why* the dilation
descent is saving-free: the factor `2^a = n` exactly cancels the `n` we wanted to beat.  The prize needs
`M(μ_n) ≤ C·√(n·log)`; any working descent must beat the per-level factor `2` by a coherence-slack
factor `ρ < 2` whose product over the `a = log₂ n` levels is `≤ √(n·log)/√?`, and the probe
`_DoorIVTwoDilateNoJointExtreme` (`34bcd204d`) showed that slack does not exist.

Lane-3 constraint lemma.  No CORE / cancellation / completion / moment / anti-concentration / capacity
claim.  CORE stays OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVDilationDescentTelescope

/-- **Abstract dyadic-descent telescoping.**  If a nonnegative level-indexed sequence `M` satisfies the
per-level doubling bound `M (k+1) ≤ 2 · M k` for every level `k < a`, then `M a ≤ 2^a · M 0`.

This is the parametric content of "iterate the factor-2 recursion `a` times": each level can at most
double, so after `a` levels the worst period is at most `2^a` times the base.  Captures the no-saving
mechanism of the dilation descent without any subgroup-tower machinery. -/
theorem telescope_le_two_pow_mul (M : ℕ → ℝ) (_hpos : ∀ k, 0 ≤ M k)
    (hstep : ∀ k, M (k + 1) ≤ 2 * M k) (a : ℕ) :
    M a ≤ 2 ^ a * M 0 := by
  induction a with
  | zero => simp
  | succ n ih =>
    calc M (n + 1) ≤ 2 * M n := hstep n
      _ ≤ 2 * (2 ^ n * M 0) := by
          have h2 : (0 : ℝ) ≤ 2 := by norm_num
          exact mul_le_mul_of_nonneg_left ih h2
      _ = 2 ^ (n + 1) * M 0 := by ring

/-- **Trivial-ceiling form of the dyadic descent.**  With the base worst period normalized to
`M 0 = 1` (the `μ_1 = {1}` value, `‖ψ(b)‖ = 1`), the descent gives exactly `M a ≤ 2^a`.  At
`2^a = n` this is the trivial `M(μ_n) ≤ n` ceiling — the dilation descent recovers the trivial bound
and nothing sharper. -/
theorem telescope_le_two_pow_of_base_one (M : ℕ → ℝ) (hpos : ∀ k, 0 ≤ M k)
    (hstep : ∀ k, M (k + 1) ≤ 2 * M k) (hbase : M 0 = 1) (a : ℕ) :
    M a ≤ 2 ^ a := by
  have := telescope_le_two_pow_mul M hpos hstep a
  rwa [hbase, mul_one] at this

/-- **The descent factor is exactly the dimension we wanted to beat.**  Writing `n = 2^a` (the thin
2-power subgroup order), the telescoped ceiling `M a ≤ 2^a · M 0` is `M a ≤ n · M 0`.  The prize target
`M ≤ C·√(n·log)` is a factor `√(n/log)/C` BELOW this — so pure factor-2 descent leaves the entire
√-cancellation gap untouched. -/
theorem telescope_factor_eq_dimension (M : ℕ → ℝ) (hpos : ∀ k, 0 ≤ M k)
    (hstep : ∀ k, M (k + 1) ≤ 2 * M k) (a : ℕ) {n : ℝ} (hn : n = 2 ^ a) :
    M a ≤ n * M 0 := by
  rw [hn]; exact_mod_cast telescope_le_two_pow_mul M hpos hstep a

/-- **No per-level saving below the doubling factor leaves the ceiling trivial (monotone form).**  If
the per-level factor is improved to `c` with `1 ≤ c ≤ 2`, the telescoped bound is `M a ≤ c^a · M 0`; for
`c < 2` this is a genuine multiplicative saving over `2^a`, but only an `a`-th power of the per-level
gain.  This records that the descent's only handle on the √-cancellation is the per-level coherence-slack
factor `c` — the object the dilation probes localized at `c = 2` (no slack). -/
theorem telescope_per_level_factor (M : ℕ → ℝ) (_hpos : ∀ k, 0 ≤ M k) {c : ℝ} (hc1 : 1 ≤ c)
    (hstep : ∀ k, M (k + 1) ≤ c * M k) (a : ℕ) :
    M a ≤ c ^ a * M 0 := by
  have hc0 : (0 : ℝ) ≤ c := le_trans (by norm_num) hc1
  induction a with
  | zero => simp
  | succ n ih =>
    calc M (n + 1) ≤ c * M n := hstep n
      _ ≤ c * (c ^ n * M 0) := mul_le_mul_of_nonneg_left ih hc0
      _ = c ^ (n + 1) * M 0 := by ring

end ArkLib.ProximityGap.Frontier.DoorIVDilationDescentTelescope
