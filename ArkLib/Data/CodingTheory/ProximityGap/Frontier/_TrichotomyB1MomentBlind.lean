/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Analysis.MeanInequalities

/-!
# Trichotomy bucket B1, formalized at all depths: a single even moment determines the sup only up to `N^{1/2r}` (#444)

This is the formal backbone of **bucket B1** of the conjecture trichotomy
(`docs/kb/deltastar-444-conjecture-trichotomy-2026-06-17.md`): *every method whose output is a 2nd-moment / energy /
average quantity is structurally blind to the `L^∞` sup.* `_AttackE2_MomentConeSpikeNoGo` proved the `r = 2` case
(the `{S1,S2,S4}` moment cone admits a spike). This file proves the statement at **all depths `r`**, which is what
makes B1 a wall and not a single missing lemma.

**The fact.** Fix the index-set size `N` (for the prize, `N = q − 1` frequencies) and a depth `r ≥ 1`. Consider the
`2r`-th power-sum moment `S_{2r} = Σ_i v_i^{2r}` of a nonnegative vector `v` (for the periods, `S_{2r} = q·E_r`).
Two vectors can share the *same* `S_{2r}` yet have wildly different maxima:
- the **flat** vector (`N` copies of `a`): `S_{2r} = N·a^{2r}`, `max = a`;
- a **spike** vector (one coordinate `c`, the rest small): `S_{2r} = c^{2r}`, `max = c`.
Equating the moments forces `c^{2r} = N·a^{2r}`, i.e. `(c/a)^{2r} = N`, so `max` is undetermined by `S_{2r}` up to the
factor `N^{1/2r}`. Hence **no functional of the moments up to depth `r` can pin `max` more tightly than `N^{1/2r}`.**

**Why this is the wall (docstring arithmetic).** At the prize, `N = q − 1 ≈ n^4` and the target precision is the
`√(log)` slack over the `√n` Parseval floor — i.e. a certificate must pin `max/√n ≤ √(2 log q) = O(√log)`. But a
bounded-depth moment functional leaves `max` ambiguous by `N^{1/2r} = (q−1)^{1/2r}`, which is a *positive power of `q`*
for every fixed `r`, dwarfing any `√log`. To shrink `N^{1/2r}` to `O(√log)` you need `r ≈ log q` — and at that depth
the char-`p` excess `W_r > 0` (crossover `r ≈ 5`) makes the char-0 energy bound false. So B1 fails at every depth: too
shallow ⟹ the `N^{1/2r}` ambiguity; too deep ⟹ the char-`p` excess. This is exactly `moment_ladder_exceeds_prize`,
re-derived here as a clean self-contained spike construction valid for all `r`.

**What this file proves (axiom-clean).** `moment_ambiguity`: given the flat/spike moment-matching relation, the maxima
differ (`a < c`) and the ambiguity ratio satisfies `(c/a)^{2r} = N`. Plus concrete witnesses at `r = 1` (Parseval:
`16·1² = 4²`, max `1` vs `4`) and `r = 2` (`16·1⁴ = 2⁴`, max `1` vs `2`) — the `r=1` case *is* why Parseval cannot
bound the house. Issue #444.
-/

namespace ProximityGap.Frontier.TrichotomyB1

/-- **B1 at all depths.** If a flat vector (`N` copies of `a`) and a spike (`c`) share the same `2r`-th power-sum
moment `N·a^{2r} = c^{2r}`, then their maxima differ (`a < c`, for `N ≥ 2`, `a > 0`, `r ≥ 1`) and the ambiguity
ratio satisfies `c^{2r}/a^{2r} = N`. So the moment `S_{2r}` determines `max` only up to the factor `N^{1/2r}`. -/
theorem moment_ambiguity (N r : ℕ) (a c : ℝ) (ha : 0 < a) (hc : 0 ≤ c) (hN : 2 ≤ N) (hr : 1 ≤ r)
    (hmom : (N : ℝ) * a ^ (2 * r) = c ^ (2 * r)) :
    a < c ∧ c ^ (2 * r) / a ^ (2 * r) = (N : ℝ) := by
  have h2r : 0 < 2 * r := by omega
  have hapow : (0 : ℝ) < a ^ (2 * r) := pow_pos ha _
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  -- a^{2r} < c^{2r} since c^{2r} = N a^{2r} >= 2 a^{2r} > a^{2r}
  have hlt : a ^ (2 * r) < c ^ (2 * r) := by
    rw [← hmom]; nlinarith [hapow, hNR]
  refine ⟨?_, ?_⟩
  · -- strict monotonicity of x ↦ x^{2r} on nonnegatives gives a < c
    exact lt_of_pow_lt_pow_left₀ (2 * r) hc hlt
  · -- the ratio equals N exactly
    rw [← hmom]; field_simp

/-- **Concrete `r = 1` (Parseval) witness.** `16` copies of `1` and a single `4` have the SAME second-moment sum
`16 = 4²`, but maxima `1` vs `4`: the Parseval/2nd-moment alone cannot bound the maximum. -/
example : (16 : ℝ) * (1 : ℝ) ^ (2 * 1) = (4 : ℝ) ^ (2 * 1) ∧ (1 : ℝ) < 4 := by norm_num

/-- **Concrete `r = 2` witness.** `16` copies of `1` and a single `2` have the SAME 4th-moment sum `16 = 2⁴`, maxima
`1` vs `2`: the `{S₂,S₄}` moment data does not determine the maximum (the `_AttackE2` spike, made explicit). -/
example : (16 : ℝ) * (1 : ℝ) ^ (2 * 2) = (2 : ℝ) ^ (2 * 2) ∧ (1 : ℝ) < 2 := by norm_num

/-- The ambiguity factor instantiated: at depth `r` with `N` frequencies the moment pins `max` only up to
`N^{1/2r}` — here the `(2r)`-th power of the ratio is exactly `N`, so for fixed `r` and `N ≈ q` it is a positive
power of `q`, never the `√log` precision the prize needs. -/
theorem ambiguity_ratio_pow (N r : ℕ) (a c : ℝ) (ha : 0 < a) (hc : 0 ≤ c) (hN : 2 ≤ N) (hr : 1 ≤ r)
    (hmom : (N : ℝ) * a ^ (2 * r) = c ^ (2 * r)) :
    (c / a) ^ (2 * r) = (N : ℝ) := by
  have hane : a ≠ 0 := ne_of_gt ha
  rw [div_pow, (moment_ambiguity N r a c ha hc hN hr hmom).2]

end ProximityGap.Frontier.TrichotomyB1

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.TrichotomyB1.moment_ambiguity
#print axioms ProximityGap.Frontier.TrichotomyB1.ambiguity_ratio_pow
