/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# LANE F (#466 round 12): the frontal conjugate-count assault on the wall — the exact GATE COLLAPSE

This file records the axiom-clean core of the **frontal assault** on the analytic wall
`W_r ≤ n^{2r}/p` at `r = β+1`.  It does NOT close the wall; it makes precise, as an *exact finite*
arithmetic statement at the prize point, *why the only unconditional tool (the conjugate/norm-count
bound) is vacuous there* — which is the exact boundary of the wall.

## The reframe (exact, probe-validated `probe_466r12_frontal.py`)

The wraparound count is
`W_r = #{ (h₁…h_{2r}) ∈ μ_n^{2r} : α = Σ εᵢhᵢ ≡ 0 (mod 𝔭),  α ≠ 0 in ℤ[ζ_n] }`,
i.e. the number of sparse `±1` sums of `≤ 2r` `n`-th roots of unity that are a **nonzero** element
of the degree-1 prime `𝔭 | p`.  Since `p` splits completely, `α ≡ 0 (mod 𝔭)` with `α ≠ 0` forces
`p ∣ N(α)`, `N(α) ≠ 0`.  (Cross-check: the norm-divisibility count equals `W_r` exactly, n=8.)

## The conjugate-count tool and its gate

`RootSumNorm.abs_norm_sum_rootsOfUnity_le`: `|N(α)| ≤ (#terms)^{[K:ℚ]} = (2r)^{φ(n)}` for a `≤ 2r`
term root-of-unity sum (`φ(2^μ) = n/2`).  Hence **`(2r)^{n/2} < p ⟹ W_r = 0`** (a nonzero `α` has
`|N(α)| ≤ (2r)^{n/2} < p`, so `p ∤ N(α)`; this is the in-tree `no_wraparound_at_depth`).  The
provable reach is `r_gate(n,p) = ⌊½ · p^{2/n}⌋`.

## The collapse — the NEW exact-finite content of this round

At the prize (`p = n^β`, `β = 4`) `p^{2/n} = n^{8/n} → 1`, so `r_gate(n) = ⌊½·n^{8/n}⌋` collapses:
`n=8 → 4`, `n=16 → 2`, `n=32 → 1`, and **`n ≥ 64 → 0`**.  Prior work
(`_AvND_NormDiameterThreshold.threshold_lt_saddle`) recorded the *asymptotic-in-p* collapse against
the saddle `r* ~ log p`.  Here we record the **exact finite** boundary: for `n ≥ 64` the gate is
already vacuous at the *very first rung* `r = 1`, because `2^{n/2} > n^4`.  So at the prize scale
`n = 2^30` the conjugate-count method certifies `W_r = 0` for **no** `r ≥ 1` whatsoever — the entire
open surface `[1, β+1]` lies past the gate.

* `gate_vacuous_at_prize` — for `64 ≤ n` (dyadic, `p = n^4`) and every `r ≥ 1`, `(2r)^{n/2} ≥ p`, so
  the sufficient condition `(2r)^{n/2} < p` for `W_r = 0` **fails at every rung** — the norm bound is
  vacuous everywhere on the prize surface.
* `two_pow_half_gt_n_pow_four` — the exact crossover `2^{n/2} > n^4` for `n ≥ 64`.
The frontal reduction (narrative, tying to the W1 object): for any `(n,p,r)`, EITHER the
conjugate-count gate closes it (`(2r)^{n/2} < p`, giving `W_r = 0` via the in-tree
`RootSumNorm.abs_norm_sum_rootsOfUnity_le` + `no_wraparound_at_depth`), OR one is in the post-gate
region where the sole open content is the phase-cancellation inequality
`WallBetaPlusOne.WraparoundBelowDC` (`p·W_r ≤ n^{2r}`).  `gate_vacuous_at_prize` shows the FIRST
disjunct is unreachable at the prize for every `r ≥ 1`, so the wall is *exactly* the second — a
magnitude-only argument cannot enter it: the conjugate product `|N| = ∏|σ|` can exceed `p` even when
no single `|σ|` is large; only inter-conjugate phase cancellation (BGK/Paley) controls the count.

**Honest verdict (LANE F).** REDUCES-TO-WALL, at the exact step: *the frontal norm/conjugate-count
assault closes the wall only where `(2r)^{n/2} < p`; at the prize that region is empty for every
`r ≥ 1`, so the residual is precisely the un-gated wraparound-below-DC inequality.*  No wall closure.

Issue #466 (lane F).
-/

namespace ArkLib.ProximityGap.FrontalConjugateGate

open scoped BigOperators

/-- Helper: `16·k^4 < 2^k` for every `k ≥ 32` (the doubling beats the quartic slack).  The base
case `k = 32` is `16·32^4 = 16777216 < 4294967296 = 2^32`; the step uses `(m+1)^4 ≤ 2 m^4` for
`m ≥ 32`.  Stated as a self-contained `∀` so the induction hypothesis carries its own bound. -/
theorem sixteen_mul_pow_four_lt : ∀ k : ℕ, 32 ≤ k → 16 * k ^ 4 < 2 ^ k := by
  intro k
  induction k with
  | zero => omega
  | succ m ih =>
    intro hk
    rcases Nat.lt_or_ge m 32 with hm | hm
    · -- forced `m + 1 = 32` (since `hk : 32 ≤ m+1` and `hm : m < 32`, so `m = 31`).
      have : m = 31 := by omega
      subst this; norm_num
    · have ihm := ih hm
      have hpow : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
      -- `(m+1)^4 ≤ 2 m^4` for `m ≥ 32` (expand; `m ≥ 4` already suffices).
      have hquartic : (m + 1) ^ 4 ≤ 2 * m ^ 4 := by
        have h5 : 5 ≤ m := by omega
        -- `(m+1)^4 = m^4 + (4m^3+6m^2+4m+1)`; show the tail `≤ m^4` from `m ≥ 5`.
        have hexp : (m + 1) ^ 4 = m ^ 4 + (4 * m ^ 3 + 6 * m ^ 2 + 4 * m + 1) := by ring
        have hm3 : 5 * m ^ 3 ≤ m ^ 4 := by
          have : 5 * m ^ 3 ≤ m * m ^ 3 := by gcongr
          simpa [pow_succ, mul_comm] using this
        have hm2 : 5 * m ^ 2 ≤ m ^ 3 := by
          have : 5 * m ^ 2 ≤ m * m ^ 2 := by gcongr
          simpa [pow_succ, mul_comm] using this
        have hm1 : 5 * m ≤ m ^ 2 := by
          have : 5 * m ≤ m * m := by gcongr
          simpa [pow_two] using this
        have htail : 4 * m ^ 3 + 6 * m ^ 2 + 4 * m + 1 ≤ m ^ 4 := by nlinarith [hm3, hm2, hm1, h5]
        rw [hexp]; nlinarith [htail]
      calc 16 * (m + 1) ^ 4 ≤ 16 * (2 * m ^ 4) := by gcongr
        _ = 2 * (16 * m ^ 4) := by ring
        _ < 2 * 2 ^ m := by omega
        _ = 2 ^ (m + 1) := hpow.symm

/-- **Exact crossover.** For `n ≥ 64` the conjugate count `2^{n/2}` (the `r = 1` norm-diameter
bound) already exceeds the prize modulus `p = n^4`.  Hence the gate `(2·1)^{n/2} < p` FAILS at the
first rung.  (Base `n = 64`: `2^{32} = 4294967296 > 16777216 = 64^4`; the LHS/RHS ratio only grows.)
-/
theorem two_pow_half_gt_n_pow_four {n : ℕ} (hn : 64 ≤ n) (hn2 : 2 ∣ n) :
    n ^ 4 < 2 ^ (n / 2) := by
  -- Write `n = 2k`, `k ≥ 32`; `n^4 = 16 k^4 < 2^k = 2^(n/2)`.
  obtain ⟨k, rfl⟩ := hn2
  have hk : 32 ≤ k := by omega
  have hkey : 16 * k ^ 4 < 2 ^ k := sixteen_mul_pow_four_lt k hk
  have hn4 : (2 * k) ^ 4 = 16 * k ^ 4 := by ring
  have hhalf : (2 * k) / 2 = k := by omega
  rw [hn4, hhalf]
  exact hkey

/-- **The prize-scale gate is vacuous at every rung.** For a dyadic subgroup order `n ≥ 64` and the
prize modulus `p = n^4`, the conjugate-count sufficient condition for no wraparound at depth `r`,
`(2r)^{n/2} < p`, is FALSE for every `r ≥ 1`.  (Monotone in `r`, so it suffices at `r = 1`.)
Consequently the norm/conjugate-count method certifies `W_r = 0` at NO rung on the prize surface —
the entire open region `1 ≤ r ≤ β+1` is past the gate. -/
theorem gate_vacuous_at_prize {n : ℕ} (hn : 64 ≤ n) (hn2 : 2 ∣ n) {r : ℕ} (hr : 1 ≤ r) :
    ¬ ((2 * r) ^ (n / 2) < n ^ 4) := by
  intro hlt
  -- `(2·1)^{n/2} = 2^{n/2} ≤ (2r)^{n/2} < n^4`, contradicting `n^4 < 2^{n/2}`.
  have hmono : (2 * 1) ^ (n / 2) ≤ (2 * r) ^ (n / 2) :=
    Nat.pow_le_pow_left (by omega) (n / 2)
  have h1 : (2 : ℕ) ^ (n / 2) ≤ (2 * r) ^ (n / 2) := by simpa using hmono
  have hgt := two_pow_half_gt_n_pow_four hn hn2
  omega

/-- **The gate at n = 64, r = 1 concretely** (a checkable witness that the collapse is real, not
asymptotic): `2^{32} = 4294967296 > 16777216 = 64^4`, so the first rung is already past the gate. -/
theorem gate_vacuous_n64_r1 : ¬ ((2 * 1) ^ (64 / 2) < 64 ^ 4) :=
  gate_vacuous_at_prize (n := 64) (by norm_num) (by norm_num) (r := 1) (by norm_num)

end ArkLib.ProximityGap.FrontalConjugateGate

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.FrontalConjugateGate.sixteen_mul_pow_four_lt
#print axioms ArkLib.ProximityGap.FrontalConjugateGate.two_pow_half_gt_n_pow_four
#print axioms ArkLib.ProximityGap.FrontalConjugateGate.gate_vacuous_at_prize
#print axioms ArkLib.ProximityGap.FrontalConjugateGate.gate_vacuous_n64_r1
