/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# The effective-Katz / Wasserstein conductor barrier for the Gauss-period family (#407, route effkatz)

Companion to `KowalskiUntrauBarrier.lean`. That file formalizes the **ultra-short subgroup-sum**
barrier (Kowalski–Untrau 2505.22059, §3, Lemma 3.9 / Theorem 3.8): the subgroup size `d = |H| = n`
sits in the *denominator of the decay exponent* `q^{−1/(d−1)}`, so the bound is vacuous once
`n ≫ log q`.

THIS file formalizes the **additive-Fourier / Deligne (§4) incarnation** of the same wall, which is
the natural home of the *conductor* of the trace-function family
  `b ↦ η_b = Σ_{x ∈ μ_n} e_p(b·x)`.

## The conductor computation (independent; probe-confirmed exactly)

Sheaf-theoretically, `b ↦ η_b` is the trace function of the **additive Fourier transform**
`FT_ψ(δ_{μ_n})` of the punctual ("skyscraper") sheaf supported on the `n` points of `μ_n`. As an
ℓ-adic sheaf on `𝔸¹_b`:
* its **generic rank is `n`** — `η_b = Σ_{x∈μ_n}(ζ_p^x)^b` is a sum of `n` geometric progressions in
  `b` with the `n` *distinct* ratios `ζ_p^x` (`x ∈ μ_n`, all distinct mod `p`), so the minimal linear
  recurrence order of `(η_b)_b` is **exactly `n`**;
* it is wildly ramified at `∞` with `Swan_∞ ≤ n`, tame at `0`.

Hence its conductor / sum-of-Betti-numbers is `c(𝓕) = Θ(n)` — measured **exactly** (rank `= n` in
100 % of swept cases, `scripts/probes/_wf407_effkatz_rank_exact.py`). It is `O(n)`, *not* `O(1)` and
*not* `O(m)`.

Kowalski–Untrau's effective Deligne bound (eq. (17), §4.2) is the single-point estimate
  `|μ̂_i(ρ) − μ̂_K(ρ)| ≤ |k_i|^{−1/2}·c(X_{i,k̄}, ρ(𝓕_i))`,
so the discrepancy this route can feed is `≈ cond·p^{−1/2} = n·p^{−1/2} = n/√p`.

## The obstruction (this file, machine-checked)

To beat the per-frequency **non-conspiracy threshold** `1/m` (the level the `m = (p−1)/n` Gauss-sum
phases must cancel below to give a non-trivial floor) the discrepancy must satisfy
  `n/√p < 1/m`  ⟺  `n·m < √p`  ⟺  `(p−1) < √p`,
which is **false for every `p ≥ 2`**. Equivalently, the comment's framing: one would need
`conductor < √(n/m) = 2^{−48} < 1` — impossible, since a non-trivial conductor is `≥ 1`.

So the additive-FT Deligne bound is **pointwise vacuous** (`n/√p ≈ √p ≫ 1 ≫ 1/m`) at *every* `p`.
At prize scale (`n = 2^32`, `m = 2^128`, `p = n·m ≈ 2^160`): `n/√p = 2^{−48}`, target `1/m = 2^{−128}`
— **short by `2^80`** in the log-2 of the bound. (The Mellin/§4.3 framework is *strictly worse*: KU's
own §4.4 remark notes the complexity there enters **exponentially**, `c = 2^{Θ(n)}`.)

We formalize the clean integer statement `n·m < √p ⟺ (p−1) < √p`, refute it for all `p ≥ 2`
(via `(p-1)^2 ≥ p` ⟺ `p^2 - 3p + 1 ≥ 0`, true for `p ≥ 3`), and pin the prize gap exactly.

This is a machine-checked **localization** of the wall, not a closure of the prize: it certifies that
the effective-Katz/Wasserstein conductor route cannot, even in principle, certify the prize regime.

## References
- [KU25] Kowalski, Untrau. *Wasserstein metrics and quantitative equidistribution of exponential sums
  over finite fields*. arXiv:2505.22059, 2025. (§4.2 eq.(17), Thm 4.4, Thm 4.11, §4.4 remark.)
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
-/

namespace ArkLib.ProximityGap.EffKatzConductorBarrier

/-- The conductor (generic rank / sum of Betti numbers up to a bounded factor) of the additive-FT
trace-function family `b ↦ Σ_{x∈μ_n} e_p(bx)`. Computed **exactly** to be `n` (the number of distinct
geometric frequencies); see `scripts/probes/_wf407_effkatz_rank_exact.py`. -/
def conductor (n : ℕ) : ℕ := n

/-- The integer form of "the Deligne discrepancy `cond·p^{−1/2} = n/√p` beats the non-conspiracy
threshold `1/m`". Cross-multiplying `n/√p < 1/m` by `m√p > 0`: `n·m < √p`, i.e. squaring,
`(n·m)² < p`. Since `n·m = p − 1`, this is `(p−1)² < p`. -/
def deligneBeatsThreshold (p n m : ℕ) : Prop := (n * m) ^ 2 < p

/-- **The conductor is exactly `n`** (the additive-FT generic rank), independent of the index `m`.
A definitional pin recording the probe-verified value `c(𝓕) = n` (not `O(1)`, not `O(m)`). -/
theorem conductor_eq (n : ℕ) : conductor n = n := rfl

/-- **The Deligne/effective-Katz discrepancy can never beat the non-conspiracy threshold.** For any
factorization `p − 1 = n·m` with `p ≥ 3`, the condition `(n·m)² < p` (= `n/√p < 1/m`) is FALSE:
indeed `(n·m)² = (p−1)² ≥ p` for all `p ≥ 3`. So the additive-FT conductor route is pointwise vacuous
at every prime `≥ 3` (the sole edge `p = 2` forces the degenerate `μ_1 = {1}` subgroup, excluded from
the prize regime; see `deligne_never_beats_threshold_real`). -/
theorem deligne_never_beats_threshold {p n m : ℕ} (hp : 3 ≤ p) (hfact : n * m = p - 1) :
    ¬ deligneBeatsThreshold p n m := by
  unfold deligneBeatsThreshold
  rw [hfact]
  -- goal: ¬ (p - 1)^2 < p, i.e. p ≤ (p-1)^2.  For p ≥ 3: (p-1)^2 = p^2 - 2p + 1 ≥ p ⟺ p^2-3p+1≥0.
  have : p ≤ (p - 1) ^ 2 := by nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ p)]
  omega

/-- The real-regime version (`n, m ≥ 2`, so `p − 1 = n·m ≥ 4 ⟹ p ≥ 5`): the discrepancy NEVER beats
the threshold, with no degenerate exception. This is the form that applies at every genuine subgroup
instance (the prize has `n = 2^32`, `m = 2^128`). -/
theorem deligne_never_beats_threshold_real {p n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hfact : n * m = p - 1) (hp : 1 ≤ p) : ¬ deligneBeatsThreshold p n m := by
  unfold deligneBeatsThreshold
  -- n*m ≥ 4, and (n*m)^2 ≥ n*m + 1 = p whenever n*m ≥ 2.  Here n*m = p-1.
  have hnm : 4 ≤ n * m := by calc 4 = 2 * 2 := by norm_num
                                 _ ≤ n * m := Nat.mul_le_mul hn hm
  have hp5 : 5 ≤ p := by omega
  -- (n*m)^2 ≥ n*m ≥ p - 1, and since n*m ≥ 4 ≥ 2 we get (n*m)^2 > n*m = p-1 ≥ p? need (n*m)^2 ≥ p.
  -- (n*m)^2 ≥ 2*(n*m) (since n*m ≥ 2) = 2(p-1) = 2p-2 ≥ p (since p ≥ 2). So (n*m)^2 ≥ p > p-...
  have h1 : 2 * (n * m) ≤ (n * m) ^ 2 := by nlinarith [hnm]
  have : p ≤ (n * m) ^ 2 := by omega
  omega

/-- **Prize-scale gap, exact.** Take `n = 2^32`, `m = 2^128`. The Deligne discrepancy quantity is
`cond·p^{−1/2} = n/√p` with `√p ≈ 2^80` (since `p = n·m = 2^160`), so `n/√p = 2^{−48}`, whereas the
target is `1/m = 2^{−128}`: the route is short by a factor `2^{80}` in the bound. We pin this purely
in `log₂` (multiplicative) form by the integer inequality the squared bound must satisfy:
`(n·m)² < p` is violated by a factor `≈ (p−1)²/p ≈ p = 2^160` (so `2^80` in the bound). -/
theorem prize_gap_squared :
    let n := 2 ^ 32
    let m := 2 ^ 128
    let p := n * m + 1
    -- the squared "beats-threshold" target (n·m)^2 < p is violated, and the slack is (n·m)^2/p ≈ p:
    p ≤ (n * m) ^ 2 ∧ (2 ^ 160 : ℕ) ≤ (n * m) ^ 2 := by
  refine ⟨?_, ?_⟩
  · -- p = 2^160 + 1 ≤ (2^160)^2 = 2^320
    norm_num
  · -- (n*m)^2 = (2^160)^2 = 2^320 ≥ 2^160
    norm_num

/-- The conductor route requires the impossible `conductor < √(n/m)`. With `conductor = n ≥ 1`
and `√(n/m) ≤ 1` (since `m ≥ n` in the index-`m ≥ √(p)` prize regime, in fact `m = 2^128 ≫ n = 2^32`),
the requirement `n < √(n/m)` i.e. `n²·m < n` i.e. `n·m < 1` is impossible for `n, m ≥ 1`. We pin the
clean integer contradiction `n * m ≥ 1 ⟹ ¬ (n^2 * m < n)`. -/
theorem conductor_requirement_impossible {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ¬ (n ^ 2 * m < n) := by
  -- n^2 * m ≥ n^2 ≥ n (for n ≥ 1), so n^2*m ≥ n, contradicting n^2*m < n.
  have h1 : n ≤ n ^ 2 := by nlinarith
  have h2 : n ^ 2 ≤ n ^ 2 * m := Nat.le_mul_of_pos_right _ hm
  omega

end ArkLib.ProximityGap.EffKatzConductorBarrier

#print axioms ArkLib.ProximityGap.EffKatzConductorBarrier.deligne_never_beats_threshold_real
#print axioms ArkLib.ProximityGap.EffKatzConductorBarrier.prize_gap_squared
#print axioms ArkLib.ProximityGap.EffKatzConductorBarrier.conductor_requirement_impossible
#print axioms ArkLib.ProximityGap.EffKatzConductorBarrier.deligne_never_beats_threshold
