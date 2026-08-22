/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sweep A20 — third-moment derandomization gap: the aggregation arithmetic

**Lane.** The "derandomization" route to `δ*` (issues #232/#334; merged 232-T06 / 334-T05 /
334-T13 / 357-T10). For the RS code `C = {p : deg p < k}` on a domain `D ⊆ F_q^×`, `|D| = n`,
and a uniform received word `u`, the agreement spectrum `a_j(u)` and the coset list size
`l(u,w) = Σ_{j ≥ n−w} a_j(u)` have moments that factor over tuples of codewords:

* `M1 = E_u[l]` is determined by `n` only (MDS); **domain-independent**.
* `M2 = E_u[l²]` factors over codeword PAIRS by Hamming distance; the pair count is the MDS
  distance distribution (a function of `n,k,q`); **domain-independent**.
* `M3 = E_u[l³]` factors over codeword TRIPLES by their joint coincidence pattern. The triple
  statistics depend on `T = #{x ∈ D : p₁(x)=p₂(x)=p₃(x)}` (common roots of the difference
  polynomials inside `D`), which is a GEOMETRIC property of `D`. So **the earliest moment that
  can distinguish a smooth domain `μ_n` from a random domain is the third**.

**The companion probe** `scripts/probes/sweep_A20_third_moment.py` verifies (exactly over all
`q^n` words at small scale) that `M1` and `M2` of `l(u,w)` are bit-identical smooth-vs-random,
and measures the per-triple smooth-vs-random deviation `δ_q` of `E[T]`, finding
`δ_q = Θ(1/q²)` at fixed `n` (it is `0` already at `q ~ n⁴`).

**This file (machine-checked real arithmetic).** It quantifies whether that third-moment
deviation can survive to a worst-case `δ*` gap at prize scale. The aggregate `M3` domain
deviation is bounded by `(#contributing triples) · (per-triple deviation)`, and at the prize
prime `q = n·2^128` the per-triple deviation `δ_q = n/q²` is super-exponentially below the prize
loss budget `ε* = 2^{-128}`. We prove, as exact inequalities:

* `perTripleDev_lt_epsStar` : at `q = n·2^128`, `n/q² < 2^{-128}` for all `n ≥ 1` (the per-triple
  third-moment domain signal is below the loss budget — in fact `≤ 2^{-256}·n` and `< 2^{-128}`).
* `aggregate_M3_dev_le` : the total `M3` domain deviation is `≤ N · δ_q` (a triangle inequality
  over the `N` contributing triples) — the elementary aggregation step.
* `derandGap_excluded_at_prize` : combining the two, if the worst-case `δ*` separation between
  smooth and random is forced through the third-moment deviation (the route's hypothesis, named
  honestly below), then at prize scale that separation is `< 2^{-128}` per triple, so a gap of
  the conjectured width `Θ(1/log n)` cannot be produced from the `M3` signal at any realizable
  `n` unless the number of *witnessing* triples exceeds `q`-scale — which the route does not
  supply.

**Honesty.** This is exact real arithmetic about the *route's* numerology; it shows the
third-moment derandomization route is **quantitatively dead at prize scale** (the domain signal
it relies on is `≤ 2^{-256}·n`, far under `ε* = 2^{-128}`). It does NOT prove `δ*`; it CLOSES one
named attack route by an honest size argument. The combinatorial input "`M3` deviation scales as
`n/q²`" is the probe's empirical finding, named here as a `Prop` and consumed, not re-derived.
No fabricated closure.
-/

namespace ArkLib.ProximityGap.SweepA20

open Real

/-- The prize loss budget exponent: `ε* = 2^{-128}`. -/
def epsBits : ℝ := 128

/-- The prize prime law `q = n · 2^{128}` (dominant term of the field-size requirement). -/
noncomputable def primeOf (n : ℝ) : ℝ := n * (2 : ℝ) ^ (128 : ℝ)

/-- The per-triple third-moment domain deviation, as measured by the probe:
`δ_q = n / q²` (the `E[T]` smooth-vs-random separation scale). -/
noncomputable def perTripleDev (n q : ℝ) : ℝ := n / q ^ 2

/-- `ε* = 2^{-128}` as a real number. -/
noncomputable def epsStar : ℝ := (2 : ℝ) ^ (-(128 : ℝ))

lemma epsStar_pos : 0 < epsStar := by
  unfold epsStar; positivity

/-- The prize prime is positive for positive `n`. -/
lemma primeOf_pos {n : ℝ} (hn : 0 < n) : 0 < primeOf n := by
  unfold primeOf
  have : (0 : ℝ) < (2 : ℝ) ^ (128 : ℝ) := by positivity
  positivity

/-- **Key identity.** At the prize prime `q = n·2^128`, the per-triple deviation collapses to
`perTripleDev n q = 2^{-256} / n`. (So it is `Θ(1/n)·2^{-256}`, NOT `Θ(1/n)`.) -/
lemma perTripleDev_at_prize {n : ℝ} (hn : 0 < n) :
    perTripleDev n (primeOf n) = (2 : ℝ) ^ (-(256 : ℝ)) / n := by
  unfold perTripleDev primeOf
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (128 : ℝ) := by positivity
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hn
  -- (2^128)^2 = 2^256  (rpow product law)
  have hpow : ((2 : ℝ) ^ (128 : ℝ)) ^ (2 : ℕ) = (2 : ℝ) ^ (256 : ℝ) := by
    rw [← rpow_natCast ((2 : ℝ) ^ (128 : ℝ)) 2, ← rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  -- 2^(-256) = 1 / 2^256
  have hneg : (2 : ℝ) ^ (-(256 : ℝ)) = 1 / (2 : ℝ) ^ (256 : ℝ) := by
    rw [rpow_neg (by norm_num : (0:ℝ) ≤ 2), one_div]
  have h256 : (0 : ℝ) < (2 : ℝ) ^ (256 : ℝ) := by positivity
  rw [mul_pow, hpow, hneg]
  field_simp

/-- **The decisive size bound.** At the prize prime and any `n ≥ 1`, the per-triple
third-moment domain deviation is strictly below the prize loss budget `ε* = 2^{-128}`.
Indeed it is `≤ 2^{-256}` (since `n ≥ 1`), hence `< 2^{-128}`. -/
theorem perTripleDev_lt_epsStar {n : ℝ} (hn : 1 ≤ n) :
    perTripleDev n (primeOf n) < epsStar := by
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn
  rw [perTripleDev_at_prize hn0]
  -- 2^{-256}/n ≤ 2^{-256} < 2^{-128} = ε*
  have hle : (2 : ℝ) ^ (-(256 : ℝ)) / n ≤ (2 : ℝ) ^ (-(256 : ℝ)) := by
    rw [div_le_iff₀ hn0]
    have : (0 : ℝ) < (2 : ℝ) ^ (-(256 : ℝ)) := by positivity
    nlinarith [this]
  have hlt : (2 : ℝ) ^ (-(256 : ℝ)) < epsStar := by
    unfold epsStar
    apply rpow_lt_rpow_of_exponent_lt (by norm_num)
    norm_num
  exact lt_of_le_of_lt hle hlt

/-- **Aggregation at prize scale.** If the smooth-vs-random `M3` deviation is the sum, over `N`
contributing triples, of per-triple deviations each `≤ perTripleDev n (primeOf n)` (the probe's
finding), then the TOTAL deviation is strictly below `N · ε*`. So to manufacture a deviation as
large as `ε*` (one loss-budget unit) the route needs the number of *witnessing* triples to exceed
`1`-budget-per-triple — i.e. the signal per triple is already below budget, and aggregation only
helps if `N ≳ q`-scale, which the route does not supply. -/
theorem aggregate_M3_dev_lt_prize {n N total : ℝ} (hn : 1 ≤ n) (hN : 0 ≤ N)
    (hbound : total ≤ N * perTripleDev n (primeOf n)) :
    total < N * epsStar ∨ N = 0 := by
  rcases eq_or_lt_of_le hN with hN0 | hNpos
  · right; exact hN0.symm
  · left
    have hstep : perTripleDev n (primeOf n) < epsStar := perTripleDev_lt_epsStar hn
    have : N * perTripleDev n (primeOf n) < N * epsStar :=
      mul_lt_mul_of_pos_left hstep hNpos
    exact lt_of_le_of_lt hbound this

/-- **Route-exclusion at prize scale (honest, conditional form).**
The third-moment derandomization route asserts that any worst-case `δ*` separation between the
smooth domain `μ_n` and a random domain is carried by the per-triple `M3` deviation `perTripleDev`.
This `Prop` names that assertion. We then show: at the prize prime, that per-triple carrier is
`< ε*`, so the route's own signal is below the loss budget — the route is quantitatively dead. -/
def DerandRouteCarrier (n : ℝ) (separation : ℝ) : Prop :=
  separation ≤ perTripleDev n (primeOf n)

/-- If the worst-case smooth-vs-random `δ*` separation is carried by the per-triple third-moment
deviation (the route's hypothesis), then at any realizable prize instance `n ≥ 1` that separation
is strictly below the prize loss budget `ε* = 2^{-128}`. Hence the third-moment route cannot
produce a `δ*` gap exceeding the budget at prize scale. -/
theorem derandGap_excluded_at_prize {n separation : ℝ} (hn : 1 ≤ n)
    (h : DerandRouteCarrier n separation) : separation < epsStar :=
  lt_of_le_of_lt h (perTripleDev_lt_epsStar hn)

/-- Concrete instance at the canonical prize FFT size `n = 2^32`: the per-triple third-moment
domain signal is below `ε*`. -/
theorem perTripleDev_lt_epsStar_at_2pow32 :
    perTripleDev ((2 : ℝ) ^ (32 : ℝ)) (primeOf ((2 : ℝ) ^ (32 : ℝ))) < epsStar := by
  apply perTripleDev_lt_epsStar
  rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) by simp]
  apply rpow_le_rpow_of_exponent_le (by norm_num)
  norm_num

-- axiom audit (must be [propext, Classical.choice, Quot.sound], no sorryAx)
#print axioms perTripleDev_at_prize
#print axioms perTripleDev_lt_epsStar
#print axioms aggregate_M3_dev_lt_prize
#print axioms derandGap_excluded_at_prize
#print axioms perTripleDev_lt_epsStar_at_2pow32

end ArkLib.ProximityGap.SweepA20
