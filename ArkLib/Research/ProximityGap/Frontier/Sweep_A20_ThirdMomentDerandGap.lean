/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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

* `M1 = E_u[l]` is determined by the code size `q^k` and the Hamming-ball volume (a function of
  `n,k,q,w`, MDS); **domain-independent**.
* `M2 = E_u[l²]` factors over codeword PAIRS by Hamming distance; the pair count is the MDS
  distance distribution (a function of `n,k,q`); **domain-independent**.
* `M3 = E_u[l³]` factors over codeword TRIPLES by their joint coincidence pattern. Individual
  triple patterns involve `T = #{x ∈ D : p₁(x)=p₂(x)=p₃(x)}` (common roots of the difference
  polynomials inside `D`), which can depend on `D`. So the third moment is the first moment at
  which a domain dependence is *possible*; nothing here proves that it is present.

**Caveat: the uniform mean of `T` carries no domain signal.** For independent uniformly chosen
codewords `p₁,p₂,p₃` of degree `< k` with `k ≥ 1`, each evaluation `pᵢ(x)` is uniform in
`F_q` at every domain point `x`, so `Pr[p₁(x)=p₂(x)=p₃(x)] = 1/q²` and by linearity
`E[T] = n/q²` EXACTLY, for every domain `D` of size `n`. The scalar `n/q²` is therefore the
domain-independent value of that mean, not a smooth-vs-random deviation. Any genuine domain
signal must come from a different statistic (richer triple coincidence patterns, or a
conditioned triple population), whose sampling/conditioning definition is not stated or
formalized here.

**The companion probe** `scripts/probes/sweep_A20_third_moment.py` verifies (exactly over all
`q^n` words at small scale) that `M1` and `M2` of `l(u,w)` are bit-identical smooth-vs-random,
and reports a measured smooth-vs-random quantity `δ_q` on the `n/q²` scale at fixed `n`. By the
caveat above this cannot be a deviation of the uniform mean `E[T]`; its precise conditioned
definition would have to be stated before it is used as a signal.

**This file (machine-checked real arithmetic).** It records the scale of the scalar
`perTripleDev n q = n/q²` at the prize prime `q = n·2^128`, where it is far below the prize loss
budget `ε* = 2^{-128}`. We prove, as exact inequalities:

* `perTripleDev_lt_epsStar` : at `q = n·2^128`, `n/q² = 2^{-256}/n < 2^{-128}` for all `n ≥ 1`.
* `aggregate_M3_dev_lt_prize` : IF a total is bounded by `N · perTripleDev`, THEN it is
  `< N · ε*` (or `N = 0`). This is a bound by `N · ε*`, NOT by `ε*`; no bound on the number
  `N` (or the weights) of contributing triples is proved, and there can be vastly more than `q`
  codeword triples (there are `q^{3k}`).
* `derandGap_excluded_at_prize` : IF the worst-case `δ*` separation is at most the single
  per-triple scalar `perTripleDev` (the entered `DerandRouteCarrier` hypothesis), THEN it is
  `< ε*`. This is transitivity through that strong entered hypothesis.

**Honesty / scope.** This is exact real arithmetic. It does NOT show that third-moment
derandomization is quantitatively dead: no third-moment-to-worst-case stability (threshold
transfer) theorem, no aggregate bound on the number or weight of contributing triples, and no
derivation of `DerandRouteCarrier` from actual RS quantities is proved or encoded, and comparing
a radius separation with a bad-probability budget would itself require such a bridge. The
route verdict is therefore limited to the conditional statement above. It does NOT prove `δ*`.
-/

namespace ArkLib.ProximityGap.SweepA20

open Real

/-- The prize loss budget exponent: `ε* = 2^{-128}`. -/
def epsBits : ℝ := 128

/-- The prize prime law `q = n · 2^{128}` (dominant term of the field-size requirement). -/
noncomputable def primeOf (n : ℝ) : ℝ := n * (2 : ℝ) ^ (128 : ℝ)

/-- The scalar `n / q²`. Under independent uniform codewords this is the EXACT,
domain-independent mean `E[T]` of the triple common-root count for every domain of size `n`; it
is not itself a smooth-vs-random separation. It is used here only as the per-triple scale that
the entered `DerandRouteCarrier` hypothesis refers to. -/
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

/-- **Scalar size bound.** At the prize prime and any `n ≥ 1`, the scalar
`perTripleDev n q = n/q²` is strictly below the prize loss budget `ε* = 2^{-128}`.
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

/-- **Aggregation arithmetic (conditional).** If a total is bounded by `N` times the scalar
`perTripleDev n (primeOf n)` (an entered hypothesis `hbound`), then the total is strictly below
`N · ε*` (or `N = 0`). The conclusion is a bound by `N · ε*`, not by `ε*`: no bound on the
number or weight `N` of contributing triples is proved here, and the number of codeword triples
(`q^{3k}`) can vastly exceed `q`, so this lemma alone does not cap the aggregate below `ε*`. -/
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

/-- **Entered carrier hypothesis (strong, not derived).**
`DerandRouteCarrier n separation` asserts that the given worst-case separation is at most the
single per-triple scalar `perTripleDev n (primeOf n)`. This is a very strong normalization: it
is neither proved nor derived from actual RS quantities here, and no third-moment-to-worst-case
stability theorem or aggregate triple-count bound supports it. Consequences drawn from it are
conditional on it and do not exclude the third-moment derandomization method as a whole. -/
def DerandRouteCarrier (n : ℝ) (separation : ℝ) : Prop :=
  separation ≤ perTripleDev n (primeOf n)

/-- Transitivity consequence of the entered carrier hypothesis: IF the separation is at most
`perTripleDev n (primeOf n)` (`DerandRouteCarrier`), THEN for `n ≥ 1` it is strictly below
`ε* = 2^{-128}`. This is only as strong as that entered hypothesis; it is not a method-wide
exclusion of third-moment derandomization. -/
theorem derandGap_excluded_at_prize {n separation : ℝ} (hn : 1 ≤ n)
    (h : DerandRouteCarrier n separation) : separation < epsStar :=
  lt_of_le_of_lt h (perTripleDev_lt_epsStar hn)

/-- Concrete instance at the canonical prize FFT size `n = 2^32`: the scalar `n/q²` at
`q = n·2^128` is below `ε*`. -/
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
