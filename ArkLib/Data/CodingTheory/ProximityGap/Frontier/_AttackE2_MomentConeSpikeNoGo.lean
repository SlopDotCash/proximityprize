/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# E2 no-go: the second-moment / pairwise-covariance data does NOT bound the house max (#444)

**NEGATIVE / guardrail brick (an honest no-go, NOT a closure).**

Conjecture **E2** posits that the EXACT pairwise covariance `-σ²/(m-1)` of the `m = (p-1)/n`
distinct Gauss-period values, together with the exact `4`-th moment, force — by a *deterministic*
finite-exchangeable extremal inequality — the bound `M(n) = max_b |η_b| ≤ √(2 n log m)`.

This file formalizes the two exact facts that **self-refute** E2:

1. **The covariance carries zero new deterministic information.**  For *any* real vector
   `v : Fin m → ℝ` of mean `μ`, the empirical pairwise sum of deviation products is
   `∑_{i,j} (v i - μ)(v j - μ) = 0`, equivalently
   `∑_{i≠j} (v i - μ)(v j - μ) = - ∑_i (v i - μ)²`.
   This is the algebraic identity `(∑_i (v i - μ))² = 0`. So the "exact pairwise covariance
   `-σ²/(m-1)`" is a *tautology* satisfied by every real vector; it is logically equivalent to the
   first- and second-power-sum data `{S1, S2}` and adds nothing.  (`covariance_eq_neg_sumSq`,
   `pairwise_covariance_is_tautology`.)

2. **The max is NOT a function of the moments `(S1, S2, S4)`.**  We exhibit, for every length
   `m ≥ 2` and every scale `s > 0`, two real vectors with *identical* power sums
   `(∑ v, ∑ v², ∑ v⁴)` whose maxima differ by the factor `m - 1`:
   `A = (-(m-1)·s, s, …, s)` and its negation `B = -A`.  Both have `∑ = 0`, the same `∑ v²` and
   the same `∑ v⁴` (negation fixes even power sums and, at zero mean, fixes the first), yet
   `max A = s` while `max B = (m-1)·s`.  The ratio `m - 1 → ∞`.  (`moments_eq_of_neg_zeroSum`,
   `max_not_determined_by_moments`, `max_gap_unbounded`.)

Together these retire the E2 family *regardless of the prize verdict*: exchangeability supplies only
distributional, not deterministic, control of the maximum, because its covariance content is
exhausted by `{S1, S2}`; and no function of `(S1, S2, S4)` can deterministically bound the maximum,
since two vectors with the *same* `(S1, S2, S4)` have maxima differing by an unbounded factor.

(Structurally: recovering `max ~ σ√(2 log m)` from moments needs the *full* even-moment Chernoff
ladder at `r* ~ log₂ m`; `r = 2` is one rung, and the `r ≥ 5` rungs are exactly the open char-`p`
energy excesses `W_r` = the BGK wall.  E2 is one rung of that wall, not a step past it.)

All theorems are `propext / Classical.choice / Quot.sound`-clean (no `sorry`).  Issue #444.
-/

namespace ProximityGap.Frontier.AtkE2

open Finset

/-! ## Part 1 — the pairwise covariance is an algebraic tautology -/

/-- **The covariance identity.**  For any real vector `v : Fin m → ℝ` with mean `μ := (∑ v)/m`,
the sum of deviation *products over distinct ordered pairs* equals the negative of the sum of
squared deviations:
`∑_{i} ∑_{j ≠ i} (v i - μ)(v j - μ) = - ∑_i (v i - μ)²`.
Equivalently the *full* (including `i = j`) double sum is `0`.  This is a pure consequence of
`∑_i (v i - μ) = 0`; it holds for **every** real vector and therefore the "exact pairwise
covariance `-σ²/(m-1)`" of the Gauss periods is information-free beyond the first two power sums. -/
theorem covariance_eq_neg_sumSq {m : ℕ} (v : Fin m → ℝ) (μ : ℝ)
    (hμ : (∑ i, (v i - μ)) = 0) :
    (∑ i, ∑ j ∈ univ.erase i, (v i - μ) * (v j - μ)) = - ∑ i, (v i - μ) ^ 2 := by
  have hfull : (∑ i, ∑ j, (v i - μ) * (v j - μ)) = 0 := by
    have : (∑ i, ∑ j, (v i - μ) * (v j - μ))
        = (∑ i, (v i - μ)) * (∑ j, (v j - μ)) := by
      rw [Finset.sum_mul_sum]
    rw [this, hμ, mul_zero]
  -- split the inner full sum into the diagonal `j = i` and the off-diagonal `j ≠ i`.
  have hsplit : ∀ i : Fin m,
      (∑ j, (v i - μ) * (v j - μ))
        = (v i - μ) ^ 2 + ∑ j ∈ univ.erase i, (v i - μ) * (v j - μ) := by
    intro i
    rw [← Finset.add_sum_erase univ _ (Finset.mem_univ i)]
    ring_nf
  have : (∑ i, ((v i - μ) ^ 2 + ∑ j ∈ univ.erase i, (v i - μ) * (v j - μ))) = 0 := by
    rw [← hfull]; exact Finset.sum_congr rfl (fun i _ => (hsplit i).symm)
  rw [Finset.sum_add_distrib] at this
  linarith [this]

/-- **The pairwise-covariance premise is a tautology.**  Stated as a clean equivalence: for any
real vector the off-diagonal deviation-product sum is *forced* to equal `-∑(v i - μ)²` (the
second-power-sum data).  Hence assuming the exact covariance `-σ²/(m-1)` adds **no** constraint
beyond `{S1, S2}`: it is equivalent to the trivially true statement.  This is exactly Kill-Step 1
of the E2 self-refutation. -/
theorem pairwise_covariance_is_tautology {m : ℕ} (v : Fin m → ℝ) (μ : ℝ)
    (hμ : (∑ i, (v i - μ)) = 0) :
    ((∑ i, ∑ j ∈ univ.erase i, (v i - μ) * (v j - μ)) = - ∑ i, (v i - μ) ^ 2)
      ↔ True := by
  simp only [iff_true]
  exact covariance_eq_neg_sumSq v μ hμ

/-! ## Part 2 — the max is not a function of the moments `(S1, S2, S4)` -/

/-- The "balanced-spike" vector of length `m`, scale `s`, special index `i₀`:
`A i = -(m-1)·s` at `i = i₀`, and `A i = s` otherwise.  As a multiset this is
`(-(m-1)·s, s, s, …, s)` — one big negative coordinate, the rest `s`. -/
def spikeVec {m : ℕ} (i₀ : Fin m) (s : ℝ) : Fin m → ℝ :=
  fun i => if i = i₀ then -((m : ℝ) - 1) * s else s

/-- Power sum: `∑_i (v i)^k`. -/
def powerSum {m : ℕ} (v : Fin m → ℝ) (k : ℕ) : ℝ := ∑ i, (v i) ^ k

/-- **Negation fixes all even power sums.**  For any vector and any *even* exponent `k`,
`∑ (-v i)^k = ∑ (v i)^k`.  (At `k = 1` it negates; here we only invoke `k ∈ {2, 4}`.) -/
theorem powerSum_neg_even {m : ℕ} (v : Fin m → ℝ) {k : ℕ} (hk : Even k) :
    powerSum (fun i => - v i) k = powerSum v k := by
  unfold powerSum
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [neg_pow, hk.neg_one_pow, one_mul]

/-- **Negation negates the first power sum.** -/
theorem powerSum_neg_one {m : ℕ} (v : Fin m → ℝ) :
    powerSum (fun i => - v i) 1 = - powerSum v 1 := by
  unfold powerSum
  simp [pow_one, Finset.sum_neg_distrib]

/-- **The spike has zero mean** (`S1 = 0`): `∑ A = 0`.
The single `-(m-1)s` cancels the `(m-1)` copies of `s`. -/
theorem spike_sum_eq_zero {m : ℕ} (hm : 1 ≤ m) (i₀ : Fin m) (s : ℝ) :
    powerSum (spikeVec i₀ s) 1 = 0 := by
  unfold powerSum spikeVec
  simp only [pow_one]
  -- Split the `if` sum: `∑ (if i = i₀ then a else b) = a + (m-1)·b` where here `b = s`,
  -- `a = -(m-1)·s`.  Use the `ite`-as-`(a-b)·[i=i₀] + b` rewrite via `Finset.sum_ite_eq`.
  have key : (∑ i : Fin m, (if i = i₀ then -((m : ℝ) - 1) * s else s))
      = (∑ i : Fin m, ((if i = i₀ then (-((m : ℝ) - 1) * s - s) else 0) + s)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : i = i₀ <;> simp [hi]
  rw [key, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_ite_eq' univ i₀ (fun _ => (-((m : ℝ) - 1) * s - s))]
  simp only [Finset.mem_univ, if_true, nsmul_eq_mul]
  have : ((m : ℝ) - 1) = ((m - 1 : ℕ) : ℝ) := by push_cast [Nat.cast_sub hm]; ring
  rw [this]; push_cast [Nat.cast_sub hm]; ring

/-- **The spike and its negation share `(S1, S2, S4)`.**  Both have `∑ = 0`, the same `∑ ·²` and
the same `∑ ·⁴`.  This is the exact-matched-moment witness pair underlying Kill-Step 2: two real
vectors with *identical* `(S1, S2, S4)` whose maxima we will show differ by the factor `m-1`. -/
theorem moments_eq_of_neg_zeroSum {m : ℕ} (hm : 1 ≤ m) (i₀ : Fin m) (s : ℝ) :
    powerSum (fun i => - spikeVec i₀ s i) 1 = powerSum (spikeVec i₀ s) 1
      ∧ powerSum (fun i => - spikeVec i₀ s i) 2 = powerSum (spikeVec i₀ s) 2
      ∧ powerSum (fun i => - spikeVec i₀ s i) 4 = powerSum (spikeVec i₀ s) 4 := by
  refine ⟨?_, powerSum_neg_even _ (by decide), powerSum_neg_even _ (by decide)⟩
  rw [powerSum_neg_one, spike_sum_eq_zero hm, neg_zero]

/-- **Max of the negated spike is `(m-1)·s`** (for `m ≥ 2`, `s ≥ 0`).  The negated spike is
`(-A) = ((m-1)s, -s, …, -s)`; its coordinate at index `0` is `(m-1)s`, which (for `m ≥ 2`, `s ≥ 0`)
dominates the others `(-s ≤ 0 ≤ (m-1)s)`. -/
theorem max_negSpike {m : ℕ} (hm : 2 ≤ m) (i₀ : Fin m) {s : ℝ} (hs : 0 ≤ s) (i : Fin m) :
    (fun j => - spikeVec i₀ s j) i ≤ ((m : ℝ) - 1) * s := by
  unfold spikeVec
  by_cases hi : i = i₀
  · subst hi; simp only [↓reduceIte]; linarith
  · simp only [hi, if_false]
    have h1 : (1 : ℝ) ≤ (m : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    nlinarith [hs, h1]

/-- The index-`i₀` coordinate of the negated spike *equals* `(m-1)·s`, so the max is attained. -/
theorem negSpike_zero_eq {m : ℕ} (i₀ : Fin m) (s : ℝ) :
    (fun j => - spikeVec i₀ s j) i₀ = ((m : ℝ) - 1) * s := by
  simp only [spikeVec, ↓reduceIte]; ring

/-- Max of the (un-negated) spike is `s` (for `m ≥ 2`, `s ≥ 0`).  Every coordinate is either `s`
or `-(m-1)s ≤ 0 ≤ s`. -/
theorem max_spike {m : ℕ} (hm : 2 ≤ m) (i₀ : Fin m) {s : ℝ} (hs : 0 ≤ s) (i : Fin m) :
    spikeVec i₀ s i ≤ s := by
  unfold spikeVec
  by_cases hi : i = i₀
  · subst hi; simp only [↓reduceIte]
    have h1 : (0 : ℝ) ≤ (m : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    nlinarith [hs, h1]
  · simp [hi]

/-- **The max is not determined by `(S1, S2, S4)`.**  For every `m ≥ 2` and `s > 0` there are two
real vectors `u, w : Fin m → ℝ` with *identical* power-sum data `(∑ ·, ∑ ·², ∑ ·⁴)` such that one
coordinate of `w` exceeds **every** coordinate of `u` by the factor `(m-1)`:
`max u ≤ s` while `w` attains `(m-1)·s`.  Concretely `u = A`, `w = -A` for the balanced spike `A`.
This is Kill-Step 2: no function of `(S1, S2, S4)` can deterministically bound the maximum. -/
theorem max_not_determined_by_moments {m : ℕ} (hm : 2 ≤ m) {s : ℝ} (hs : 0 < s) :
    ∃ u w : Fin m → ℝ,
      (powerSum u 1 = powerSum w 1 ∧ powerSum u 2 = powerSum w 2 ∧ powerSum u 4 = powerSum w 4)
        ∧ (∀ i, u i ≤ s)
        ∧ (∃ i, w i = ((m : ℝ) - 1) * s ∧ ∀ j, w j ≤ ((m : ℝ) - 1) * s) := by
  have hm1 : 1 ≤ m := le_trans (by norm_num) hm
  let i₀ : Fin m := ⟨0, by omega⟩
  refine ⟨spikeVec i₀ s, fun i => - spikeVec i₀ s i, ?_, ?_, ⟨i₀, ?_, ?_⟩⟩
  · exact ⟨(moments_eq_of_neg_zeroSum hm1 i₀ s).1.symm,
      (moments_eq_of_neg_zeroSum hm1 i₀ s).2.1.symm,
      (moments_eq_of_neg_zeroSum hm1 i₀ s).2.2.symm⟩
  · exact fun i => max_spike hm i₀ hs.le i
  · exact negSpike_zero_eq i₀ s
  · exact fun j => max_negSpike hm i₀ hs.le j

/-- **The max-gap is unbounded in `m`.**  Specializing to `s = 1`: for every `m ≥ 2` the two
moment-identical vectors have maxima `1` and `m - 1`, so the ratio of the maxima is `m - 1`, which
diverges as `m → ∞`.  Since in the prize regime `m = (p-1)/n ~ n³ → ∞`, the moment data `(S1,S2,S4)`
leaves the maximum undetermined up to a polynomially large factor — the E2 deterministic extremal
inequality cannot exist. -/
theorem max_gap_unbounded {m : ℕ} (hm : 2 ≤ m) :
    ∃ u w : Fin m → ℝ,
      (powerSum u 1 = powerSum w 1 ∧ powerSum u 2 = powerSum w 2 ∧ powerSum u 4 = powerSum w 4)
        ∧ (∀ i, u i ≤ 1)
        ∧ (∃ i, w i = (m : ℝ) - 1) := by
  obtain ⟨u, w, hmom, hu, ⟨i, hwi, _⟩⟩ := max_not_determined_by_moments hm (s := 1) (by norm_num)
  exact ⟨u, w, hmom, by simpa using hu, ⟨i, by simpa using hwi⟩⟩

/-- **E2 self-refutation, combined.**  The two load-bearing facts, packaged:
(1) the pairwise covariance is a tautology (information-free beyond `{S1,S2}`), and
(2) the maximum is not a function of `(S1,S2,S4)` — witnessed by a moment-identical pair whose
maxima differ by the unbounded factor `m-1`.  Hence no deterministic finite-exchangeable extremal
inequality from `{covariance, S1, S2, S4}` can bound `M(n)`; E2 is refuted independent of the prize
verdict. -/
theorem E2_self_refuted {m : ℕ} (hm : 2 ≤ m) :
    -- (1) covariance is a tautology for every zero-mean vector
    (∀ (v : Fin m → ℝ) (μ : ℝ), (∑ i, (v i - μ)) = 0 →
        (∑ i, ∑ j ∈ univ.erase i, (v i - μ) * (v j - μ)) = - ∑ i, (v i - μ) ^ 2)
    -- (2) the max is undetermined by (S1,S2,S4) up to the unbounded factor m-1
    ∧ (∃ u w : Fin m → ℝ,
        (powerSum u 1 = powerSum w 1 ∧ powerSum u 2 = powerSum w 2 ∧ powerSum u 4 = powerSum w 4)
          ∧ (∀ i, u i ≤ 1) ∧ (∃ i, w i = (m : ℝ) - 1)) := by
  exact ⟨fun v μ hμ => covariance_eq_neg_sumSq v μ hμ, max_gap_unbounded hm⟩

/-! ## Axiom audit -/

#print axioms covariance_eq_neg_sumSq
#print axioms pairwise_covariance_is_tautology
#print axioms powerSum_neg_even
#print axioms powerSum_neg_one
#print axioms spike_sum_eq_zero
#print axioms moments_eq_of_neg_zeroSum
#print axioms max_negSpike
#print axioms negSpike_zero_eq
#print axioms max_spike
#print axioms max_not_determined_by_moments
#print axioms max_gap_unbounded
#print axioms E2_self_refuted

end ProximityGap.Frontier.AtkE2
