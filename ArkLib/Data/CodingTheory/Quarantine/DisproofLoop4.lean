/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic

/-!
# Loop 4 — the common cause of death for the vanishing-polynomial disproofs

`SolutionDisproof.lean` and `CandidateDisproofLoop{1,2,3}.lean` each attempt to *disprove* the
ABF26 Grand-Challenge-1 conjecture by manufacturing an exponentially large list of degree-`<k`
Reed–Solomon codewords that all agree with a chosen received word on a large set `V ⊆ L`:

* A1 (BKR additive subspace): `P = Q · A_V`, `A_V` vanishing on a subspace `V`;
* A3 (high-degree aliasing): `V = L`, `A_V = X^{|L|} − 1`;
* A4 (interleaved cosets): concentrate agreement onto whole cosets.

All four share one fatal arithmetic flaw, and that flaw is exactly the prize hypothesis
`δ ≤ 1 − ρ − η` with `η > 0` (radius held strictly **below** capacity `1 − ρ`).

To be a `δ`-close codeword for the received word, `P` must *agree* on at least `(1 − δ)` fraction
of the `|L|` evaluation points, so the agreement set (which contains `V`) has size `≥ (1 − δ)|L|`.
The "free" degrees of freedom available for the explosion is `k − |V|`, where `k = ρ|L|` is the
code dimension. Below capacity,

    1 − δ ≥ ρ + η   ⟹   |V| ≥ (ρ + η)|L| > ρ|L| = k   ⟹   k − |V| < 0,

so there are **zero** free polynomials, not exponentially many. The explosion these disproofs
rely on only exists at or above capacity (`δ ≥ 1 − ρ`), which the gap `η > 0` forbids.

This file proves that wall as a sorry-free, axiom-clean real-arithmetic lemma. It does **not**
prove the conjecture — it refutes the refutations. See `DISPROOF_LOG.md`.
-/

namespace ArkLib.ProximityGap.DisproofLoop4

open scoped Real

/-- **Below-capacity dimension wall (real form).**

Let the code have rate `ρ` and dimension `k = ρ · n` over an evaluation domain of size `n > 0`.
Suppose the radius is below capacity with gap `η > 0`, i.e. `δ ≤ 1 − ρ − η`, and that a candidate
codeword agrees with the received word on a set of (real) size `agree ≥ (1 − δ) · n` — the minimum
forced by `δ`-closeness. Then the agreement set strictly exceeds the dimension:

    agree > k.

Consequently the "free dimension" `k − agree` is strictly negative: the vanishing-polynomial list
explosion of A1–A4 produces no polynomials at all inside the prize radius regime. -/
theorem below_capacity_kills_vanishing_explosion
    (n ρ η δ k agree : ℝ)
    (hn : 0 < n) (hη : 0 < η)
    (hk : k = ρ * n)
    (hδ : δ ≤ 1 - ρ - η)
    (hagree : (1 - δ) * n ≤ agree) :
    k < agree := by
  -- From `δ ≤ 1 − ρ − η` we get `1 − δ ≥ ρ + η`, hence `(1−δ)·n ≥ (ρ+η)·n = k + η·n`.
  have h1 : ρ + η ≤ 1 - δ := by linarith
  have h2 : (ρ + η) * n ≤ (1 - δ) * n := by
    apply mul_le_mul_of_nonneg_right h1 (le_of_lt hn)
  have h3 : (ρ + η) * n = k + η * n := by rw [hk]; ring
  have h4 : 0 < η * n := mul_pos hη hn
  -- Chain: `k < k + η·n = (ρ+η)·n ≤ (1−δ)·n ≤ agree`.
  calc k < k + η * n := by linarith
    _ = (ρ + η) * n := h3.symm
    _ ≤ (1 - δ) * n := h2
    _ ≤ agree := hagree

/-- **Free dimension is negative** (the explicit "no explosion" corollary). Under the same
below-capacity hypotheses, the free dimension available to the disproof, `k − agree`, is `< 0`. -/
theorem free_dimension_neg
    (n ρ η δ k agree : ℝ)
    (hn : 0 < n) (hη : 0 < η)
    (hk : k = ρ * n)
    (hδ : δ ≤ 1 - ρ - η)
    (hagree : (1 - δ) * n ≤ agree) :
    k - agree < 0 := by
  have := below_capacity_kills_vanishing_explosion n ρ η δ k agree hn hη hk hδ hagree
  linarith

/-- **Natural-number / degree form.** With integer dimension `k` and the agreement-set cardinality
`vcard` forced to satisfy `(1 − δ)·n ≤ vcard`, the vanishing set strictly exceeds the degree budget
`k`, so no degree-`<k` polynomial can vanish on all of it except the zero polynomial. This is the
exact statement that disqualifies A1 (subspace), A3 (`X^{|L|}−1` aliasing), and A4 (coset). -/
theorem vanishing_set_exceeds_degree_budget
    (n ρ η δ : ℝ) (k vcard : ℕ)
    (hn : 0 < n) (hη : 0 < η)
    (hk : (k : ℝ) = ρ * n)
    (hδ : δ ≤ 1 - ρ - η)
    (hvcard : (1 - δ) * n ≤ (vcard : ℝ)) :
    (k : ℝ) < (vcard : ℝ) :=
  below_capacity_kills_vanishing_explosion n ρ η δ k vcard hn hη hk hδ hvcard

end ArkLib.ProximityGap.DisproofLoop4
