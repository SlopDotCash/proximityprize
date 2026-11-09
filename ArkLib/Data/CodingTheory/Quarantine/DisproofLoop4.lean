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
of the `|L|` evaluation points, so its total agreement set has size `≥ (1 − δ)|L|`. Note that this
lower bound is on the **total** agreement set, which *contains* `V`; containment only gives
`|V| ≤ |agreement|`, so it does **not** by itself force `|V| ≥ (1 − δ)|L|` (a tiny or empty `V`
fits inside a large agreement set). The wall below therefore applies only to those constructions
that **force their common vanishing set itself** to carry the full agreement, i.e. where the
argument needs `|V| ≥ (1 − δ)|L|` (e.g. A3, where `V = L`, and any variant in which the listed
codewords agree with the received word *only* on `V`). For such constructions, below capacity,

    1 − δ ≥ ρ + η   ⟹   |V| ≥ (ρ + η)|L| > ρ|L| = k,

so a polynomial of degree `< k` vanishing on all of `V` must be the zero polynomial (root count):
the construction yields no *nonzero* polynomials of the stated degree. (A negative real "free
dimension" `k − |V|` is only arithmetic bookkeeping; the actual conclusion is the root-count one.)
This file does **not** prove the bridge from the total-agreement bound to `|V|` for A1 or A4 —
that bridge must be supplied separately for each construction — so it does not by itself dispose
of every listed vanishing-polynomial construction.

This file proves that wall as a sorry-free, axiom-clean real-arithmetic lemma. It does **not**
prove the conjecture — it refutes the refutations. See `docs/research/proximity-gap/DISPROOF_LOG.md`.
-/

namespace ArkLib.ProximityGap.DisproofLoop4

open scoped Real

/-- **Below-capacity dimension wall (real form).**

Let the code have rate `ρ` and dimension `k = ρ · n` over an evaluation domain of size `n > 0`.
Suppose the radius is below capacity with gap `η > 0`, i.e. `δ ≤ 1 − ρ − η`, and that a candidate
codeword agrees with the received word on a set of (real) size `agree ≥ (1 − δ) · n` — the minimum
forced by `δ`-closeness. Then the agreement set strictly exceeds the dimension:

    agree > k.

This is pure arithmetic about the number `agree`; the hypothesis `hagree` must be established
separately for whatever set is being bounded. In particular, instantiating `agree` with the size of
a construction's vanishing set `V` requires a proof that `V` itself meets the agreement threshold —
the total-agreement bound of a `δ`-close codeword does not supply this, since it only bounds a
superset of `V`. -/
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

/-- **Free dimension is negative** (arithmetic corollary). Under the same below-capacity
hypotheses, the real quantity `k − agree` is `< 0`. This is bookkeeping only: it is not by itself a
proof that no polynomial exists (the zero polynomial always does); the meaningful consequence is the
root-count one, recorded in `vanishing_set_exceeds_degree_budget`. -/
theorem free_dimension_neg
    (n ρ η δ k agree : ℝ)
    (hn : 0 < n) (hη : 0 < η)
    (hk : k = ρ * n)
    (hδ : δ ≤ 1 - ρ - η)
    (hagree : (1 - δ) * n ≤ agree) :
    k - agree < 0 := by
  have := below_capacity_kills_vanishing_explosion n ρ η δ k agree hn hη hk hδ hagree
  linarith

/-- **Natural-number / degree form.** With integer dimension `k` and a vanishing-set cardinality
`vcard` *assumed* to satisfy `(1 − δ)·n ≤ vcard`, the vanishing set strictly exceeds the degree
budget `k`, so no nonzero degree-`<k` polynomial can vanish on all of it. The hypothesis `hvcard` is
about the vanishing set itself, not the total agreement set; it disqualifies a construction (such as
A3, with `V = L`) only once that construction is shown to force its common vanishing set to meet the
agreement threshold. No such bridge is proved here for A1 (subspace) or A4 (coset). -/
theorem vanishing_set_exceeds_degree_budget
    (n ρ η δ : ℝ) (k vcard : ℕ)
    (hn : 0 < n) (hη : 0 < η)
    (hk : (k : ℝ) = ρ * n)
    (hδ : δ ≤ 1 - ρ - η)
    (hvcard : (1 - δ) * n ≤ (vcard : ℝ)) :
    (k : ℝ) < (vcard : ℝ) :=
  below_capacity_kills_vanishing_explosion n ρ η δ k vcard hn hη hk hδ hvcard

end ArkLib.ProximityGap.DisproofLoop4
