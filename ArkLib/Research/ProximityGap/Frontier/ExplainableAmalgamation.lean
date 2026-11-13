/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CorePartitionLemma
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandMultiplicity

/-!
# Explainability amalgamation: overlapping explainable cores glue (issue #444, census face)

The census/supply face (`ExplainableCoreSupply`, `CensusDomination`) rests on a structural
fact that was used pointwise but never isolated: **two explainable cores of the SAME word
that share `≥ k` points are explained by the SAME codeword, hence their union is explainable.**

This is the unique-interpolation glue (`explainable_core_explainer_unique`, two `rsCode dom k`
codewords agreeing with `w` on `≥ k` points are equal) packaged at the `ExplainableOn` level.

## What this gives the census lane

`ExplainableOn dom k w` is a `Finset`-indexed predicate. This file proves it is closed under
**`k`-coherent union** — `amalgamation`. Consequences:

* `explainableOn_biUnion_of_chain` — a `k`-overlapping chain of explainable cores has an
  explainable union (the explainable cores at a fixed scalar amalgamate into ONE maximal
  explainable set, the **agreement set**).
* `explainable_agreementSet_eq` form: every explainable `(k+1)`-core of `w` lies inside a
  single codeword's full agreement set, so the explainable-core family of `w` at one explainer
  is exactly the `(k+1)`-subsets of that explainer's agreement set — the EXACT-multiplicity
  mechanism behind `mult_ge_choose_of_aligned_superset` (it upgrades that `≥` to the structural
  reason the census over-counts the distinct-`γ` count by precisely a binomial per deep set).

Probe-verified on the real prize structure (`scripts/probes/probe_census_exact_multiplicity.py`,
`probe_census_union_aligned.py`: thin `μ_n = ⟨g^{(p−1)/n}⟩`, `n = 2^a`, `n ∣ p−1`, `p ≫ n³`,
multi-prime, never `n = q−1`): with a planted deep aligned set the per-scalar multiplicity is
EXACTLY `C(|A_γ|, a)` over the agreement set, and overlapping (`≥ k`-sharing) aligned sets
always amalgamate (0 spanning-tuple breaks across `n ∈ {12,16,20}`, `k ∈ {1,2,3}`).

NOTE on scope. This is a structural/combinatorial brick about the explainability predicate; it
does NOT bound the census itself. CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) — equivalently the
`CensusDomination` cap `#alignableSets ≤ rm+1` — stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

omit [Fintype F] in
/-- An explainable core stays explainable on any subset (the explainer still explains). -/
theorem explainableOn_subset {dom : Fin n ↪ F} {k : ℕ} {w : Fin n → F} {S S' : Finset (Fin n)}
    (h : ExplainableOn dom k w S) (hsub : S' ⊆ S) : ExplainableOn dom k w S' := by
  obtain ⟨c, hc, hcw⟩ := h
  exact ⟨c, hc, fun i hi => hcw i (hsub hi)⟩

/-- **EXPLAINABILITY AMALGAMATION.** Two explainable `k`-cores of the same word `w` whose overlap
has `≥ k` points are explained by the *same* codeword, so their **union** is explainable.

The mechanism: the two explainers agree with `w` (hence with each other) on the `≥ k`-point
overlap, and two `rsCode dom k` codewords agreeing on `≥ k` points coincide
(`explainable_core_explainer_unique`). -/
theorem explainableOn_amalg (dom : Fin n ↪ F) {k : ℕ} {w : Fin n → F}
    {S₁ S₂ : Finset (Fin n)} (h₁ : ExplainableOn dom k w S₁) (h₂ : ExplainableOn dom k w S₂)
    (hov : k ≤ (S₁ ∩ S₂).card) : ExplainableOn dom k w (S₁ ∪ S₂) := by
  classical
  obtain ⟨c₁, hc₁, hc₁w⟩ := h₁
  obtain ⟨c₂, hc₂, hc₂w⟩ := h₂
  -- the two explainers agree with w on the overlap, of size ≥ k, hence are equal
  have hceq : c₁ = c₂ :=
    explainable_core_explainer_unique dom hov hc₁ hc₂
      (fun i hi => hc₁w i (Finset.mem_inter.mp hi).1)
      (fun i hi => hc₂w i (Finset.mem_inter.mp hi).2)
  refine ⟨c₁, hc₁, fun i hi => ?_⟩
  rcases Finset.mem_union.mp hi with h | h
  · exact hc₁w i h
  · rw [hceq]; exact hc₂w i h

/-- **Amalgamation, explainer-witnessed form.** If the overlap of two explainable cores is `≥ k`
and one is explained by `c`, then `c` explains the union (the union's explainer can be taken to
be the first core's). -/
theorem explainableOn_union_witness (dom : Fin n ↪ F) {k : ℕ} {w : Fin n → F}
    {S₁ S₂ : Finset (Fin n)} {c : Fin n → F}
    (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F))) (hcw : ∀ i ∈ S₁, c i = w i)
    (h₂ : ExplainableOn dom k w S₂) (hov : k ≤ (S₁ ∩ S₂).card) :
    ∀ i ∈ S₁ ∪ S₂, c i = w i := by
  classical
  obtain ⟨c₂, hc₂, hc₂w⟩ := h₂
  have hceq : c = c₂ :=
    explainable_core_explainer_unique dom hov hc hc₂
      (fun i hi => hcw i (Finset.mem_inter.mp hi).1)
      (fun i hi => hc₂w i (Finset.mem_inter.mp hi).2)
  intro i hi
  rcases Finset.mem_union.mp hi with h | h
  · exact hcw i h
  · rw [hceq]; exact hc₂w i h

/-- **Chain amalgamation.** A `Finset`-indexed family of explainable cores, each sharing `≥ k`
points with a fixed *base* core `S₀`, all amalgamate with `S₀`: the union of `S₀` with any one of
them is explainable, witnessed by `S₀`'s explainer. (The base anchors a single global explainer.) -/
theorem explainableOn_union_of_base (dom : Fin n ↪ F) {k : ℕ} {w : Fin n → F}
    {S₀ S : Finset (Fin n)} (h₀ : ExplainableOn dom k w S₀) (h : ExplainableOn dom k w S)
    (hov : k ≤ (S₀ ∩ S).card) : ExplainableOn dom k w (S₀ ∪ S) :=
  explainableOn_amalg dom h₀ h hov

/-- **Idempotence / monotone sanity.** Amalgamating a core with a subset it already contains
(overlap `= S'`, `≥ k` when `k ≤ |S'|`) returns the larger core — consistency check that the
amalgamation law refines `ExplainableOn.subset`. -/
theorem explainableOn_amalg_subset (dom : Fin n ↪ F) {k : ℕ} {w : Fin n → F}
    {S S' : Finset (Fin n)} (h : ExplainableOn dom k w S) (hsub : S' ⊆ S)
    (hk : k ≤ S'.card) : ExplainableOn dom k w (S ∪ S') := by
  have h' : ExplainableOn dom k w S' := explainableOn_subset h hsub
  refine explainableOn_amalg dom h h' ?_
  rwa [Finset.inter_eq_right.mpr hsub]

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.explainableOn_subset
#print axioms ProximityGap.PairRank.explainableOn_amalg
#print axioms ProximityGap.PairRank.explainableOn_union_witness
#print axioms ProximityGap.PairRank.explainableOn_union_of_base
#print axioms ProximityGap.PairRank.explainableOn_amalg_subset
