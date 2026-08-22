/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.AlignedAmalgamation

/-!
# The agreement set is the maximal γ-aligned set (issue #444, census face)

`AlignedAmalgamation` showed `γ`-aligned sets glue. This file makes the **agreement set** concrete:
for a degree-`< k` codeword `c` explaining the `γ`-pencil, the set `agreeSet c (γ-pencil)` (the
coordinates where `c` matches the pencil) is

  * itself `γ`-aligned  (`agreeSet_pencil_aligned`), and
  * a SUPERSET of every `γ`-aligned set whose `(k+1)`-tuples `c` explains
    (`aligned_subset_agreeSet_of_explainer`).

So `agreeSet c (γ-pencil)` is the MAXIMAL `γ`-aligned set explained by `c` — the agreement set
`A_γ`.  Consequently the non-degenerate `γ`-aligned `a`-sets explained by `c` are EXACTLY the
non-degenerate `a`-subsets of `A_γ` (`alignedSet_explained_iff_subset_agreeSet`).  This is the
exact-multiplicity mechanism: the census incidence owned by `c` is `#{a-subsets of A_γ with a
non-degenerate tuple}`, a single binomial-controlled quantity, upgrading the in-tree LOWER bound
`CensusScalarPartition.mult_ge_choose_of_aligned_superset` to its structural cause.

Probe (`scripts/probes/probe_census_exact_multiplicity.py`): with a planted deep aligned set the
per-scalar incidence is EXACTLY `C(|A_γ|, a)` (`n=8,k=1,a=3 ⟹ C(5,3)=10`; `k=2,a=4 ⟹ C(6,4)=15`),
thin `μ_n`, `p≫n³`, never `n=q−1`.

NOTE on scope. Structural identity for the per-explainer incidence; does NOT bound the census
over all explainers. CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) = the `CensusDomination` cap, stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

/-- Coordinates where a codeword `c` matches the `γ`-pencil word. -/
noncomputable def agreementSet (dom : Fin n ↪ F) (u₀ u₁ : Fin n → F) (γ : F)
    (c : Fin n → F) : Finset (Fin n) :=
  Finset.univ.filter (fun i => c i = pencil u₀ u₁ γ i)

omit [Fintype F] in
@[simp] theorem mem_agreementSet {dom : Fin n ↪ F} {u₀ u₁ : Fin n → F} {γ : F}
    {c : Fin n → F} {i : Fin n} :
    i ∈ agreementSet dom u₀ u₁ γ c ↔ c i = pencil u₀ u₁ γ i := by
  simp [agreementSet]

/-- **The agreement set is `γ`-aligned.** Where a degree-`< k` codeword `c` matches the
`γ`-pencil, every `(k+1)`-tuple is explained by `c`, so the pencil's residual vanishes there
(`explainableOn_iff_forall_residual`) — i.e. the set is `γ`-aligned. -/
theorem agreeSet_pencil_aligned (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {u₀ u₁ : Fin n → F} {γ : F} {c : Fin n → F}
    (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    Aligned dom k u₀ u₁ γ (agreementSet dom u₀ u₁ γ c) := by
  classical
  rw [aligned_iff_explainableOn_pencil dom hk]
  exact ⟨c, hc, fun i hi => (mem_agreementSet.mp hi)⟩

/-- **Maximality.** Any `γ`-aligned set whose `(k+1)`-tuples are all explained by `c`
(equivalently: `c` matches the pencil on the set) is a subset of the agreement set. The clean
sufficient hypothesis: `c` agrees with the pencil on `S`. -/
theorem aligned_subset_agreementSet_of_agree (dom : Fin n ↪ F)
    {u₀ u₁ : Fin n → F} {γ : F} {c : Fin n → F} {S : Finset (Fin n)}
    (hcS : ∀ i ∈ S, c i = pencil u₀ u₁ γ i) :
    S ⊆ agreementSet dom u₀ u₁ γ c := by
  intro i hi
  rw [mem_agreementSet]
  exact hcS i hi

/-- **The per-explainer census identity (set form).** For a fixed degree-`< k` explainer `c`, a
`γ`-aligned `a`-set is explained by `c` (i.e. `c` matches the pencil on it) **iff** it is an
`a`-subset of the agreement set `agreementSet … c`. So the `γ`-aligned `a`-sets explained by `c`
are EXACTLY the `a`-subsets of `A_γ = agreementSet … c`. -/
theorem aligned_aSet_explained_iff_subset_agreementSet (dom : Fin n ↪ F)
    {u₀ u₁ : Fin n → F} {γ : F} {c : Fin n → F} {a : ℕ} {S : Finset (Fin n)} (hcard : S.card = a) :
    (∀ i ∈ S, c i = pencil u₀ u₁ γ i)
      ↔ (S ⊆ agreementSet dom u₀ u₁ γ c ∧ S.card = a) := by
  constructor
  · intro hcS
    exact ⟨aligned_subset_agreementSet_of_agree dom hcS, hcard⟩
  · rintro ⟨hsub, -⟩ i hi
    exact mem_agreementSet.mp (hsub hi)

open Classical in
/-- **The per-explainer incidence as a binomial-controlled count.** The `a`-subsets of the domain
on which `c` matches the `γ`-pencil are exactly the `a`-subsets of the agreement set, so there are
`C(|A_γ|, a)` of them — the EXACT per-explainer census incidence (before the non-degeneracy
refinement). This pins the multiplicity to a single binomial, the structural reason the census
over-counts the distinct-`γ` count by `Σ (mult − 1)`. -/
theorem agreementSet_aSubset_count (dom : Fin n ↪ F)
    {u₀ u₁ : Fin n → F} {γ : F} {c : Fin n → F} (a : ℕ) :
    ((Finset.univ.powersetCard a).filter
        (fun S : Finset (Fin n) => ∀ i ∈ S, c i = pencil u₀ u₁ γ i)).card
      = (agreementSet dom u₀ u₁ γ c).card.choose a := by
  classical
  have hset : ((Finset.univ.powersetCard a).filter
      (fun S : Finset (Fin n) => ∀ i ∈ S, c i = pencil u₀ u₁ γ i))
      = (agreementSet dom u₀ u₁ γ c).powersetCard a := by
    ext S
    rw [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨-, hcard⟩, hcS⟩
      exact ⟨aligned_subset_agreementSet_of_agree dom hcS, hcard⟩
    · rintro ⟨hsub, hcard⟩
      refine ⟨⟨Finset.subset_univ _, hcard⟩, fun i hi => ?_⟩
      exact mem_agreementSet.mp (hsub hi)
  rw [hset, Finset.card_powersetCard]

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.agreeSet_pencil_aligned
#print axioms ProximityGap.PairRank.aligned_subset_agreementSet_of_agree
#print axioms ProximityGap.PairRank.aligned_aSet_explained_iff_subset_agreementSet
#print axioms ProximityGap.PairRank.agreementSet_aSubset_count
