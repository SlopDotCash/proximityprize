/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CorePartitionLemma
import ArkLib.Data.CodingTheory.ProximityGap.PopularCodewords
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandMultiplicity
import Mathlib.LinearAlgebra.Lagrange

/-!
# The moment–supply identity: the supply IS the degenerate-set count (#389)

The word-coupled dictionary for the sub-Johnson wall, in exact identity form.  For a
word `w`, codewords `c` of `rsCode dom k`, agreement sets `A_c = agreeSet c w`, and any
`j ≥ k`:

> **`moment_supply_identity`** —
> `Σ_c C(|A_c|, j) = N_j(w) := #{ j-subsets S of the domain : ExplainableOn dom k w S }`
>
> an IDENTITY, not a bound: every degenerate `j`-set has a UNIQUE explaining codeword
> (`explainable_core_explainer_unique`, `j ≥ k`), so the pairs `(c, S ⊆ A_c)` partition.

Consequences landed here:

* **`moment_identity_base`** (`j = k`) — `Σ_c C(|A_c|, k) = C(n, k)`: EVERY `k`-set is
  degenerate (Lagrange interpolation through the `k` graph points), the exact pencil
  partition of all `k`-sets.  This is the set-system-tight quadratic layer in identity
  form: the pair statistic is frozen at `C(n,k)` regardless of `w`.
* **`explainableCoreSupply_iff_moment`** — the issue's named residual
  `ExplainableCoreSupply dom k m B` is EQUIVALENT to the uniform `(k+m+1)`-moment bound
  `∀ w, Σ_c C(|A_c|, k+m+1) ≤ B`: the charter quantity is literally the `t`-th moment
  of the agreement spectrum.
* **`rich_count_mul_le_moment`** — the moment consumer: `#{c : |A_c| ≥ t}·C(t,j) ≤ N_j`.

The first genuinely word-coupled statistic is `N_{k+1}(w)` (collinear triples of the
graph at `k = 2`): `N_k` is frozen, every `N_j`, `j > k` depends on `w`.  The shallow
target (census `10253d151`: size-weighted supply linear while mass is quadratic) is now
formally: bound `N_t(w)` for capped words below the Johnson line.  Probe:
`scripts/probes/probe_affine_sharpness_triple_moment.py` (section B, identity exact at
`(q,k) ∈ {(11,2),(13,2),(11,3)}`, all `j ∈ [k, k+2]`).  Issue #389.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- The finset of codewords of `rsCode dom k`. -/
noncomputable def codewordFinset (dom : Fin n ↪ F) (k : ℕ) : Finset (Fin n → F) :=
  Finset.univ.filter (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F)))

open Classical in
lemma mem_codewordFinset {dom : Fin n ↪ F} {k : ℕ} {c : Fin n → F} :
    c ∈ codewordFinset dom k ↔ c ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
  simp only [codewordFinset, Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in
/-- The degenerate `j`-sets of `w`: `j`-subsets of the domain on which `w` collapses to
a codeword.  At `j = k + m + 1` this is the explainable-core family of the issue's
`ExplainableCoreSupply`. -/
noncomputable def degenerateSets (dom : Fin n ↪ F) (k j : ℕ) (w : Fin n → F) :
    Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)).powersetCard j).filter
    (fun S => ExplainableOn dom k w S)

open Classical in
lemma mem_degenerateSets {dom : Fin n ↪ F} {k j : ℕ} {w : Fin n → F}
    {S : Finset (Fin n)} :
    S ∈ degenerateSets dom k j w ↔ S.card = j ∧ ExplainableOn dom k w S := by
  simp only [degenerateSets, Finset.mem_filter, Finset.mem_powersetCard,
    Finset.subset_univ, true_and]

open Classical in
/-- **THE MOMENT–SUPPLY IDENTITY**: for `j ≥ k`, the `j`-th binomial moment of the
agreement spectrum equals the degenerate-`j`-set count — exactly. -/
theorem moment_supply_identity (dom : Fin n ↪ F) {k j : ℕ} (hkj : k ≤ j)
    (w : Fin n → F) :
    ∑ c ∈ codewordFinset dom k, ((agreeSet c w).card.choose j)
      = (degenerateSets dom k j w).card := by
  classical
  have hdisj : ∀ c ∈ codewordFinset dom k, ∀ c' ∈ codewordFinset dom k, c ≠ c' →
      Disjoint ((agreeSet c w).powersetCard j) ((agreeSet c' w).powersetCard j) := by
    intro c hc c' hc' hne
    rw [Finset.disjoint_left]
    intro S hS hS'
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
    obtain ⟨hsub', -⟩ := Finset.mem_powersetCard.mp hS'
    refine hne (explainable_core_explainer_unique dom (w := w)
      (by omega : k ≤ S.card)
      (mem_codewordFinset.mp hc) (mem_codewordFinset.mp hc') ?_ ?_)
    · intro i hi
      have := hsub hi
      rw [agreeSet, Finset.mem_filter] at this
      exact this.2
    · intro i hi
      have := hsub' hi
      rw [agreeSet, Finset.mem_filter] at this
      exact this.2
  have hset : degenerateSets dom k j w
      = (codewordFinset dom k).biUnion (fun c => (agreeSet c w).powersetCard j) := by
    ext S
    constructor
    · intro hS
      obtain ⟨hcard, c, hc, hagree⟩ := mem_degenerateSets.mp hS
      refine Finset.mem_biUnion.mpr ⟨c, mem_codewordFinset.mpr hc, ?_⟩
      refine Finset.mem_powersetCard.mpr ⟨?_, hcard⟩
      intro i hi
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ i, hagree i hi⟩
    · intro hS
      obtain ⟨c, hc, hSp⟩ := Finset.mem_biUnion.mp hS
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hSp
      refine mem_degenerateSets.mpr ⟨hcard, c, mem_codewordFinset.mp hc, ?_⟩
      intro i hi
      have := hsub hi
      rw [agreeSet, Finset.mem_filter] at this
      exact this.2
  rw [hset, Finset.card_biUnion hdisj]
  exact Finset.sum_congr rfl fun c _ => (Finset.card_powersetCard _ _).symm

open Classical in
/-- Every `k`-set is degenerate: Lagrange interpolation through the `k` graph points. -/
theorem degenerateSets_base (dom : Fin n ↪ F) (k : ℕ) (w : Fin n → F) :
    degenerateSets dom k k w = (Finset.univ : Finset (Fin n)).powersetCard k := by
  unfold degenerateSets
  refine Finset.filter_true_of_mem ?_
  intro S hS
  obtain ⟨-, hcard⟩ := Finset.mem_powersetCard.mp hS
  have hinj : Set.InjOn (fun i => dom i) (S : Set (Fin n)) := dom.injective.injOn
  set p : F[X] := Lagrange.interpolate S (fun i => dom i) w with hp
  have hdeg : p.degree < (k : WithBot ℕ) := by
    have := Lagrange.degree_interpolate_lt (s := S) (v := fun i => dom i) (r := w) hinj
    rwa [hcard] at this
  refine ⟨fun i => p.eval (dom i), ⟨p, hdeg, rfl⟩, ?_⟩
  intro i hi
  exact Lagrange.eval_interpolate_at_node (s := S) (v := fun i => dom i) (r := w) hinj hi

open Classical in
/-- **The pencil partition of all `k`-sets** (`j = k`): `Σ_c C(|A_c|, k) = C(n, k)`
identically in `w` — the pair/`k`-wise statistic is frozen; word geometry only enters
at `j > k`. -/
theorem moment_identity_base (dom : Fin n ↪ F) (k : ℕ) (w : Fin n → F) :
    ∑ c ∈ codewordFinset dom k, ((agreeSet c w).card.choose k) = n.choose k := by
  rw [moment_supply_identity dom le_rfl w, degenerateSets_base,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

open Classical in
/-- **The charter quantity is a moment**: `ExplainableCoreSupply dom k m B` holds iff
the `(k+m+1)`-th binomial moment of every word's agreement spectrum is at most `B`. -/
theorem explainableCoreSupply_iff_moment (dom : Fin n ↪ F) (k m B : ℕ) :
    ExplainableCoreSupply dom k m B ↔
      ∀ w : Fin n → F,
        ∑ c ∈ codewordFinset dom k, ((agreeSet c w).card.choose (k + m + 1)) ≤ B := by
  unfold ExplainableCoreSupply
  constructor
  · intro h w
    rw [moment_supply_identity dom (by omega : k ≤ k + m + 1) w]
    exact h w
  · intro h w
    have := h w
    rwa [moment_supply_identity dom (by omega : k ≤ k + m + 1) w] at this

open Classical in
/-- The moment consumer: codewords with agreement `≥ t` number at most
`N_j / C(t,j)` (product form), for every `k ≤ j ≤ t`. -/
theorem rich_count_mul_le_moment (dom : Fin n ↪ F) {k j t : ℕ} (hkj : k ≤ j)
    (w : Fin n → F) :
    ((codewordFinset dom k).filter (fun c => t ≤ (agreeSet c w).card)).card
        * t.choose j
      ≤ (degenerateSets dom k j w).card := by
  rw [← moment_supply_identity dom hkj w]
  calc ((codewordFinset dom k).filter (fun c => t ≤ (agreeSet c w).card)).card
          * t.choose j
      = ∑ _c ∈ (codewordFinset dom k).filter (fun c => t ≤ (agreeSet c w).card),
          t.choose j := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ c ∈ (codewordFinset dom k).filter (fun c => t ≤ (agreeSet c w).card),
          ((agreeSet c w).card.choose j) := by
        refine Finset.sum_le_sum fun c hc => ?_
        exact Nat.choose_le_choose j (Finset.mem_filter.mp hc).2
    _ ≤ ∑ c ∈ codewordFinset dom k, ((agreeSet c w).card.choose j) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.moment_supply_identity
#print axioms ProximityGap.PairRank.moment_identity_base
#print axioms ProximityGap.PairRank.explainableCoreSupply_iff_moment
#print axioms ProximityGap.PairRank.rich_count_mul_le_moment
