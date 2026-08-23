/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CosetWordCap

/-!
# The core-partition keystone: unique explainers (#389, the reformulated core)

The capped-optimum census reduced residual (b) to a configuration question via the
partition `supply = Σ_c C(a_c, t)`.  This file lands the partition's keystone:

> **`explainable_core_explainer_unique`** — an explainable `(k+m+1)`-core has exactly
> one explaining codeword: two explainers agree with the word (hence each other) on
> `k+m+1 ≥ k` points, forcing their degree-`< k` polynomials equal.

> **`core_families_disjoint`** — consequently the core families of distinct codewords
> are disjoint: the explainable cores PARTITION by their unique explainer, and the
> capped supply is literally `Σ_c C(|agreeSet c w|, k+m+1)` over the (pairwise
> `≤ k−1`-intersecting) agreement-set family — the object whose partition optimum the
> census measured at `2·C(cap, t)` exactly.

With this, residual (b) is formally the **capped agreement-configuration bound**: how
large can `Σ_c C(a_c, t)` be for a family of `≤ 2k+m+1`-sized, pairwise
`≤ (k−1)`-intersecting RS agreement sets?  (The census says: the disjoint-partition
value, `poly(n)·C(2k+m+1, k+m+1)`.)  Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **Unique explainers**: two codewords of `rsCode dom k` agreeing with a common word
on a common set of `≥ k` points are equal. -/
theorem explainable_core_explainer_unique (dom : Fin n ↪ F) {k : ℕ}
    {w : Fin n → F} {T : Finset (Fin n)} (hT : k ≤ T.card)
    {c c' : Fin n → F} (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hc' : c' ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hagree : ∀ i ∈ T, c i = w i) (hagree' : ∀ i ∈ T, c' i = w i) : c = c' := by
  classical
  obtain ⟨P, hPdeg, rfl⟩ := hc
  obtain ⟨P', hP'deg, rfl⟩ := hc'
  suffices hPP : P = P' by rw [hPP]
  have hzero : P - P' = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
      (s := T.image dom) ?_ ?_
    · rw [Finset.card_image_of_injective _ dom.injective]
      refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
      · exact lt_of_lt_of_le hPdeg (by exact_mod_cast hT)
      · exact lt_of_lt_of_le hP'deg (by exact_mod_cast hT)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      rw [Polynomial.eval_sub]
      linear_combination (hagree i hi) - (hagree' i hi)
  have := sub_eq_zero.mp hzero
  exact this

open Classical in
/-- **The partition**: core families of distinct codewords are disjoint — every
explainable `(k+m+1)`-core (`1 ≤ k`, so `k ≤ k+m+1`) determines its explainer. -/
theorem core_families_disjoint (dom : Fin n ↪ F) {k m : ℕ}
    {w : Fin n → F} {c c' : Fin n → F}
    (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hc' : c' ∈ (rsCode dom k : Submodule F (Fin n → F))) (hne : c ≠ c') :
    Disjoint
      (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ∀ i ∈ T, c i = w i))
      (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ∀ i ∈ T, c' i = w i)) := by
  classical
  rw [Finset.disjoint_left]
  intro T hT1 hT2
  obtain ⟨hTmem, h1⟩ := Finset.mem_filter.mp hT1
  obtain ⟨-, h2⟩ := Finset.mem_filter.mp hT2
  obtain ⟨-, hTcard⟩ := Finset.mem_powersetCard.mp hTmem
  exact hne (explainable_core_explainer_unique dom
    (by omega : k ≤ T.card) hc hc' h1 h2)

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.explainable_core_explainer_unique
#print axioms ProximityGap.PairRank.core_families_disjoint
