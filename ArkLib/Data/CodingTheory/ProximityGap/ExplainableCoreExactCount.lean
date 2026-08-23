/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonSplitSupply

/-!
# The exact explainable-core count: the supply is the agreement-size profile

Issue #389. The supply statement counts the **explainable `(k+m+1)`-cores** of a word `w`
(subsets `T`, `|T| = k+m+1`, on which some codeword matches `w`). The in-tree bound
`explainable_cores_card_le_list_mul` gives `≤ L · C(A, k+m+1)`. This file proves the
**exact identity** underneath it:

> **`explainable_cores_eq_sum_agreement`** —
> `#explainable cores = Σ_{c : agreement ≥ k+m+1} C(|agreeSet c w|, k+m+1)`.

The mechanism is a *partition*: since `k+m+1 > k−1`, each core `T` lies in the agreement set
of **exactly one** codeword (two would force `|agreeSet c c'| ≥ k+m+1`, contradicting the
RS pairwise bound `rsCode_pairwise_agreeSet_card_le`). So the explainable cores are the
disjoint union, over codewords with large agreement, of the `(k+m+1)`-subsets of each
agreement set.

**Consequence (the extremal reading of the supply wall).** Combined with the `k`-subset
packing constraint `Σ_c C(|agreeSet c w|, k) ≤ C(n,k)` (the same intersection bound),
the supply is the extremal problem *maximize `Σ C(aᵢ, k+m+1)` s.t. `Σ C(aᵢ, k) ≤ C(n,k)`*.
Because `C(a,k+m+1)/C(a,k)` is increasing in `a`, the maximizer concentrates on a single
large agreement `aᵢ ≈ n`, giving `≈ C(n,k+m+1)` = the trivial bound: **the pure packing
bound is worst-case vacuous** (a word near one codeword saturates it). Hence any
sub-trivial supply bound must use the algebraic constraint on *which* words arise as
bad-scalar lines — it cannot come from combinatorics alone. (Probe
`probe_extremal.py`; DISPROOF_LOG 2026-06-12.)

## References

* Issue #389; `JohnsonSplitSupply.lean` (`rsCode_pairwise_agreeSet_card_le`,
  `explainable_cores_card_le_list_mul`), `DeepBandMultiplicity.lean` (`ExplainableOn`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The exact explainable-core count.** The explainable `(k+m+1)`-cores of `w` are the
disjoint union, over codewords with agreement `≥ k+m+1`, of the `(k+m+1)`-subsets of each
agreement set; hence their number is `Σ_c C(|agreeSet c w|, k+m+1)`. -/
theorem explainable_cores_eq_sum_agreement (dom : Fin n ↪ F) {k : ℕ} (m : ℕ)
    (hk : 1 ≤ k) (w : Fin n → F) :
    (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ExplainableOn dom k w T)).card
      = ∑ c ∈ (Finset.univ : Finset (Fin n → F)).filter
          (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
            ∧ k + m + 1 ≤ (agreeSet c w).card),
        (agreeSet c w).card.choose (k + m + 1) := by
  classical
  set a : ℕ := k + m + 1 with ha
  set L : Finset (Fin n → F) := (Finset.univ : Finset (Fin n → F)).filter
    (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
      ∧ a ≤ (agreeSet c w).card) with hL
  -- the explainable cores are the disjoint biUnion of the a-subsets of each agreement set
  have hbij : (((Finset.univ : Finset (Fin n)).powersetCard a).filter
      (fun T => ExplainableOn dom k w T))
      = L.biUnion (fun c => (agreeSet c w).powersetCard a) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_biUnion, hL,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨-, hTcard⟩, c, hc, hcw⟩
      have hTsub : T ⊆ agreeSet c w := by
        intro i hi
        rw [agreeSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hcw i hi⟩
      refine ⟨c, ⟨hc, ?_⟩, hTsub, hTcard⟩
      calc a = T.card := hTcard.symm
        _ ≤ (agreeSet c w).card := Finset.card_le_card hTsub
    · rintro ⟨c, ⟨hc, -⟩, hTsub, hTcard⟩
      refine ⟨⟨Finset.subset_univ _, hTcard⟩, c, hc, fun i hi => ?_⟩
      have := hTsub hi
      rw [agreeSet, Finset.mem_filter] at this
      exact this.2
  -- the biUnion is disjoint: a core in two agreement sets forces the codewords equal
  have hdisj : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' →
      Disjoint ((agreeSet c w).powersetCard a) ((agreeSet c' w).powersetCard a) := by
    intro c hc c' hc' hne
    rw [Finset.disjoint_left]
    intro T hT hT'
    obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
    obtain ⟨hTsub', -⟩ := Finset.mem_powersetCard.mp hT'
    obtain ⟨-, hcmem, -⟩ := Finset.mem_filter.mp hc
    obtain ⟨-, hc'mem, -⟩ := Finset.mem_filter.mp hc'
    -- T ⊆ agreeSet c c', so a = |T| ≤ k-1
    have hTcc' : T ⊆ agreeSet c c' := by
      intro i hi
      have h1 := hTsub hi; have h2 := hTsub' hi
      rw [agreeSet, Finset.mem_filter] at h1 h2 ⊢
      exact ⟨Finset.mem_univ _, h1.2.trans h2.2.symm⟩
    have hcard := rsCode_pairwise_agreeSet_card_le dom hk hcmem hc'mem hne
    have : a ≤ k - 1 := by
      calc a = T.card := hTcard.symm
        _ ≤ (agreeSet c c').card := Finset.card_le_card hTcc'
        _ ≤ k - 1 := hcard
    omega
  rw [hbij, Finset.card_biUnion hdisj]
  exact Finset.sum_congr rfl fun c _ => Finset.card_powersetCard a (agreeSet c w)

/-! ## Source audit -/

#print axioms explainable_cores_eq_sum_agreement

end ProximityGap.Ownership
