/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonSplitSupply

/-!
# The sub-Johnson list-size bound for Reed–Solomon codes (#389)

The Johnson list bound `rsCode_agreement_list_card_le` (`n²/(a²−n(k−1))`) is only
meaningful ABOVE the Johnson radius `a² > n(k−1)`.  Below it the denominator goes
non-positive.  This file lands the **sub-Johnson** bound, valid at EVERY agreement
`a ≥ k`, from pairwise `(k−1)`-intersection alone (the Deza–Frankl / fiber bound):

> **`rsCode_subJohnson_list_card_le`** — for any word `w` and any agreement target
> `a`, the codewords of `rsCode dom k` with agreement `≥ a` satisfy
>
>   `#list · C(a, k) ≤ C(n, k)`,  i.e.  `#list ≤ C(n,k)/C(a,k) ≈ (n/a)^k`.

Mechanism: distinct codewords agree pairwise on `≤ k−1` points
(`rsCode_pairwise_agreeSet_card_le`), so a `k`-subset of the domain lies in at most
one codeword's agreement set — the `k`-subset families `agreeSet(c,w).powersetCard k`
are pairwise disjoint, each of size `C(|agreeSet|, k) ≥ C(a, k)`, and together fit
inside the `C(n, k)` domain `k`-subsets.

This is the EXACT worst-case sub-Johnson list size over general domains: the bound
is tight for additive constructions (the symmetric-interval cubic word
`CubicSupplyCountermodel`, where `k = 2, a = 3` gives `Θ(n²) = Θ(C(n,2)/C(3,2))`).
Multiplicative (smooth) domains sit strictly below it — the additive-energy/Weil
suppression — which is the remaining open improvement.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
open Classical in
/-- **The sub-Johnson list bound**: `#{codewords with agreement ≥ a} · C(a,k) ≤
C(n,k)`, valid at every agreement `a` (below as well as above the Johnson radius),
purely from pairwise `(k−1)`-intersection of distinct codewords. -/
theorem rsCode_subJohnson_list_card_le (dom : Fin n ↪ F) {k a : ℕ}
    (hk : 1 ≤ k) (w : Fin n → F) :
    ((Finset.univ : Finset (Fin n → F)).filter
        (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
          ∧ a ≤ (agreeSet c w).card)).card * a.choose k
      ≤ n.choose k := by
  classical
  set L := (Finset.univ : Finset (Fin n → F)).filter
    (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
      ∧ a ≤ (agreeSet c w).card) with hL
  -- the k-subset families of the agreement sets are pairwise disjoint
  have hdisj : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' →
      Disjoint ((agreeSet c w).powersetCard k) ((agreeSet c' w).powersetCard k) := by
    intro c hc c' hc' hne
    rw [Finset.disjoint_left]
    intro K hK hK'
    obtain ⟨hKsub, hKcard⟩ := Finset.mem_powersetCard.mp hK
    obtain ⟨hKsub', -⟩ := Finset.mem_powersetCard.mp hK'
    have hcmem := (Finset.mem_filter.mp hc).2.1
    have hc'mem := (Finset.mem_filter.mp hc').2.1
    have hinter := rsCode_pairwise_agreeSet_card_le dom hk hcmem hc'mem hne
    -- K ⊆ agreeSet c w ∩ agreeSet c' w ⊆ agreeSet c c'
    have hKcc' : K ⊆ agreeSet c c' := by
      intro i hi
      have h1 : c i = w i := by
        have := hKsub hi; rw [agreeSet, Finset.mem_filter] at this; exact this.2
      have h2 : c' i = w i := by
        have := hKsub' hi; rw [agreeSet, Finset.mem_filter] at this; exact this.2
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h1.trans h2.symm⟩
    have : k ≤ k - 1 := by
      calc k = K.card := hKcard.symm
        _ ≤ (agreeSet c c').card := Finset.card_le_card hKcc'
        _ ≤ k - 1 := hinter
    omega
  -- assemble the disjoint biUnion inside the domain k-subsets
  calc L.card * a.choose k
      = ∑ _c ∈ L, a.choose k := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ c ∈ L, (agreeSet c w).card.choose k := by
        refine Finset.sum_le_sum fun c hc => ?_
        exact Nat.choose_le_choose k (Finset.mem_filter.mp hc).2.2
    _ = ∑ c ∈ L, ((agreeSet c w).powersetCard k).card := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.card_powersetCard]
    _ = (L.biUnion (fun c => (agreeSet c w).powersetCard k)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ ((Finset.univ : Finset (Fin n)).powersetCard k).card := by
        refine Finset.card_le_card ?_
        intro K hK
        obtain ⟨c, -, hKc⟩ := Finset.mem_biUnion.mp hK
        obtain ⟨-, hKcard⟩ := Finset.mem_powersetCard.mp hKc
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hKcard⟩
    _ = n.choose k := by
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

omit [NeZero n] in
open Classical in
/-- The division form: `#{codewords with agreement ≥ a} ≤ C(n,k) / C(a,k)` for
`k ≤ a` — sub-Johnson, valid at every agreement `≈ (n/a)^k`. -/
theorem rsCode_subJohnson_list_card_le_div (dom : Fin n ↪ F) {k a : ℕ}
    (hk : 1 ≤ k) (hka : k ≤ a) (w : Fin n → F) :
    ((Finset.univ : Finset (Fin n → F)).filter
        (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F))
          ∧ a ≤ (agreeSet c w).card)).card
      ≤ n.choose k / a.choose k := by
  rw [Nat.le_div_iff_mul_le (Nat.choose_pos hka)]
  exact rsCode_subJohnson_list_card_le dom hk w

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.rsCode_subJohnson_list_card_le
#print axioms ProximityGap.Ownership.rsCode_subJohnson_list_card_le_div
