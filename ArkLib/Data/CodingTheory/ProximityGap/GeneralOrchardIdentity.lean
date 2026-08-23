/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CorePartitionLemma
import ArkLib.Data.CodingTheory.ProximityGap.GeneralOrchardSumZero

/-!
# The general-`k` orchard identity, in the RS code (#389)

`cubic_list_eq_zeroSum` (in tree) is the `k = 2` orchard identity: the deepest-band supply
of `x^3` equals the zero-sum-triple count.  `GeneralOrchardSumZero.lean` proved the
polynomial-level general-`k` "iff" (`agree_iff_sum_zero`).  This file welds the two into the
**RS-code general-`k` orchard identity at every rate**:

> **`general_orchard_card`** — for any domain and `1 ≤ k`:
> `#{c ∈ rsCode dom k : agreement(c, x^{k+1}) ≥ k+1} = #{(k+1)-subsets T of the domain :
> ∑_{i∈T} dom i = 0}`.

So the deepest pre-capacity (sub-Johnson, agreement-`k+1`) supply of the tower word `x^{k+1}`
equals the domain's zero-sum-`(k+1)`-subset count, at **every** rate `k` — the complete
generalization of the cubic case.  The worst-case of that count (tower-extremality) is the
open kernel.  Issue #389.
-/

open Finset Polynomial

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
omit [Fintype F] [NeZero n] in
/-- A listed codeword's agreement with `x^{k+1}` is at most `k+1`: `X^{k+1} − P` is a degree-
`(k+1)` polynomial whose roots include all agreement points (distinct, via `dom`). -/
theorem agree_card_le (dom : Fin n ↪ F) {k : ℕ} {P : F[X]} (hPdeg : P.degree < (k : ℕ)) :
    (agreeSet (fun i => P.eval (dom i)) (fun i => (dom i) ^ (k + 1))).card ≤ k + 1 := by
  classical
  set Q : F[X] := X ^ (k + 1) - P with hQ
  have hPdeg' : P.degree < (k + 1 : ℕ) := lt_trans hPdeg (by exact_mod_cast Nat.lt_succ_self k)
  have hQmonic : Q.Monic := monic_X_pow_sub hPdeg'
  have hQne : Q ≠ 0 := hQmonic.ne_zero
  have hQnat : Q.natDegree = k + 1 := by
    have hd : Q.degree = (k + 1 : ℕ) := by
      rw [hQ, degree_sub_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
    exact (Polynomial.degree_eq_iff_natDegree_eq hQne).mp hd
  set S := agreeSet (fun i => P.eval (dom i)) (fun i => (dom i) ^ (k + 1)) with hS
  have hroot : ∀ i ∈ S, dom i ∈ Q.roots.toFinset := by
    intro i hi
    have hPi : P.eval (dom i) = (dom i) ^ (k + 1) := by
      have := (Finset.mem_filter.mp hi).2
      simpa [agreeSet] using this
    rw [Multiset.mem_toFinset, mem_roots hQne, hQ, IsRoot, eval_sub, eval_pow, eval_X,
      hPi, sub_self]
  calc S.card = (S.image dom).card := (Finset.card_image_of_injective _ dom.injective).symm
    _ ≤ Q.roots.toFinset.card := by
        refine Finset.card_le_card ?_
        intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        exact hroot i hi
    _ ≤ Multiset.card Q.roots := Multiset.toFinset_card_le _
    _ ≤ Q.natDegree := Q.card_roots'
    _ = k + 1 := hQnat

open Classical in
/-- **THE GENERAL-`k` ORCHARD IDENTITY** in the RS code: the deepest-band supply of `x^{k+1}`
equals the domain's zero-sum-`(k+1)`-subset count, at every rate `k`. -/
theorem general_orchard_card (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) :
    ((Finset.univ : Finset (Fin n → F)).filter (fun c =>
        c ∈ (rsCode dom k : Submodule F (Fin n → F))
          ∧ k + 1 ≤ (agreeSet c (fun i => (dom i) ^ (k + 1))).card)).card
      = (((Finset.univ : Finset (Fin n)).powersetCard (k + 1)).filter
          (fun T => ∑ i ∈ T, dom i = 0)).card := by
  classical
  -- agreement is EXACTLY k+1 for a listed codeword
  have hcard : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      k + 1 ≤ (agreeSet c (fun i => (dom i) ^ (k + 1))).card →
      (agreeSet c (fun i => (dom i) ^ (k + 1))).card = k + 1 := by
    intro c hc hge
    obtain ⟨P, hPdeg, rfl⟩ := hc
    exact le_antisymm (agree_card_le dom hPdeg) hge
  -- forward: the agreement set sums to zero
  have hsum0 : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      k + 1 ≤ (agreeSet c (fun i => (dom i) ^ (k + 1))).card →
      ∑ i ∈ agreeSet c (fun i => (dom i) ^ (k + 1)), dom i = 0 := by
    intro c hc hge
    obtain ⟨P, hPdeg, rfl⟩ := hc
    set S := agreeSet (fun i => P.eval (dom i)) (fun i => (dom i) ^ (k + 1)) with hS
    have hScard : S.card = k + 1 := hcard _ ⟨P, hPdeg, rfl⟩ hge
    -- the field values
    have hTcard : (S.image dom).card = k + 1 := by
      rw [Finset.card_image_of_injective _ dom.injective, hScard]
    have hagree : ∀ a ∈ S.image dom, P.eval a = a ^ (k + 1) := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      have := (Finset.mem_filter.mp hi).2
      simpa [agreeSet] using this
    have hfield := ProximityGap.GeneralOrchard.sum_eq_zero_of_agree P hk hPdeg
      (S.image dom) hTcard hagree
    rwa [Finset.sum_image (fun i _ j _ h => dom.injective h)] at hfield
  refine Finset.card_bij (fun c _ => agreeSet c (fun i => (dom i) ^ (k + 1))) ?_ ?_ ?_
  · -- maps into the zero-sum (k+1)-subsets
    intro c hc
    obtain ⟨-, hmem, hge⟩ := Finset.mem_filter.mp hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, hcard c hmem hge⟩, hsum0 c hmem hge⟩
  · -- injective: unique explainer on the common agreement set (card k+1 ≥ k)
    intro c hc cb hcb heq
    obtain ⟨-, hmem, hge⟩ := Finset.mem_filter.mp hc
    obtain ⟨-, hmemb, hgeb⟩ := Finset.mem_filter.mp hcb
    refine explainable_core_explainer_unique (k := k) (w := fun i => (dom i) ^ (k + 1))
      (T := agreeSet c (fun i => (dom i) ^ (k + 1))) (c := c) (c' := cb) dom
      (by rw [hcard c hmem hge]; omega) hmem hmemb
      (fun i hi => (Finset.mem_filter.mp hi).2) ?_
    intro i hi
    have hib : i ∈ agreeSet cb (fun i => (dom i) ^ (k + 1)) := (Finset.ext_iff.mp heq i).mp hi
    exact (Finset.mem_filter.mp hib).2
  · -- surjective: each zero-sum (k+1)-subset is the agreement set of a codeword
    intro T hT
    obtain ⟨hTmem, hTsum⟩ := Finset.mem_filter.mp hT
    obtain ⟨-, hTcard⟩ := Finset.mem_powersetCard.mp hTmem
    -- field values of T
    have hTfield : (T.image dom).card = k + 1 := by
      rw [Finset.card_image_of_injective _ dom.injective, hTcard]
    have hTfsum : ∑ a ∈ T.image dom, a = 0 := by
      rw [Finset.sum_image (fun i _ j _ h => dom.injective h)]; exact hTsum
    obtain ⟨P, hPdeg, hP⟩ := ProximityGap.GeneralOrchard.exists_agree_of_sum_zero
      (T.image dom) hTfield hTfsum
    set c0 : Fin n → F := fun i => P.eval (dom i) with hc0
    have hc0mem : c0 ∈ (rsCode dom k : Submodule F (Fin n → F)) := ⟨P, hPdeg, rfl⟩
    -- T ⊆ agreeSet c0
    have hTsub : T ⊆ agreeSet c0 (fun i => (dom i) ^ (k + 1)) := by
      intro i hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have := hP (dom i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      simpa [hc0] using this
    have hge0 : k + 1 ≤ (agreeSet c0 (fun i => (dom i) ^ (k + 1))).card := by
      calc k + 1 = T.card := hTcard.symm
        _ ≤ _ := Finset.card_le_card hTsub
    refine ⟨c0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc0mem, hge0⟩, ?_⟩
    exact (Finset.eq_of_subset_of_card_le hTsub
      (by rw [hcard c0 hc0mem hge0, hTcard])).symm

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.agree_card_le
#print axioms ProximityGap.PairRank.general_orchard_card
