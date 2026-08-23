/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS
import Mathlib.Data.Fintype.CardEmbedding

/-!
# The popular-codeword packing bound (#371, general-k assembly piece i)

The general-`k` popularity count: codewords agreeing with a fixed word on ≥ `m`
positions are **packed** by their `k`-tuples — `k` distinct agreement positions
determine the codeword (interpolation), so the ordered injective `k`-tuples inside
the agreement sets are owned disjointly, giving

  **`#popular · (m−k+1)^k ≤ n^k`**.

This is the third instance of the ownership mechanism (after the `(k+1)`-tuple
scalar count and the `k = 1` popularity argument), and the piece the general-`k`
sparse-direction bound consumes: at `m = n − w − e` the popular-codeword count is
`≤ (n/(n−w−e+... ))^k` — polynomial, window-valid.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The agreement set of a codeword with a word. -/
def agreeSet (c y : Fin n → F) : Finset (Fin n) :=
  Finset.univ.filter (fun i => c i = y i)

open Classical in
/-- **Interpolation disjointness**: two codewords agreeing with `y` on a common
injective `k`-tuple are equal. -/
theorem codeword_eq_of_common_tuple (dom : Fin n ↪ F) {k : ℕ}
    {c c' y : Fin n → F}
    (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hc' : c' ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (t : Fin k → Fin n) (hinj : Function.Injective t)
    (ht : ∀ a, c (t a) = y (t a)) (ht' : ∀ a, c' (t a) = y (t a)) :
    c = c' := by
  obtain ⟨P, hPdeg, rfl⟩ := hc
  obtain ⟨Q, hQdeg, rfl⟩ := hc'
  have hPQ : P = Q := by
    by_cases hk0 : k = 0
    · subst hk0
      have hP0 : P = 0 := by
        rw [← Polynomial.degree_eq_bot]
        exact Nat.WithBot.lt_zero_iff.mp (by exact_mod_cast hPdeg)
      have hQ0 : Q = 0 := by
        rw [← Polynomial.degree_eq_bot]
        exact Nat.WithBot.lt_zero_iff.mp (by exact_mod_cast hQdeg)
      rw [hP0, hQ0]
    have hdiff : P - Q = 0 := by
      refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
        (f := P - Q) (s := (Finset.univ.image t).image dom) ?_ ?_
      · have hcard : ((Finset.univ.image t).image dom).card = k := by
          rw [Finset.card_image_of_injective _ dom.injective,
            Finset.card_image_of_injective _ hinj, Finset.card_univ,
            Fintype.card_fin]
        rw [hcard]
        calc (P - Q).degree ≤ max P.degree Q.degree := degree_sub_le _ _
          _ < k := max_lt hPdeg hQdeg
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hi
        rw [eval_sub, sub_eq_zero]
        have h1 := ht a
        have h2 := ht' a
        simp only at h1 h2
        rw [h1, h2]
    rw [← sub_eq_zero]
    exact hdiff
  rw [hPQ]

open Classical in
/-- Injective tuples inside a set of size `≥ m` number at least `(m+1−k)^k`. -/
theorem injective_tuples_card_ge {k m : ℕ} (A : Finset (Fin n)) (hA : m ≤ A.card) :
    (m + 1 - k) ^ k ≤ (Finset.univ.filter
      (fun t : Fin k → Fin n => Function.Injective t ∧ ∀ a, t a ∈ A)).card := by
  -- embeddings Fin k ↪ ↑A inject into the filter
  have hcard : ((Finset.univ : Finset (Fin k ↪ {x // x ∈ A})).card)
      ≤ (Finset.univ.filter
        (fun t : Fin k → Fin n => Function.Injective t ∧ ∀ a, t a ∈ A)).card := by
    refine Finset.card_le_card_of_injOn
      (fun e => fun a => ((e : Fin k ↪ {x // x ∈ A}) a : Fin n)) ?_ ?_
    · intro e _
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, fun a => (e a).2⟩
      intro a b hab
      exact e.injective (Subtype.ext hab)
    · intro e _ e' _ heq
      refine DFunLike.ext _ _ fun a => ?_
      simpa using congrFun heq a
  calc (m + 1 - k) ^ k ≤ (A.card + 1 - k) ^ k := by
        refine Nat.pow_le_pow_left ?_ k
        omega
    _ ≤ A.card.descFactorial k := Nat.pow_sub_le_descFactorial A.card k
    _ = Fintype.card (Fin k ↪ {x // x ∈ A}) := by
        rw [Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_fin]
    _ = ((Finset.univ : Finset (Fin k ↪ {x // x ∈ A})).card) :=
        (Finset.card_univ).symm
    _ ≤ _ := hcard

open Classical in
/-- **THE PACKING BOUND**: codewords agreeing with `y` on ≥ `m` positions number at
most `n^k / (m+1−k)^k` — in product form, `#popular · (m+1−k)^k ≤ n^k`. -/
theorem popular_codewords_card_mul_le (dom : Fin n ↪ F) (k : ℕ) (y : Fin n → F)
    (m : ℕ) (hmk : k ≤ m) :
    ((Finset.univ.filter (fun c : Fin n → F =>
        c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧ m ≤ (agreeSet c y).card)).card)
      * (m + 1 - k) ^ k ≤ n ^ k := by
  set pop := Finset.univ.filter (fun c : Fin n → F =>
    c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧ m ≤ (agreeSet c y).card) with hpop
  -- each popular codeword owns the injective tuples of its agreement set
  set 𝒯 : (Fin n → F) → Finset (Fin k → Fin n) := fun c =>
    Finset.univ.filter (fun t => Function.Injective t ∧ ∀ a, t a ∈ agreeSet c y)
    with h𝒯
  have hdisj : ∀ c ∈ pop, ∀ c' ∈ pop, c ≠ c' → Disjoint (𝒯 c) (𝒯 c') := by
    intro c hc c' hc' hne
    rw [Finset.disjoint_left]
    intro t ht ht'
    obtain ⟨hinj, hmem⟩ := (Finset.mem_filter.mp ht).2
    obtain ⟨-, hmem'⟩ := (Finset.mem_filter.mp ht').2
    obtain ⟨-, hcC, -⟩ := Finset.mem_filter.mp hc
    obtain ⟨-, hc'C, -⟩ := Finset.mem_filter.mp hc'
    refine hne (codeword_eq_of_common_tuple dom (y := y) hcC hc'C t hinj ?_ ?_)
    · intro a
      have := hmem a
      exact (Finset.mem_filter.mp this).2
    · intro a
      have := hmem' a
      exact (Finset.mem_filter.mp this).2
  calc pop.card * (m + 1 - k) ^ k = ∑ _c ∈ pop, (m + 1 - k) ^ k := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ c ∈ pop, (𝒯 c).card := by
        refine Finset.sum_le_sum fun c hc => ?_
        obtain ⟨-, -, hagree⟩ := Finset.mem_filter.mp hc
        exact injective_tuples_card_ge _ hagree
    _ = (pop.biUnion 𝒯).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.univ : Finset (Fin k → Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = n ^ k := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.codeword_eq_of_common_tuple
#print axioms ProximityGap.Ownership.injective_tuples_card_ge
#print axioms ProximityGap.Ownership.popular_codewords_card_mul_le
