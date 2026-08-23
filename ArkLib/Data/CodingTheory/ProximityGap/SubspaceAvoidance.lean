/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib

/-!
# The subspace-avoidance counting engine (issues #334 / #329, hypothesis A1)

The shared counting core behind three in-tree consumers:

* the **codimension-1 kernel count** of Spartan's RLC round
  (`Spartan.Spec.Bricks.card_linearForm_kernel_of_ne`, `TightRLCKernel.lean` — the kernel of a
  nonzero linear form is a codimension-1 subspace);
* the **proper-subspace avoidance ratio** of [Jo26] (ePrint 2026/891) Lemma 3.1, the counting
  step of the field-size-weighted interleaving bound (Theorem 4.2): a proper subspace
  `K ⊊ F^s` misses at least `q^s − q^{s−1}` of the `q^s − 1` nonzero vectors;
* the **union-covering lemma** ([Jo26] Lemma 3.2, in-tree as
  `exists_nonzero_notMem_of_proper_family`, `InterleavingStabilityMCA.lean`).

This file provides the single-subspace counting facts ([Jo26] Lemma 3.1's content):

* `Submodule.card_le_pow_finrank_pred_of_ne_top` — a proper subspace of an `s`-dimensional
  space over a finite field `F` has at most `|F|^(s−1)` elements;
* `card_nonzero_avoiding_ge` — at least `|F|^s − |F|^(s−1)` nonzero vectors avoid any proper
  subspace (the `1/A(q,s)` avoidance numerator of [Jo26] Theorem 4.2);
* `exists_avoiding_count_ge` — the **averaging/double-counting step** ([Jo26] Theorem 4.2's
  second half): if every seed in a bad set survives at least `m` of the candidate combiners,
  some single combiner preserves an `m/|Λ|` fraction of the bad set (stated multiplicatively
  over `ℕ` to avoid division).
-/

open Finset

namespace SubspaceAvoidance

variable {F : Type*} [Field F] [Fintype F] {s : ℕ}

/-- A **proper** subspace of the `s`-dimensional space `Fin s → F` over a finite field has at
most `|F|^(s−1)` elements: its rank is at most `s − 1`, and a finite-dimensional space over `F`
has cardinality `|F|^rank`. -/
theorem card_le_pow_finrank_pred_of_ne_top (K : Submodule F (Fin s → F)) (hK : K ≠ ⊤) :
    Nat.card K ≤ Fintype.card F ^ (s - 1) := by
  classical
  have hfin : Module.finrank F (Fin s → F) = s := by simp
  have hlt : Module.finrank F K < s := by
    have h := Submodule.finrank_lt hK
    omega
  have hcard : Nat.card K = Fintype.card F ^ (Module.finrank F K) := by
    simpa [Nat.card_eq_fintype_card] using
      (Module.card_eq_pow_finrank (K := F) (V := K))
  rw [hcard]
  exact Nat.pow_le_pow_right Fintype.card_pos (by omega)

/-- **The avoidance count** ([Jo26] Lemma 3.1 / the `1/A(q,s)` numerator): a proper subspace
`K ⊊ Fin s → F` is avoided by at least `|F|^s − |F|^(s−1)` of the (nonzero) vectors — since
`0 ∈ K`, every vector outside `K` is automatically nonzero. -/
theorem card_nonzero_avoiding_ge (K : Submodule F (Fin s → F)) (hK : K ≠ ⊤)
    [DecidablePred (fun x : Fin s → F => x ∈ K)] :
    Fintype.card F ^ s - Fintype.card F ^ (s - 1)
      ≤ (univ.filter (fun x : Fin s → F => x ∉ K)).card := by
  classical
  have hsum : (univ.filter (fun x : Fin s → F => x ∈ K)).card
      + (univ.filter (fun x : Fin s → F => ¬ x ∈ K)).card
      = Fintype.card (Fin s → F) := by
    rw [Finset.filter_card_add_filter_neg_card_eq_card]
    simp
  have hKcard : (univ.filter (fun x : Fin s → F => x ∈ K)).card = Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    simpa using (Fintype.card_subtype (fun x : Fin s → F => x ∈ K)).symm
  have hle := card_le_pow_finrank_pred_of_ne_top K hK
  have htot : Fintype.card (Fin s → F) = Fintype.card F ^ s := by
    simp
  have hcongr : (univ.filter (fun x : Fin s → F => x ∉ K)).card
      = (univ.filter (fun x : Fin s → F => ¬ x ∈ K)).card := rfl
  omega

/-- **The averaging / double-counting step** ([Jo26] Theorem 4.2, upper-bound half): if every
seed `ω` in the bad set `B` survives at least `m` of the candidate combiners `Λ`, then some
single combiner `λ ∈ Λ` preserves at least an `m/|Λ|` fraction of `B` — stated
multiplicatively (`B.card * m ≤ count * Λ.card`) to stay in `ℕ`. -/
theorem exists_avoiding_count_ge {Ω L : Type*} [DecidableEq Ω] [DecidableEq L]
    (B : Finset Ω) (Λ : Finset L) (hΛ : Λ.Nonempty)
    (P : Ω → L → Prop) [∀ ω l, Decidable (P ω l)]
    (m : ℕ) (h : ∀ ω ∈ B, m ≤ (Λ.filter (fun l => P ω l)).card) :
    ∃ l ∈ Λ, B.card * m ≤ (B.filter (fun ω => P ω l)).card * Λ.card := by
  classical
  -- Double counting: ∑_{l ∈ Λ} #{ω ∈ B | P ω l} = ∑_{ω ∈ B} #{l ∈ Λ | P ω l} ≥ |B|·m.
  have hdc : ∑ l ∈ Λ, (B.filter (fun ω => P ω l)).card
      = ∑ ω ∈ B, (Λ.filter (fun l => P ω l)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have hlow : B.card * m ≤ ∑ l ∈ Λ, (B.filter (fun ω => P ω l)).card := by
    rw [hdc]
    calc B.card * m = ∑ _ω ∈ B, m := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ ω ∈ B, (Λ.filter (fun l => P ω l)).card := Finset.sum_le_sum h
  -- Max ≥ average: some l attains at least the average.
  by_contra hcon
  push Not at hcon
  have hstrict : ∑ l ∈ Λ, (B.filter (fun ω => P ω l)).card * Λ.card
      < ∑ _l ∈ Λ, B.card * m := by
    apply Finset.sum_lt_sum_of_nonempty hΛ
    intro l hl
    exact hcon l hl
  rw [Finset.sum_const, smul_eq_mul, ← Finset.sum_mul] at hstrict
  have := Nat.lt_of_mul_lt_mul_right (a := Λ.card) (by
    calc (∑ l ∈ Λ, (B.filter (fun ω => P ω l)).card) * Λ.card < Λ.card * (B.card * m) := hstrict
    _ = (B.card * m) * Λ.card := by ring)
  omega

/-! ### Sharpness ([Jo26] Remark 4.3, hypothesis A2)

The factor `A(q,s)` is sharp: a codimension-1 obstruction — the kernel of a nonzero linear
form — has *exactly* `q^(s-1)` elements, so it is avoided by *exactly* `q^s − q^(s-1)` vectors.
The counting core is the coordinate-restriction bijection (the index-generic form of the
Spartan RLC kernel count, `TightRLCKernel.lean`, which should eventually consume this). -/

/-- The kernel of a linear form with a nonzero coefficient at `i₀` is in bijection (by
restriction to the other coordinates) with the functions on the other coordinates: the value
at `i₀` is uniquely determined and always recoverable (multiplication by a nonzero field
element is bijective). -/
theorem bijective_kernelRestrict (d : Fin s → F) (i₀ : Fin s) (hd : d i₀ ≠ 0) :
    Function.Bijective
      (fun (r : {r : Fin s → F // ∑ i, r i * d i = 0}) (j : {i : Fin s // i ≠ i₀}) =>
        r.1 j.1) := by
  constructor
  · rintro ⟨r, hr⟩ ⟨t, ht⟩ h
    have h' : ∀ j : {i : Fin s // i ≠ i₀}, r j.1 = t j.1 := fun j => congrFun h j
    have htail : ∑ j : {i : Fin s // i ≠ i₀}, r j.1 * d j.1
        = ∑ j : {i : Fin s // i ≠ i₀}, t j.1 * d j.1 :=
      Finset.sum_congr rfl fun j _ => by rw [h' j]
    have hr' : r i₀ * d i₀ + ∑ j : {i : Fin s // i ≠ i₀}, r j.1 * d j.1 = 0 :=
      (Fintype.sum_eq_add_sum_subtype_ne (fun i => r i * d i) i₀).symm.trans hr
    have ht' : t i₀ * d i₀ + ∑ j : {i : Fin s // i ≠ i₀}, t j.1 * d j.1 = 0 :=
      (Fintype.sum_eq_add_sum_subtype_ne (fun i => t i * d i) i₀).symm.trans ht
    have hhead : r i₀ * d i₀ = t i₀ * d i₀ := by
      have h1 := eq_neg_of_add_eq_zero_left hr'
      have h2 := eq_neg_of_add_eq_zero_left ht'
      rw [h1, h2, htail]
    have hi₀ : r i₀ = t i₀ := mul_right_cancel₀ hd hhead
    exact Subtype.ext (funext fun i => by
      by_cases hi : i = i₀
      · subst hi; exact hi₀
      · exact h' ⟨i, hi⟩)
  · intro g
    refine ⟨⟨fun i => if h : i = i₀
        then -(∑ j : {i : Fin s // i ≠ i₀}, g j * d j.1) / d i₀ else g ⟨i, h⟩, ?_⟩, ?_⟩
    · calc ∑ i, (if h : i = i₀
            then -(∑ j : {i : Fin s // i ≠ i₀}, g j * d j.1) / d i₀ else g ⟨i, h⟩) * d i
          = (if h : i₀ = i₀
              then -(∑ j : {i : Fin s // i ≠ i₀}, g j * d j.1) / d i₀ else g ⟨i₀, h⟩) * d i₀
            + ∑ j : {i : Fin s // i ≠ i₀}, (if h : j.1 = i₀
              then -(∑ j : {i : Fin s // i ≠ i₀}, g j * d j.1) / d i₀
              else g ⟨j.1, h⟩) * d j.1 :=
            Fintype.sum_eq_add_sum_subtype_ne _ i₀
        _ = -(∑ j : {i : Fin s // i ≠ i₀}, g j * d j.1)
            + ∑ j : {i : Fin s // i ≠ i₀}, g j * d j.1 := by
            rw [dif_pos rfl, div_mul_cancel₀ _ hd]
            congr 1
            exact Finset.sum_congr rfl fun j _ => by rw [dif_neg j.2]
        _ = 0 := neg_add_cancel _
    · funext j
      show (if h : j.1 = i₀ then _ else g ⟨j.1, h⟩) = g j
      rw [dif_neg j.2]

/-- **Sharpness of the avoidance factor** ([Jo26] Remark 4.3): the kernel of a nonzero linear
form on `Fin s → F` has exactly `|F|^(s-1)` elements — so the avoidance bound
`card_nonzero_avoiding_ge` is attained with equality at codimension-1 obstructions, and the
field-size factor `A(q,s)` of [Jo26] Theorem 4.2 cannot be improved at the
subspace-avoidance step. -/
theorem card_linearForm_kernel_eq (d : Fin s → F) (i₀ : Fin s) (hd : d i₀ ≠ 0) :
    Nat.card {r : Fin s → F // ∑ i, r i * d i = 0} = Fintype.card F ^ (s - 1) := by
  classical
  rw [Nat.card_eq_fintype_card,
    Fintype.card_of_bijective (bijective_kernelRestrict d i₀ hd), Fintype.card_fun]
  congr 1
  have hcard : Fintype.card {i : Fin s // i ≠ i₀} + 1 = s := by
    rw [← Fintype.card_option]
    simpa using Fintype.card_congr (Equiv.optionSubtypeNe i₀)
  omega

end SubspaceAvoidance

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms SubspaceAvoidance.card_le_pow_finrank_pred_of_ne_top
#print axioms SubspaceAvoidance.card_nonzero_avoiding_ge
#print axioms SubspaceAvoidance.exists_avoiding_count_ge
#print axioms SubspaceAvoidance.bijective_kernelRestrict
#print axioms SubspaceAvoidance.card_linearForm_kernel_eq
