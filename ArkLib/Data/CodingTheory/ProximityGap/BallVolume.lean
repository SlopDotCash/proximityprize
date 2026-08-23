/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# The Hamming ball volume in closed form (direction A for #232)

`ListSizeMoments.lean` expresses the first/second-moment list bounds in terms of the Hamming ball
volume `V(r) = #{g : d(0,g) ≤ r}`. This file makes `V(r)` an explicit number, the classical formula

`V(r) = Σ_{i=0}^{r} C(n,i) · (q-1)^i`,  `n = |ι|`, `q = |F|`,

so `exists_large_list`, `covering_lower_bound`, and `markov_tail_bound` become concrete inequalities
in `n, q, r` for any code. The keystone is the **Hamming sphere count**
`#{f : wt(f) = i} = C(n,i)·(q-1)^i`, proven by realizing the support-fixed slice as a
`Fintype.piFinset` (nonzero values on the support, `0` off it). This identity is not currently in
mathlib.
-/

namespace ArkLib.CodingTheory.BallVolume

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [Zero F]

/-- The number of nonzero field elements is `q - 1`. -/
theorem card_filter_ne_zero :
    (Finset.univ.filter (fun x : F => x ≠ 0)).card = Fintype.card F - 1 := by
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]

/-- **Support-fixed slice count.** The number of vectors with support *exactly* `S` is `(q-1)^|S|`:
each coordinate in `S` is an arbitrary nonzero value, each coordinate off `S` is `0`. -/
theorem support_eq_card (S : Finset ι) :
    (Finset.univ.filter
        (fun f : ι → F => Finset.univ.filter (fun i => f i ≠ 0) = S)).card
      = (Fintype.card F - 1) ^ S.card := by
  classical
  set A : ι → Finset F :=
    fun i => if i ∈ S then Finset.univ.filter (fun x => x ≠ 0) else {0} with hA
  have hset : (Finset.univ.filter
      (fun f : ι → F => Finset.univ.filter (fun i => f i ≠ 0) = S))
      = Fintype.piFinset A := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, hA]
    constructor
    · intro hsupp i
      split_ifs with hi
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← hsupp, Finset.mem_filter] at hi
        exact hi.2
      · simp only [Finset.mem_singleton]
        by_contra hne
        exact hi (by rw [← hsupp, Finset.mem_filter]; exact ⟨Finset.mem_univ i, hne⟩)
    · intro hmem
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hne
        by_contra hiS
        have h := hmem i
        rw [if_neg hiS, Finset.mem_singleton] at h
        exact hne h
      · intro hiS
        have h := hmem i
        rw [if_pos hiS, Finset.mem_filter] at h
        exact h.2
  rw [hset, Fintype.card_piFinset]
  have hoff : ∀ i ∈ (Finset.univ : Finset ι), i ∉ S → (A i).card = 1 := by
    intro i _ hiS
    simp only [hA, if_neg hiS, Finset.card_singleton]
  have hon : ∀ i ∈ S, (A i).card = Fintype.card F - 1 := by
    intro i hiS
    rw [hA]
    simp only [if_pos hiS]
    exact card_filter_ne_zero
  rw [← Finset.prod_subset (Finset.subset_univ S) hoff, Finset.prod_congr rfl hon,
    Finset.prod_const]

/-- **Hamming sphere count.** `#{f : wt(f) = i} = C(n,i)·(q-1)^i`. -/
theorem hammingNorm_card (i : ℕ) :
    (Finset.univ.filter (fun f : ι → F => hammingNorm f = i)).card
      = (Fintype.card ι).choose i * (Fintype.card F - 1) ^ i := by
  classical
  have H : ∀ f ∈ Finset.univ.filter (fun f : ι → F => hammingNorm f = i),
      Finset.univ.filter (fun j => f j ≠ 0) ∈ Finset.univ.powersetCard i := by
    intro f hf
    rw [Finset.mem_filter] at hf
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.filter_subset _ _, hf.2⟩
  rw [Finset.card_eq_sum_card_fiberwise H]
  have hterm : ∀ S ∈ Finset.univ.powersetCard i,
      ((Finset.univ.filter (fun f : ι → F => hammingNorm f = i)).filter
          (fun f => Finset.univ.filter (fun j => f j ≠ 0) = S)).card
        = (Fintype.card F - 1) ^ i := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    have hrw : ((Finset.univ.filter (fun f : ι → F => hammingNorm f = i)).filter
        (fun f => Finset.univ.filter (fun j => f j ≠ 0) = S))
        = Finset.univ.filter (fun f : ι → F => Finset.univ.filter (fun j => f j ≠ 0) = S) := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        change (Finset.univ.filter (fun j => f j ≠ 0)).card = i
        rw [h]; exact hS.2
    rw [hrw, support_eq_card, hS.2]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, smul_eq_mul]

/-- **Hamming ball volume in closed form.** `#{f : wt(f) ≤ r} = Σ_{i≤r} C(n,i)·(q-1)^i`. -/
theorem ballVol_eq (r : ℕ) :
    (Finset.univ.filter (fun f : ι → F => hammingNorm f ≤ r)).card
      = ∑ i ∈ Finset.range (r + 1),
          (Fintype.card ι).choose i * (Fintype.card F - 1) ^ i := by
  classical
  have H : ∀ f ∈ Finset.univ.filter (fun f : ι → F => hammingNorm f ≤ r),
      hammingNorm f ∈ Finset.range (r + 1) := by
    intro f hf
    rw [Finset.mem_filter] at hf
    rw [Finset.mem_range]
    omega
  rw [Finset.card_eq_sum_card_fiberwise H]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  have hrw : ((Finset.univ.filter (fun f : ι → F => hammingNorm f ≤ r)).filter
      (fun f => hammingNorm f = i))
      = Finset.univ.filter (fun f : ι → F => hammingNorm f = i) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨by omega, h⟩
  rw [hrw, hammingNorm_card]

#print axioms support_eq_card
#print axioms hammingNorm_card
#print axioms ballVol_eq

end ArkLib.CodingTheory.BallVolume
