/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Lam-Leung tightness for the `e_1 = 0` fiber: antipodal invariance of vanishing subsets

This file proves a *conditional* upper bound (tightness) statement of "Lam-Leung" type
for the smooth `2^m`-domain Reed-Solomon setting.

Setup. `F` is a field. We have an element `ζ : F` and a natural `N` with `ζ^N = -1`. Thus
negation acts as multiplication by `ζ^N`, i.e. `ζ^{j+N} = -ζ^j`, and `ζ` has multiplicative
order dividing `2N` with `ζ^{2N} = 1`. (Characteristic `≠ 2` is implicit: if `2 = 0` then
`ζ^N = -1 = 1`; the proof below uses no `2 ≠ 0` directly — the content lives in `hindep`.)

The crucial *conditional* hypothesis `hindep` is the **cyclotomic linear-independence** of
`{1, ζ, …, ζ^{N-1}}` against `{-1,0,1}` coefficient vectors:
any `{-1,0,1}`-combination of the first `N` powers of `ζ` that vanishes must be the zero
combination. Over `ℂ` (or any field where `ζ` is a primitive `2N`-th root of unity and the
minimal polynomial of `ζ` has degree `≥ N`, e.g. `ζ = exp(πi/N)` with `2N` a prime power),
this holds. In a finite "prize" field `F = 𝔽_q` it generally **fails** — and the extra
fibre elements that show up there are exactly the `q`-dependent antipodal-violating subsets,
which is the whole point of the open problem.

Statement proven. If `A ⊆ range (2N)` and `∑_{a ∈ A} ζ^a = 0`, then `A` is invariant under
the antipodal shift `j ↦ j + N` on the low half: `∀ j < N, (j ∈ A ↔ j + N ∈ A)`.

So, conditionally on `hindep`, the vanishing subsets are **exactly** the negation-symmetric
(antipodal) ones. This is an *upper* bound on the `e_1 = 0` fibre count: every vanishing set
is a union of antipodal pairs `{j, j+N}`.

This is **not** an unconditional theorem and does NOT prove the prize: it isolates the
content (`hindep`) that holds over `ℂ`/full extensions and fails in finite fields. The
re-grouping of the vanishing sum is the load-bearing combinatorial step and is fully verified.
-/

open Finset

namespace ArkLib.CodingTheory.Round9LamLeung

variable {F : Type*} [Field F]

/-- **Lam-Leung tightness (conditional).**

Given `ζ : F` with `ζ^N = -1`, the cyclotomic linear-independence hypothesis `hindep`
on `{-1,0,1}`-combinations of `{1, ζ, …, ζ^{N-1}}`, and a subset `A ⊆ range (2N)` whose
`ζ`-power sum vanishes, the set `A` is invariant under the antipodal shift `j ↦ j + N`. -/
theorem antipodal_invariant_of_vanishing_sum
    (ζ : F) (N : ℕ) (hζN : ζ ^ N = -1)
    (hindep : ∀ c : ℕ → F, (∀ j, j < N → c j = 1 ∨ c j = -1 ∨ c j = 0) →
        (∑ j ∈ Finset.range N, c j * ζ ^ j) = 0 → ∀ j, j < N → c j = 0)
    (A : Finset ℕ) (hA : A ⊆ Finset.range (2 * N))
    (hsum : ∑ a ∈ A, ζ ^ a = 0) :
    ∀ j, j < N → (j ∈ A ↔ j + N ∈ A) := by
  -- The coefficient vector `c j = [j ∈ A] - [j + N ∈ A]`.
  set c : ℕ → F := fun j =>
      (if j ∈ A then 1 else 0) - (if j + N ∈ A then 1 else 0) with hc
  -- Step 1: each `c j ∈ {-1, 0, 1}`.
  have hcoeff : ∀ j, j < N → c j = 1 ∨ c j = -1 ∨ c j = 0 := by
    intro j _
    simp only [hc]
    by_cases h1 : j ∈ A <;> by_cases h2 : j + N ∈ A <;>
      simp only [h1, h2, if_true, if_false] <;> norm_num
  -- Step 2: re-group the vanishing sum. We show `∑_{a∈A} ζ^a = ∑_{j<N} c j * ζ^j`.
  -- Split `A` by `(· < N)`.
  have hsplit : ∑ a ∈ A, ζ ^ a
      = (∑ a ∈ A.filter (· < N), ζ ^ a) + ∑ a ∈ A.filter (¬ · < N), ζ ^ a := by
    rw [Finset.sum_filter_add_sum_filter_not]
  -- Low part as a sum of indicators over `range N`. Note `A.filter(·<N) = (range N).filter(·∈A)`.
  have hlow : (∑ a ∈ A.filter (· < N), ζ ^ a)
      = ∑ j ∈ Finset.range N, (if j ∈ A then 1 else 0) * ζ ^ j := by
    have hset : A.filter (· < N) = (Finset.range N).filter (· ∈ A) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_range]
      tauto
    rw [hset, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : j ∈ A <;> simp [h]
  -- High part: reindex `a = j + N`, use `ζ^{j+N} = ζ^j * ζ^N = -ζ^j`.
  -- High part: first reindex `A.filter(¬·<N)` to `(range N).filter(·+N∈A)` by `a ↦ a-N`,
  -- then convert to a full `range N` indicator sum, using `ζ^{j+N} = -ζ^j`.
  have hhigh : (∑ a ∈ A.filter (¬ · < N), ζ ^ a)
      = ∑ j ∈ Finset.range N, (if j + N ∈ A then -(1 : F) else 0) * ζ ^ j := by
    -- Step (a): reindex to a filtered sum over `range N`.
    have hreindex : (∑ a ∈ A.filter (¬ · < N), ζ ^ a)
        = ∑ j ∈ (Finset.range N).filter (· + N ∈ A), (-(1 : F)) * ζ ^ j := by
      apply Finset.sum_nbij' (i := fun a => a - N) (j := fun j => j + N)
      · -- forward maps into the filtered range
        intro a ha
        simp only [Finset.mem_filter, not_lt] at ha
        obtain ⟨haA, hge⟩ := ha
        have hlt : a < 2 * N := by simpa [Finset.mem_range] using hA haA
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        have : a - N + N = a := by omega
        rw [this]; exact haA
      · -- backward maps into the high part of `A`
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        obtain ⟨hjN, hjA⟩ := hj
        simp only [Finset.mem_filter, not_lt]
        exact ⟨hjA, by omega⟩
      · -- left inverse
        intro a ha
        simp only [Finset.mem_filter, not_lt] at ha
        omega
      · -- right inverse
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        omega
      · -- the summand matches: `ζ^a = -1 * ζ^{a-N}` when `a ≥ N`
        intro a ha
        simp only [Finset.mem_filter, not_lt] at ha
        obtain ⟨_, hge⟩ := ha
        have key : ζ ^ a = -1 * ζ ^ (a - N) := by
          have heq : ζ ^ a = ζ ^ ((a - N) + N) := by
            congr 1; omega
          rw [heq, pow_add, hζN]; ring
        exact key
    rw [hreindex]
    -- Step (b): convert filtered sum over `range N` to a full indicator sum.
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : j + N ∈ A <;> simp [h]
  -- Combine: `∑_{a∈A} ζ^a = ∑_{j<N} c j * ζ^j`.
  have hregroup : ∑ a ∈ A, ζ ^ a = ∑ j ∈ Finset.range N, c j * ζ ^ j := by
    rw [hsplit, hlow, hhigh, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [hc]
    by_cases h1 : j ∈ A <;> by_cases h2 : j + N ∈ A <;>
      simp only [h1, h2, if_true, if_false] <;> ring
  -- The combined sum vanishes, so `hindep` forces every `c j = 0`.
  have hcsum : (∑ j ∈ Finset.range N, c j * ζ ^ j) = 0 := by
    rw [← hregroup]; exact hsum
  have hczero : ∀ j, j < N → c j = 0 := hindep c hcoeff hcsum
  -- Conclude: `[j∈A] = [j+N∈A]`, i.e. `j ∈ A ↔ j + N ∈ A`.
  intro j hj
  have hz := hczero j hj
  simp only [hc] at hz
  by_cases h1 : j ∈ A <;> by_cases h2 : j + N ∈ A <;>
    simp only [h1, h2, if_true, if_false] at hz
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · -- `1 - 0 = 0` is false
    exfalso; norm_num at hz
  · -- `0 - 1 = 0` is false
    exfalso; norm_num at hz
  · constructor <;> intro hcon <;> [exact absurd hcon h1; exact absurd hcon h2]

end ArkLib.CodingTheory.Round9LamLeung

#print axioms ArkLib.CodingTheory.Round9LamLeung.antipodal_invariant_of_vanishing_sum
