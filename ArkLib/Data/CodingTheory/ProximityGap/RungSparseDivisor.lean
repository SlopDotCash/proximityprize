/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Sparse divisors of `Xⁿ − 1` are few (#371/#389 prize, Mann lead)

The formalizable structural heart of the Johnson-scale fiber collapse
(`probe_prize_johnsonfiber`/`fiberstruct`): the maximally-sparse (binomial)
divisors `Xᵃ − c` of `Xⁿ − 1` take at most `n` values of `c`.  This is the
Mann-extremal case (deepest over-determination `e₁=…=e_{a-1}=0`), where the
explainable fiber is forced to coset structure; the count `≤ n` is the
polynomial bound the prize's positive direction needs.

Mechanism: every root `r` of a divisor `Xᵃ − c` of `Xⁿ − 1` satisfies `rⁿ = 1`
and `c = rᵃ`, so each valid `c` is an `a`-th power of an `n`-th root of unity.
The valid `c`'s inject into `{rᵃ : r root of Xⁿ−1}` (≤ n elements).
-/

open Polynomial

namespace ProximityGap.PrizeWorkbench

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- A root `r` of `Xᵃ − C c` has `rᵃ = c`. -/
theorem sparse_divisor_root_pow {a : ℕ} {c r : F}
    (hr : (X ^ a - C c).IsRoot r) : r ^ a = c := by
  rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hr
  exact hr

open Classical in
/-- **Sparse divisors are few.**  Given a finset `rootsN` that supplies, for
each binomial divisor `Xᵃ − C c` of `Xⁿ − 1`, a root `r ∈ rootsN` of that
divisor (e.g. `rootsN =` the roots of `Xⁿ − 1` when it splits — the
smooth-domain setting), the number of distinct values `c` with
`(Xᵃ − C c) ∣ (Xⁿ − 1)` is at most `#rootsN`. -/
theorem sparse_divisors_card_le {n a : ℕ} (rootsN : Finset F)
    (hsplit : ∀ c : F, (X ^ a - C c) ∣ (X ^ n - C 1) →
      ∃ r ∈ rootsN, (X ^ a - C c).IsRoot r) :
    (Finset.univ.filter
      (fun c : F => (X ^ a - C c) ∣ (X ^ n - C 1))).card ≤ rootsN.card := by
  classical
  have hsub : Finset.univ.filter (fun c : F => (X ^ a - C c) ∣ (X ^ n - C 1))
      ⊆ rootsN.image (· ^ a) := by
    intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨r, hr, hroot⟩ := hsplit c hc.2
    rw [Finset.mem_image]
    exact ⟨r, hr, sparse_divisor_root_pow hroot⟩
  calc (Finset.univ.filter
          (fun c : F => (X ^ a - C c) ∣ (X ^ n - C 1))).card
      ≤ (rootsN.image (· ^ a)).card := Finset.card_le_card hsub
    _ ≤ rootsN.card := Finset.card_image_le

open Classical in
/-- **The polynomial count.**  When `Xⁿ − 1 ≠ 0` (`n ≥ 1` in a field), its
root finset has at most `n` elements, so the sparse divisors number `≤ n`. -/
theorem sparse_divisors_card_le_n {n a : ℕ} (hn : 0 < n)
    (rootsN : Finset F)
    (hrootsN : rootsN = (X ^ n - C 1 : F[X]).roots.toFinset)
    (hsplit : ∀ c : F, (X ^ a - C c) ∣ (X ^ n - C 1) →
      ∃ r ∈ rootsN, (X ^ a - C c).IsRoot r) :
    (Finset.univ.filter
      (fun c : F => (X ^ a - C c) ∣ (X ^ n - C 1))).card ≤ n := by
  classical
  have hdeg : (X ^ n - C (1 : F)).natDegree = n := natDegree_X_pow_sub_C
  have hcard : rootsN.card ≤ n := by
    rw [hrootsN]
    calc (X ^ n - C 1 : F[X]).roots.toFinset.card
        ≤ Multiset.card (X ^ n - C 1 : F[X]).roots := Multiset.toFinset_card_le _
      _ ≤ (X ^ n - C 1 : F[X]).natDegree := card_roots' _
      _ = n := hdeg
  exact le_trans (sparse_divisors_card_le rootsN hsplit) hcard

end ProximityGap.PrizeWorkbench

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PrizeWorkbench.sparse_divisor_root_pow
#print axioms ProximityGap.PrizeWorkbench.sparse_divisors_card_le
#print axioms ProximityGap.PrizeWorkbench.sparse_divisors_card_le_n
