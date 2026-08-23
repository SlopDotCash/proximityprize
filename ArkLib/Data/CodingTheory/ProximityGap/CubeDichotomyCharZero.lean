/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ThreeRootsSumZeroCharZero
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The char-0 cubic dichotomy: three roots of unity sum to zero IFF `3 ∣ n` (#389)

`ThreeRootsSumZeroCharZero.lean` proved the `3 ∤ n` direction (no three `n`-th roots of unity
sum to zero).  This file lands the converse and assembles the full dichotomy over `ℂ`,
generalizing the per-prime finite-field witnesses (`CubicSupplyZeroF73`,
`CubicSupplyDichotomy`) to all `n` at once:

> **`exists_three_distinct_roots_sum_zero`** — `3 ∣ n ⟹ ∃` three distinct `n`-th roots of
> unity summing to zero (the cube roots `1, ω, ω²` with `1 + ω + ω² = 0`).
> **`three_roots_sum_zero_iff`** — for `n ≠ 0`: three distinct `n`-th roots of unity sum to
> zero **iff `3 ∣ n`**.

Via the cubic orchard identity (`cubic_list_eq_zeroSum`), this is the exact char-0
characterization of the deepest-band (sub-Johnson, agreement-3) supply of the word `x³`:
zero precisely when `3 ∤ n`.  It is the characteristic-zero truth whose finite-field lift
(prime-arithmetic, Mann–Conway–Jones) is witnessed concretely in the `F_p` files.
Issue #389.
-/

open Complex
namespace ProximityGap.CubeDichotomy

/-- **`3 ∣ n ⟹ ∃` three distinct `n`-th roots of unity summing to zero** (the cube roots
`1, ω, ω²`).  The complement of `no_three_roots_sum_zero`. -/
theorem exists_three_distinct_roots_sum_zero {n : ℕ} (h3 : 3 ∣ n) :
    ∃ a b c : ℂ, a ^ n = 1 ∧ b ^ n = 1 ∧ c ^ n = 1 ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a + b + c = 0 := by
  obtain ⟨k, rfl⟩ := h3
  obtain ⟨ω, hω⟩ : ∃ ω : ℂ, IsPrimitiveRoot ω 3 :=
    ⟨_, Complex.isPrimitiveRoot_exp 3 (by norm_num)⟩
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hωne1 : ω ≠ 1 := hω.ne_one (by norm_num)
  -- 1 + ω + ω² = 0
  have hquad : ω ^ 2 + ω + 1 = 0 := by
    have hfac : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
      have : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
      rw [this, hω3]; ring
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (by linear_combination h : ω = 1) hωne1
    · exact h
  -- ω^n = 1 for n = 3*k
  have hωn : ∀ m : ℕ, ω ^ (3 * m) = 1 := by
    intro m; rw [pow_mul, hω3, one_pow]
  refine ⟨1, ω, ω ^ 2, by simp, hωn k, ?_, hωne1.symm, ?_, ?_, ?_⟩
  · rw [← pow_mul, show 2 * (3 * k) = 3 * (2 * k) from by ring, pow_mul, hω3, one_pow]
  · -- 1 ≠ ω²: else ω² = 1, but ord ω = 3
    intro h
    have h2 : (3 : ℕ) ∣ 2 := hω.dvd_of_pow_eq_one 2 h.symm
    norm_num at h2
  · -- ω ≠ ω²: else ω = 1 (cancel ω ≠ 0)
    intro h
    have hω0 : ω ≠ 0 := hω.ne_zero (by norm_num)
    have hz : ω * (ω - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp hz with h0 | h1
    · exact hω0 h0
    · exact hωne1 (by linear_combination h1)
  · linear_combination hquad

/-- **The char-0 cubic-supply dichotomy** (full): for `n ≥ 1`, three distinct `n`-th roots
of unity sum to zero **iff `3 ∣ n`** — `no_three_roots_sum_zero` (`3 ∤ n` direction) ⊕ the
cube-root construction (`3 ∣ n` direction). -/
theorem three_roots_sum_zero_iff {n : ℕ} (hn : n ≠ 0) :
    (∃ a b c : ℂ, a ^ n = 1 ∧ b ^ n = 1 ∧ c ^ n = 1 ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a + b + c = 0) ↔ 3 ∣ n := by
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, _, _, _, hsum⟩
    by_contra h3
    exact ProximityGap.ThreeRoots.no_three_roots_sum_zero hn h3 ha hb hc hsum
  · exact exists_three_distinct_roots_sum_zero

end ProximityGap.CubeDichotomy

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.CubeDichotomy.exists_three_distinct_roots_sum_zero
#print axioms ProximityGap.CubeDichotomy.three_roots_sum_zero_iff
