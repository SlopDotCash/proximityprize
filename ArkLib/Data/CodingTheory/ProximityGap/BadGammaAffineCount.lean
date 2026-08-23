/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.LinearCombination

/-!
# Bad-scalar counting for affine error lines (UDR MCA upper bound engine, #232)

The unique-decoding-regime upper bound `ε_mca(C, δ) ≤ O(δn)/|F|` (ABF26 Table-1, row 2,
[ACFY25],[BCIKS20]) hinges on the following purely combinatorial fact. After subtracting the
nearby codewords `c₀, c₁` of `u₀, u₁` (which exist and are unique below the unique-decoding radius),
a "bad" scalar `γ` makes the affine error word `e₀ + γ·e₁` (with `e₀ = u₀ − c₀`, `e₁ = u₁ − c₁`)
vanish at some coordinate `i` where `e₁ i ≠ 0`. At such a coordinate `γ = −e₀ i / e₁ i` is the
*unique* root, so distinct bad scalars require distinct coordinates:

  `#{γ : ∃ i, e₁ i ≠ 0 ∧ e₀ i + γ·e₁ i = 0}  ≤  weight(e₁)`     (`badGamma_affine_card_le`).

Since `weight(e₁) ≤ 2δn` below the unique-decoding radius, the per-stack bad-scalar count is
`O(δn)`, giving `ε_mca ≤ O(δn)/|F|`. This file proves the counting engine; wiring it to `mcaEvent`
via the minimum-distance codeword extraction is the remaining (min-distance) step.

The result is hole-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
- [ACFY25] WHIR; [BCIKS20] Proximity gaps for Reed–Solomon codes.
-/

namespace CodingTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- **Bad-scalar counting on an affine error line.** The scalars `γ` for which `e₀ + γ·e₁` vanishes
at some coordinate where `e₁ ≠ 0` number at most the Hamming weight of `e₁`. Each such `γ` equals
the unique root `−e₀ i / e₁ i`; distinct `γ` force distinct support coordinates. -/
theorem badGamma_affine_card_le (e₀ e₁ : ι → F) :
    (Finset.univ.filter
        (fun γ : F => ∃ i, e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0)).card
      ≤ (Finset.univ.filter (fun i => e₁ i ≠ 0)).card := by
  apply Finset.card_le_card_of_injOn
    (fun γ => if h : ∃ i, e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0 then h.choose else Classical.arbitrary ι)
  · intro γ hγ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hγ
    have hspec := hγ.choose_spec
    simp only [dif_pos hγ, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact hspec.1
  · intro γ₁ hγ₁ γ₂ hγ₂ heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hγ₁ hγ₂
    simp only [dif_pos hγ₁, dif_pos hγ₂] at heq
    have h1 := hγ₁.choose_spec
    have h2 := hγ₂.choose_spec
    rw [← heq] at h2
    have he : γ₁ * e₁ hγ₁.choose = γ₂ * e₁ hγ₁.choose := by linear_combination h1.2 - h2.2
    exact mul_right_cancel₀ h1.1 he

#print axioms badGamma_affine_card_le

end CodingTheory
