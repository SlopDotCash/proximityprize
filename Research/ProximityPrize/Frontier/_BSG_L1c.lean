/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Abel

/-!
# BSG Lemma L1c: Cauchy–Schwarz packaging on the difference side

`#A ^ 4 ≤ E[A] * #(A - A)`.

This is the difference-set analogue of Mathlib's `le_card_add_mul_addEnergy`
(`#A ^ 2 * #A ^ 2 ≤ #(A + A) * E[A]`). It is obtained by applying the Mathlib lemma to the pair
`(A, -A)`, using:

* `A + (-A) = A - A` (pointwise);
* `E[A, -A] = E[A]` (negating one coordinate set is a bijection of the energy quadruples,
  combined with swapping the two `b`-coordinates);
* `#(-A) = #A`.
-/

open Finset
open scoped BigOperators Pointwise Combinatorics.Additive

namespace Finset

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-- Additive energy is invariant under negating the second set: `E[A, -B] = E[A, B]`.

The map `((a₁, a₂), (b₁, b₂)) ↦ ((a₁, a₂), (-b₂, -b₁))` is an involution of the defining
quadruples: it negates the `b`-coordinates (turning `-B`-membership into `B`-membership) and swaps
them, so the energy relation `a₁ + b₁ = a₂ + b₂` becomes `a₁ + (-b₂) = a₂ + (-b₁)`. -/
lemma addEnergy_neg_right (A B : Finset α) :
    E[A, -B] = E[A, B] := by
  classical
  unfold Finset.addEnergy
  refine Finset.card_nbij'
    (fun x => ((x.1.1, x.1.2), (-x.2.2, -x.2.1)))
    (fun x => ((x.1.1, x.1.2), (-x.2.2, -x.2.1))) ?_ ?_ ?_ ?_
  · rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq,
      mem_product, Finset.mem_neg'] at hx ⊢
    refine ⟨⟨⟨hx.1.1.1, hx.1.1.2⟩, ?_, ?_⟩, ?_⟩
    · simpa using hx.1.2.2
    · simpa using hx.1.2.1
    · have h := hx.2
      have ha₁ : a₁ = a₂ + b₂ - b₁ := by rw [← h]; abel
      rw [ha₁]; abel
  · rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq,
      mem_product, Finset.mem_neg'] at hx ⊢
    refine ⟨⟨⟨hx.1.1.1, hx.1.1.2⟩, ?_, ?_⟩, ?_⟩
    · simpa using hx.1.2.2
    · simpa using hx.1.2.1
    · have h := hx.2
      have ha₁ : a₁ = a₂ + b₂ - b₁ := by rw [← h]; abel
      rw [ha₁]; abel
  · rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ _; simp
  · rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ _; simp

/-- The pointwise sumset of `A` with `-A` is the difference set. -/
lemma add_neg_eq_sub (A : Finset α) : A + (-A) = A - A := by
  ext x
  simp only [mem_add, mem_sub, mem_neg]
  constructor
  · rintro ⟨a, ha, b, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨a, ha, c, hc, by abel⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, -b, ⟨b, hb, rfl⟩, by abel⟩

/-- **BSG Lemma L1c (Cauchy–Schwarz on the difference side).**
`#A ^ 4 ≤ E[A] * #(A - A)`.

Equivalently `(∑_x r(x))² ≤ #(A - A) · ∑_x r(x)²`, where `r(x)` counts representations of `x` as a
difference of two elements of `A`; the left side is `#A²·#A² = #A⁴` and the right is
`#(A - A)·E[A]`. -/
theorem card_sq_le_addEnergy_mul_card_diff (A : Finset α) :
    (#A : ℚ) ^ 4 ≤ E[A] * #(A - A) := by
  have hbase : #A ^ 2 * #(-A) ^ 2 ≤ #(A + (-A)) * E[A, -A] :=
    le_card_add_mul_addEnergy A (-A)
  rw [addEnergy_neg_right, add_neg_eq_sub, Finset.card_neg] at hbase
  -- `hbase : #A ^ 2 * #A ^ 2 ≤ #(A - A) * E[A]` over ℕ; cast to ℚ.
  have hcast : ((#A : ℚ) ^ 2 * (#A : ℚ) ^ 2) ≤ (#(A - A) : ℚ) * (E[A] : ℚ) := by
    exact_mod_cast hbase
  calc (#A : ℚ) ^ 4 = (#A : ℚ) ^ 2 * (#A : ℚ) ^ 2 := by ring
    _ ≤ (#(A - A) : ℚ) * (E[A] : ℚ) := hcast
    _ = (E[A] : ℚ) * (#(A - A) : ℚ) := by ring

end Finset

-- Axiom audit (expected: propext, Classical.choice, Quot.sound)
#print axioms Finset.addEnergy_neg_right
#print axioms Finset.add_neg_eq_sub
#print axioms Finset.card_sq_le_addEnergy_mul_card_diff
