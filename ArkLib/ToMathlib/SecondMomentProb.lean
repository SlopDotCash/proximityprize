/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SqSumCardSupport

/-!
# The second-moment method in uniform-probability form (Paley–Zygmund ratio)

`Finset.sq_sum_le_card_support_mul_sum_sq` gives the raw Cauchy–Schwarz `(∑ f)² ≤ #{f ≠ 0}·∑ f²`.
This file packages it as the **uniform-probability** lower bound that list-size arguments actually
consume: over a finite uniform space, for a random variable `f`,

  `E[f]² / E[f²]  ≤  Pr[f ≠ 0]`,

equivalently `(∑ f)² / (N · ∑ f²) ≤ #{f ≠ 0} / N` with `N = |α|`. This is the form the GLMRSW22 /
random-RS list-size **lower** bounds plug into (a random structure is nonzero — a large list
exists — with probability at least the first-moment-squared over the second moment).

## Main result (`sorry`-free; axioms = `propext, Classical.choice, Quot.sound`)

* `sq_sum_div_le_card_support_div_card`.
-/

namespace ArkLib

open Finset

/-- **Second-moment method, uniform-probability form.** Over a finite nonempty type with the
uniform law, `E[f]² / E[f²] ≤ Pr[f ≠ 0]`, written `(∑ f)² / (|α|·∑ f²) ≤ #{f ≠ 0} / |α|`. -/
theorem sq_sum_div_le_card_support_div_card {α : Type*} [Fintype α] [Nonempty α]
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]
    (f : α → R) (hf2 : 0 < ∑ a, f a ^ 2) :
    (∑ a, f a) ^ 2 / ((Fintype.card α : R) * ∑ a, f a ^ 2)
      ≤ ((Finset.univ.filter (fun a => f a ≠ 0)).card : R) / (Fintype.card α : R) := by
  have hcard : (0 : R) < (Fintype.card α : R) := by
    have : 0 < Fintype.card α := Fintype.card_pos
    exact_mod_cast this
  have hbase := Finset.sq_sum_le_card_support_mul_sum_sq f
  have hB : (0:R) < (Fintype.card α : R) * ∑ a, f a ^ 2 := by positivity
  rw [div_le_iff₀ hB, div_mul_eq_mul_div, le_div_iff₀ hcard]
  calc (∑ a, f a) ^ 2 * (Fintype.card α : R)
      ≤ (((Finset.univ.filter (fun a => f a ≠ 0)).card : R) * (∑ a, f a ^ 2))
          * (Fintype.card α : R) :=
        mul_le_mul_of_nonneg_right hbase (le_of_lt hcard)
    _ = ((Finset.univ.filter (fun a => f a ≠ 0)).card : R)
          * ((Fintype.card α : R) * ∑ a, f a ^ 2) := by ring

end ArkLib

-- Axiom audit.
#print axioms ArkLib.sq_sum_div_le_card_support_div_card
