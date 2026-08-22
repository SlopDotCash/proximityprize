/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# BSG Lemma L1b: energy ↔ representation function (difference form)

`E(A) = ∑_{x ∈ A - A} r(x)²` where `r(x) = #{(a,b) ∈ A×A : a - b = x}`.

This is the hinge of the Balog–Szemerédi–Gowers proof. A quadruple
`(a₁, a₂, b₁, b₂)` with `a₁ + b₁ = a₂ + b₂` satisfies `a₁ - a₂ = b₂ - b₁`, so the
energy fibers over the common difference `x` as `r(x) · r(x) = r(x)²`.
-/

open Finset
open scoped Combinatorics.Additive Pointwise

namespace ArkLib.BSG.L1b

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-- The representation function `r(x) = #{(a, b) ∈ A × A : a - b = x}`. -/
def repCount (A : Finset α) (x : α) : ℕ := #{p ∈ A ×ˢ A | p.1 - p.2 = x}

/-- L1b: additive energy equals the sum of squares of the representation function over
differences. -/
theorem addEnergy_eq_sum_repCount_sq (A : Finset α) :
    Finset.addEnergy A A = ∑ x ∈ A - A, (repCount A x) ^ 2 := by
  -- `addEnergy A A = #{x ∈ (A×A)×(A×A) | x.1.1 + x.2.1 = x.1.2 + x.2.2}`
  rw [Finset.addEnergy]
  -- Fiber over the common difference `x.1.1 - x.1.2 ∈ A - A`.
  rw [card_eq_sum_card_fiberwise
    (f := fun x : (α × α) × (α × α) => x.1.1 - x.1.2) (t := A - A) ?maps]
  case maps =>
    intro x hx
    rw [mem_coe, mem_filter, mem_product, mem_product, mem_product] at hx
    exact sub_mem_sub hx.1.1.1 hx.1.1.2
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [sq]
  -- The fiber over `x` is a product of two `repCount`-fibers.
  simp only [repCount]
  rw [← card_product]
  -- Cardinality-preserving bijection: swap the second pair `(b₁,b₂) ↦ (b₂,b₁)`.
  apply Finset.card_nbij'
    (i := fun (q : (α × α) × (α × α)) => (q.1, (q.2.2, q.2.1)))
    (j := fun (q : (α × α) × (α × α)) => (q.1, (q.2.2, q.2.1)))
  · -- forward maps into the product
    intro q hq
    simp only [mem_coe, mem_filter, mem_product] at hq ⊢
    obtain ⟨⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, heq⟩, hfib⟩ := hq
    refine ⟨⟨⟨ha1, ha2⟩, hfib⟩, ⟨hb2, hb1⟩, ?_⟩
    -- need q.2.2 - q.2.1 = x; from a₁+b₁=a₂+b₂ and a₁-a₂=x we get b₂-b₁=x
    have hx0 : q.1.1 - q.1.2 = x := hfib
    have hb : q.2.2 - q.2.1 = x := by
      rw [← hx0, sub_eq_sub_iff_add_eq_add]
      -- goal: q.2.2 + q.1.2 = q.1.1 + q.2.1
      rw [add_comm q.2.2 q.1.2]
      exact heq.symm
    exact hb
  · -- backward maps into the product (the energy fiber)
    intro q hq
    simp only [mem_coe, mem_filter, mem_product] at hq ⊢
    obtain ⟨⟨⟨ha1, ha2⟩, hfib⟩, ⟨hb2, hb1⟩, hb⟩ := hq
    refine ⟨⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, ?_⟩, hfib⟩
    -- need q.1.1 + q.2.2 = q.1.2 + q.2.1
    -- hfib : q.1.1 - q.1.2 = x,  hb : q.2.1 - q.2.2 = x
    rw [← hfib] at hb
    rw [sub_eq_sub_iff_add_eq_add] at hb
    -- hb : q.2.1 + q.1.2 = q.1.1 + q.2.2
    rw [add_comm q.1.2 q.2.1]
    exact hb.symm
  · intro q _; simp
  · intro q _; simp

end ArkLib.BSG.L1b
