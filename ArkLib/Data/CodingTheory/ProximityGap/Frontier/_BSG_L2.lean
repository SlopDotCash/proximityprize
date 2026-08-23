/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# BSG L2 — popular *differences* carry half the energy (rational threshold)

This scratch file develops the **difference-representation** form of the popular-pair averaging
lemma used in the Balog–Szemerédi–Gowers argument, with a *rational* threshold `#A / (2 K)`.

* `repCount A x` — `#{(a, b) ∈ A × A : a - b = x}`, the difference-representation count.
* `repCount_sum_eq_card_sq` (L1a) — `∑_{x ∈ A - A} repCount A x = #A ^ 2`.
* `addEnergy_eq_sum_repCount_sq` (L1b) — `E[A] = ∑_{x ∈ A - A} repCount A x ^ 2`.
* `popularDiffs A K` — `{x ∈ A - A | #A / (2 K) ≤ repCount A x}`.
* `popular_carries_half_energy` (**L2**) — under `#A ^ 3 / K ≤ E[A]` and `1 ≤ K`,
  `E[A] / 2 ≤ ∑_{x ∈ popularDiffs A K} repCount A x ^ 2`.
-/

open Finset
open scoped BigOperators Pointwise Combinatorics.Additive

namespace Finset

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-- The **difference-representation count** of `x` in `A`: the number of ordered pairs
`(a, b) ∈ A × A` with `a - b = x`. -/
noncomputable def repCount (A : Finset α) (x : α) : ℕ :=
  #{p ∈ A ×ˢ A | p.1 - p.2 = x}

lemma repCount_def (A : Finset α) (x : α) :
    repCount A x = #{p ∈ A ×ˢ A | p.1 - p.2 = x} := rfl

/-- The total difference-representation count over `A - A` is `#A ^ 2`: every ordered pair has one
difference, which lies in `A - A`. -/
lemma repCount_sum_eq_card_sq (A : Finset α) :
    ∑ x ∈ A - A, repCount A x = #A ^ 2 := by
  classical
  simp_rw [repCount]
  rw [sq, ← card_product A A]
  refine (Finset.card_eq_sum_card_fiberwise (f := fun p : α × α => p.1 - p.2)
    (s := A ×ˢ A) (t := A - A) ?_).symm
  rintro ⟨a, b⟩ hp
  have hp' := Finset.mem_product.1 hp
  exact sub_mem_sub hp'.1 hp'.2

/-- **Energy as the sum of squared difference-representation counts.**
`E[A] = ∑_{x ∈ A - A} repCount A x ^ 2`.

Proof: `E[A]` counts quadruples `(a₁, a₂, b₁, b₂) ∈ A⁴` with `a₁ + b₁ = a₂ + b₂`, i.e.
`a₁ - a₂ = b₂ - b₁`.  The energy filter is the disjoint union over `x ∈ A - A` of the products
`F(x) ×ˢ F(x)` where `F(x) = {(a, a') ∈ A × A : a - a' = x}` has card `repCount A x`, via the
bijection `((a₁, a₂), (b₁, b₂)) ↦ ((a₁, a₂), (b₂, b₁))`. -/
lemma addEnergy_eq_sum_repCount_sq (A : Finset α) :
    E[A] = ∑ x ∈ A - A, repCount A x ^ 2 := by
  classical
  -- `∑_x repCount A x ^ 2 = ∑_x #(F x ×ˢ F x) = #(disjiUnion ...)`, then biject with the energy set.
  have hrw : (∑ x ∈ A - A, repCount A x ^ 2)
      = ∑ x ∈ A - A, #(({p ∈ A ×ˢ A | p.1 - p.2 = x}) ×ˢ ({q ∈ A ×ˢ A | q.1 - q.2 = x})) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [repCount, sq, ← card_product]
  rw [hrw, ← card_disjiUnion _ _ (by
        intro d₁ _ d₂ _ hne
        rw [Function.onFun, disjoint_left]
        rintro ⟨⟨a₁, a₂⟩, ⟨b₂, b₁⟩⟩ h1 h2
        simp only [mem_product, mem_filter] at h1 h2
        exact hne (h1.1.2 ▸ h2.1.2))]
  rw [addEnergy]
  -- Bijection between the energy filter and the disjoint union of fiber-products.  Both sets live in
  -- `(α × α) × (α × α)`; the (self-inverse) map swaps the two second coordinates.
  refine card_nbij'
    (fun x : (α × α) × (α × α) => ((x.1.1, x.1.2), (x.2.2, x.2.1)))
    (fun y : (α × α) × (α × α) => ((y.1.1, y.1.2), (y.2.2, y.2.1)))
    ?_ ?_ ?_ ?_
  · rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ h
    simp only [mem_coe, mem_filter, mem_product] at h
    obtain ⟨⟨⟨ha₁, ha₂⟩, hb₁, hb₂⟩, hrel⟩ := h
    simp only [mem_coe, mem_disjiUnion, mem_product, mem_filter]
    refine ⟨a₁ - a₂, sub_mem_sub ha₁ ha₂, ⟨⟨ha₁, ha₂⟩, rfl⟩, ⟨hb₂, hb₁⟩, ?_⟩
    -- `a₁ + b₁ = a₂ + b₂ ⟹ b₂ - b₁ = a₁ - a₂`
    rw [sub_eq_sub_iff_add_eq_add, hrel, add_comm]
  · rintro ⟨⟨a₁, a₂⟩, ⟨b₂, b₁⟩⟩ h
    simp only [mem_coe, mem_disjiUnion, mem_product, mem_filter] at h
    obtain ⟨d, _hd, ⟨⟨ha₁, ha₂⟩, hpd⟩, ⟨hb₂, hb₁⟩, hqd⟩ := h
    simp only [mem_coe, mem_filter, mem_product]
    refine ⟨⟨⟨ha₁, ha₂⟩, hb₁, hb₂⟩, ?_⟩
    -- `a₁ - a₂ = d = b₂ - b₁ ⟹ a₁ + b₁ = a₂ + b₂`
    have heq : a₁ - a₂ = b₂ - b₁ := by rw [hpd, hqd]
    rw [sub_eq_sub_iff_add_eq_add, add_comm b₂ a₂] at heq
    exact heq
  · rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ _
    rfl
  · rintro ⟨⟨a₁, a₂⟩, ⟨b₂, b₁⟩⟩ _
    rfl

/-- The **popular differences** of `A` at level `K`: those `x ∈ A - A` whose difference-
representation count is at least `#A / (2 K)`. -/
noncomputable def popularDiffs (A : Finset α) (K : ℚ) : Finset α :=
  {x ∈ A - A | (#A : ℚ) / (2 * K) ≤ (repCount A x : ℚ)}

/-- **L2 — popular differences carry half the energy.** Under `#A ^ 3 / K ≤ E[A]` (with `1 ≤ K`),
the popular differences (those with `repCount ≥ #A / (2 K)`) carry at least half the energy:
`E[A] / 2 ≤ ∑_{x popular} repCount A x ^ 2`. -/
theorem popular_carries_half_energy (A : Finset α) (K : ℚ) (hK : 1 ≤ K)
    (hE : (#A : ℚ) ^ 3 / K ≤ Finset.addEnergy A A) :
    (Finset.addEnergy A A : ℚ) / 2 ≤ ∑ x ∈ popularDiffs A K, (repCount A x : ℚ) ^ 2 := by
  classical
  have hKpos : (0 : ℚ) < K := lt_of_lt_of_le one_pos hK
  set θ : ℚ := (#A : ℚ) / (2 * K) with hθdef
  -- Cast the energy identity into ℚ.
  have hEsum : (Finset.addEnergy A A : ℚ)
      = ∑ x ∈ A - A, ((repCount A x : ℚ)) ^ 2 := by
    rw [addEnergy_eq_sum_repCount_sq]
    push_cast
    rfl
  -- Split `A - A` into popular `P` / unpopular `Q`.
  set P : Finset α := popularDiffs A K with hP
  set Q : Finset α := {x ∈ A - A | ¬ θ ≤ (repCount A x : ℚ)} with hQ
  have hsplit : (∑ x ∈ A - A, ((repCount A x : ℚ)) ^ 2)
      = (∑ x ∈ P, ((repCount A x : ℚ)) ^ 2) + ∑ x ∈ Q, ((repCount A x : ℚ)) ^ 2 := by
    rw [hP, popularDiffs, hQ]
    exact (Finset.sum_filter_add_sum_filter_not (A - A) (fun x => θ ≤ (repCount A x : ℚ)) _).symm
  -- Bound the unpopular energy `∑_Q repCount² ≤ θ * #A²`.
  have hQ_bound : (∑ x ∈ Q, ((repCount A x : ℚ)) ^ 2) ≤ θ * (#A : ℚ) ^ 2 := by
    have hsub : Q ⊆ A - A := by rw [hQ]; exact Finset.filter_subset _ _
    calc ∑ x ∈ Q, ((repCount A x : ℚ)) ^ 2
        ≤ ∑ x ∈ Q, θ * (repCount A x : ℚ) := by
          refine Finset.sum_le_sum (fun x hx => ?_)
          rw [hQ, mem_filter, not_le] at hx
          rw [sq]
          have hnn : (0 : ℚ) ≤ (repCount A x : ℚ) := Nat.cast_nonneg _
          exact mul_le_mul_of_nonneg_right (le_of_lt hx.2) hnn
      _ = θ * ∑ x ∈ Q, (repCount A x : ℚ) := by rw [Finset.mul_sum]
      _ ≤ θ * ∑ x ∈ A - A, (repCount A x : ℚ) := by
          have hθnn : (0 : ℚ) ≤ θ := by
            rw [hθdef]
            apply div_nonneg (Nat.cast_nonneg _)
            linarith [hKpos]
          apply mul_le_mul_of_nonneg_left _ hθnn
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
          intro x _ _; exact Nat.cast_nonneg _
      _ = θ * (#A : ℚ) ^ 2 := by
          rw [← Nat.cast_sum, repCount_sum_eq_card_sq]; push_cast; ring
  -- `θ * #A² = #A³ / (2K) ≤ E[A] / 2`.
  have hθcard : θ * (#A : ℚ) ^ 2 = (#A : ℚ) ^ 3 / (2 * K) := by
    rw [hθdef]; ring
  have hhalf : θ * (#A : ℚ) ^ 2 ≤ (Finset.addEnergy A A : ℚ) / 2 := by
    rw [hθcard]
    have h1 : (#A : ℚ) ^ 3 / (2 * K) = ((#A : ℚ) ^ 3 / K) / 2 := by
      rw [div_div]; ring_nf
    rw [h1]
    linarith [hE]
  -- Assemble: E = ∑_P + ∑_Q ≤ ∑_P + E/2.
  have hEeq : (Finset.addEnergy A A : ℚ)
      = (∑ x ∈ P, ((repCount A x : ℚ)) ^ 2) + ∑ x ∈ Q, ((repCount A x : ℚ)) ^ 2 := by
    rw [hEsum, hsplit]
  linarith [hEeq, hQ_bound, hhalf]

end Finset

-- Axiom audit (expected: propext, Classical.choice, Quot.sound)
#print axioms Finset.repCount_sum_eq_card_sq
#print axioms Finset.addEnergy_eq_sum_repCount_sq
#print axioms Finset.popular_carries_half_energy
