/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# The multinomial chain rule — the `prefactor_eq_paper` reconciliation (BCIKS20 A.1)

The combinatorial reconciliation gating the final P2 residual
(`coeff_succ_eval_βHenselAssembled` in `HenselNumerator.lean`): the paper's (A.1)
coefficient `(j; j₀, λ₁, …, λ_l)` (full multinomial including the `α₀`-slot `j₀`)
factors as

  `(j; j₀, λ₁, …, λ_l) = C(j, Σλ) · (Σλ; λ₁, …, λ_l)`,   `j = j₀ + Σλ`,

where `C(j, Σλ)` is exactly the weight the iterated Hasse derivative intrinsically
carries (inside `B_coeff`/`hasseCoeffRepr𝒪`), and `(Σλ; λ₁, …, λ_l)` is exactly the
in-tree `Nat.multinomial lam.parts.toFinset (lam.parts.count ·)` used by `prefactor`.
Numerically validated on all small cases (orchestrator, 2026-06-05); here it is proven
in full generality from mathlib's `Nat.multinomial_insert` + `Nat.choose_symm_add`.

The `j₀`-slot is kept type-disjoint from the part-value slots via `Option ℕ`
(`none` = the `α₀`-slot, `some l` = the part-size-`l` slot), avoiding any collision
between `j₀` and a part value.
-/

namespace ProximityPrize.MultinomialChainRule

open Finset

/-- **Injective reindexing of `Nat.multinomial`.** The multinomial is invariant under an
injective relabeling of the index set (sum and factorial-product both transport). -/
theorem multinomial_map {α β : Type*} (s : Finset α) (e : α ↪ β) (f : β → ℕ) :
    Nat.multinomial (s.map e) f = Nat.multinomial s (f ∘ e) := by
  unfold Nat.multinomial
  rw [Finset.sum_map, Finset.prod_map]
  rfl

/-- **The chain rule / `prefactor_eq_paper` reconciliation (abstract form).**
For a fresh slot of weight `j₀` adjoined to a finite family of slot-weights `f` on `s`:

  `multinomial (j₀-slot ∪ s) = C(j₀ + Σf, Σf) · multinomial s f`.

With `s` = the distinct part sizes of a partition `λ` and `f` = their multiplicities
(`Σf = Σλ`), this is exactly `(j; j₀, λ) = C(j, Σλ)·(Σλ; λ)`. -/
theorem multinomial_option_insert {α : Type*} [DecidableEq α]
    (s : Finset α) (j₀ : ℕ) (f : α → ℕ) :
    Nat.multinomial (insert (none : Option α) (s.map ⟨some, Option.some_injective α⟩))
        (fun o => o.elim j₀ f)
      = Nat.choose (j₀ + ∑ a ∈ s, f a) (∑ a ∈ s, f a)
        * Nat.multinomial s f := by
  have hnone : (none : Option α) ∉ s.map ⟨some, Option.some_injective α⟩ := by
    simp
  rw [Nat.multinomial_insert hnone]
  have hsum : ∑ o ∈ s.map ⟨some, Option.some_injective α⟩, (fun o => o.elim j₀ f) o
      = ∑ a ∈ s, f a := by
    rw [Finset.sum_map]; rfl
  have hmap : Nat.multinomial (s.map ⟨some, Option.some_injective α⟩)
      (fun o => o.elim j₀ f) = Nat.multinomial s f := by
    rw [multinomial_map]; rfl
  rw [hsum, hmap]
  -- `(j₀ + Σ).choose j₀ = (j₀ + Σ).choose Σ`
  simp only [Option.elim]
  rw [Nat.choose_symm_add]

/-- **Specialisation to a `Nat.Partition`** — the literal `prefactor_eq_paper` shape:
`(j₀ + Σλ; j₀, λ₁, …) = C(j₀ + Σλ, Σλ) · (Σλ; λ₁, …)` with `Σλ = lam.parts.card`
(`∑ count = card`) and the in-tree multiplicities `lam.parts.count`. -/
theorem prefactor_paper_factorization {m : ℕ} (j₀ : ℕ) (lam : Nat.Partition m) :
    Nat.multinomial
        (insert (none : Option ℕ) (lam.parts.toFinset.map ⟨some, Option.some_injective ℕ⟩))
        (fun o => o.elim j₀ (fun l => lam.parts.count l))
      = Nat.choose (j₀ + lam.parts.card) lam.parts.card
        * Nat.multinomial lam.parts.toFinset (fun l => lam.parts.count l) := by
  have hcard : ∑ l ∈ lam.parts.toFinset, lam.parts.count l = lam.parts.card :=
    Multiset.toFinset_sum_count_eq lam.parts
  rw [multinomial_option_insert, hcard]

/-- Numeric witness (kernel-checked, non-vacuity): partition `[1,1]` of `2`, `j₀ = 2`:
`(4; 2,2) = 6 = C(4,2)·(2;2) = 6·1`. (The slot multiset is `{j₀=2, count(1)=2}`.) -/
example :
    Nat.multinomial ({none, some 1} : Finset (Option ℕ))
        (fun o => o.elim 2 (fun _ => 2)) = 6 := by decide

example : Nat.choose 4 2 * Nat.multinomial ({1} : Finset ℕ) (fun _ => 2) = 6 := by decide


/-! ## The W/ξ exponent telescoping inputs (pure partition arithmetic)

The cleared-defect identity's exponent bookkeeping: assembling the product
`∏_{l ∈ parts} (coefficient l)` of the truncated series, each factor carries a
`W^{l+1}` (and `ξ^{e_l}`) denominator; the total `W`-exponent over a partition `λ ⊢ m`
is `∑_{l ∈ parts} (l+1) = m + Σλ` — the sum of the parts plus their number. -/

/-- `∑_{l ∈ λ.parts} (l + 1) = m + Σλ` for a partition `λ ⊢ m`: the `W`-power telescope. -/
theorem partition_sum_add_one {m : ℕ} (lam : Nat.Partition m) :
    (lam.parts.map (· + 1)).sum = m + lam.parts.card := by
  rw [Multiset.sum_map_add]
  simp [lam.parts_sum, Multiset.map_id']

/-- General multiset form: over positive entries, `∑ (2l − 1) + #s = 2·∑ l`. -/
theorem multiset_sum_two_mul_sub_one (s : Multiset ℕ) (hpos : ∀ l ∈ s, 1 ≤ l) :
    (s.map (fun l => 2 * l - 1)).sum + Multiset.card s = 2 * s.sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
      have ha : 1 ≤ a := hpos a (Multiset.mem_cons_self a t)
      have ht : ∀ l ∈ t, 1 ≤ l := fun l hl => hpos l (Multiset.mem_cons_of_mem hl)
      have iht := ih ht
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Multiset.sum_cons]
      omega

theorem partition_sum_two_mul_sub_one {m : ℕ} (lam : Nat.Partition m) :
    (lam.parts.map (fun l => 2 * l - 1)).sum + Multiset.card lam.parts = 2 * m := by
  rw [multiset_sum_two_mul_sub_one lam.parts (fun l hl => lam.parts_pos hl), lam.parts_sum]

end ProximityPrize.MultinomialChainRule
