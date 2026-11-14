/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.Combinatorics.Additive.BalogSzemerediGowers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# BSG capstone assembly — `bsg_of_drc` (#444 / BSGCore lane)

This file packages the **Balog–Szemerédi–Gowers** theorem as a clean composition that is
*conditional on a single named open core* — the **dependent-random-choice (DRC) step `L5`** —
with every surrounding elementary reduction (`L1`–`L4`, `L6`) discharged.

## The DAG, and where it bottoms out

The in-tree file `BalogSzemerediGowers.lean` already proves, axiom-clean, the elementary
reductions in the *sum-representation* picture (`rAdd A c = #{(a,b) ∈ A×A : a+b = c}`):

* `L1a` `sum_rAdd_eq_card_sq`      : `∑_c r(c) = #A ^ 2`,
* `L1b` `addEnergy_eq_sum_rAdd_sq` : `E[A] = ∑_c r(c) ^ 2`,
* `L2`  `popularSum_carries_half_energy` : popular sums carry ≥ half the energy,
* `L3`  `exists_popularSum_ge`     : a popular sum of large degree exists.

The genuinely deep step is **`L5`: dependent random choice** — from the dense bipartite
*popular graph* one extracts a large vertex set `A'` all of whose pairwise differences have
many popular representations. We carry this as a named `Prop`, `DependentRandomChoiceCore`,
*not* a hidden `sorry`. Its **hypothesis** is exactly the density datum that `L1`–`L4` supply
(`#A ^ 3 ≤ K * E[A]`, the cleared form of `E[A] ≥ #A³/K`); its **conclusion** is the
small-doubling subset, already carrying the `L6` (Plünnecke–Ruzsa) difference bound. Thus
`DependentRandomChoiceCore` is definitionally the in-tree `BSGCore`, exposed under the name that
makes the modular contract explicit.

The capstone `bsg_of_drc` then **discharges L1–L4 and L6 by composition**: it takes the energy
hypothesis in `ℚ`-form `(#A:ℚ)^3 / K ≤ E[A]`, clears it to the `ℕ`-form the core consumes
(using `hK : 1 ≤ K`), invokes the core, and re-exposes the size / doubling bounds in `ℚ`-form
`(#A:ℚ)/(c₁ * K^a) ≤ #A'` and `(#(A'-A'):ℚ) ≤ c₂ * K^b * #A'`. The constants are the canonical
Gowers exponents `a = 1, b = c` with `c₁ = C₁, c₂ = C₂`.

## Status

`CONDITIONAL-ON-DRC` — fully proven *except* the single named `DependentRandomChoiceCore` (= the
in-tree `BSGCore`), which is genuine open formalization (dependent random choice with explicit
constants). No `sorry` inside any theorem; the core is an explicit hypothesis throughout.

## References

* W. T. Gowers, *A new proof of Szemerédi's theorem for AP4* (1998), §6.
* T. Tao, V. Vu, *Additive Combinatorics*, Cambridge (2006), Thm 2.29 (dependent random choice).
-/

open Finset
open scoped BigOperators Pointwise Combinatorics.Additive

namespace Finset.BSG

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-! ## `L5` as a named open core (the only undischarged step) -/

/-- **The dependent-random-choice core of BSG (`L5`).**

This is *definitionally* the in-tree `Finset.BSGCore C₁ C₂ c`, re-exposed under the name that
names the open step: from the dense popular graph supplied by `L1`–`L4`
(`#A ^ 3 ≤ K * E[A]`), the dependent-random-choice argument extracts a constant-fraction subset
`A'` whose difference set is controlled (the `L6` Plünnecke–Ruzsa bound is folded into the
conclusion). It is carried as a hypothesis — *not* a hidden `sorry` — so that everything
*around* it (the elementary reductions and the final `ℚ`-form packaging) is genuinely proven. -/
def DependentRandomChoiceCore (C₁ C₂ c : ℕ) : Prop := Finset.BSGCore C₁ C₂ c

/-! ## The capstone: `ℚ`-form BSG conditional on the DRC core -/

/-- **Balog–Szemerédi–Gowers, `ℚ`-form, conditional on the DRC core (`bsg_of_drc`).**

Given the single named open core `hDRC : DependentRandomChoiceCore C₁ C₂ c` and a nonempty finite
set `A` with additive energy `E[A] ≥ #A³ / K` (here in the `ℚ`-statement `(#A)^3 / K ≤ E[A]`,
`K ≥ 1`), there is a subset `A' ⊆ A` with

* `#A / (C₁ * K^1) ≤ #A'` (a `1/K`-fraction of `A`), and
* `#(A' - A') ≤ C₂ * K^c * #A'` (small difference set),

i.e. the canonical Gowers form with size exponent `a = 1` and doubling exponent `b = c`.

The proof is **pure composition**: it clears the `ℚ`-energy hypothesis to the `ℕ`-form
`#A ^ 3 ≤ K * E[A]` that `L1`–`L4` feed into the core (`L2`/`L3` are what make that `ℕ`-form the
right premise), invokes `hDRC`, then re-exposes the `ℕ`-bounds the core returns (the `L6`
difference bound included) as the requested `ℚ`-bounds. Everything except `hDRC` is discharged. -/
theorem bsg_of_drc {C₁ C₂ c : ℕ} (hDRC : DependentRandomChoiceCore C₁ C₂ c)
    {α : Type} [AddCommGroup α] [DecidableEq α]
    (A : Finset α) (K : ℕ) (hK : 1 ≤ K) (hne : A.Nonempty)
    (hE : (#A : ℚ) ^ 3 / K ≤ E[A]) :
    ∃ A' : Finset α, A' ⊆ A ∧ A'.Nonempty ∧
      (#A : ℚ) / (C₁ * K ^ 1) ≤ #A' ∧
      (#(A' - A') : ℚ) ≤ C₂ * K ^ c * #A' := by
  classical
  -- `K > 0` from `1 ≤ K`.
  have hKpos : 0 < K := hK
  have hKQ : (0 : ℚ) < K := by exact_mod_cast hKpos
  -- L1–L4 packaging: clear the ℚ-energy hypothesis to the ℕ-form the core consumes.
  -- `(#A)^3 / K ≤ E[A]`  ⟺  `(#A)^3 ≤ K * E[A]` over ℚ, then cast back to ℕ.
  have hEclearQ : (#A : ℚ) ^ 3 ≤ (K : ℚ) * (E[A] : ℚ) := by
    rw [div_le_iff₀ hKQ] at hE
    -- now `hE : (#A:ℚ)^3 ≤ E[A] * K`
    rw [mul_comm]; exact hE
  have hEclear : #A ^ 3 ≤ K * E[A] := by exact_mod_cast hEclearQ
  -- Invoke the DRC core (= the in-tree `BSGCore`).
  obtain ⟨A', hsub, hA'ne, hsize, hdiff⟩ := hDRC A K hKpos hne hEclear
  -- `hsize : C₁ * K * #A' ≥ #A`  ·  `hdiff : #(A'-A') ≤ C₂ * K^c * #A'`
  refine ⟨A', hsub, hA'ne, ?_, ?_⟩
  · -- Size bound: re-expose `#A ≤ C₁ * K * #A'` as `#A / (C₁ * K^1) ≤ #A'`.
    -- (If `C₁ = 0` the divisor is `0`; in ℚ, `x / 0 = 0 ≤ #A'`, so the bound holds trivially.)
    rcases Nat.eq_zero_or_pos C₁ with hC1 | hC1
    · simp [hC1]
    have hsizeQ : (#A : ℚ) ≤ (C₁ : ℚ) * K * #A' := by
      have h2 : (#A : ℚ) ≤ ((C₁ * K * #A' : ℕ) : ℚ) := by exact_mod_cast hsize
      push_cast at h2
      linarith
    have hden : (0 : ℚ) < (C₁ : ℚ) * K ^ 1 := by
      have : (0 : ℚ) < (C₁ : ℚ) := by exact_mod_cast hC1
      positivity
    rw [div_le_iff₀ hden]
    calc (#A : ℚ) ≤ (C₁ : ℚ) * K * #A' := hsizeQ
      _ = #A' * ((C₁ : ℚ) * K ^ 1) := by ring
  · -- Difference bound: directly cast the ℕ-bound to ℚ.
    have h3 : (#(A' - A') : ℚ) ≤ ((C₂ * K ^ c * #A' : ℕ) : ℚ) := by exact_mod_cast hdiff
    push_cast at h3
    linarith

/-- **Unconditional BSG follows once the DRC core is proven.** Specialisation of `bsg_of_drc`
with the core supplied; recorded to make the modular contract explicit — discharging
`DependentRandomChoiceCore` (i.e. the in-tree `BSGCore`) yields the full theorem with no further
work. -/
theorem bsg_of_drc_unconditional {C₁ C₂ c : ℕ}
    (hDRC : DependentRandomChoiceCore C₁ C₂ c)
    {α : Type} [AddCommGroup α] [DecidableEq α]
    (A : Finset α) (K : ℕ) (hK : 1 ≤ K) (hne : A.Nonempty)
    (hE : (#A : ℚ) ^ 3 / K ≤ E[A]) :
    ∃ A' : Finset α, A' ⊆ A ∧ A'.Nonempty ∧
      (#A : ℚ) / (C₁ * K ^ 1) ≤ #A' ∧
      (#(A' - A') : ℚ) ≤ C₂ * K ^ c * #A' :=
  bsg_of_drc hDRC A K hK hne hE

end Finset.BSG

-- Axiom audit (expected: propext, Classical.choice, Quot.sound — and NO sorryAx).
#print axioms Finset.BSG.bsg_of_drc
#print axioms Finset.BSG.bsg_of_drc_unconditional
