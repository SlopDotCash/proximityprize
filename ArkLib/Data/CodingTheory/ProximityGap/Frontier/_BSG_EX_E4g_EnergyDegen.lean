/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BSG_EX_E4f_PathCalibrate

/-!
# BSG `E4g` — the relative-difference ENERGY clause is DEGENERATE (settled, axiom-clean)

This file targets the *energy clause* of `PrunedFibreWithEnergy`
(`_BSG_EX_E4f_PathCalibrate.lean`):

  `#(A'' - A) * #(N₁ - A) ≤ #A * #A''`,    where `A'' ⊆ A`, `N₁ ⊆ A`, `A''` nonempty, `N₁` nonempty.

The downstream calibration `relativeDiffCalibration_of_prunedFibreWithEnergy` is **proven**
axiom-clean, so any axiom-clean supply of `PrunedFibreWithEnergy` finishes the BSG leg of BGK.
The question for this pass is whether the energy clause can be *supplied* by the genuine
post-averaging (Tao–Vu Lemma 2.30) argument.

## The settled answer: the energy clause is DEGENERATE

We prove a clean, standalone, axiom-clean lower bound on relative difference sets:

  `relativeDiff_card_ge` :  `A''` nonempty, `A'' ⊆ A`  ⟹  `#A ≤ #(A'' - A)`.

(For a fixed `a₀ ∈ A''`, the translation `a ↦ a₀ - a` injects `A` into `A'' - A`.)
By symmetry the same holds for `N₁`. Combined with `#A'' ≤ #A` (from `A'' ⊆ A`), the energy bound

  `#A * #A ≤ #(A'' - A) * #(N₁ - A) ≤ #A * #A'' ≤ #A * #A`

collapses to a chain of *equalities*. Hence (`energy_forces_full`, axiom-clean):

  the energy clause `#(A'' - A) * #(N₁ - A) ≤ #A * #A''`  **forces**  `#A'' = #A`,
  and therefore (`A'' ⊆ A`)  `A'' = A`.

So the energy clause is satisfiable only in the degenerate case `A'' = A`: it cannot be the output
of a genuine constant-fraction pruning (which delivers `#A'' ≈ #A / (C₁K)`, strictly smaller than
`#A` once `K > 1`). The energy clause of `PrunedFibreWithEnergy` therefore **cannot be supplied**
by the real DRC averaging, and `PrunedFibreWithEnergy` — though every theorem *downstream* of it is
genuinely proven axiom-clean — is the **wrong target**: its premise is unreachable.

## What this pass establishes (all axiom-clean, no `sorry`)

* `relativeDiff_card_ge` — the genuine, reusable lower bound `#A ≤ #(A'' - A)`.
* `energy_clause_unsat_of_proper` — if `A'' ⊊ A` is a *proper* nonempty subset (the real pruning
  regime), the energy clause is **false**: `#A * #A'' < #(A'' - A) * #(N₁ - A)`.
* `energy_forces_full` — the energy clause forces `A'' = A`.

## The honest residual (named, NOT proven here)

The provable replacement drops the degenerate energy clause and keeps only what the symmetric
path-count `pathCount_card_bound` actually needs in the *relative* form. We name it
`PrunedFibreRelEnergy`: the energy hypothesis is replaced by the *scaled* relative-difference bound

  `#(A'' - A) * #(N₁ - A) ≤ s * #A * #A''`

with the **same factor `s`** that already calibrates the sizes — non-degenerate (it holds with
`A'' = N₁ = A` a coset and room to spare for `s ≥ 1`), and exactly strong enough to drive the
path-count after the extra `s` is absorbed into the Ruzsa factor. Whether the DRC averaging supplies
`PrunedFibreRelEnergy` (with `s = Θ(K^c)`) is the genuine remaining gap; it is recorded as a
`def … : Prop`, NOT proven.

## Status

`PARTIAL`. The energy clause of `PrunedFibreWithEnergy` is **settled degenerate** (3 axiom-clean
theorems pinning it to `A'' = A`). The non-degenerate replacement and its calibration are named
residuals, not proven.

## References
* T. Tao, V. Vu, *Additive Combinatorics*, Cambridge (2006), Lemma 2.30.
-/

open Finset
open scoped BigOperators Pointwise

namespace Finset.BSG

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-! ## The genuine lower bound on relative difference sets (axiom-clean) -/

/-- **Relative-difference lower bound.** For a nonempty `A'' ⊆ A` in an additive group, the
relative difference set `A'' - A` has at least `#A` elements: for any fixed `a₀ ∈ A''`, the
translation `a ↦ a₀ - a` injects `A` into `A'' - A`.

This is the structural fact that makes the energy clause of `PrunedFibreWithEnergy` degenerate. -/
theorem relativeDiff_card_ge (A A'' : Finset α) (hsub : A'' ⊆ A) (hne : A''.Nonempty) :
    #A ≤ #(A'' - A) := by
  classical
  obtain ⟨a₀, ha₀⟩ := hne
  refine Finset.card_le_card_of_injOn (fun a => a₀ - a) ?_ ?_
  · intro a ha
    exact Finset.sub_mem_sub ha₀ ha
  · intro a _ a' _ h
    simpa using sub_right_injective h

/-- Symmetric companion: `#A ≤ #(N₁ - A)` for nonempty `N₁ ⊆ A`. (Same proof.) -/
theorem relativeDiff_card_ge' (A N₁ : Finset α) (hsub : N₁ ⊆ A) (hne : N₁.Nonempty) :
    #A ≤ #(N₁ - A) :=
  relativeDiff_card_ge A N₁ hsub hne

/-! ## The energy clause is degenerate -/

/-- **Energy clause forces `A'' = A` (cardinality form).** Under the genuine subset/nonemptiness
hypotheses, the energy bound `#(A'' - A) * #(N₁ - A) ≤ #A * #A''` forces `#A ≤ #A''`; with
`A'' ⊆ A` (hence `#A'' ≤ #A`) this pins `#A'' = #A`. -/
theorem energy_forces_full_card (A A'' N₁ : Finset α)
    (hsub : A'' ⊆ A) (hne : A''.Nonempty)
    (hsub₁ : N₁ ⊆ A) (hne₁ : N₁.Nonempty)
    (henergy : #(A'' - A) * #(N₁ - A) ≤ #A * #A'') :
    #A'' = #A := by
  have hlo : #A ≤ #(A'' - A) := relativeDiff_card_ge A A'' hsub hne
  have hlo₁ : #A ≤ #(N₁ - A) := relativeDiff_card_ge' A N₁ hsub₁ hne₁
  have hAsub : #A'' ≤ #A := Finset.card_le_card hsub
  have hchain : #A * #A ≤ #A * #A'' :=
    le_trans (Nat.mul_le_mul hlo hlo₁) henergy
  have hApos : 0 < #A := hne.mono hsub |>.card_pos
  have hle : #A ≤ #A'' := Nat.le_of_mul_le_mul_left hchain hApos
  omega

/-- **Energy clause forces `A'' = A` (set form).** Combining the cardinality pin with `A'' ⊆ A`
gives set equality. -/
theorem energy_forces_full (A A'' N₁ : Finset α)
    (hsub : A'' ⊆ A) (hne : A''.Nonempty)
    (hsub₁ : N₁ ⊆ A) (hne₁ : N₁.Nonempty)
    (henergy : #(A'' - A) * #(N₁ - A) ≤ #A * #A'') :
    A'' = A :=
  Finset.eq_of_subset_of_card_le hsub
    (le_of_eq (energy_forces_full_card A A'' N₁ hsub hne hsub₁ hne₁ henergy).symm)

/-- **The energy clause is FALSE on any proper pruning.** If `A'' ⊊ A` is a proper nonempty
subset — the regime a genuine constant-fraction pruning produces (`#A'' < #A`) — then the energy
clause cannot hold: `#A * #A'' < #(A'' - A) * #(N₁ - A)`. So the energy clause of
`PrunedFibreWithEnergy` is unsatisfiable exactly where the real argument lives. -/
theorem energy_clause_unsat_of_proper (A A'' N₁ : Finset α)
    (hsub : A'' ⊆ A) (hne : A''.Nonempty)
    (hsub₁ : N₁ ⊆ A) (hne₁ : N₁.Nonempty)
    (hproper : #A'' < #A) :
    #A * #A'' < #(A'' - A) * #(N₁ - A) := by
  have hlo : #A ≤ #(A'' - A) := relativeDiff_card_ge A A'' hsub hne
  have hlo₁ : #A ≤ #(N₁ - A) := relativeDiff_card_ge' A N₁ hsub₁ hne₁
  have hApos : 0 < #A := hne.mono hsub |>.card_pos
  have hstrict : #A * #A'' < #A * #A := by
    rw [Nat.mul_lt_mul_left hApos]; exact hproper
  calc #A * #A'' < #A * #A := hstrict
    _ ≤ #(A'' - A) * #(N₁ - A) := Nat.mul_le_mul hlo hlo₁

/-! ## The non-degenerate replacement (named residual, NOT proven)

Replace the degenerate energy clause `#(A''-A)*#(N₁-A) ≤ #A*#A''` by the *scaled* relative bound
`#(A''-A)*#(N₁-A) ≤ s*#A*#A''` with the SAME factor `s` that calibrates the sizes. -/

/-- **`PrunedFibreRelEnergy` — the non-degenerate replacement residual.** Identical to
`PrunedFibreWithEnergy` except the energy clause carries the calibration factor `s`:
`#(A'' - A) * #(N₁ - A) ≤ s * (#A * #A'')`. NOT proven here. -/
def PrunedFibreRelEnergy (C₁ s_C s_c : ℕ) : Prop :=
  ∀ {α : Type} [inst : AddCommGroup α] [inst2 : DecidableEq α],
    ∀ (A : Finset α) (K : ℕ) (G : Finset (α × α)) (b₀ : α),
      0 < K → A.Nonempty → G ⊆ A ×ˢ A → b₀ ∈ A →
      #A ^ 2 ≤ 4 * K ^ 2 * #G →
      #A ^ 4 ≤ 16 * K ^ 4 * (#A * (∑ b ∈ A, rDeg A G b ^ 2)) →
      #A ≤ 4 * K ^ 2 * rDeg A G b₀ →
      ∃ (A'' : Finset α) (b₁ : α) (s : ℕ),
        b₁ ∈ A ∧
        A'' ⊆ leftNbhd A G b₀ ∧ A''.Nonempty ∧ (leftNbhd A G b₁).Nonempty ∧
        s ≤ s_C * K ^ s_c ∧
        C₁ * K * #A'' ≥ #A ∧
        #A'' ≤ s * #(leftNbhd A G b₁) ∧
        (∀ a ∈ A'', ∀ a' ∈ leftNbhd A G b₁, #A ≤ s * commonNeighbors A G a a') ∧
        #(A'' - A) * #(leftNbhd A G b₁ - A) ≤ s * (#A * #A'')

end Finset.BSG

-- Axiom audit (expected: propext, Classical.choice, Quot.sound — and NO sorryAx).
#print axioms Finset.BSG.relativeDiff_card_ge
#print axioms Finset.BSG.relativeDiff_card_ge'
#print axioms Finset.BSG.energy_forces_full_card
#print axioms Finset.BSG.energy_forces_full
#print axioms Finset.BSG.energy_clause_unsat_of_proper
