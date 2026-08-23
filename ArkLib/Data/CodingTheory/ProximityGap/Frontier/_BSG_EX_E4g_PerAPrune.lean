/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BSG_EX_E4f_PathCalibrate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# BSG `E4g` — the per-`a` Markov pruning sub-lemma (standalone, axiom-clean)

The genuinely deep step of Tao–Vu Lemma 2.30 (the DRC "cleaning") is the **per-vertex pruning**:
having chosen a candidate left-neighbourhood `N = leftNbhd A G b₀` and a per-vertex
"well-connectedness weight" `goodDeg a = #{a' ∈ N₁ | a is well-connected to a'}`, one discards every
`a ∈ N` whose weight is below a threshold `θ`, keeping `A'' = {a ∈ N | θ ≤ goodDeg a}`, and must show
**`A''` retains a constant fraction of `N`** so the downstream size calibration `C₁ K #A'' ≥ #A`
survives.

This file proves the per-`a` pruning sub-lemma standalone and axiom-clean, in two layers:

1. **Abstract Markov-pruning brick** (`keep_card_ge_of_total_ge`): for any per-vertex weight
   `w : α → ℕ` on a finite `N`, with total mass `≥ M` and per-vertex cap `≤ W`, the kept set
   `{a ∈ N | θ ≤ w a}` satisfies `#kept · W + #N · θ ≥ M`. Choosing `θ ≤ M/(2#N)` keeps mass `≥ M/2`.

2. **Concrete instantiation on the DRC objects** (`goodDeg`, `prunedA''`): the pruned set is a subset
   of `leftNbhd A G b₀` (`prunedA''_subset`), every kept `a` is well-connected to `≥ θ` vertices of
   `N₁` (`prunedA''_mostA'`), and its size is controlled by the abstract brick (`prunedA''_card_ge`).

## The honest finding: the per-`a` prune yields MOST-`a'`, not every-`a'`

`PrunedFibreWithEnergy` (the target) asks for *every-pair* richness
`∀ a ∈ A'', ∀ a' ∈ N₁, #A ≤ s·cn(a,a')`. A single per-`a` Markov prune **cannot** deliver the
every-`a'` clause — discarding `a` with small `goodDeg a` only certifies that `≥ θ` of the `#N₁`
neighbours are good, never *all*. (This is exactly why 3 prior per-pair shortcuts were refuted.) The
genuinely achievable per-`a` shape is **every `a ∈ A''`, `goodDeg a ≥ θ`** (every-`a`, MOST-`a'`),
which this file proves. The every-`a'` upgrade requires a *second* (symmetric) prune of `N₁`, after
which the already-proven path-count engine `pathCount_card_bound` converts well-connectedness to the
difference-set bound. The post-prune obligation is named honestly as `PrunedFibreMostA`; it is NOT
claimed proven.

## Status

`PARTIAL` — the per-`a` Markov pruning core (abstract + concrete size + MOST-`a'` richness) is
**proven axiom-clean**. The every-`a'` upgrade, the second-fibre choice, the total-mass supply, and
the energy clause stay the named `def : Prop` `PrunedFibreMostA`.

## References
* T. Tao, V. Vu, *Additive Combinatorics*, Cambridge (2006), Lemma 2.30.
* W. T. Gowers, *A new proof of Szemerédi's theorem for AP4* (1998), §6.
-/

open Finset
open scoped BigOperators Pointwise

namespace Finset.BSG

variable {α : Type*} [DecidableEq α]

/-! ## Layer 1 — the abstract per-vertex Markov pruning -/

/-- **Markov inequality, sum form.** Over a finite index set `N`, the elements with weight `< θ`
carry at most `#N · θ` of the total weight. -/
theorem sum_low_weight_le (N : Finset α) (w : α → ℕ) (θ : ℕ) :
    ∑ a ∈ {a ∈ N | w a < θ}, w a ≤ #N * θ := by
  classical
  calc ∑ a ∈ {a ∈ N | w a < θ}, w a
      ≤ ∑ _a ∈ {a ∈ N | w a < θ}, θ := by
        refine Finset.sum_le_sum (fun a ha => ?_)
        rw [mem_filter] at ha
        exact le_of_lt ha.2
    _ = #({a ∈ N | w a < θ}) * θ := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ #N * θ := Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.filter_subset _ _))

/-- **The kept-fraction bound (the per-`a` pruning core).** Let `w : α → ℕ` be a per-vertex weight on
a finite `N`, with total weight at least `M` and each weight capped by `W`. Pruning at threshold `θ`
(`A'' := {a ∈ N | θ ≤ w a}`) keeps a set with `#A'' · W + #N · θ ≥ M`. In particular, with
`#N · θ ≤ M/2`, `#A'' · W ≥ M/2` — a constant fraction of the mass survives. -/
theorem keep_card_ge_of_total_ge (N : Finset α) (w : α → ℕ) (θ W M : ℕ)
    (hcap : ∀ a ∈ N, w a ≤ W) (htot : M ≤ ∑ a ∈ N, w a) :
    M ≤ #({a ∈ N | θ ≤ w a}) * W + #N * θ := by
  classical
  have hsplit : ∑ a ∈ N, w a
      = (∑ a ∈ {a ∈ N | θ ≤ w a}, w a) + ∑ a ∈ {a ∈ N | ¬ θ ≤ w a}, w a :=
    (Finset.sum_filter_add_sum_filter_not N (fun a => θ ≤ w a) _).symm
  have hkept : ∑ a ∈ {a ∈ N | θ ≤ w a}, w a ≤ #({a ∈ N | θ ≤ w a}) * W := by
    calc ∑ a ∈ {a ∈ N | θ ≤ w a}, w a
        ≤ ∑ _a ∈ {a ∈ N | θ ≤ w a}, W := by
          refine Finset.sum_le_sum (fun a ha => ?_)
          rw [mem_filter] at ha
          exact hcap a ha.1
      _ = #({a ∈ N | θ ≤ w a}) * W := by rw [Finset.sum_const, smul_eq_mul]
  have hdisc_eq : ({a ∈ N | ¬ θ ≤ w a} : Finset α) = {a ∈ N | w a < θ} := by
    apply Finset.filter_congr; intro a _; simp [not_le]
  have hdisc : ∑ a ∈ {a ∈ N | ¬ θ ≤ w a}, w a ≤ #N * θ := by
    rw [hdisc_eq]; exact sum_low_weight_le N w θ
  calc M ≤ ∑ a ∈ N, w a := htot
    _ = (∑ a ∈ {a ∈ N | θ ≤ w a}, w a) + ∑ a ∈ {a ∈ N | ¬ θ ≤ w a}, w a := hsplit
    _ ≤ #({a ∈ N | θ ≤ w a}) * W + #N * θ := Nat.add_le_add hkept hdisc

end Finset.BSG

/-! ## Layer 2 — the concrete instantiation on the DRC objects -/

namespace Finset.BSG

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-- **Per-`a` good-degree.** The number of `a' ∈ N₁` to which `a` is *well-connected* at factor `s`,
i.e. `#A ≤ s · cn(a,a')`. -/
noncomputable def goodDeg (A : Finset α) (G : Finset (α × α)) (N₁ : Finset α) (s : ℕ) (a : α) : ℕ :=
  #{a' ∈ N₁ | #A ≤ s * commonNeighbors A G a a'}

lemma goodDeg_le_card_N₁ (A : Finset α) (G : Finset (α × α)) (N₁ : Finset α) (s : ℕ) (a : α) :
    goodDeg A G N₁ s a ≤ #N₁ :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- **The per-`a` pruned set.** Keep the left-vertices of `leftNbhd A G b₀` whose good-degree into
`N₁` is at least the threshold `θ`. -/
noncomputable def prunedA'' (A : Finset α) (G : Finset (α × α)) (b₀ : α) (N₁ : Finset α)
    (s θ : ℕ) : Finset α :=
  {a ∈ leftNbhd A G b₀ | θ ≤ goodDeg A G N₁ s a}

lemma prunedA''_subset (A : Finset α) (G : Finset (α × α)) (b₀ : α) (N₁ : Finset α) (s θ : ℕ) :
    prunedA'' A G b₀ N₁ s θ ⊆ leftNbhd A G b₀ := Finset.filter_subset _ _

/-- **Per-`a` MOST-`a'` richness (PROVEN).** Every surviving `a ∈ A''` is well-connected (at factor
`s`) to at least `θ` vertices `a' ∈ N₁`. The honest, achievable per-`a` output of the prune: the
*every*-`a'` clause is NOT delivered by a single prune. -/
theorem prunedA''_mostA' (A : Finset α) (G : Finset (α × α)) (b₀ : α) (N₁ : Finset α) (s θ : ℕ)
    (a : α) (ha : a ∈ prunedA'' A G b₀ N₁ s θ) :
    θ ≤ #{a' ∈ N₁ | #A ≤ s * commonNeighbors A G a a'} := by
  rw [prunedA'', mem_filter] at ha
  exact ha.2

/-- **The kept-fraction bound for the concrete prune (PROVEN).** Given a total good-mass lower bound
`M ≤ ∑_{a ∈ leftNbhd A G b₀} goodDeg a`, the pruned set satisfies
`#A'' · #N₁ + #(leftNbhd A G b₀) · θ ≥ M`. With `θ` below `M/(2 #N₀)`, the kept size is `≥ M/(2 #N₁)`
— the constant fraction. The per-vertex cap `W = #N₁` is unconditional (`goodDeg_le_card_N₁`). -/
theorem prunedA''_card_ge (A : Finset α) (G : Finset (α × α)) (b₀ : α) (N₁ : Finset α) (s θ M : ℕ)
    (htot : M ≤ ∑ a ∈ leftNbhd A G b₀, goodDeg A G N₁ s a) :
    M ≤ #(prunedA'' A G b₀ N₁ s θ) * #N₁ + #(leftNbhd A G b₀) * θ := by
  have hcap : ∀ a ∈ leftNbhd A G b₀, goodDeg A G N₁ s a ≤ #N₁ :=
    fun a _ => goodDeg_le_card_N₁ A G N₁ s a
  have := keep_card_ge_of_total_ge (leftNbhd A G b₀) (goodDeg A G N₁ s) θ (#N₁) M hcap htot
  simpa [prunedA''] using this

/-! ## The named residual after the per-`a` prune (NOT proven) -/

/-- **`PrunedFibreMostA` — the residual the per-`a` prune leaves.** Identical to
`PrunedFibreWithEnergy` except the every-`a'` richness clause is replaced by the **MOST-`a'`** form
`∀ a ∈ A'', θ ≤ goodDeg a`, with a threshold `θ` controlling it. NOT claimed proven; the every-`a'`
upgrade routes through a second prune of `N₁` and the already-proven `pathCount_card_bound`. -/
def PrunedFibreMostA (C₁ s_C s_c : ℕ) : Prop :=
  ∀ {α : Type} [inst : AddCommGroup α] [inst2 : DecidableEq α],
    ∀ (A : Finset α) (K : ℕ) (G : Finset (α × α)) (b₀ : α),
      0 < K → A.Nonempty → G ⊆ A ×ˢ A → b₀ ∈ A →
      #A ^ 2 ≤ 4 * K ^ 2 * #G →
      #A ^ 4 ≤ 16 * K ^ 4 * (#A * (∑ b ∈ A, rDeg A G b ^ 2)) →
      #A ≤ 4 * K ^ 2 * rDeg A G b₀ →
      ∃ (A'' : Finset α) (b₁ : α) (s θ : ℕ),
        b₁ ∈ A ∧
        A'' ⊆ leftNbhd A G b₀ ∧ A''.Nonempty ∧ (leftNbhd A G b₁).Nonempty ∧
        s ≤ s_C * K ^ s_c ∧
        C₁ * K * #A'' ≥ #A ∧
        #A'' ≤ s * #(leftNbhd A G b₁) ∧
        (∀ a ∈ A'', θ ≤ goodDeg A G (leftNbhd A G b₁) s a) ∧
        #(A'' - A) * #(leftNbhd A G b₁ - A) ≤ #A * #A''

end Finset.BSG

-- Axiom audit (expected: propext, Classical.choice, Quot.sound — and NO sorryAx).
#print axioms Finset.BSG.sum_low_weight_le
#print axioms Finset.BSG.keep_card_ge_of_total_ge
#print axioms Finset.BSG.goodDeg_le_card_N₁
#print axioms Finset.BSG.prunedA''_subset
#print axioms Finset.BSG.prunedA''_mostA'
#print axioms Finset.BSG.prunedA''_card_ge
