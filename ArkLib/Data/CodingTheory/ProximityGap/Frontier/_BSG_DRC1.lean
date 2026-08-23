/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BSG_Reduce
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# BSG — the dependent-random-choice (DRC) counting core (`L5`, partial)

This file proves the **counting / averaging heart** of the dependent-random-choice step
(`BareDRC` in `_BSG_Reduce.lean`) as standalone axiom-clean lemmas, and isolates the *remaining*
content of `BareDRC` into a strictly smaller named residual.

## The DRC step, decomposed

`BareDRC` consumes an edge-dense, cherry-rich bipartite graph `G ⊆ A ×ˢ A` and must output a
constant-fraction small-doubling subset `A'`. The standard proof (Tao–Vu, *Additive
Combinatorics*, Thm 2.29; Gowers 1998 §6) has three pieces:

1. **(DRC-count)** the *cherry double-count*: the cherry count `∑_{b} deg(b)²` (number of length-2
   paths `a — b — a'`) equals `∑_{(a,a')} cn(a,a')`, where `cn(a,a')` is the number of common
   right-neighbours of `a, a'`. A pure double-count — **proven here**
   (`sum_rDeg_sq_eq_sum_commonNeighbors`).

2. **(DRC-average)** the *neighbourhood averaging*: `∑_b |N(b)| = #G`, so a `b` with a large
   neighbourhood exists by pigeonhole — **proven here** (`exists_rDeg_ge_avg`), built on
   `Finset.exists_le_of_sum_le`.

3. **(DRC-extract)** the *bad-pair refinement*: choosing a good `b` weighted by the cherry count,
   the number of pairs `(a,a') ∈ N(b)²` with *few* common neighbours is small; set
   `A' = N(b) \ bad` and bound `|A' - A'|` via the common-neighbour density (Plünnecke). This is the
   **only** remaining content; it is the named residual `BareDRCExtract`, and `BareDRC` is reduced
   to it (`bareDRC_of_extract`).

## Status

`PARTIAL` — pieces 1 and 2 (DRC-count, DRC-average) are **proven axiom-clean**. Piece 3
(DRC-extract) is a named residual `BareDRCExtract` strictly smaller than `BareDRC` (it is handed a
single good vertex, removing the averaging/pigeonhole layer), and
`bareDRC_of_extract : BareDRCExtract C₁ C₂ c → BareDRC C₁ C₂ c` is **proven axiom-clean**.

## References

* W. T. Gowers, *A new proof of Szemerédi's theorem for AP4* (1998), §6.
* T. Tao, V. Vu, *Additive Combinatorics*, Cambridge (2006), Theorem 2.29.
-/

open Finset
open scoped BigOperators Pointwise Combinatorics.Additive

namespace Finset.BSG

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-! ## Neighbourhoods and common neighbours -/

/-- The **left-neighbourhood** of a right-vertex `b` in `G ⊆ A ×ˢ A`: the left vertices `a ∈ A`
with `(a, b) ∈ G`. Its cardinality is `rDeg A G b`. -/
noncomputable def leftNbhd (A : Finset α) (G : Finset (α × α)) (b : α) : Finset α :=
  {a ∈ A | (a, b) ∈ G}

lemma card_leftNbhd (A : Finset α) (G : Finset (α × α)) (b : α) :
    #(leftNbhd A G b) = rDeg A G b := rfl

/-- The **common-neighbour count** of a left-pair `(a, a')`: the number of right-vertices `b ∈ A`
adjacent (in `G`) to both `a` and `a'`. -/
noncomputable def commonNeighbors (A : Finset α) (G : Finset (α × α)) (a a' : α) : ℕ :=
  #{b ∈ A | (a, b) ∈ G ∧ (a', b) ∈ G}

/-- `rDeg` as a sum of `{0,1}` indicators over `A`. -/
lemma rDeg_eq_sum_indicator (A : Finset α) (G : Finset (α × α)) (b : α) :
    rDeg A G b = ∑ a ∈ A, (if (a, b) ∈ G then 1 else 0) := by
  classical
  rw [rDeg, Finset.card_filter]

/-- `commonNeighbors` as a sum of `{0,1}` indicators over `A`. -/
lemma commonNeighbors_eq_sum_indicator (A : Finset α) (G : Finset (α × α)) (a a' : α) :
    commonNeighbors A G a a' = ∑ b ∈ A, (if (a, b) ∈ G ∧ (a', b) ∈ G then 1 else 0) := by
  classical
  rw [commonNeighbors, Finset.card_filter]

/-! ## Piece 1 — the cherry double-count (`DRC-count`)

Both `∑_b deg(b)²` and `∑_{(a,a')} cn(a,a')` count ordered triples `(a, a', b) ∈ A×A×A` with
`(a,b) ∈ G` and `(a',b) ∈ G`; they differ only by the order of summation. -/

/-- **DRC-count — cherry double-count.** The cherry count `∑_b deg(b)²` equals the total
common-neighbour count `∑_{(a,a') ∈ A×ˢA} cn(a,a')`.

Proof: expand both as the triple sum `∑_a ∑_{a'} ∑_b [(a,b)∈G][(a',b)∈G]` and swap order. -/
theorem sum_rDeg_sq_eq_sum_commonNeighbors (A : Finset α) (G : Finset (α × α)) :
    ∑ b ∈ A, rDeg A G b ^ 2 = ∑ p ∈ A ×ˢ A, commonNeighbors A G p.1 p.2 := by
  classical
  -- LHS as a triple sum over `b, a, a'`.
  have hL : ∑ b ∈ A, rDeg A G b ^ 2
      = ∑ b ∈ A, ∑ a ∈ A, ∑ a' ∈ A,
          (if (a, b) ∈ G then 1 else 0) * (if (a', b) ∈ G then 1 else 0) := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [sq, rDeg_eq_sum_indicator, Finset.sum_mul_sum]
  -- RHS as a triple sum over `a, a', b`.
  have hR : ∑ p ∈ A ×ˢ A, commonNeighbors A G p.1 p.2
      = ∑ a ∈ A, ∑ a' ∈ A, ∑ b ∈ A,
          (if (a, b) ∈ G then 1 else 0) * (if (a', b) ∈ G then 1 else 0) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun a' _ => ?_))
    rw [commonNeighbors_eq_sum_indicator]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases h1 : (a, b) ∈ G <;> by_cases h2 : (a', b) ∈ G <;> simp [h1, h2]
  rw [hL, hR]
  -- Reorder `∑_b ∑_a ∑_a'` to `∑_a ∑_a' ∑_b`.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_comm]

/-! ## Piece 2 — neighbourhood averaging (`DRC-average`) -/

/-- **DRC-average — neighbourhood averaging / pigeonhole.** Since `∑_b deg(b) = #G`, there is a
right-vertex `b ∈ A` whose neighbourhood is at least the average: `#A * deg(b) ≥ #G`.

(The `#A * deg(b) ≥ #G` form is the cleared `deg(b) ≥ #G / #A`.) -/
theorem exists_rDeg_ge_avg (A : Finset α) (G : Finset (α × α)) (hG : G ⊆ A ×ˢ A)
    (hA : A.Nonempty) :
    ∃ b ∈ A, #G ≤ #A * rDeg A G b := by
  classical
  -- `∑_b deg(b) = #G`, so `∑_b deg(b) ≤ ∑_b (max deg)`... use pigeonhole directly:
  -- if all `#A * deg(b) < #G` then `∑_b #A*deg(b) < #A * #G = ∑_b #G`, contradiction.
  by_contra h
  push_neg at h
  -- h : ∀ b ∈ A, #A * rDeg A G b < #G
  have hlt : ∑ b ∈ A, #A * rDeg A G b < ∑ b ∈ A, #G :=
    Finset.sum_lt_sum_of_nonempty hA h
  rw [Finset.sum_const, ← Finset.mul_sum, ← card_eq_sum_rDeg A G hG] at hlt
  simp only [smul_eq_mul] at hlt
  -- hlt : #A * #G < #A * #G
  omega

/-! ## Bad-pair counting (the Cauchy–Schwarz / Markov heart of DRC)

A pair `(a, a') ∈ A ×ˢ A` is *bad at threshold `t`* if it has *few* common neighbours,
`cn(a,a') < t`. The bad pairs contribute at most `#(A ×ˢ A) · t` to the total cherry count
`∑_{(a,a')} cn(a,a')`. Hence whenever the cherry count is large (cherry-richness), the *good* pairs
(those with `cn ≥ t`) carry almost all the cherries — this is exactly the averaging that lets
dependent random choice find a neighbourhood in which almost every pair is well-connected. -/

/-- The **bad pairs at threshold `t`**: left-pairs with fewer than `t` common neighbours. -/
noncomputable def badPairs (A : Finset α) (G : Finset (α × α)) (t : ℕ) : Finset (α × α) :=
  {p ∈ A ×ˢ A | commonNeighbors A G p.1 p.2 < t}

/-- **Bad-pair Markov bound.** The total common-neighbour mass carried by the bad pairs is at most
`#(A ×ˢ A) · t`. (Each bad pair has `cn < t`, i.e. `cn ≤ t - 1 < t`.) -/
theorem sum_commonNeighbors_badPairs_le (A : Finset α) (G : Finset (α × α)) (t : ℕ) :
    ∑ p ∈ badPairs A G t, commonNeighbors A G p.1 p.2 ≤ #(A ×ˢ A) * t := by
  classical
  have hsub : badPairs A G t ⊆ A ×ˢ A := Finset.filter_subset _ _
  calc ∑ p ∈ badPairs A G t, commonNeighbors A G p.1 p.2
      ≤ ∑ _p ∈ badPairs A G t, t := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        rw [badPairs, mem_filter] at hp
        exact le_of_lt hp.2
    _ = #(badPairs A G t) * t := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ #(A ×ˢ A) * t := Nat.mul_le_mul_right _ (Finset.card_le_card hsub)

/-- **Good pairs carry the cherries.** From the cherry double-count and the bad-pair Markov bound:
the common-neighbour mass on the *good* pairs (`cn ≥ t`) is at least `(∑_b deg(b)²) − #(A×A)·t`.
This is the quantitative statement that, at a threshold `t` below the cherry average, most cherries
sit on well-connected pairs — the input to the extraction step. -/
theorem sum_commonNeighbors_goodPairs_ge (A : Finset α) (G : Finset (α × α)) (t : ℕ) :
    (∑ b ∈ A, rDeg A G b ^ 2) ≤
      (∑ p ∈ {p ∈ A ×ˢ A | t ≤ commonNeighbors A G p.1 p.2}, commonNeighbors A G p.1 p.2)
        + #(A ×ˢ A) * t := by
  classical
  -- Split the cherry double-count over good/bad pairs, then Markov on bad.
  rw [sum_rDeg_sq_eq_sum_commonNeighbors A G]
  have hsplit :
      ∑ p ∈ A ×ˢ A, commonNeighbors A G p.1 p.2
        = (∑ p ∈ {p ∈ A ×ˢ A | t ≤ commonNeighbors A G p.1 p.2}, commonNeighbors A G p.1 p.2)
          + ∑ p ∈ {p ∈ A ×ˢ A | ¬ t ≤ commonNeighbors A G p.1 p.2}, commonNeighbors A G p.1 p.2 :=
    (Finset.sum_filter_add_sum_filter_not (A ×ˢ A)
      (fun p => t ≤ commonNeighbors A G p.1 p.2) _).symm
  rw [hsplit]
  have hbad : ({p ∈ A ×ˢ A | ¬ t ≤ commonNeighbors A G p.1 p.2} : Finset (α × α))
      = badPairs A G t := by
    rw [badPairs]; apply Finset.filter_congr; intro p _; simp [not_le]
  rw [hbad]
  have := sum_commonNeighbors_badPairs_le A G t
  omega

/-! ## Piece 3 — the remaining residual `BareDRCExtract`

After DRC-average supplies a good vertex `b` and DRC-count quantifies the cherry density, the
*remaining* content of `BareDRC` is the extraction of a small-doubling subset from a single
neighbourhood with a quantified bad-pair bound. We state this as the strictly smaller residual
`BareDRCExtract`: it is handed the chosen vertex `b₀` together with its neighbourhood-quality data,
and need only output `A'`. The averaging/pigeonhole layer (piece 2) is gone from its hypotheses.

`BareDRC` reduces to `BareDRCExtract` (`bareDRC_of_extract`). -/

/-- **The post-averaging extraction residual `BareDRCExtract`.**

It receives the same `A, K, G` as `BareDRC`, the same density data, **plus** a distinguished good
right-vertex `b₀ ∈ A` whose left-neighbourhood `N = leftNbhd A G b₀` is large
(`#A ≤ 4 * K ^ 2 * #N`, the exact bound the averaging step delivers), and must output the BSG
subset `A'`. The averaging step that produces `b₀` is discharged by `exists_rDeg_ge_avg`; what
remains (the genuinely deep part) is turning the large neighbourhood `N` into a small-doubling
`A'`. -/
def BareDRCExtract (C₁ C₂ c : ℕ) : Prop :=
  ∀ {α : Type} [inst : AddCommGroup α] [inst2 : DecidableEq α],
    ∀ (A : Finset α) (K : ℕ) (G : Finset (α × α)) (b₀ : α),
      0 < K → A.Nonempty → G ⊆ A ×ˢ A → b₀ ∈ A →
      #A ^ 2 ≤ 4 * K ^ 2 * #G →
      #A ^ 4 ≤ 16 * K ^ 4 * (#A * (∑ b ∈ A, rDeg A G b ^ 2)) →
      #A ≤ 4 * K ^ 2 * rDeg A G b₀ →
      ∃ A' : Finset α, A' ⊆ A ∧ A'.Nonempty ∧
        C₁ * K * #A' ≥ #A ∧ #(A' - A') ≤ C₂ * K ^ c * #A'

/-- **`BareDRC` reduces to `BareDRCExtract`.** The averaging/pigeonhole layer (`exists_rDeg_ge_avg`)
supplies a good vertex `b₀` with `#A ≤ 4K²·deg(b₀)` from the edge-density `#A² ≤ 4K²·#G`:

`#G ≤ #A · deg(b₀)` (pigeonhole) and `#A² ≤ 4K²·#G ≤ 4K²·#A·deg(b₀)`, so cancelling one `#A`
gives `#A ≤ 4K²·deg(b₀)` — exactly the neighbourhood-quality datum `BareDRCExtract` consumes. -/
theorem bareDRC_of_extract {C₁ C₂ c : ℕ} (hExt : BareDRCExtract C₁ C₂ c) :
    BareDRC C₁ C₂ c := by
  intro α _ _ A K G hK hA hGsub hdense hcherry
  classical
  -- Get the good vertex `b₀` from averaging.
  obtain ⟨b₀, hb₀A, hb₀⟩ := exists_rDeg_ge_avg A G hGsub hA
  -- `hb₀ : #G ≤ #A * rDeg A G b₀`.  Combine with `#A² ≤ 4K²·#G` to bound `#A`.
  -- `#A² ≤ 4K²·#G ≤ 4K²·#A·deg`, so `#A ≤ 4K²·deg` (after cancelling one `#A`).
  have hApos : 0 < #A := hA.card_pos
  have hchain : #A * #A ≤ #A * (4 * K ^ 2 * rDeg A G b₀) := by
    calc #A * #A = #A ^ 2 := by ring
      _ ≤ 4 * K ^ 2 * #G := hdense
      _ ≤ 4 * K ^ 2 * (#A * rDeg A G b₀) := Nat.mul_le_mul_left _ hb₀
      _ = #A * (4 * K ^ 2 * rDeg A G b₀) := by ring
  have hgood : #A ≤ 4 * K ^ 2 * rDeg A G b₀ := Nat.le_of_mul_le_mul_left hchain hApos
  exact hExt A K G b₀ hK hA hGsub hb₀A hdense hcherry hgood

end Finset.BSG

-- Axiom audit (expected: propext, Classical.choice, Quot.sound — and NO sorryAx).
#print axioms Finset.BSG.sum_rDeg_sq_eq_sum_commonNeighbors
#print axioms Finset.BSG.exists_rDeg_ge_avg
#print axioms Finset.BSG.sum_commonNeighbors_badPairs_le
#print axioms Finset.BSG.sum_commonNeighbors_goodPairs_ge
#print axioms Finset.BSG.bareDRC_of_extract
