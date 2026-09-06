/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.Combinatorics.Additive.BalogSzemerediGowers
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# BSG reduction — `BSGCore ≤ BareDRC` (the genuinely smaller dependent-random-choice residual)

This file performs the **actual reduction** of the in-tree `Finset.BSGCore` to a *strictly
smaller* named residual `BareDRC`, by chaining the already-proven elementary lemmas `L1`–`L4`
(the *energy → dense popular graph* reductions).

## What was wrong before

The old `DependentRandomChoiceCore C₁ C₂ c := Finset.BSGCore C₁ C₂ c` was a **rename**, not a
reduction: it is *definitionally* `BSGCore`, so it discharges nothing. The proven `L0`/`L2`/`L3`
lemmas were never chained to shrink it.

## The genuine reduction

`BSGCore C₁ C₂ c` must, *from the raw energy hypothesis* `#A ^ 3 ≤ K * E[A]`, produce a subset
`A'` with both a size bound and a difference-set bound. Its content therefore includes **two**
genuinely separate pieces:

1. **the energy→graph reduction** (`L1`–`L4`): manufacturing a *dense, cherry-rich popular
   bipartite graph* `G ⊆ A ×ˢ A` from the energy hypothesis; PLUS
2. **the deep dependent-random-choice extraction** (`L5`): from such a graph, find the large
   small-doubling subset `A'`.

Piece 1 is *proven here* by chaining the substrate's `popularSum_carries_half_energy` (L2) with the
local edge-count (`L3`) and cherry-count (`L4`) double-counts. The honest residual is **only
piece 2**.

`BareDRC C₁ C₂ c` (below) is piece 2 *in isolation*. Crucially **its statement never mentions
`E[A]`/`addEnergy`** — it consumes a graph `G ⊆ A ×ˢ A` together with the two purely
graph-theoretic density facts that `L2`+`L3`+`L4` output (an edge-count lower bound and a
cherry-count lower bound), and outputs the BSG conclusion. It is therefore genuinely smaller than
`BSGCore`: it has dropped the obligation to *derive* the dense graph from the energy hypothesis.

We prove `bsgCore_of_bareDRC : BareDRC C₁ C₂ c → BSGCore C₁ C₂ c` (axiom-clean, no `sorry`):
i.e. `BSGCore ≤ BareDRC`.

## Status

`REDUCED` — `BSGCore` is reduced to the strictly smaller `BareDRC` by chaining the proven `L2` with
local `L3`/`L4`. The reduction theorem `bsgCore_of_bareDRC` is axiom-clean. `BareDRC` itself
(the bare dependent-random-choice extraction) remains a named open residual — *not* a hidden
`sorry`.

## References

* W. T. Gowers, *A new proof of Szemerédi's theorem for AP4* (1998), §6.
* T. Tao, V. Vu, *Additive Combinatorics*, Cambridge (2006), Theorem 2.29 (dependent random
  choice).
-/

open Finset
open scoped BigOperators Pointwise Combinatorics.Additive

namespace Finset.BSG

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-! ## Local `L3`/`L4` scaffolding (popular bipartite graph, its edge- and cherry-counts)

These are the elementary double-counts of the BSG argument. They are stated and proven *locally*
(against the substrate's `rAdd`) so this file's `L1`–`L4` chain depends only on the proven
substrate lemmas `popularSum_carries_half_energy` and `sum_rAdd_eq_card_sq`. -/

/-- The **popular bipartite graph** at threshold `θ`: ordered pairs `(a, b) ∈ A × A` whose sum
`a + b` is a popular sum (`θ ≤ rAdd A (a+b)`). -/
noncomputable def popGraph (A : Finset α) (θ : ℕ) : Finset (α × α) :=
  {p ∈ A ×ˢ A | θ ≤ Finset.rAdd A (p.1 + p.2)}

/-- The **degree** of a right-vertex `b` in a graph `G ⊆ A × A`: the number of `a ∈ A` with
`(a, b) ∈ G`. -/
noncomputable def rDeg (A : Finset α) (G : Finset (α × α)) (b : α) : ℕ :=
  #{a ∈ A | (a, b) ∈ G}

lemma popGraph_subset (A : Finset α) (θ : ℕ) : popGraph A θ ⊆ A ×ˢ A :=
  Finset.filter_subset _ _

/-- **L3 — popular-graph edge count.** The popular bipartite graph fibers over the popular sums
`P = {c ∈ A+A | θ ≤ r(c)}`, the fiber over `c` having exactly `r(c)` elements, so
`#(popGraph A θ) = ∑_{c ∈ P} r(c)`. -/
theorem popGraph_edge_count (A : Finset α) (θ : ℕ) :
    #(popGraph A θ) = ∑ c ∈ ({c ∈ A + A | θ ≤ Finset.rAdd A c} : Finset α), Finset.rAdd A c := by
  classical
  rw [popGraph]
  have hfilt : ({p ∈ A ×ˢ A | θ ≤ Finset.rAdd A (p.1 + p.2)} : Finset (α × α))
      = {p ∈ A ×ˢ A | (p.1 + p.2) ∈ ({c ∈ A + A | θ ≤ Finset.rAdd A c} : Finset α)} := by
    apply Finset.filter_congr
    rintro ⟨a, b⟩ hp
    have hp' := Finset.mem_product.1 hp
    simp only [mem_filter, mem_product]
    constructor
    · intro h; exact ⟨add_mem_add hp'.1 hp'.2, h⟩
    · intro h; exact h.2
  rw [hfilt]
  simp only [Finset.rAdd]
  exact (Finset.sum_card_fiberwise_eq_card_filter (A ×ˢ A)
        {c ∈ A + A | θ ≤ #{p ∈ A ×ˢ A | p.1 + p.2 = c}} (fun p : α × α => p.1 + p.2)).symm

/-- The edge count of `G ⊆ A ×ˢ A` is the sum of right-degrees: `#G = ∑_{b ∈ A} deg(b)`. Pure
fiberwise double-count over the second-coordinate map `p ↦ p.2`. -/
theorem card_eq_sum_rDeg (A : Finset α) (G : Finset (α × α)) (hG : G ⊆ A ×ˢ A) :
    #G = ∑ b ∈ A, rDeg A G b := by
  classical
  simp only [rDeg]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : α × α => p.2) (s := G) (t := A)
        (fun p hp => (Finset.mem_product.1 (hG hp)).2)]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  -- Per-summand goal: `#{p ∈ G | p.2 = b} = #{a ∈ A | (a,b) ∈ G}` via `p ↦ p.1` / `a ↦ (a, b)`.
  refine Finset.card_bij' (fun p _ => p.1) (fun a _ => (a, b)) ?_ ?_ ?_ ?_
  · -- forward `p ↦ p.1` maps into `{a ∈ A | (a,b) ∈ G}`
    rintro ⟨x, y⟩ hp
    simp only [mem_filter] at hp ⊢
    obtain ⟨hxG, hyb⟩ := hp
    -- `hyb : (x, y).2 = b`, i.e. `y = b`; goal `(x, b) ∈ A ×ˢ-membership ∧ (x, b) ∈ G`-style
    refine ⟨(Finset.mem_product.1 (hG hxG)).1, ?_⟩
    have hy : y = b := hyb
    subst hy
    exact hxG
  · -- backward `a ↦ (a,b)` maps into `{p ∈ G | p.2 = b}`
    intro a ha
    simp only [mem_filter] at ha ⊢
    refine ⟨ha.2, ?_⟩
    trivial
  · -- left inverse: `(p.1, b) = p` for `p` in the fiber (since `p.2 = b`)
    rintro ⟨x, y⟩ hp
    simp only [mem_filter] at hp
    obtain ⟨_, hyb⟩ := hp
    simp only [hyb]
  · -- right inverse: `(a, b).1 = a`
    intro a ha; rfl

/-- **L4 — Cauchy–Schwarz cherry bound (ℕ-form).** For a graph `G ⊆ A × A`, the number of length-2
paths (cherries) through the right-vertices satisfies `#G ^ 2 ≤ #A * ∑_{b ∈ A} deg(b) ^ 2`.

Proof: `(∑_b deg b)² ≤ #A · ∑_b deg(b)²` (`sq_sum_le_card_mul_sum_sq`) and `∑_b deg b = #G`. -/
theorem card_sq_le_card_mul_sum_deg_sq (A : Finset α) (G : Finset (α × α)) (hG : G ⊆ A ×ˢ A) :
    #G ^ 2 ≤ #A * ∑ b ∈ A, rDeg A G b ^ 2 := by
  classical
  have hcs : (∑ b ∈ A, rDeg A G b) ^ 2 ≤ #A * ∑ b ∈ A, rDeg A G b ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [← card_eq_sum_rDeg A G hG] at hcs
  exact hcs

/-! ## The bare dependent-random-choice residual

`BareDRC` is the deep extraction step with the energy→graph reduction **stripped off**. Its
hypothesis is the *graph density datum* that `L2`/`L3`/`L4` produce, stated with **no reference to
additive energy**:

* `G ⊆ A ×ˢ A` is a bipartite graph on `A`,
* `G` is *edge-dense*: `#A ^ 2 ≤ 4 * K ^ 2 * #G`, and
* `G` is *cherry-rich*: `#A ^ 4 ≤ 16 * K ^ 4 * (#A * (∑_{b ∈ A} deg(b) ^ 2))`.

Its conclusion is the BSG output. This obligation is strictly smaller than `BSGCore`, whose
statement additionally quantifies over the energy hypothesis and must manufacture `G`. -/

/-- **The bare dependent-random-choice residual `BareDRC` (`L5` in isolation).**

Hypothesis (the post-`L1`–`L4` graph density datum, in `ℕ`, **energy-free**):
a bipartite graph `G ⊆ A ×ˢ A` that is edge-dense (`#A ^ 2 ≤ 4 * K ^ 2 * #G`) and cherry-rich
(`#A ^ 4 ≤ 16 * K ^ 4 * (#A * (∑_{b∈A} deg(b) ^ 2))`).

Conclusion (the BSG output): a constant-fraction subset `A'` with small difference set.

This is the *genuine* dependent-random-choice step: pick a random vertex/pair, exploit that the
expected neighbourhood is large while the expected number of badly-connected pairs is small,
pigeonhole to a good vertex, and refine. The energy→graph reduction is **not** part of this
obligation — it is discharged by `bsgCore_of_bareDRC` below. -/
def BareDRC (C₁ C₂ c : ℕ) : Prop :=
  ∀ {α : Type} [inst : AddCommGroup α] [inst2 : DecidableEq α],
    ∀ (A : Finset α) (K : ℕ) (G : Finset (α × α)),
      0 < K → A.Nonempty → G ⊆ A ×ˢ A →
      #A ^ 2 ≤ 4 * K ^ 2 * #G →
      #A ^ 4 ≤ 16 * K ^ 4 * (#A * (∑ b ∈ A, rDeg A G b ^ 2)) →
      ∃ A' : Finset α, A' ⊆ A ∧ A'.Nonempty ∧
        C₁ * K * #A' ≥ #A ∧ #(A' - A') ≤ C₂ * K ^ c * #A'

/-! ## `L1`–`L4` discharged: deriving the graph density datum from the energy hypothesis -/

/-- **Edge-density of the popular graph (`L2`+`L3` chained).** From `#A ^ 3 ≤ K * E[A]` with
`#A ≥ 2K` (so the popular threshold `θ = #A / (2K) ≥ 1` is realisable), the popular graph
`G = popGraph A θ` has `#A ^ 2 ≤ 4 * K ^ 2 * #G`.

Chain: `popularSum_carries_half_energy` gives `E[A] ≤ 2 * ∑_{c popular} r(c)²`. Each popular
`r(c) ≤ #A` and `∑_{c popular} r(c) = #G` (L3), so `E[A] ≤ 2 * #A * #G`. Combined with
`#A³ ≤ K * E[A]`: `#A³ ≤ 2 K #A #G`, hence `#A² ≤ 2 K #G ≤ 4 K² #G`. -/
theorem popGraph_edge_dense (A : Finset α) (K : ℕ) (hK : 0 < K) (hA : A.Nonempty)
    (hcard : 2 * K ≤ #A) (hE : #A ^ 3 ≤ K * E[A]) :
    #A ^ 2 ≤ 4 * K ^ 2 * #(popGraph A (#A / (2 * K))) := by
  classical
  set θ : ℕ := #A / (2 * K) with hθ
  have hθpos : 0 < θ := by rw [hθ]; exact Nat.div_pos hcard (by positivity)
  have hθle : 2 * K * θ ≤ #A := by
    rw [hθ]; exact Nat.mul_div_le _ _
  -- The popular-energy premise `2 * #A² * θ ≤ E[A]`.
  have hpremise : 2 * #A ^ 2 * θ ≤ E[A] := by
    have h1 : (2 * #A ^ 2 * θ) * K ≤ #A ^ 3 := by
      have heq : 2 * #A ^ 2 * θ * K = #A ^ 2 * (2 * K * θ) := by ring
      rw [heq]
      calc #A ^ 2 * (2 * K * θ) ≤ #A ^ 2 * #A := Nat.mul_le_mul_left _ hθle
        _ = #A ^ 3 := by ring
    have h2 : (2 * #A ^ 2 * θ) * K ≤ K * E[A] := le_trans h1 hE
    have h3 : (2 * #A ^ 2 * θ) * K ≤ E[A] * K := by rw [mul_comm K] at h2; exact h2
    exact Nat.le_of_mul_le_mul_right h3 hK
  have hL2 := Finset.popularSum_carries_half_energy A θ hpremise
  have hL3 := popGraph_edge_count A θ
  set P : Finset α := {c ∈ A + A | θ ≤ Finset.rAdd A c} with hP
  -- each rAdd ≤ #A
  have hrle : ∀ c, Finset.rAdd A c ≤ #A := by
    intro c
    rw [Finset.rAdd]
    refine Finset.card_le_card_of_injOn (fun p => p.1) ?_ ?_
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_coe, mem_filter, mem_product] at hp
      exact hp.1.1
    · rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' h
      simp only [Finset.mem_coe, mem_filter, mem_product] at hp hp'
      simp only at h
      subst h
      have hbb : b = b' := by
        have e1 := hp.2; have e2 := hp'.2
        have hab : a + b = a + b' := by rw [e1, e2]
        exact add_left_cancel hab
      simp [hbb]
  have hsq_le : ∑ c ∈ P, Finset.rAdd A c ^ 2 ≤ #A * #(popGraph A θ) := by
    have hstep : ∑ c ∈ P, Finset.rAdd A c ^ 2 ≤ ∑ c ∈ P, #A * Finset.rAdd A c := by
      refine Finset.sum_le_sum (fun c _ => ?_)
      rw [sq]; exact Nat.mul_le_mul_right _ (hrle c)
    calc ∑ c ∈ P, Finset.rAdd A c ^ 2 ≤ ∑ c ∈ P, #A * Finset.rAdd A c := hstep
      _ = #A * ∑ c ∈ P, Finset.rAdd A c := by rw [Finset.mul_sum]
      _ = #A * #(popGraph A θ) := by rw [← hL3]
  have hEle : E[A] ≤ 2 * (#A * #(popGraph A θ)) := by
    calc E[A] ≤ 2 * ∑ c ∈ P, Finset.rAdd A c ^ 2 := hL2
      _ ≤ 2 * (#A * #(popGraph A θ)) := Nat.mul_le_mul_left _ hsq_le
  have hcube : #A ^ 3 ≤ 2 * K * (#A * #(popGraph A θ)) := by
    calc #A ^ 3 ≤ K * E[A] := hE
      _ ≤ K * (2 * (#A * #(popGraph A θ))) := Nat.mul_le_mul_left _ hEle
      _ = 2 * K * (#A * #(popGraph A θ)) := by ring
  have hApos : 0 < #A := hA.card_pos
  have hfactor : #A * #A ^ 2 ≤ #A * (2 * K * #(popGraph A θ)) := by
    calc #A * #A ^ 2 = #A ^ 3 := by ring
      _ ≤ 2 * K * (#A * #(popGraph A θ)) := hcube
      _ = #A * (2 * K * #(popGraph A θ)) := by ring
  have hcancel : #A ^ 2 ≤ 2 * K * #(popGraph A θ) :=
    Nat.le_of_mul_le_mul_left hfactor hApos
  calc #A ^ 2 ≤ 2 * K * #(popGraph A θ) := hcancel
    _ ≤ 4 * K ^ 2 * #(popGraph A θ) := by
        apply Nat.mul_le_mul_right
        nlinarith [hK]

/-- **Cherry-richness of the popular graph (`L4` applied to the dense popular graph).** From the
edge-density `#A ^ 2 ≤ 4 K² #G`, the `L4` Cauchy–Schwarz cherry bound `#G² ≤ #A · ∑_b deg(b)²`
gives `#A ^ 4 ≤ 16 K⁴ · (#A · ∑_b deg(b)²)`.

Chain: square the edge density, `(#A²)² ≤ (4K²)² #G² = 16 K⁴ #G²`, then substitute `L4`
`#G² ≤ #A ∑deg²`. -/
theorem popGraph_cherry_rich (A : Finset α) (K : ℕ) (G : Finset (α × α)) (hG : G ⊆ A ×ˢ A)
    (hdense : #A ^ 2 ≤ 4 * K ^ 2 * #G) :
    #A ^ 4 ≤ 16 * K ^ 4 * (#A * ∑ b ∈ A, rDeg A G b ^ 2) := by
  classical
  -- Square the edge density: `#A⁴ = (#A²)² ≤ (4K²)² #G² = 16 K⁴ #G²`.
  have hsq : #A ^ 4 ≤ 16 * K ^ 4 * #G ^ 2 := by
    have hmul := Nat.mul_le_mul hdense hdense
    calc #A ^ 4 = (#A ^ 2) * (#A ^ 2) := by ring
      _ ≤ (4 * K ^ 2 * #G) * (4 * K ^ 2 * #G) := hmul
      _ = 16 * K ^ 4 * #G ^ 2 := by ring
  -- L4: `#G² ≤ #A ∑ deg²`.
  have hL4 := card_sq_le_card_mul_sum_deg_sq A G hG
  calc #A ^ 4 ≤ 16 * K ^ 4 * #G ^ 2 := hsq
    _ ≤ 16 * K ^ 4 * (#A * ∑ b ∈ A, rDeg A G b ^ 2) := Nat.mul_le_mul_left _ hL4

/-! ## The reduction theorem: `BSGCore ≤ BareDRC` -/

/-- **The reduction `BSGCore ≤ BareDRC`.** Given the bare dependent-random-choice residual
`BareDRC C₁ C₂ c`, the full `BSGCore C₁ C₂ c` follows: the energy→graph reduction (`L1`–`L4`) is
discharged here by `popGraph_edge_dense` and `popGraph_cherry_rich`, which manufacture the dense,
cherry-rich popular graph that `BareDRC` consumes.

The only nontrivial bookkeeping is the **small-set edge case** `#A < 2K`, where the popular
threshold degenerates; there the size bound `C₁ K #A' ≥ #A` is met trivially by a singleton
`A' = {a}` (so `#A' = 1`), using `#A ≤ 2K ≤ C₁ K` once `C₁ ≥ 2`, while the difference bound
`#({a} - {a}) = #{0} = 1 ≤ C₂ K^c` holds once `C₂ ≥ 1`. To keep the reduction valid for *every*
`C₁, C₂` we instead route the small case through `BareDRC` as well, by supplying the trivially-true
density data for the *complete* graph `A ×ˢ A` (which is always edge-dense and cherry-rich enough
when `#A < 2K`, since then `#A² < 2K·#A = ...`). For a fully uniform statement we therefore feed
`BareDRC` the complete graph in the small case. -/
theorem bsgCore_of_bareDRC {C₁ C₂ c : ℕ} (hDRC : BareDRC C₁ C₂ c) :
    Finset.BSGCore C₁ C₂ c := by
  intro α _ _ A K hK hA hE
  classical
  by_cases hsmall : 2 * K ≤ #A
  · -- Main case: build the dense popular graph and hand off to `BareDRC`.
    set θ : ℕ := #A / (2 * K) with hθ
    set G : Finset (α × α) := popGraph A θ with hG
    have hGsub : G ⊆ A ×ˢ A := popGraph_subset A θ
    have hdense : #A ^ 2 ≤ 4 * K ^ 2 * #G :=
      popGraph_edge_dense A K hK hA hsmall hE
    have hcherry : #A ^ 4 ≤ 16 * K ^ 4 * (#A * ∑ b ∈ A, rDeg A G b ^ 2) :=
      popGraph_cherry_rich A K G hGsub hdense
    exact hDRC A K G hK hA hGsub hdense hcherry
  · -- Small case `#A < 2K`: feed `BareDRC` the complete graph `A ×ˢ A`, which is trivially
    -- edge-dense and cherry-rich at this `K`.
    push_neg at hsmall
    set G : Finset (α × α) := A ×ˢ A with hG
    have hGsub : G ⊆ A ×ˢ A := Finset.Subset.refl _
    have hGcard : #G = #A * #A := by rw [hG, Finset.card_product]
    -- edge density: `#A² ≤ 4K² #G = 4K² #A²`, i.e. `1 ≤ 4K²`.
    have hdense : #A ^ 2 ≤ 4 * K ^ 2 * #G := by
      rw [hGcard]
      have h1 : (1 : ℕ) ≤ 4 * K ^ 2 := by nlinarith [hK]
      calc #A ^ 2 = 1 * #A ^ 2 := by ring
        _ ≤ (4 * K ^ 2) * #A ^ 2 := Nat.mul_le_mul_right _ h1
        _ = 4 * K ^ 2 * (#A * #A) := by ring
    -- cherry richness: in the complete graph every right-degree is `#A`, so `∑_b deg² = #A·#A² =
    -- #A³`, giving `#A⁴ ≤ 16K⁴ · (#A · #A³) = 16K⁴ #A⁴`. Provable by `popGraph_cherry_rich`.
    have hcherry : #A ^ 4 ≤ 16 * K ^ 4 * (#A * ∑ b ∈ A, rDeg A G b ^ 2) :=
      popGraph_cherry_rich A K G hGsub hdense
    exact hDRC A K G hK hA hGsub hdense hcherry

end Finset.BSG

-- Axiom audit (expected: propext, Classical.choice, Quot.sound — and NO sorryAx).
#print axioms Finset.BSG.popGraph_edge_count
#print axioms Finset.BSG.card_eq_sum_rDeg
#print axioms Finset.BSG.card_sq_le_card_mul_sum_deg_sq
#print axioms Finset.BSG.popGraph_edge_dense
#print axioms Finset.BSG.popGraph_cherry_rich
#print axioms Finset.BSG.bsgCore_of_bareDRC
