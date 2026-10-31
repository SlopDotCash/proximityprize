/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Research.ProximityPrize.Frontier._BSG_Reduce
import Research.ProximityPrize.Frontier._BSG_DRC1
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# BSG — dependent random choice (DRC), step 2: the proven averaging core + the irreducible kernel

This file attacks the residual `BareDRC` (the energy-free dependent-random-choice extraction left
open by `_BSG_Reduce.lean`).

**Status correction.** `BareDRC` and the `DRCKernel` defined here are both **false for every choice
of constants** (`bareDRC_false`, `drcKernel_false` in `_BSG_EX_BareDRCExtractFalse.lean`). At
`K = 1` the complete graph `G = A ×ˢ A` on any nonempty `A` meets the squared-neighbourhood
premise of `DRCKernel` (`#A² ≤ 16 · #A²`), and a large Sidon set has no constant-fraction subset
with linear doubling. So `DRCKernel` is not an open residual and no refinement/Plünnecke argument
can discharge it: it discards the additive-energy information the genuine argument uses. The
reduction `bareDRC_of_kernel` below is valid but vacuous. The averaging core
`exists_large_left_neighborhood` is a genuine, reusable lemma. The energy-coupled replacement is
`DRCKernelEnergy` (`_BSGC_attempt4.lean`), still open.

The original (now superseded) plan of this file was:

1. **PROVE the averaging core of DRC** (`exists_large_left_neighborhood`). This is the genuinely
   provable, constant-explicit heart of dependent random choice: from the *cherry-richness*
   hypothesis `#A⁴ ≤ 16 K⁴ · (#A · ∑_b deg(b)²)` it extracts, by a pure pigeonhole/averaging
   argument on `∑_b deg(b)²`, a **specific right-vertex `b` whose left-neighbourhood is large**:
   `#A² ≤ 16 K⁴ · deg(b)²`, i.e. `deg(b) ≥ #A / (4K²)`. This is exactly the "pick the vertex that
   maximises the (squared) neighbourhood size" move at the start of DRC — and it is now a theorem,
   axiom-clean, with the constants tracked.

2. **State the smallest irreducible kernel `DRCKernel`** that remains after the averaging core is
   discharged, and **PROVE `BareDRC ← DRCKernel`** (`bareDRC_of_kernel`, axiom-clean). `DRCKernel`
   is *strictly smaller* than `BareDRC`: it no longer has to manufacture or average over the graph;
   it is handed the single large-neighbourhood vertex `b` (with `#A² ≤ 16 K⁴ deg(b)²` already
   established) and must only perform the **refinement + Plünnecke–Ruzsa** step that converts the
   large neighbourhood `A' = N(b)` together with the "few bad pairs" control into the small-doubling
   conclusion. The energy layer is gone (discharged in `_BSG_Reduce`); the averaging layer is gone
   (discharged here); only the refinement/Plünnecke layer remains as the named open residual.

## What is PROVEN here (axiom-clean, no `sorry`)

* `card_filter_left_eq_rDeg` — `#{a ∈ A | (a,b) ∈ G} = rDeg A G b` (definitional bridge).
* `exists_large_left_neighborhood` — **the DRC averaging core**: cherry-richness ⟹ a single
  vertex with a squared neighbourhood `≥ #A² / (16K⁴)`. Pure `Finset.exists_le_of_sum_le`
  pigeonhole.
* `bareDRC_of_kernel : DRCKernel C₁ C₂ c → BareDRC C₁ C₂ c` — the reduction wiring the averaging
  core into `BareDRC`, leaving only `DRCKernel`.

## What was left (REFUTED, not open)

* `DRCKernel` — intended as the refinement + Plünnecke–Ruzsa step in isolation. It is **false for
  every choice of constants** (`drcKernel_false`), so it is not a remaining residual.

## Status

The averaging core of DRC is proven outright. `BareDRC` is reduced to `DRCKernel`, but both are
refuted for all constants, so the reduction carries no content toward `BSGCore`.

## References

* W. T. Gowers, *A new proof of Szemerédi's theorem for AP4* (1998), §6.
* T. Tao, V. Vu, *Additive Combinatorics*, Cambridge (2006), Theorem 2.29 + Corollary 2.30
  (dependent random choice; the averaging step is the `∑ deg²` pigeonhole proven here).
-/

open Finset
open scoped BigOperators Pointwise

namespace Finset.BSG

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-! ## Definitional bridge: the left-neighbourhood card is the right-degree -/

/-- The **left-neighbourhood** of a right-vertex `b` in `G ⊆ A ×ˢ A`. Its cardinality is `rDeg`.
Compatibility alias for the canonical `leftNbhd` of `_BSG_DRC1` (kept so existing statements that
mention `leftNbhdDRC2` are unchanged). -/
noncomputable def leftNbhdDRC2 (A : Finset α) (G : Finset (α × α)) (b : α) : Finset α :=
  leftNbhd A G b

@[simp] lemma card_leftNbhdDRC2 (A : Finset α) (G : Finset (α × α)) (b : α) :
    #(leftNbhdDRC2 A G b) = rDeg A G b := rfl

/-! ## The DRC averaging core (PROVEN)

The single genuinely-provable heart of dependent random choice: averaging `∑_b deg(b)²` against the
cherry-richness bound produces a *specific* large neighbourhood. -/

/-- **DRC averaging core (PROVEN).** From cherry-richness `#A⁴ ≤ 16 K⁴ · (#A · ∑_b deg(b)²)` with
`A` nonempty, there is a right-vertex `b ∈ A` whose left-neighbourhood `N(b)` is large:
`#A² ≤ 16 K⁴ · deg(b)²` (equivalently `#N(b) = deg(b) ≥ #A / (4K²)`).

Proof. Cancel `#A` (nonempty) in cherry-richness to get `#A³ ≤ 16 K⁴ · ∑_b deg(b)²`. Rewrite
`#A³ = ∑_{b∈A} #A²` (constant sum over `#A` terms) and pull the constant `16K⁴` inside the sum:
`∑_{b∈A} #A² ≤ ∑_{b∈A} 16 K⁴ deg(b)²`. `Finset.exists_le_of_sum_le` (pigeonhole) yields the vertex.
-/
theorem exists_large_left_neighborhood (A : Finset α) (K : ℕ) (G : Finset (α × α))
    (hA : A.Nonempty)
    (hcherry : #A ^ 4 ≤ 16 * K ^ 4 * (#A * ∑ b ∈ A, rDeg A G b ^ 2)) :
    ∃ b ∈ A, #A ^ 2 ≤ 16 * K ^ 4 * rDeg A G b ^ 2 := by
  classical
  have hApos : 0 < #A := hA.card_pos
  -- Step 1: cancel one factor of `#A` from cherry-richness: `#A³ ≤ 16 K⁴ · ∑ deg²`.
  have hcube : #A ^ 3 ≤ 16 * K ^ 4 * ∑ b ∈ A, rDeg A G b ^ 2 := by
    have hfac : #A * #A ^ 3 ≤ #A * (16 * K ^ 4 * ∑ b ∈ A, rDeg A G b ^ 2) := by
      calc #A * #A ^ 3 = #A ^ 4 := by ring
        _ ≤ 16 * K ^ 4 * (#A * ∑ b ∈ A, rDeg A G b ^ 2) := hcherry
        _ = #A * (16 * K ^ 4 * ∑ b ∈ A, rDeg A G b ^ 2) := by ring
    exact Nat.le_of_mul_le_mul_left hfac hApos
  -- Step 2: rewrite `#A³` as the constant sum `∑_{b∈A} #A²`.
  have hconst : ∑ _b ∈ A, #A ^ 2 = #A ^ 3 := by
    rw [Finset.sum_const, smul_eq_mul]; ring
  -- Step 3: pigeonhole `∑_{b∈A} #A² ≤ ∑_{b∈A} 16 K⁴ deg(b)²`.
  have hsumle : ∑ _b ∈ A, #A ^ 2 ≤ ∑ b ∈ A, 16 * K ^ 4 * rDeg A G b ^ 2 := by
    rw [hconst]
    calc #A ^ 3 ≤ 16 * K ^ 4 * ∑ b ∈ A, rDeg A G b ^ 2 := hcube
      _ = ∑ b ∈ A, 16 * K ^ 4 * rDeg A G b ^ 2 := by rw [Finset.mul_sum]
  -- Step 4: `exists_le_of_sum_le` extracts the vertex.
  obtain ⟨b, hbA, hb⟩ := Finset.exists_le_of_sum_le hA hsumle
  exact ⟨b, hbA, hb⟩

/-! ## The kernel `DRCKernel` (REFUTED for all constants)

`DRCKernel` was meant to package the **refinement + Plünnecke** step left after the energy layer
(`_BSG_Reduce`) and the averaging layer (above) are stripped: it is handed the large-neighbourhood
vertex `b` (with the squared-degree bound) and must produce the small-doubling subset. Because its
hypotheses mention neither additive energy nor any property of `G` beyond one large neighbourhood,
it is false for every choice of constants (`drcKernel_false`,
`_BSG_EX_BareDRCExtractFalse.lean`). -/

/-- **The DRC kernel `DRCKernel` (refinement + Plünnecke, in isolation) — REFUTED for all constants
by `drcKernel_false`.**

Hypothesis (post-averaging, energy-free *and* graph-sum-free): a graph `G ⊆ A ×ˢ A` and a single
right-vertex `b ∈ A` whose left-neighbourhood `N(b) = leftNbhdDRC2 A G b` is large
(`#A² ≤ 16 K⁴ · #N(b)²`).

Conclusion: the BSG output — a constant-fraction subset `A'` with a controlled difference set.

This proposition is unsatisfiable: at `K = 1` the complete graph on a large Sidon set satisfies
the hypothesis, while no constant-fraction subset of a large Sidon set has linear doubling. -/
def DRCKernel (C₁ C₂ c : ℕ) : Prop :=
  ∀ {α : Type} [inst : AddCommGroup α] [inst2 : DecidableEq α],
    ∀ (A : Finset α) (K : ℕ) (G : Finset (α × α)) (b : α),
      0 < K → A.Nonempty → G ⊆ A ×ˢ A → b ∈ A →
      #A ^ 2 ≤ 16 * K ^ 4 * (#(leftNbhdDRC2 A G b)) ^ 2 →
      ∃ A' : Finset α, A' ⊆ A ∧ A'.Nonempty ∧
        C₁ * K * #A' ≥ #A ∧ #(A' - A') ≤ C₂ * K ^ c * #A'

/-! ## The reduction `BareDRC ← DRCKernel` (PROVEN axiom-clean) -/

/-- **`BareDRC ← DRCKernel`.** Given the bare refinement kernel `DRCKernel`, the full energy-free
extraction `BareDRC` follows: the averaging core `exists_large_left_neighborhood` discharges the
cherry-richness hypothesis into the single large-neighbourhood vertex that `DRCKernel` consumes.

The edge-density hypothesis of `BareDRC` is not even needed for this wiring — cherry-richness alone
drives the averaging core — so it is simply not forwarded. The implication is valid but vacuous,
since `DRCKernel` is false for all constants (`drcKernel_false`). -/
theorem bareDRC_of_kernel {C₁ C₂ c : ℕ} (hker : DRCKernel C₁ C₂ c) :
    BareDRC C₁ C₂ c := by
  intro α _ _ A K G hK hA hGsub _hdense hcherry
  classical
  -- Averaging core: extract the large-neighbourhood vertex `b`.
  obtain ⟨b, hbA, hb⟩ := exists_large_left_neighborhood A K G hA hcherry
  -- Translate `rDeg A G b` to `#(leftNbhdDRC2 A G b)` (definitionally equal).
  have hb' : #A ^ 2 ≤ 16 * K ^ 4 * (#(leftNbhdDRC2 A G b)) ^ 2 := by
    rwa [card_leftNbhdDRC2]
  -- Hand off to the kernel.
  exact hker A K G b hK hA hGsub hbA hb'

end Finset.BSG

-- Axiom audit (expected: propext, Classical.choice, Quot.sound — and NO sorryAx).
#print axioms Finset.BSG.card_leftNbhdDRC2
#print axioms Finset.BSG.exists_large_left_neighborhood
#print axioms Finset.BSG.bareDRC_of_kernel
