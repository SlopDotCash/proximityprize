/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BSG_DRC1

/-!
# BSG — refutation of `BareDRCExtract` at the trivial constants `(1,1,1)` (negative brick)

`BareDRCExtract C₁ C₂ c` is the post-averaging dependent-random-choice extraction residual
(`_BSG_DRC1.lean`). At the **trivial constants** `C₁ = C₂ = c = 1` it is **false**: this file
exhibits a machine-checked countermodel and proves `¬ BareDRCExtract 1 1 1`.

## The countermodel

Carrier `α = ZMod 7`, `A = {0, 1, 3}` (a Sidon / `B₂` set: all `3·3 = 9` ordered differences
land on `7` *distinct* values, so `#(A - A) = 7`), `K = 1`, `G = A ×ˢ A` the complete bipartite
graph, `b₀ = 0`.

* All three hypotheses of `BareDRCExtract` hold at this instance:
  - edge-density `#A² ≤ 4K²·#G`: `9 ≤ 36` (since `#G = #(A ×ˢ A) = 9`);
  - cherry-richness `#A⁴ ≤ 16K⁴·(#A · ∑_b deg(b)²)`: each `deg(b) = #A = 3`, the diagonal term
    alone gives `∑_b deg(b)² ≥ 9`, so `16·(3·9) = 432 ≥ 81`;
  - apex `#A ≤ 4K²·deg(b₀)`: `3 ≤ 12`.
* The conclusion fails. With `C₁ = C₂ = c = K = 1` it demands
  `A' ⊆ A`, `#A' ≥ #A = 3`, and `#(A' - A') ≤ #A'`. From `A' ⊆ A` and `#A' ≥ 3 = #A` we get
  `A' = A`, hence `#(A' - A') = #(A - A) = 7 > 3 = #A'`. Contradiction.

This is a **negative result**: at the trivial constants the extraction step cannot hold; a Sidon
set is the canonical obstruction (a small-doubling refinement of constant density is impossible
when the whole set already has the maximal doubling `#(A-A) ≈ #A²`).

The countermodel is verified by `decide` (over the finite carrier `ZMod 7`), `Finset.single_le_sum`,
and `Finset.eq_of_subset_of_card_le`; no `sorry`, `native_decide`, or extra axioms.
-/

open Finset
open scoped BigOperators Pointwise

namespace Finset.BSG

/-- The witness set `A = {0, 1, 3} ⊆ ZMod 7`: a Sidon set with maximal doubling `#(A - A) = 7`. -/
def exA : Finset (ZMod 7) := {0, 1, 3}

/-- The complete bipartite graph `G = A ×ˢ A` on the witness set. -/
def exG : Finset (ZMod 7 × ZMod 7) := exA ×ˢ exA

@[simp] lemma card_exA : #exA = 3 := by decide

/-- `A - A` is everything in `ZMod 7`: the Sidon property gives the maximal doubling. -/
@[simp] lemma card_exA_sub : #(exA - exA) = 7 := by decide

@[simp] lemma card_exG : #exG = 9 := by decide

/-- Every right-vertex `b ∈ A` has full left-degree `#A = 3` in the complete graph `G = A ×ˢ A`. -/
lemma rDeg_exG (b : ZMod 7) (hb : b ∈ exA) : rDeg exA exG b = 3 := by
  revert hb
  revert b
  decide

/-- **Refutation brick.** `BareDRCExtract` is **false** at the trivial constants `(1, 1, 1)`. -/
theorem bareDRCExtract_false_1_1_1 : ¬ Finset.BSG.BareDRCExtract 1 1 1 := by
  intro h
  -- The three hypotheses, supplied as `#A`-cleared numeric facts at this instance.
  have hKpos : (0 : ℕ) < 1 := one_pos
  have hAne : exA.Nonempty := ⟨0, by decide⟩
  have hGsub : exG ⊆ exA ×ˢ exA := by rw [exG]
  have hb₀ : (0 : ZMod 7) ∈ exA := by decide
  -- h1 : edge-density `#A² ≤ 4·K²·#G`,  9 ≤ 36.
  have h1 : #exA ^ 2 ≤ 4 * (1 : ℕ) ^ 2 * #exG := by
    simp only [card_exA, card_exG]; norm_num
  -- h2 : cherry-richness.  Bound the cherry sum below by its `b₀ = 0` diagonal term `deg(0)² = 9`.
  have hsum_ge : (3 : ℕ) ^ 2 ≤ ∑ b ∈ exA, rDeg exA exG b ^ 2 := by
    have hterm : rDeg exA exG (0 : ZMod 7) ^ 2 ≤ ∑ b ∈ exA, rDeg exA exG b ^ 2 :=
      Finset.single_le_sum (f := fun b => rDeg exA exG b ^ 2)
        (fun i _ => Nat.zero_le _) hb₀
    rw [rDeg_exG 0 hb₀] at hterm
    exact hterm
  have h2 : #exA ^ 4 ≤ 16 * (1 : ℕ) ^ 4 * (#exA * (∑ b ∈ exA, rDeg exA exG b ^ 2)) := by
    rw [card_exA]
    calc (3 : ℕ) ^ 4 = 81 := by norm_num
      _ ≤ 16 * 1 ^ 4 * (3 * 3 ^ 2) := by norm_num
      _ ≤ 16 * 1 ^ 4 * (3 * (∑ b ∈ exA, rDeg exA exG b ^ 2)) := by
            have := hsum_ge
            exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this)
  -- h3 : apex `#A ≤ 4·K²·deg(b₀)`,  3 ≤ 12.
  have h3 : #exA ≤ 4 * (1 : ℕ) ^ 2 * rDeg exA exG (0 : ZMod 7) := by
    rw [card_exA, rDeg_exG 0 hb₀]; norm_num
  -- Apply the (assumed) extraction to obtain a small-doubling refinement `A'`.
  obtain ⟨A', hsub, _hne, hsize, hdoub⟩ :=
    h exA 1 exG 0 hKpos hAne hGsub hb₀ h1 h2 h3
  -- `hsize : 1 · 1 · #A' ≥ #A`, i.e. `#A' ≥ 3`; combined with `#A' ≤ #A = 3` forces `A' = A`.
  have hsubcard : #A' ≤ #exA := Finset.card_le_card hsub
  rw [card_exA] at hsubcard
  have hge3 : (3 : ℕ) ≤ #A' := by
    have : (1 : ℕ) * 1 * #A' ≥ #exA := hsize
    rw [card_exA] at this
    simpa using this
  have hAeq : A' = exA := Finset.eq_of_subset_of_card_le hsub (by rw [card_exA]; omega)
  subst hAeq
  -- `hdoub : #(A' - A') ≤ 1 · 1^1 · #A'`, i.e. `#(A - A) ≤ #A = 3`; but `#(A - A) = 7`.
  rw [card_exA_sub] at hdoub
  have : (7 : ℕ) ≤ 1 * 1 ^ 1 * #exA := hdoub
  rw [card_exA] at this
  omega

end Finset.BSG

-- Axiom audit (expected: propext, Classical.choice, Quot.sound — and NO sorryAx).
#print axioms Finset.BSG.bareDRCExtract_false_1_1_1
