/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ExplainableCoreExactCount
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread

/-!
# The line-core partition: the algebraic constraint the supply wall needs

Issue #389. The extremal analysis (`ExplainableCoreExactCount.lean`) showed the pure
combinatorial packing bound is worst-case vacuous — a word near a single codeword saturates
it — so any sub-trivial supply bound must use the *algebraic* structure of which words arise
as bad-scalar lines `w_γ = u₀ + γ·u₁`. This file supplies exactly that structure for the
case that matters (the direction row `u₁ = xᵏ` is far from the code):

> **`line_core_unique_scalar`** — if `u₁` agrees with every codeword on `< k+m+1` points,
> then each `(k+m+1)`-core `T` is explainable for **at most one** scalar `γ` on the line.

The mechanism is the in-tree slope lever (`line_slope_codeword_of_two_witnesses`): two
explanations of the same core `T` at `γ ≠ γ'` give witnesses `c, c'` with
`c − c' = (γ−γ')·u₁` on `T`, so the codeword `(γ−γ')⁻¹(c−c')` agrees with `u₁` on all of
`T` — impossible when `u₁` is far.

Consequence:

> **`line_total_cores_le`** — when `u₁` is far, the explainable cores **partition** across
> the line: `Σ_γ #cores(u₀ + γ·u₁) ≤ C(n, k+m+1)`.

So even though the *per-scalar* supply is worst-case trivial, the *aggregate over the
bad-scalar line* is bounded by the total core count `C(n,k+m+1)` — exactly the witness-mass
numerator. This is the structural reason the MCA failure mass, spread over the line, stays
controlled: it is the line-level form of the supply, with the far-direction hypothesis
(`u₁ = xᵏ` is the maximally-far row) doing the algebraic work combinatorics cannot.

## References

* Issue #389; `MCAWitnessSpread.lean` (`line_slope_codeword_of_two_witnesses`),
  `ExplainableCoreExactCount.lean` (the extremal refutation), `DeepBandMultiplicity.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap ProximityGap.MCAWitnessSpread

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **Each core has a unique explaining scalar (far direction).** If `u₁` agrees with every
codeword on fewer than `k+m+1` points, then any `(k+m+1)`-core explainable for both `γ` and
`γ'` forces `γ = γ'`. -/
theorem line_core_unique_scalar (dom : Fin n ↪ F) {k m : ℕ}
    {u₀ u₁ : Fin n → F}
    (hfar : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card < k + m + 1)
    {T : Finset (Fin n)} (hT : T.card = k + m + 1) {γ γ' : F}
    (hγ : ExplainableOn dom k (fun i => u₀ i + γ • u₁ i) T)
    (hγ' : ExplainableOn dom k (fun i => u₀ i + γ' • u₁ i) T) :
    γ = γ' := by
  by_contra hne
  obtain ⟨c, hc, hcw⟩ := hγ
  obtain ⟨c', hc', hc'w⟩ := hγ'
  -- the secant slope is a codeword agreeing with u₁ on T
  obtain ⟨hvmem, hvu₁⟩ := line_slope_codeword_of_two_witnesses
    (rsCode dom k : Submodule F (Fin n → F)) hne hc hc' hcw hc'w
  set v : Fin n → F := (γ - γ')⁻¹ • (c - c') with hv
  have hTsub : T ⊆ agreeSet v u₁ := by
    intro i hi
    rw [agreeSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hvu₁ i (Finset.mem_inter.mpr ⟨hi, hi⟩)⟩
  have : k + m + 1 ≤ (agreeSet v u₁).card := by
    calc k + m + 1 = T.card := hT.symm
      _ ≤ (agreeSet v u₁).card := Finset.card_le_card hTsub
  exact absurd this (not_le.mpr (hfar v hvmem))

open Classical in
/-- **The line-core partition.** When `u₁` is far from the code (agreement `< k+m+1` with
every codeword), the explainable cores along the line `u₀ + γ·u₁` are pairwise disjoint
across scalars, so their total is at most the full `(k+m+1)`-core count:
`Σ_γ #cores(u₀ + γ·u₁) ≤ C(n, k+m+1)`. -/
theorem line_total_cores_le (dom : Fin n ↪ F) {k : ℕ} (m : ℕ)
    {u₀ u₁ : Fin n → F}
    (hfar : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card < k + m + 1) :
    ∑ γ : F, (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ExplainableOn dom k (fun i => u₀ i + γ • u₁ i) T)).card
      ≤ n.choose (k + m + 1) := by
  classical
  set a : ℕ := k + m + 1 with ha
  set cores : F → Finset (Finset (Fin n)) := fun γ =>
    ((Finset.univ : Finset (Fin n)).powersetCard a).filter
      (fun T => ExplainableOn dom k (fun i => u₀ i + γ • u₁ i) T) with hcores
  -- the per-scalar core families are pairwise disjoint
  have hdisj : ∀ γ ∈ (Finset.univ : Finset F), ∀ γ' ∈ (Finset.univ : Finset F),
      γ ≠ γ' → Disjoint (cores γ) (cores γ') := by
    intro γ _ γ' _ hne
    rw [Finset.disjoint_left]
    intro T hT hT'
    obtain ⟨hTmem, hTexp⟩ := Finset.mem_filter.mp hT
    obtain ⟨-, hT'exp⟩ := Finset.mem_filter.mp hT'
    obtain ⟨-, hTcard⟩ := Finset.mem_powersetCard.mp hTmem
    exact hne (line_core_unique_scalar dom hfar hTcard hTexp hT'exp)
  calc ∑ γ : F, (cores γ).card
      = ((Finset.univ : Finset F).biUnion cores).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ ((Finset.univ : Finset (Fin n)).powersetCard a).card := by
        refine Finset.card_le_card ?_
        intro T hT
        obtain ⟨γ, -, hTγ⟩ := Finset.mem_biUnion.mp hT
        exact (Finset.mem_filter.mp hTγ).1
    _ = n.choose a := by
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-! ## Source audit -/

#print axioms line_core_unique_scalar
#print axioms line_total_cores_le

end ProximityGap.Ownership
