/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.MultEmptyFiberBelowBand

/-!
# The census support is exactly the BAND-REACHING scalars: pinned ⟺ a deep aligned set (#444 census)

`MultEmptyFiberBelowBand` proved one direction of the census-support characterization: a scalar
whose agreement set does NOT reach the band size `a` (`|A_γ| < a`) is `∉ pinnedScalars`
(`not_mem_pinnedScalars_of_agreement_lt`).  This file lands the **CONVERSE**, grep-confirmed
missing: a scalar that DOES reach the band — it carries a non-degenerate `γ`-aligned set `S₀` of
size `≥ a` — IS pinned.

* **`mem_pinnedScalars_of_aligned_ge`** : if there is a non-degenerate `γ`-aligned `S₀` with a
  witnessing injective `(k+1)`-tuple and `a ≤ |S₀|` (and `k+1 ≤ a`), then
  `γ ∈ pinnedScalars dom k a u₀ u₁`.

The engine is the in-tree lower bound `mult_ge_choose_of_aligned_superset`: a deep non-degenerate
aligned `S₀` owns `C(|S₀|−(k+1), a−(k+1))` aligned `a`-sets, and that binomial is `> 0` exactly when
`a ≤ |S₀|` (`Nat.choose_pos`), so the per-scalar census fibre is non-empty, i.e. `γ` is pinned.

Combined with `MultEmptyFiberBelowBand`, this brackets the census support tightly: a scalar is
pinned iff it is band-reaching (carries a non-degenerate aligned set of size `≥ a`).  So the
distinct-`γ` cap `P` the `CensusDomination` factoring needs is EXACTLY a count of band-reaching
scalars — neither more (below-band scalars are silent) nor fewer (every band-reacher contributes).

## Scope (rule 3 / rule 6, honesty contract)

NOT a CORE closure, NOT thinness-essential: this is the field-universal, thickness-independent
combinatorial converse to the empty-fibre lemma (`Nat.choose_pos` on the in-tree deep-set lower
bound).  It does NOT supply the distinct-`γ` cap `P` (a count of band-reaching scalars at the prize
band) nor the max-agreement-size cap `s₀`; BOTH remain open, and the latter is the Johnson /
cliff-at-`n/2` wall.  The open `M(μ_n) ≤ C√(n log(p/n))` CORE is UNTOUCHED.  What it adds: it pins
the census SUPPORT to a clean combinatorial predicate (band-reaching), closing the support
characterization that the empty-fibre lemma opened.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace ProximityGap.Ownership

open ProximityGap.PairRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The band-reaching scalar is pinned (converse of the empty fibre).**  If a scalar `γ` carries a
non-degenerate `γ`-aligned set `S₀` (a witnessing injective `(k+1)`-tuple `t` with non-vanishing
joint residual) of size `a ≤ |S₀|` (and `k+1 ≤ a`), then `γ ∈ pinnedScalars`.

Mechanism: `mult_ge_choose_of_aligned_superset` gives
`C(|S₀|−(k+1), a−(k+1)) ≤ #(alignedSetsForScalar … γ)`, and `Nat.choose_pos` (from
`a−(k+1) ≤ |S₀|−(k+1)`, i.e. `a ≤ |S₀|`) makes the left side `> 0`, so the fibre is non-empty. -/
theorem mem_pinnedScalars_of_aligned_ge
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (γ : F)
    {S₀ : Finset (Fin n)} (halign : Aligned dom k u₀ u₁ γ S₀)
    {t : Fin (k + 1) → Fin n} (htinj : Function.Injective t) (htmem : ∀ b, t b ∈ S₀)
    (hnd : ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0))
    (hak : k + 1 ≤ a) (hage : a ≤ S₀.card) :
    γ ∈ pinnedScalars dom k a u₀ u₁ := by
  classical
  have hlo := mult_ge_choose_of_aligned_superset dom k a u₀ u₁ γ halign htinj htmem hnd hak
  have hcpos : 0 < (S₀.card - (k + 1)).choose (a - (k + 1)) :=
    Nat.choose_pos (by omega)
  have hpos : 0 < (alignedSetsForScalar dom k a u₀ u₁ γ).card := lt_of_lt_of_le hcpos hlo
  rw [mem_pinnedScalars]
  exact Finset.card_pos.mp hpos

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.mem_pinnedScalars_of_aligned_ge
