/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CensusDominationWeld
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.AlignableLePinnedMaxMult

/-!
# The census-domination SUFFICIENCY reduction: the two sub-obligations IMPLY the `$1M` Prop
# (#444 census face)

`CensusDominationWeld` proves the deployed `δ*` pin **conditional on** the named Prop
`CensusDomination dom k a₀ K` (every stack has at most `K` alignable `a`-sets at every band
`a ≥ a₀`), and `AlignableLePinnedMaxMult.alignableSets_card_le_budget` proves the per-band
incidence cap `#alignableSets ≤ K` from a distinct-`γ` cap `P`, a per-scalar multiplicity cap
`M`, and `P · M ≤ K`.  But the two were **never connected**: every site *consumes*
`CensusDomination` as a hypothesis; **no theorem PRODUCES it** from the per-band sub-bounds.

This file supplies the missing **sufficiency reduction**.  First the definitional bridge

  **`censusDomination_iff_alignableSets`** : the inlined filter in `CensusDomination` is exactly
  the `alignableSets` census object, so `CensusDomination dom k a₀ K ↔
    ∀ u₀ u₁, ∀ a ≥ a₀, (alignableSets dom k a u₀ u₁).card ≤ K`.

Then the headline lift, turning the per-band `alignableSets_card_le_budget` into the actual Prop:

  **`censusDomination_of_caps`** : if for every `u₀ u₁` and every band `a ≥ a₀` the distinct-`γ`
  count is `≤ P` and every pinned scalar owns `≤ M` aligned `a`-sets, and `P · M ≤ K`, then
  `CensusDomination dom k a₀ K`.

So the `$1M` obligation the weld consumes is now *implied* (not merely "consumed") by the two
census sub-obligations the prior bricks isolated: a uniform distinct-`γ` bound and a uniform
per-scalar multiplicity bound.  This is the equivalence between the census-partition incidence cap
and the deployed Prop that the prose asserted but the tree never carried.

## Scope (rule 3 / rule 6, honesty contract)

NOT a CORE closure, NOT thinness-essential: this is the *logical* assembly (∀-introduction over
bands + the per-band product cap), field-universal and thickness-independent.  It does NOT supply
`P` (the distinct-`γ` cap at the prize band) nor `M` (the per-scalar multiplicity cap at the prize
band), BOTH remain open; the open `M(μ_n) ≤ C√(n log(p/n))` CORE is UNTOUCHED.  What it adds: the
sufficiency direction was a genuine gap, the weld asserts `CensusDomination` as a black-box
hypothesis, and this file is the first theorem that DISCHARGES that hypothesis from the in-tree
per-band incidence cap, closing the assembly between the two halves the census cluster built.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {p : ℕ} [Fact p.Prime]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The definitional bridge.**  The inlined filter that `CensusDomination` counts is exactly the
`alignableSets` census object, so the Prop is the per-band incidence cap on `alignableSets`. -/
theorem censusDomination_iff_alignableSets (dom : Fin n ↪ ZMod p) (k a₀ K : ℕ) :
    CensusDomination dom k a₀ K ↔
      ∀ u₀ u₁ : Fin n → ZMod p, ∀ a : ℕ, a₀ ≤ a →
        (alignableSets dom k a u₀ u₁).card ≤ K := by
  unfold CensusDomination alignableSets Aligned
  rfl

open Classical in
/-- **The sufficiency reduction (headline).**  If for every word pair `u₀ u₁` and every deep band
`a ≥ a₀` the distinct-`γ` count is at most `P` (`#pinnedScalars ≤ P`) and every pinned scalar owns
at most `M` aligned `a`-sets, and the budget `P · M ≤ K`, then `CensusDomination dom k a₀ K` holds.

This DISCHARGES the `CensusDomination` hypothesis the `δ*`-weld consumes, reducing it to the two
in-tree census sub-obligations: a uniform distinct-`γ` cap and a uniform per-scalar multiplicity
cap.  Engine: `alignableSets_card_le_budget` at each band, packaged under the band quantifier. -/
theorem censusDomination_of_caps (dom : Fin n ↪ ZMod p) (k a₀ : ℕ) {P M K : ℕ}
    (hPMK : P * M ≤ K)
    (hP : ∀ u₀ u₁ : Fin n → ZMod p, ∀ a : ℕ, a₀ ≤ a →
      (pinnedScalars dom k a u₀ u₁).card ≤ P)
    (hM : ∀ u₀ u₁ : Fin n → ZMod p, ∀ a : ℕ, a₀ ≤ a →
      ∀ γ ∈ pinnedScalars dom k a u₀ u₁,
        (alignedSetsForScalar dom k a u₀ u₁ γ).card ≤ M) :
    CensusDomination dom k a₀ K := by
  rw [censusDomination_iff_alignableSets]
  intro u₀ u₁ a ha
  exact alignableSets_card_le_budget dom k a u₀ u₁ (hP u₀ u₁ a ha) (hM u₀ u₁ a ha) hPMK

open Classical in
/-- **The exact-budget specialization.**  Taking `K = P · M` directly, the uniform distinct-`γ` cap
`P` and per-scalar multiplicity cap `M` give `CensusDomination dom k a₀ (P · M)`, the sharpest
budget the factorization yields. -/
theorem censusDomination_of_caps_exact (dom : Fin n ↪ ZMod p) (k a₀ : ℕ) {P M : ℕ}
    (hP : ∀ u₀ u₁ : Fin n → ZMod p, ∀ a : ℕ, a₀ ≤ a →
      (pinnedScalars dom k a u₀ u₁).card ≤ P)
    (hM : ∀ u₀ u₁ : Fin n → ZMod p, ∀ a : ℕ, a₀ ≤ a →
      ∀ γ ∈ pinnedScalars dom k a u₀ u₁,
        (alignedSetsForScalar dom k a u₀ u₁ γ).card ≤ M) :
    CensusDomination dom k a₀ (P * M) :=
  censusDomination_of_caps dom k a₀ (le_refl _) hP hM

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.censusDomination_iff_alignableSets
#print axioms ProximityGap.Ownership.censusDomination_of_caps
#print axioms ProximityGap.Ownership.censusDomination_of_caps_exact
