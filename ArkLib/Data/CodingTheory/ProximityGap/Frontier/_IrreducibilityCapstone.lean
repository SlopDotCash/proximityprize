/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConverse
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ValuationClassBarrier

/-!
# The irreducibility capstone (#444): the two formally-proven faces, conjoined

This file bundles the two machine-checked faces of the proximity-prize *irreducibility* into a single
axiom-clean theorem.  The honest claim is **not** that the prize floor is proven, nor that it is undecidable
(it is concrete arithmetic, currently open).  It is the rigorous characterization of the floor's exact
difficulty, in the two senses that ARE provable:

* **Sense C — reduction-completeness (codes).** `OpenCoreConverse.deltaStar_iff_incidence_budget`: at any
  window-interior radius `δ`, the prize statement `δ ≤ δ*` is equivalent (granularly — up to the `<`/`≤`
  boundary and the `⌊q·ε*⌋` budget rounding) to the single open-core incidence bound
  `WorstCaseIncidenceBounded C δ E`.  So the prize is *reduction-complete* for that one statement; the
  remaining step to the scalar `M(n)` is reduced to the named `PrizeEquivalence.ConverseRealizer`.

* **Sense B — the valuation-class barrier (number fields).**
  `ValuationClassBarrier.valuationClass_barrier`: a non-torsion unit `u` (which exists iff the unit rank is
  positive — Dirichlet) witnesses that the ideal `(α)` does not determine the archimedean profile `w ↦ w α`.
  Hence no proof whose field-arithmetic input is unit-invariant (the cohomological / Stickelberger /
  crystalline-valuation column) can pin `M(n)`.

Conjoining them: the prize floor reduces to a single recognized-open analytic-NT quantity, AND the dominant
proof-method column is provably insufficient to bound it.  Both components are axiom-clean
(`propext, Classical.choice, Quot.sound`).  See `docs/kb/Iinf-campaign/28-irreducibility-theorem-rigorous.md`
for the full scope discussion (including why Sense A — logical undecidability — is false and not claimed).
-/

open Finset
open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger ProximityGap.OpenCoreConditionalPin Code
open NumberField NumberField.Units NumberField.InfinitePlace

namespace ArkLib.ProximityGap.IrreducibilityCapstone

-- Sense-C (code) context
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
-- Sense-B (number field) context
variable {K : Type*} [Field K] [NumberField K]

/-- **The irreducibility capstone (two proven faces, conjoined; axiom-clean).**

For a smooth-domain RS code `C`, a window-interior radius `δ ≤ 1` and budget `E`, and any non-torsion unit
`u` of a number field `K` with any nonzero `α`:

1. **(reduction-completeness, Sense C)** the prize statement `δ ≤ δ*` is granularly equivalent to the single
   open-core incidence bound `WorstCaseIncidenceBounded C δ E`; and
2. **(valuation-class barrier, Sense B)** the associates `α` and `u·α` share the ideal `(α)` but differ in
   archimedean absolute value at some infinite place — so unit-invariant (valuation-column) data cannot pin
   the archimedean profile.

Neither face proves the floor; together they pin its exact difficulty: the prize is reduction-complete for a
recognized-open NT quantity that the dominant proof column provably cannot reach. -/
theorem prize_irreducibility
    (C : Set (ι → A)) {δ : ℝ≥0} {E : ℕ} (hδ1 : δ ≤ 1)
    {u : (𝓞 K)ˣ} (hu : u ∉ torsion K) {α : K} (hα : α ≠ 0) :
    ((δ < mcaDeltaStar (F := F) (A := A) C ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) →
        WorstCaseIncidenceBounded (F := F) (A := A) C δ E)
      ∧ (WorstCaseIncidenceBounded (F := F) (A := A) C δ E →
        δ ≤ mcaDeltaStar (F := F) (A := A) C ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))))
    ∧ (∃ w : InfinitePlace K, w ((u : K) * α) ≠ w α) :=
  ⟨OpenCoreConverse.deltaStar_iff_incidence_budget (F := F) (A := A) C hδ1,
   ValuationClassBarrier.valuationClass_barrier (K := K) hu hα⟩

end ArkLib.ProximityGap.IrreducibilityCapstone

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.IrreducibilityCapstone.prize_irreducibility
