/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PinnedScalarMultDivision

/-!
# The incidence count is the distinct-γ count INFLATED by the per-scalar multiplicity
# (#444 census face)

`CensusScalarPartition` gives the exact partition `#alignableSets = Σ_{pinned γ} mult(γ)`, and
`PinnedScalarMultDivision` proved the LOWER side `#pinnedScalars · M ≤ #alignableSets` (every pinned
scalar owns at least `M` aligned `a`-sets) ⟹ `#pinnedScalars ≤ #alignableSets / M`.

This file supplies the structural **DUAL**: if every pinned scalar owns AT MOST `M` aligned
`a`-sets, then the incidence count is the distinct-γ count *inflated* by `M`:

  **`#alignableSets ≤ #pinnedScalars · M`**     (`alignableSets_card_le_pinned_mul`).

Engine: `#alignableSets = Σ_{pinned γ} mult(γ)` and each summand is `≤ M`, so the sum is
`≤ #pinnedScalars · M`.  This is the exact reciprocal of `pinnedScalars_card_mul_le_alignable`.

## Why this is the lever the `CensusDomination` obligation consumes

`CensusDominationWeld.CensusDomination` (the `δ*`-pinning Prop, the `$1M` obligation in census
normal form) requires the **incidence** count `#alignableSets ≤ K` at every deep band.  Every
prior census brick (ratio-image, multiplicity-division) bounds the **distinct-γ** count
`#pinnedScalars`, which is the SMALLER object: it does not by itself cap the incidence.  This
dual is the missing bridge: a distinct-γ cap `#pinnedScalars ≤ P` together with a per-scalar
multiplicity cap `mult(γ) ≤ M` yields the incidence cap `#alignableSets ≤ P · M = K`
(`alignableSets_card_le_of_pinned_le_mult_le`).  So the open `CensusDomination` obligation
factors into TWO sub-obligations: a distinct-γ count bound (handle: the ratio-image /
divided-difference image) and a per-scalar multiplicity bound (handle: the agreement-set
binomial of `AgreementSetMaximal`), neither of which is the full incidence count.

Probe `scripts/probes/probe_alignable_le_pinned_maxmult.py` (planted-codeword words on PROPER thin
`μ_n`, `n = 2^a`, prize-regime `p ≫ n³`, `p ≡ 1 mod n`, NEVER `n = q-1`): `#alignableSets ≤
#pinnedScalars · maxMult` holds in every run, and it is EXACTLY TIGHT (`#alignableSets =
#pinnedScalars · maxMult`) at the agreement-structured worst case where all multiplicities coincide
(e.g. `n=16, k=2, a=6, s=12`: `#alignable = 3168 = 4 · 792`).  The probe ALSO records that the
per-scalar `maxMult` is NOT in general bounded by the single-explainer binomial `C(s, a)` (multiple
explainers / non-degenerate tuples contribute), so the multiplicity cap is a genuine second
sub-obligation, not a free corollary of `AgreementSetMaximal`.

## Scope (rule 3 / rule 6, honesty contract)

NOT a CORE closure, NOT thinness-essential: field-universal combinatorics (it holds for any embedded
domain, any `k, a, M`, independent of thickness).  It supplies the reciprocal of the multiplicity
over-count: it bounds the incidence count BY the distinct-γ count inflated by `M`, but it does
NOT supply `M` (the per-scalar multiplicity cap at the prize band) nor the distinct-γ bound `P`.  It
factors the open incidence cap into those two pieces; both stay OPEN.  CORE
(`M(μ_n) ≤ C√(n log(p/n))`) stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The reverse partition bound (incidence ≤ distinct-γ · max multiplicity).**  If every pinned
scalar owns AT MOST `M` aligned `a`-sets, then `#alignableSets ≤ #pinnedScalars · M`.  Engine:
`#alignableSets = Σ_{pinned γ} mult(γ)` and each summand is `≤ M`, so the sum is bounded by
`#pinnedScalars · M`.  The exact dual of `pinnedScalars_card_mul_le_alignable`. -/
theorem alignableSets_card_le_pinned_mul (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    {M : ℕ} (hM : ∀ γ ∈ pinnedScalars dom k a u₀ u₁,
      (alignedSetsForScalar dom k a u₀ u₁ γ).card ≤ M) :
    (alignableSets dom k a u₀ u₁).card ≤ (pinnedScalars dom k a u₀ u₁).card * M := by
  classical
  rw [alignableSets_card_eq_sum_pinned]
  calc ∑ γ ∈ pinnedScalars dom k a u₀ u₁, (alignedSetsForScalar dom k a u₀ u₁ γ).card
      ≤ ∑ _γ ∈ pinnedScalars dom k a u₀ u₁, M := Finset.sum_le_sum hM
    _ = (pinnedScalars dom k a u₀ u₁).card * M := by
        rw [Finset.sum_const, smul_eq_mul]

open Classical in
/-- **The incidence cap from a distinct-γ cap AND a per-scalar multiplicity cap.**  The
`CensusDomination`-facing factorization: if the distinct-γ count is at most `P`
(`#pinnedScalars ≤ P`) and every pinned scalar owns at most `M` aligned `a`-sets, then the incidence
count obeys the product cap

  `#alignableSets ≤ P · M`.

So the open incidence obligation `#alignableSets ≤ K` is implied by `P · M ≤ K` together with the
two sub-bounds: a distinct-γ bound (`#pinnedScalars ≤ P`) and a per-scalar multiplicity bound. -/
theorem alignableSets_card_le_of_pinned_le_mult_le (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    {P M : ℕ} (hP : (pinnedScalars dom k a u₀ u₁).card ≤ P)
    (hM : ∀ γ ∈ pinnedScalars dom k a u₀ u₁,
      (alignedSetsForScalar dom k a u₀ u₁ γ).card ≤ M) :
    (alignableSets dom k a u₀ u₁).card ≤ P * M :=
  le_trans (alignableSets_card_le_pinned_mul dom k a u₀ u₁ hM)
    (Nat.mul_le_mul_right M hP)

open Classical in
/-- **The incidence cap reaches the budget `K`.**  If `#pinnedScalars ≤ P`, every pinned scalar owns
at most `M` aligned `a`-sets, and `P · M ≤ K`, then `#alignableSets ≤ K`, exactly the per-band
incidence bound the `CensusDomination` Prop asserts.  This is the `K`-form of the factorization: it
reduces the open incidence cap to the conjunction of a distinct-γ bound and a per-scalar
multiplicity bound. -/
theorem alignableSets_card_le_budget (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    {P M K : ℕ} (hP : (pinnedScalars dom k a u₀ u₁).card ≤ P)
    (hM : ∀ γ ∈ pinnedScalars dom k a u₀ u₁,
      (alignedSetsForScalar dom k a u₀ u₁ γ).card ≤ M)
    (hPMK : P * M ≤ K) :
    (alignableSets dom k a u₀ u₁).card ≤ K :=
  le_trans (alignableSets_card_le_of_pinned_le_mult_le dom k a u₀ u₁ hP hM) hPMK

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.alignableSets_card_le_pinned_mul
#print axioms ProximityGap.Ownership.alignableSets_card_le_of_pinned_le_mult_le
#print axioms ProximityGap.Ownership.alignableSets_card_le_budget
