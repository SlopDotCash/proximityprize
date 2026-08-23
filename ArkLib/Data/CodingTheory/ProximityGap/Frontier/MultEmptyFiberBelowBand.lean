/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.MultUpperAgreementBinom

/-!
# The census multiplicity VANISHES below the band: `|A_γ| < a ⟹ mult γ = 0` (#444 census face)

`MultUpperAgreementBinom` brackets the per-scalar census multiplicity
`mult γ := #(alignedSetsForScalar dom k a u₀ u₁ γ)` between two agreement-set binomials,

  `C(|A_γ| − (k+1), a − (k+1)) ≤ mult γ ≤ C(|A_γ|, a)`,     `A_γ = agreementSet dom u₀ u₁ γ c`,

under the common-explainer hypothesis (`c` matches the `γ`-pencil on every non-degenerate
`γ`-aligned `a`-set).  The upper binomial `C(|A_γ|, a)` is already `0` whenever `|A_γ| < a` — but
that arithmetic fact was never lifted to the SET-level statement that the census consumer wants:
**a scalar whose agreement set does not reach the band size `a` owns NO aligned `a`-set**, i.e. it
is not pinned and contributes `0` to the incidence count.

This file lands that empty-fibre lemma, grep-confirmed missing:

* **`alignedSetsForScalar_eq_empty_of_agreement_lt`** : if `|A_γ| < a` (under the common-explainer
  `hc`), then `alignedSetsForScalar dom k a u₀ u₁ γ = ∅`.
* **`mult_eq_zero_of_agreement_lt`** : hence `mult γ = 0`.
* **`not_mem_pinnedScalars_of_agreement_lt`** : hence `γ ∉ pinnedScalars`, so the distinct-`γ`
  census ranges ONLY over band-reaching scalars (`|A_γ| ≥ a`).

## Why this is the lever the census-domination obligation consumes

`CensusDomination` (the `δ*`-pinning Prop welded to the `$1M` floor in `CensusDominationWeld`)
caps the incidence count `#alignableSets = Σ_{pinned γ} mult γ`.  The sufficiency reduction
(`censusDomination_of_caps`) factors that cap into a distinct-`γ` count cap `#pinnedScalars ≤ P`
and a per-scalar multiplicity cap `mult γ ≤ M`.  This lemma is the structural *support* refinement
of the `P`-side: it identifies the pinned scalars as exactly the **band-reaching** ones
(`|A_γ| ≥ a`), so any distinct-`γ` cap need only count scalars whose pencil agreement reaches the
band — every below-band scalar is automatically silent.  It is the set-level companion to the
upper binomial: `C(|A_γ|, a) = 0` is the *arithmetic* witness, `alignedSetsForScalar = ∅` is the
*combinatorial* witness, and `mult_eq_zero_of_agreement_lt` welds them.

## Scope (rule 3 / rule 6, honesty contract)

NOT a CORE closure, NOT thinness-essential: this is a field-universal, thickness-independent
combinatorial support fact (`powersetCard` of a set below the band size is empty).  It does NOT
supply the distinct-`γ` cap `P` nor the max-agreement-size cap `s₀ = |A_γ| ≤ ?` (BOTH remain open,
and the latter is precisely the Johnson / cliff-at-`n/2` wall the asymptotic guard flags); the open
`M(μ_n) ≤ C√(n log(p/n))` CORE is UNTOUCHED.  What it adds: the census-support direction was a
genuine gap — the upper binomial gives `mult γ = 0` only *arithmetically* via `C(s, a) = 0` for
`s < a`, never lifted to the set-level emptiness the `pinnedScalars` membership predicate needs.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ProximityGap.Ownership

open ProximityGap.PairRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The empty fibre below the band.**  Under the common-explainer hypothesis `hc` (the deg-`< k`
codeword `c` matches the `γ`-pencil on every non-degenerate `γ`-aligned `a`-set, i.e. `c` explains
the maximal aligned set `A_γ = agreementSet dom u₀ u₁ γ c`), if the agreement set does not reach the
band size `a` (`|A_γ| < a`), then the scalar owns NO aligned `a`-set.

Mechanism: `alignedSetsForScalar ⊆ (A_γ).powersetCard a` (`MultUpperAgreementBinom`), and
`(A_γ).powersetCard a = ∅` exactly when `|A_γ| < a` (`Finset.powersetCard_eq_empty`). -/
theorem alignedSetsForScalar_eq_empty_of_agreement_lt
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (γ : F) {c : Fin n → F}
    (hc : ∀ S ∈ alignedSetsForScalar dom k a u₀ u₁ γ, ∀ i ∈ S, c i = pencil u₀ u₁ γ i)
    (hlt : (agreementSet dom u₀ u₁ γ c).card < a) :
    alignedSetsForScalar dom k a u₀ u₁ γ = ∅ := by
  classical
  have hsub := alignedSetsForScalar_subset_agreement_powersetCard dom k a u₀ u₁ γ hc
  have hpc : (agreementSet dom u₀ u₁ γ c).powersetCard a = ∅ := by
    rw [Finset.powersetCard_eq_empty]
    exact hlt
  rw [hpc] at hsub
  exact Finset.subset_empty.mp hsub

/-- **The per-scalar census multiplicity vanishes below the band.**  Immediate from the empty
fibre: `mult γ = #(alignedSetsForScalar …) = 0` when `|A_γ| < a`.  This is the set-level
counterpart of the upper binomial `C(|A_γ|, a) = 0`. -/
theorem mult_eq_zero_of_agreement_lt
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (γ : F) {c : Fin n → F}
    (hc : ∀ S ∈ alignedSetsForScalar dom k a u₀ u₁ γ, ∀ i ∈ S, c i = pencil u₀ u₁ γ i)
    (hlt : (agreementSet dom u₀ u₁ γ c).card < a) :
    (alignedSetsForScalar dom k a u₀ u₁ γ).card = 0 := by
  rw [alignedSetsForScalar_eq_empty_of_agreement_lt dom k a u₀ u₁ γ hc hlt]
  exact Finset.card_empty

/-- **Below-band scalars are not pinned.**  A scalar whose agreement set does not reach the band
size `a` is `∉ pinnedScalars` (the support of the per-scalar census), so the distinct-`γ` census
`#pinnedScalars` ranges ONLY over band-reaching scalars (`|A_γ| ≥ a`).  This is the support
refinement of the distinct-`γ` (`P`) side of the `CensusDomination` factoring. -/
theorem not_mem_pinnedScalars_of_agreement_lt
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (γ : F) {c : Fin n → F}
    (hc : ∀ S ∈ alignedSetsForScalar dom k a u₀ u₁ γ, ∀ i ∈ S, c i = pencil u₀ u₁ γ i)
    (hlt : (agreementSet dom u₀ u₁ γ c).card < a) :
    γ ∉ pinnedScalars dom k a u₀ u₁ := by
  classical
  rw [mem_pinnedScalars, Finset.nonempty_iff_ne_empty, not_not]
  exact alignedSetsForScalar_eq_empty_of_agreement_lt dom k a u₀ u₁ γ hc hlt

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.alignedSetsForScalar_eq_empty_of_agreement_lt
#print axioms ProximityGap.Ownership.mult_eq_zero_of_agreement_lt
#print axioms ProximityGap.Ownership.not_mem_pinnedScalars_of_agreement_lt
