/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.AgreementSetMaximal
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CensusScalarPartition

/-!
# The per-scalar census multiplicity is capped by ONE agreement-set binomial (#444)

`CensusScalarPartition.mult_ge_choose_of_aligned_superset` proves the in-tree LOWER bound on
the per-scalar census multiplicity `mult γ := #(alignedSetsForScalar dom k a u₀ u₁ γ)` (the
non-degenerate `γ`-aligned `a`-sets):

  `C(|A_γ| − (k+1), a − (k+1)) ≤ mult γ`     (a deep aligned set of size `|A_γ|` owns all the
  `a`-subsets through its non-degenerate tuple).

This file lands the **EXACT UPPER companion**, grep-confirmed missing: the matching cap by a
SINGLE binomial in the agreement-set size,

  **`mult γ ≤ C(|A_γ|, a)`**     (`alignedSetsForScalar_card_le_agreement_choose`),

so the two together BRACKET the multiplicity:

  `C(|A_γ| − (k+1), a − (k+1)) ≤ mult γ ≤ C(|A_γ|, a)`.

**The mechanism (upper side).** `AgreementSetMaximal.aligned_subset_agreementSet_of_agree`:
every `a`-set on which the deg-`< k` explainer `c` matches the `γ`-pencil is an `a`-subset of
`A_γ = agreementSet … c`.  Hence, once `c` explains the WHOLE `γ`-fibre (the maximal-set
hypothesis, `c` is the common explainer guaranteed by `aligned_amalg`), every member of
`alignedSetsForScalar γ` is an `a`-subset of `A_γ`, so

  `alignedSetsForScalar γ ⊆ (A_γ).powersetCard a`,

and `Finset.card_le_card` + `Finset.card_powersetCard` give `mult γ ≤ C(|A_γ|, a)`.

This is the precise UPPER cap that the `CensusDomination` obligation consumes: a distinct-`γ`
cap `#pinnedScalars ≤ P` PLUS a max-agreement-size cap `|A_γ| ≤ s₀` give the incidence cap
`#alignableSets ≤ P · C(s₀, a) = K` that `CensusDominationWeld` welds to `δ*`.  Previously only
the LOWER half of the multiplicity was in tree; this supplies the structural upper half.

**Honest scope (rules 1,3,4,6 + ASYMPTOTIC GUARD).**  Field-universal combinatorics about the
census object (NOT thinness-essential, NOT a moment/Wick move, NOT an orbit/spectrum
re-derivation).  It is NOT a CORE closure and NOT a refutation: it pins `mult γ` between two
binomials in `|A_γ|`, the structural upper companion to the in-tree lower bound.  It makes no
capacity / beyond-Johnson / growth-law claim; the `δ*`/incidence cliff-at-`n/2` object is
untouched.  Probe `scripts/probes/probe_mult_le_agreement_binom.py` (thin `μ_n`, `μ=3..7`,
`p ≫ n³`, never `n=q−1`): the bracket holds at every level and is TIGHT (`mult = C(|A_γ|, a)`)
at the generic deep agreement set; anchors `C(5,3)=10`, `C(6,4)=15` match `AgreementSetMaximal`.
CORE (`M(μ_n) ≤ C√(n log(p/n))`) stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ProximityGap.Ownership

open ProximityGap.PairRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The census multiplicity is contained in the agreement-set powerset.**  If the deg-`< k`
explainer `c` matches the `γ`-pencil on every member of `alignedSetsForScalar dom k a u₀ u₁ γ`
(the common-explainer / maximal-set hypothesis), then every such member is an `a`-subset of the
agreement set `A_γ = agreementSet dom u₀ u₁ γ c`, i.e.

  `alignedSetsForScalar dom k a u₀ u₁ γ ⊆ (agreementSet dom u₀ u₁ γ c).powersetCard a`.

The non-degeneracy + alignment data of `alignedSetsForScalar` is DISCARDED on the upper side:
membership only needs the cardinality (`= a`) and the agreement (`c` matches on the set), which
forces the `a`-subset-of-`A_γ` containment via `aligned_subset_agreementSet_of_agree`. -/
theorem alignedSetsForScalar_subset_agreement_powersetCard
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (γ : F) {c : Fin n → F}
    (hc : ∀ S ∈ alignedSetsForScalar dom k a u₀ u₁ γ, ∀ i ∈ S, c i = pencil u₀ u₁ γ i) :
    alignedSetsForScalar dom k a u₀ u₁ γ
      ⊆ (agreementSet dom u₀ u₁ γ c).powersetCard a := by
  intro S hS
  have hScard : S.card = a := (mem_alignedSetsForScalar.mp hS).1
  rw [Finset.mem_powersetCard]
  exact ⟨aligned_subset_agreementSet_of_agree dom (hc S hS), hScard⟩

/-- **The per-scalar census multiplicity is capped by ONE agreement-set binomial**, the EXACT
UPPER companion to `mult_ge_choose_of_aligned_superset`.  Under the common-explainer hypothesis
(the deg-`< k` codeword `c` matches the `γ`-pencil on every non-degenerate `γ`-aligned `a`-set,
i.e. `c` explains the maximal aligned set `A_γ`):

  `#(alignedSetsForScalar dom k a u₀ u₁ γ) ≤ C(|A_γ|, a)`,   `A_γ = agreementSet dom u₀ u₁ γ c`.

Together with the in-tree lower bound this brackets the multiplicity in
`[C(|A_γ| − (k+1), a − (k+1)), C(|A_γ|, a)]`. -/
theorem alignedSetsForScalar_card_le_agreement_choose
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (γ : F) {c : Fin n → F}
    (hc : ∀ S ∈ alignedSetsForScalar dom k a u₀ u₁ γ, ∀ i ∈ S, c i = pencil u₀ u₁ γ i) :
    (alignedSetsForScalar dom k a u₀ u₁ γ).card
      ≤ (agreementSet dom u₀ u₁ γ c).card.choose a := by
  classical
  calc (alignedSetsForScalar dom k a u₀ u₁ γ).card
      ≤ ((agreementSet dom u₀ u₁ γ c).powersetCard a).card :=
        Finset.card_le_card
          (alignedSetsForScalar_subset_agreement_powersetCard dom k a u₀ u₁ γ hc)
    _ = (agreementSet dom u₀ u₁ γ c).card.choose a := Finset.card_powersetCard _ _

/-- **The two-sided multiplicity bracket.**  Combining the in-tree lower bound
(`mult_ge_choose_of_aligned_superset`, fed a deep base aligned set `S₀` of size `s₀ = |A_γ|`
through a non-degenerate tuple) with the upper cap above, the per-scalar census multiplicity is
pinned between two binomials in the agreement-set size:

  `C(|A_γ| − (k+1), a − (k+1)) ≤ mult γ ≤ C(|A_γ|, a)`.

`S₀` is the base aligned set whose agreement set is `A_γ = agreementSet … c`; its size
`S₀.card = (agreementSet … c).card` is supplied by `hsize` (it equals `|A_γ|` exactly when `S₀`
is the maximal aligned set, which is the regime of this bracket). -/
theorem alignedSetsForScalar_card_bracket
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (γ : F) {c : Fin n → F}
    {S₀ : Finset (Fin n)} (halign : Aligned dom k u₀ u₁ γ S₀)
    {t : Fin (k + 1) → Fin n} (htinj : Function.Injective t) (htmem : ∀ b, t b ∈ S₀)
    (hnd : ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0)) (hak : k + 1 ≤ a)
    (hsize : S₀.card = (agreementSet dom u₀ u₁ γ c).card)
    (hc : ∀ S ∈ alignedSetsForScalar dom k a u₀ u₁ γ, ∀ i ∈ S, c i = pencil u₀ u₁ γ i) :
    ((agreementSet dom u₀ u₁ γ c).card - (k + 1)).choose (a - (k + 1))
        ≤ (alignedSetsForScalar dom k a u₀ u₁ γ).card
      ∧ (alignedSetsForScalar dom k a u₀ u₁ γ).card
        ≤ (agreementSet dom u₀ u₁ γ c).card.choose a := by
  refine ⟨?_, alignedSetsForScalar_card_le_agreement_choose dom k a u₀ u₁ γ hc⟩
  have hlo := mult_ge_choose_of_aligned_superset dom k a u₀ u₁ γ halign htinj htmem hnd hak
  rwa [hsize] at hlo

end ProximityGap.Ownership
