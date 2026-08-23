/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.MultUpperAgreementBinom
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.AlignableLePinnedMaxMult

/-!
# The census M-side monotone lift: a uniform agreement-size cap ⟹ a uniform multiplicity cap
# (#444 census face)

`MultUpperAgreementBinom` pins the per-scalar census multiplicity by ONE agreement-set binomial,
`mult γ = #(alignedSetsForScalar … γ) ≤ C(|A_γ|, a)`, where `A_γ = agreementSet dom u₀ u₁ γ c`
and `c` is the common explainer of the maximal `γ`-aligned set (hypothesis `hc`).  But the binomial
`C(|A_γ|, a)` still varies *with `γ`* (through `|A_γ|`); the consumer
`AlignableLePinnedMaxMult.alignableSets_card_le_budget` needs a *single* `M` valid for **every**
pinned `γ`.  The two were never welded: `MultUpperAgreementBinom` produces a per-`γ` binomial, the
budget lemma consumes a uniform `M`, and nothing lifts the former to the latter.

This file carries that lift, using the top-index monotonicity of `Nat.choose`
(`Nat.choose_le_choose a : s ≤ s₀ → C(s, a) ≤ C(s₀, a)`):

* **`mult_le_choose_of_agreement_le`** (per-`γ`): under the explainer `hc`, if `|A_γ| ≤ s₀` then
  `mult γ ≤ C(s₀, a)`.  Mechanism: `mult γ ≤ C(|A_γ|, a)` (the in-tree upper cap) and
  `C(|A_γ|, a) ≤ C(s₀, a)` (`Nat.choose_le_choose`).

* **`uniform_mult_cap_of_agreementSizeCap`** (the uniform `hM`): given a per-`γ` explainer family
  `c : F → (Fin n → F)` and a **uniform agreement-size cap** `|A_γ| ≤ s₀` for every pinned `γ`,
  every pinned scalar owns `≤ C(s₀, a)` aligned `a`-sets — exactly the `hM` hypothesis the budget
  lemma consumes, with `M := C(s₀, a)`.

* **`alignableSets_card_le_pinned_mul_choose`** / **`alignableSets_card_le_choose_budget`**
  (end-to-end): feeding the uniform cap into `alignableSets_card_le_of_pinned_le_mult_le` /
  `alignableSets_card_le_budget` gives `#alignableSets ≤ P · C(s₀, a)` and, with `P · C(s₀,a) ≤ K`,
  the `CensusDomination` per-band incidence bound `#alignableSets ≤ K`.

So the census M-side now reads: a distinct-`γ` cap `P` **and** a uniform agreement-size cap `s₀`
(both at the prize band) imply the budget — the per-scalar binomial is lifted to a uniform `M`.
This is the M-side companion of the EMPTYFIBER P-side support refinement
(`MultEmptyFiberBelowBand`): together they reduce the census incidence cap to two scalar caps,
`P` (distinct pinned scalars) and `s₀` (maximum agreement-set size).

## Scope (rule 3 / rule 6, honesty contract)

NOT a CORE closure, NOT thinness-essential, field-universal and thickness-independent.  It is the
*logical lift* from a per-`γ` binomial to a uniform `M` via `Nat.choose` monotonicity.  It does NOT
supply the agreement-size cap `s₀` itself — bounding `|A_γ| = #{i : c i = pencil u₀ u₁ γ i}` at the
prize band IS the open list-decoding / agreement-sharing input (the BGK contribution = the wall).
The probe `probe_mside_agreement_choose_mono.py` confirms the lift is sound and non-vacuous
(realized `#(a`-subsets of an `s`-set`) = C(s, a)` exactly, `C(s, a) ≤ C(s₀, a)` for `s ≤ s₀`, and
`Σ mult γ ≤ P · C(s₀, a)`).  CORE (`M(μ_n) ≤ C√(n log(p/n))`) stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ProximityGap.Ownership

open ProximityGap.PairRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

-- `Fintype F` is used in the PROOF (via `alignedSetsForScalar_card_le_agreement_choose`) but not
-- in the type signature, so the `unusedFintypeInType` linter flags it spuriously; silenced here.
set_option linter.unusedFintypeInType false in
/-- **Per-`γ` monotone cap.**  Under the common-explainer hypothesis `hc` (the deg-`< k` codeword
`c` matches the `γ`-pencil on every non-degenerate `γ`-aligned `a`-set), a bound `|A_γ| ≤ s₀` on
the agreement-set size lifts the per-`γ` binomial cap to a `γ`-independent one:

  `#(alignedSetsForScalar dom k a u₀ u₁ γ) ≤ C(s₀, a)`.

Mechanism: `mult γ ≤ C(|A_γ|, a)` (`alignedSetsForScalar_card_le_agreement_choose`) chained with
`C(|A_γ|, a) ≤ C(s₀, a)` (`Nat.choose_le_choose a` on the top index, monotone for `|A_γ| ≤ s₀`). -/
theorem mult_le_choose_of_agreement_le
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (γ : F) {c : Fin n → F} {s₀ : ℕ}
    (hc : ∀ S ∈ alignedSetsForScalar dom k a u₀ u₁ γ, ∀ i ∈ S, c i = pencil u₀ u₁ γ i)
    (hsz : (agreementSet dom u₀ u₁ γ c).card ≤ s₀) :
    (alignedSetsForScalar dom k a u₀ u₁ γ).card ≤ s₀.choose a := by
  calc (alignedSetsForScalar dom k a u₀ u₁ γ).card
      ≤ (agreementSet dom u₀ u₁ γ c).card.choose a :=
        alignedSetsForScalar_card_le_agreement_choose dom k a u₀ u₁ γ hc
    _ ≤ s₀.choose a := Nat.choose_le_choose a hsz

/-- **The uniform multiplicity cap from a uniform agreement-size cap.**  Given a per-`γ` explainer
family `c : F → (Fin n → F)` such that for every pinned `γ`:
* `c γ` explains the maximal `γ`-aligned set (`hc γ`), and
* the agreement-set size is uniformly bounded, `|A_γ| ≤ s₀` (`hsz γ`),

every pinned scalar owns at most `C(s₀, a)` aligned `a`-sets:

  `∀ γ ∈ pinnedScalars dom k a u₀ u₁, #(alignedSetsForScalar dom k a u₀ u₁ γ) ≤ C(s₀, a)`.

This is exactly the `hM` hypothesis `alignableSets_card_le_budget` consumes, with `M = C(s₀, a)`. -/
theorem uniform_mult_cap_of_agreementSizeCap
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) {c : F → Fin n → F} {s₀ : ℕ}
    (hc : ∀ γ ∈ pinnedScalars dom k a u₀ u₁,
      ∀ S ∈ alignedSetsForScalar dom k a u₀ u₁ γ, ∀ i ∈ S, c γ i = pencil u₀ u₁ γ i)
    (hsz : ∀ γ ∈ pinnedScalars dom k a u₀ u₁, (agreementSet dom u₀ u₁ γ (c γ)).card ≤ s₀) :
    ∀ γ ∈ pinnedScalars dom k a u₀ u₁,
      (alignedSetsForScalar dom k a u₀ u₁ γ).card ≤ s₀.choose a :=
  fun γ hγ => mult_le_choose_of_agreement_le dom k a u₀ u₁ γ (hc γ hγ) (hsz γ hγ)

open Classical in
/-- **End-to-end (the product form).**  A distinct-`γ` cap `#pinnedScalars ≤ P` together with a
per-`γ` explainer family and a uniform agreement-size cap `|A_γ| ≤ s₀` give the census incidence
product bound

  `#alignableSets ≤ P · C(s₀, a)`.

The per-scalar binomial is lifted to the uniform `M = C(s₀, a)` and fed to
`alignableSets_card_le_of_pinned_le_mult_le`. -/
theorem alignableSets_card_le_pinned_mul_choose
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    {P s₀ : ℕ} {c : F → Fin n → F}
    (hP : (pinnedScalars dom k a u₀ u₁).card ≤ P)
    (hc : ∀ γ ∈ pinnedScalars dom k a u₀ u₁,
      ∀ S ∈ alignedSetsForScalar dom k a u₀ u₁ γ, ∀ i ∈ S, c γ i = pencil u₀ u₁ γ i)
    (hsz : ∀ γ ∈ pinnedScalars dom k a u₀ u₁, (agreementSet dom u₀ u₁ γ (c γ)).card ≤ s₀) :
    (alignableSets dom k a u₀ u₁).card ≤ P * s₀.choose a :=
  alignableSets_card_le_of_pinned_le_mult_le dom k a u₀ u₁ hP
    (uniform_mult_cap_of_agreementSizeCap dom k a u₀ u₁ hc hsz)

open Classical in
/-- **End-to-end (the budget form).**  With the additional product cap `P · C(s₀, a) ≤ K`, the
census per-band incidence bound the `CensusDomination` Prop asserts holds:

  `#alignableSets ≤ K`.

So the open per-band incidence cap is now implied by THREE scalar caps at the prize band: a
distinct-`γ` cap `P`, a uniform agreement-size cap `s₀`, and the product budget `P · C(s₀,a) ≤ K`.
The agreement-size cap `s₀` is the only one still open (= the wall). -/
theorem alignableSets_card_le_choose_budget
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    {P s₀ K : ℕ} {c : F → Fin n → F}
    (hP : (pinnedScalars dom k a u₀ u₁).card ≤ P)
    (hc : ∀ γ ∈ pinnedScalars dom k a u₀ u₁,
      ∀ S ∈ alignedSetsForScalar dom k a u₀ u₁ γ, ∀ i ∈ S, c γ i = pencil u₀ u₁ γ i)
    (hsz : ∀ γ ∈ pinnedScalars dom k a u₀ u₁, (agreementSet dom u₀ u₁ γ (c γ)).card ≤ s₀)
    (hPMK : P * s₀.choose a ≤ K) :
    (alignableSets dom k a u₀ u₁).card ≤ K :=
  alignableSets_card_le_budget dom k a u₀ u₁ hP
    (uniform_mult_cap_of_agreementSizeCap dom k a u₀ u₁ hc hsz) hPMK

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.mult_le_choose_of_agreement_le
#print axioms ProximityGap.Ownership.uniform_mult_cap_of_agreementSizeCap
#print axioms ProximityGap.Ownership.alignableSets_card_le_pinned_mul_choose
#print axioms ProximityGap.Ownership.alignableSets_card_le_choose_budget
