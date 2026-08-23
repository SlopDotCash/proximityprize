/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.EvenDirectionDescent

/-!
# The ODD-PART EXCESS of the 2-adic even–odd descent (issue #407, odd-excess-law)

The deployed `δ*` object is the far-line incidence `I = |explainableScalars|`
(`ProximityGap.FarCosetExplosion.explainableScalars`, the REAL in-tree bad-scalar set).
`EvenDirectionDescent.lean` proves the **forward lift** for an *even / imprimitive* monomial
direction `x^{2a'} = (x²)^{a'}` (the squaring pullback `f : μ_n → μ_{n/2}`):

  `I_{n/2}(x^{a'}; RS[μ_{n/2},k]) ≤ I_n(x^{2a'}; RS[μ_n,2k])`     (`*_sq_pullback_subset`)

i.e. every half-domain bad scalar lifts to a full-domain bad scalar. The prize-useful **reverse**
collapse `I_n ≤ I_{n/2}` is the named open `Prop` `EvenDirectionIncidenceCollapse`.

This file pins the **gap** between the two: the *odd-part excess*

  `oddExcess := full_bad \ half_bad`   (`Finset.sdiff` of the two REAL `explainableScalars`),

the scalars that are bad for the even full-domain line but whose witnessing `RS[μ_n,2k]` codeword
is **not** the even pullback of an `RS[μ_{n/2},k]` codeword (its odd part carries the agreement on a
non-fibre-symmetric witness set). Everything here references the REAL `explainableScalars` and the
REAL `EvenDirectionIncidenceCollapse` of `EvenDirectionDescent.lean`.

## What is proved (axiom-clean)

* `half_subset_full` — restatement of the forward lift: `half ⊆ full` (so the excess is the honest
  set-difference and `full = half ⊔ oddExcess`).
* `oddExcess_card` — **the EXACT additive excess law** `E := |oddExcess| = I_n − I_{n/2}` (the gap is
  exactly the excess of the full incidence over its proven floor). This is the in-tree statement of
  the measured `E(n,a',a₀,r) = I_n(x^{2a'}) − I_{n/2}(x^{a'})`.
* `oddExcess_eq_empty_iff_collapse` — **the exact pin**: the excess set is empty **iff** the named
  reverse-collapse `Prop` holds. So `E = 0 ⟺ EvenDirectionIncidenceCollapse`: the odd-excess is
  *precisely* the obstruction to the 2-adic collapse — it is the open core, measured.
* `collapse_iff_card_eq` — the cardinality face: `EvenDirectionIncidenceCollapse ⟺ I_n = I_{n/2}`.

## The measured law (named, NOT proved — the honest residual)

Exact probe data (`probe_farline_incidence_exact` + the matched-rate forward lift), `ρ = 1/4`:

| n  | rung r' | I_n(x^{2a'}) | I_{n/2}(x^{a'}) | E = I_n − I_{n/2} |
|----|---------|--------------|------------------|--------------------|
| 16 |  ≤ 4    |  (= floor)   |  (= floor)       | **0**              |
| 16 |   5     |     89       |       25         | **64 = (n/2)²**    |

(`E = 0` for every rung *below* the half-domain's own binding rung `r' = 5`, then `E` *spikes* to
`(n/2)² = 64` exactly at that rung; below `ρ = 1/4` — e.g. `ρ = 1/8`, `n = 16` — `E = 0` at every
rung, so the spike is **ρ-gated**.) Whether the spike *compounds* (`E = (n/2)²`, growing with `n`)
or is bounded is captured by the named conjecture `OddExcessSpikeLaw` below — it is **measured**, not
proved (the `n = 32` confirmation of `(n/2)² = 256` was the live numerical check). If it compounds,
the even-direction collapse fails by a growing `Θ(n²)` margin at the binding rung — locating the
collapse failure mode squarely on the odd part, one 2-adic level down.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issue #407.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.FarCosetExplosion

variable {ι ι' : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  [Fintype ι'] [Nonempty ι'] [DecidableEq ι']
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The odd-part excess set, on the REAL `explainableScalars` -/

open Classical in
/-- **The odd-part excess set.** The set-difference of the full-domain even-direction bad set
`full = explainableScalars RS[μ_n,2k] δ (u₀'∘f) (u₁'∘f)` and the half-domain bad set
`half = explainableScalars RS[μ_{n/2},k] δ' u₀' u₁'`. By the forward lift `half ⊆ full`, so this is
the honest gap `full \ half`: the scalars bad for the even full-domain line whose witness does NOT
descend through a single square-fibre representative (the odd-part witnesses). Its cardinality is
the measured odd-excess `E = I_n − I_{n/2}`. -/
noncomputable def oddExcess
    (domain : ι ↪ F) (domain' : ι' ↪ F) (k : ℕ) (f : ι → ι')
    (δ δ' : ℝ≥0) (u₀' u₁' : ι' → F) : Finset F :=
  explainableScalars (F := F) (ReedSolomon.code domain (2 * k) : Set (ι → F)) δ
      (u₀' ∘ f) (u₁' ∘ f)
    \ explainableScalars (F := F) (ReedSolomon.code domain' k : Set (ι' → F)) δ' u₀' u₁'

/-- **Forward lift, restated as `half ⊆ full`.** This is exactly
`explainableScalars_sq_pullback_subset` of `EvenDirectionDescent.lean`: the half-domain bad set
injects into the full-domain even-direction bad set, so `oddExcess` is a genuine set-difference and
the incidences satisfy `I_{n/2} ≤ I_n`. -/
theorem half_subset_full
    (domain : ι ↪ F) (domain' : ι' ↪ F) (k : ℕ) (f : ι → ι')
    (hf : ∀ i, domain' (f i) = (domain i) ^ 2)
    (δ δ' : ℝ≥0) (u₀' u₁' : ι' → F)
    (hbudget : ∀ S' : Finset ι', ((S'.card : ℝ≥0) ≥ (1 - δ') * Fintype.card ι') →
      (((Finset.univ.filter (fun i : ι => f i ∈ S')).card : ℝ≥0)
        ≥ (1 - δ) * Fintype.card ι)) :
    explainableScalars (F := F) (ReedSolomon.code domain' k : Set (ι' → F)) δ' u₀' u₁'
      ⊆ explainableScalars (F := F) (ReedSolomon.code domain (2 * k) : Set (ι → F)) δ
          (u₀' ∘ f) (u₁' ∘ f) :=
  explainableScalars_sq_pullback_subset domain domain' k f hf δ δ' u₀' u₁' hbudget

/-! ## The exact additive excess law `E = I_n − I_{n/2}` -/

open Classical in
/-- **The exact additive excess law.** With the forward lift `half ⊆ full`, the full incidence splits
disjointly as `full = half ⊔ oddExcess`, so the odd-excess count is exactly the gap between the full
incidence and its proven floor:

  `|oddExcess| = I_n(x^{2a'}) − I_{n/2}(x^{a'})`.

This is the in-tree exact form of the measured `E(n,a',a₀,r)`. It is unconditional (only the
forward lift is used); the open question is the *value/growth* of `|oddExcess|`, named below. -/
theorem oddExcess_card
    (domain : ι ↪ F) (domain' : ι' ↪ F) (k : ℕ) (f : ι → ι')
    (hf : ∀ i, domain' (f i) = (domain i) ^ 2)
    (δ δ' : ℝ≥0) (u₀' u₁' : ι' → F)
    (hbudget : ∀ S' : Finset ι', ((S'.card : ℝ≥0) ≥ (1 - δ') * Fintype.card ι') →
      (((Finset.univ.filter (fun i : ι => f i ∈ S')).card : ℝ≥0)
        ≥ (1 - δ) * Fintype.card ι)) :
    (oddExcess domain domain' k f δ δ' u₀' u₁').card
      = (explainableScalars (F := F) (ReedSolomon.code domain (2 * k) : Set (ι → F)) δ
            (u₀' ∘ f) (u₁' ∘ f)).card
        - (explainableScalars (F := F) (ReedSolomon.code domain' k : Set (ι' → F)) δ' u₀' u₁').card := by
  classical
  unfold oddExcess
  rw [Finset.card_sdiff_of_subset (half_subset_full domain domain' k f hf δ δ' u₀' u₁' hbudget)]

/-! ## The exact pin: excess empty ⟺ the reverse collapse -/

open Classical in
/-- **The exact pin (set form): the odd-excess vanishes iff the collapse holds.** The named open
`Prop` `EvenDirectionIncidenceCollapse` is exactly `full ⊆ half`. Combined with the forward lift
`half ⊆ full`, the excess set `full \ half` is empty **iff** `full ⊆ half`, i.e. iff the collapse
holds. So `oddExcess = ∅ ⟺ EvenDirectionIncidenceCollapse`: the odd-part excess **is** the
obstruction to the 2-adic even-direction collapse, exactly. -/
theorem oddExcess_eq_empty_iff_collapse
    (domain : ι ↪ F) (domain' : ι' ↪ F) (k : ℕ) (f : ι → ι')
    (hf : ∀ i, domain' (f i) = (domain i) ^ 2)
    (δ δ' : ℝ≥0) (u₀' u₁' : ι' → F)
    (hbudget : ∀ S' : Finset ι', ((S'.card : ℝ≥0) ≥ (1 - δ') * Fintype.card ι') →
      (((Finset.univ.filter (fun i : ι => f i ∈ S')).card : ℝ≥0)
        ≥ (1 - δ) * Fintype.card ι)) :
    oddExcess domain domain' k f δ δ' u₀' u₁' = ∅
      ↔ EvenDirectionIncidenceCollapse domain domain' k f δ δ' u₀' u₁' := by
  classical
  unfold oddExcess EvenDirectionIncidenceCollapse
  rw [Finset.sdiff_eq_empty_iff_subset]

/-- **The exact pin (cardinality form): collapse ⟺ `I_n = I_{n/2}`.** The reverse collapse holds iff
the full even-direction incidence equals its proven floor — i.e. iff the odd-excess `E` is zero. This
is the cardinality face of `oddExcess_eq_empty_iff_collapse`. -/
theorem collapse_iff_card_eq
    (domain : ι ↪ F) (domain' : ι' ↪ F) (k : ℕ) (f : ι → ι')
    (hf : ∀ i, domain' (f i) = (domain i) ^ 2)
    (δ δ' : ℝ≥0) (u₀' u₁' : ι' → F)
    (hbudget : ∀ S' : Finset ι', ((S'.card : ℝ≥0) ≥ (1 - δ') * Fintype.card ι') →
      (((Finset.univ.filter (fun i : ι => f i ∈ S')).card : ℝ≥0)
        ≥ (1 - δ) * Fintype.card ι)) :
    EvenDirectionIncidenceCollapse domain domain' k f δ δ' u₀' u₁'
      ↔ (explainableScalars (F := F) (ReedSolomon.code domain (2 * k) : Set (ι → F)) δ
            (u₀' ∘ f) (u₁' ∘ f)).card
          = (explainableScalars (F := F) (ReedSolomon.code domain' k : Set (ι' → F)) δ' u₀' u₁').card := by
  classical
  constructor
  · -- collapse ⟹ both subsets ⟹ equal ⟹ equal cards
    intro hcollapse
    have heq := Finset.Subset.antisymm hcollapse
      (half_subset_full domain domain' k f hf δ δ' u₀' u₁' hbudget)
    rw [heq]
  · -- equal cards + `half ⊆ full` ⟹ `full = half` ⟹ collapse
    intro hcard
    have hsub := half_subset_full domain domain' k f hf δ δ' u₀' u₁' hbudget
    -- `eq_of_subset_of_card_le : half ⊆ full → full.card ≤ half.card → half = full`
    have heq : _ = _ := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard)
    unfold EvenDirectionIncidenceCollapse
    rw [← heq]

/-! ## The named measured residual (the spike law) -/

open Classical in
/--
**`OddExcessSpikeLaw` — the measured odd-excess spike, named as a `Prop` (NOT proved).**

Exact probe data (matched-rate forward lift, `ρ = 1/4`): the odd-excess `E = |oddExcess|` is `0` at
every rung *below* the half-domain's own binding radius and *spikes* to `(n/2)²` exactly at that
rung (`n = 16`: `E = 64 = 8²`, with `I_n = 89`, `I_{n/2} = 25`). Below `ρ = 1/4` (e.g. `ρ = 1/8`)
the spike is absent (`E = 0` everywhere) — it is **ρ-gated**.

This `Prop` asserts the spike *value* `(n/2)²` at the binding rung. It is the in-tree statement of
the open question **"is `E` bounded (⟹ a polynomial tower) or does it compound with `n`?"** — the law
`E = (n/2)²` says it **compounds** (`Θ(n²)` at the binding rung), so the even-direction collapse fails
by a growing margin and `EvenDirectionIncidenceCollapse` is *false* at the binding rung whenever
`(n/2)² > 0`. We do NOT prove this here (it would refute the collapse): it is the measured-but-open
characterization of the collapse failure mode, stated so a downstream consumer can be written
`*_of_OddExcessSpikeLaw` and so a future proof/refutation of the spike value pins the collapse.

(`Fintype.card ι' = n/2` is the half-domain size, so `(Fintype.card ι')²` is the `(n/2)²` spike.) -/
def OddExcessSpikeLaw
    (domain : ι ↪ F) (domain' : ι' ↪ F) (k : ℕ) (f : ι → ι')
    (δ δ' : ℝ≥0) (u₀' u₁' : ι' → F) : Prop :=
  (oddExcess domain domain' k f δ δ' u₀' u₁').card = (Fintype.card ι') ^ 2

/-- **Spike ⟹ collapse fails.** If the measured spike law holds at the binding rung with a nonempty
half-domain (`0 < n/2`, always true here), then the odd-excess is nonempty, so by the exact pin the
reverse collapse `EvenDirectionIncidenceCollapse` is **false**. This is the in-tree consequence of
"the spike compounds": the even-direction collapse cannot hold at the binding rung. -/
theorem collapse_false_of_spike
    (domain : ι ↪ F) (domain' : ι' ↪ F) (k : ℕ) (f : ι → ι')
    (hf : ∀ i, domain' (f i) = (domain i) ^ 2)
    (δ δ' : ℝ≥0) (u₀' u₁' : ι' → F)
    (hbudget : ∀ S' : Finset ι', ((S'.card : ℝ≥0) ≥ (1 - δ') * Fintype.card ι') →
      (((Finset.univ.filter (fun i : ι => f i ∈ S')).card : ℝ≥0)
        ≥ (1 - δ) * Fintype.card ι))
    (hspike : OddExcessSpikeLaw domain domain' k f δ δ' u₀' u₁') :
    ¬ EvenDirectionIncidenceCollapse domain domain' k f δ δ' u₀' u₁' := by
  classical
  rw [← oddExcess_eq_empty_iff_collapse domain domain' k f hf δ δ' u₀' u₁' hbudget]
  intro hempty
  unfold OddExcessSpikeLaw at hspike
  rw [hempty, Finset.card_empty] at hspike
  -- `0 = (n/2)²` is impossible since `n/2 = Fintype.card ι' ≥ 1` (`ι'` nonempty)
  have hpos : 0 < Fintype.card ι' := Fintype.card_pos
  have : 0 < (Fintype.card ι') ^ 2 := by positivity
  omega

end ProximityGap.FarCosetExplosion

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.FarCosetExplosion.half_subset_full
#print axioms ProximityGap.FarCosetExplosion.oddExcess_card
#print axioms ProximityGap.FarCosetExplosion.oddExcess_eq_empty_iff_collapse
#print axioms ProximityGap.FarCosetExplosion.collapse_iff_card_eq
#print axioms ProximityGap.FarCosetExplosion.collapse_false_of_spike
