/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CensusScalarPartition

/-!
# The bad-scalar census IS the distinct-`γ` count, exactly (#444 §6.4/§6.7)

The campaign's deployed census bound (`UniversalAlignmentLaw`, used by the `CensusDominationWeld`)
routes the MCA bad-scalar count through the **incidence** census object `alignableSets`:

  `epsMCA ≤ #alignableSets / |F|`     (`epsMCA_le_of_alignableSets_card_le`).

But the issue (#444 §6.4/§6.7) repeatedly states the governing quantity is the **distinct-`γ`**
count, NOT the `(subset,γ)`-incidence:
  *"`δ*` is governed by the distinct-`γ` count, NOT the (subset,`γ`) incidence."*
and the `CensusScalarPartition` worker measured the incidence to over-count the distinct-`γ`
count by the multiplicity excess `Σ (mult γ − 1)` (often a 5–50× factor at accessible `n`).

This file pins the missing identification that makes the distinct-`γ` count a USABLE census bound:
the set of MCA-bad scalars is, under the radius hypotheses, EXACTLY the set of pinned scalars
(`pinnedScalars`, the distinct-`γ` that own ≥1 non-degenerate aligned `a`-set):

* `badScalars_eq_pinnedScalars` — **`badScalars = pinnedScalars`** as `Finset`s.  The engine is the
  in-tree universal law `mcaEvent_iff_aligned_subset`: `γ` is MCA-bad iff some `a`-set is
  `γ`-aligned with a non-degenerate tuple, which is precisely `alignedSetsForScalar γ ≠ ∅`, i.e.
  `γ ∈ pinnedScalars`.
* `badScalars_card_eq_pinnedScalars_card` — hence **`#bad = #pinnedScalars`** exactly.  (Probe
  `probe_badscalars_eq_pinned2.py`: equality holds at every tested `n,k,a`, while
  `#pinnedScalars < #alignableSets` strictly — the incidence over-count is real slack, NOT bad mass.)
* `badScalars_card_le_pinnedScalars` together with `pinnedScalars_card_le` recover the in-tree census
  bound `#bad ≤ #alignableSets` THROUGH the strictly-tighter distinct-`γ` waypoint
  `#bad = #pinnedScalars ≤ #alignableSets`.
* `epsMCA_le_of_pinnedScalars_card_le` — **the deployed consequence**: a uniform bound
  `#pinnedScalars ≤ L` (the distinct-`γ` / governing count) gives `epsMCA ≤ L/|F|`.  This is the
  honest census bound the `δ*` weld wants — it consumes the distinct-`γ` count directly, so any
  future supply bound on distinct alignable scalars (rather than on the lossy incidence) plugs in
  here without paying the multiplicity excess.

## Scope (rule 3 / rule 6, honesty contract)

This is NOT a CORE closure and NOT thinness-essential: it is field-universal combinatorics threading
the bad-scalar census through its exact distinct-`γ` representation.  It does NOT supply a bound on
`#pinnedScalars` (that — the actual distinct-`γ` supply at the prize band — is the open content the
partition worker's band-collapse probe is circling).  It removes the structural gap between the
campaign's "the governing count is distinct-`γ`" narrative and the deployed bound, which previously
only had access to the incidence count.  CORE (`M(μ_n) ≤ C√(n log(p/n))`) stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The bad-scalar set equals the pinned-scalar set.**  Under the radius hypotheses
(`a−1 < (1−δ)n ≤ a`, `a ≥ k+1`, `k ≥ 1`), a scalar `γ` is MCA-bad iff it owns at least one
non-degenerate `γ`-aligned `a`-set, i.e. iff `γ ∈ pinnedScalars`.  The forward/back implications are
the two directions of the in-tree universal alignment law `mcaEvent_iff_aligned_subset`, repackaged
at the `Finset` level.  This identifies the bad census with the distinct-`γ` (`δ*`-governing) count,
NOT the lossy `(subset,γ)` incidence count. -/
theorem badScalars_eq_pinnedScalars (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k)
    (hka : k + 1 ≤ a) {δ : ℝ≥0}
    (hlo : ((a - 1 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (a : ℕ))
    (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ))
      = pinnedScalars dom k a u₀ u₁ := by
  classical
  ext γ
  rw [Finset.mem_filter, mem_pinnedScalars]
  constructor
  · rintro ⟨-, hbad⟩
    -- universal law: bad ⟹ exists non-degenerate aligned a-set ⟹ alignedSetsForScalar γ nonempty
    obtain ⟨S, hScard, halign, t, htinj, htmem, hnd⟩ :=
      (mcaEvent_iff_aligned_subset dom hk hka hlo hhi u₀ u₁ γ).mp hbad
    exact ⟨S, by rw [mem_alignedSetsForScalar]; exact ⟨hScard, halign, t, htinj, htmem, hnd⟩⟩
  · rintro ⟨S, hS⟩
    rw [mem_alignedSetsForScalar] at hS
    obtain ⟨hScard, halign, ht⟩ := hS
    refine ⟨Finset.mem_univ _, ?_⟩
    -- universal law: a non-degenerate aligned a-set witnesses mcaEvent for γ
    exact (mcaEvent_iff_aligned_subset dom hk hka hlo hhi u₀ u₁ γ).mpr
      ⟨S, hScard, halign, ht⟩

open Classical in
/-- **`#bad = #pinnedScalars`** exactly: the MCA bad-scalar count is the distinct-`γ` count.  (Probe
`probe_badscalars_eq_pinned2.py`: this equality holds at every tested `n,k,a`, with
`#pinnedScalars < #alignableSets` strictly — the incidence census over-counts the bad mass, it does
not under-count it.) -/
theorem badScalars_card_eq_pinnedScalars_card (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k)
    (hka : k + 1 ≤ a) {δ : ℝ≥0}
    (hlo : ((a - 1 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (a : ℕ))
    (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      = (pinnedScalars dom k a u₀ u₁).card := by
  rw [badScalars_eq_pinnedScalars dom hk hka hlo hhi u₀ u₁]

open Classical in
/-- **`#bad ≤ #pinnedScalars`** (the ≤ half, the form the census weld consumes).  Immediate from the
exact equality; stated separately as the tighter census bound that the deployed `δ*` weld wants. -/
theorem badScalars_card_le_pinnedScalars (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k)
    (hka : k + 1 ≤ a) {δ : ℝ≥0}
    (hlo : ((a - 1 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (a : ℕ))
    (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ (pinnedScalars dom k a u₀ u₁).card :=
  le_of_eq (badScalars_card_eq_pinnedScalars_card dom hk hka hlo hhi u₀ u₁)

open Classical in
/-- **The in-tree census bound, re-derived THROUGH the distinct-`γ` waypoint.**  The campaign's
`#bad ≤ #alignableSets` now factors as `#bad = #pinnedScalars ≤ #alignableSets`, exposing the
multiplicity excess `#alignableSets − #pinnedScalars` as pure incidence slack (never bad mass). -/
theorem badScalars_card_le_alignable_via_pinned (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k)
    (hka : k + 1 ≤ a) {δ : ℝ≥0}
    (hlo : ((a - 1 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (a : ℕ))
    (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ (alignableSets dom k a u₀ u₁).card :=
  le_trans (badScalars_card_le_pinnedScalars dom hk hka hlo hhi u₀ u₁)
    (pinnedScalars_card_le dom k a u₀ u₁)

open Classical in
/-- **THE DEPLOYED CONSEQUENCE — census via the distinct-`γ` count.**  A uniform bound
`#pinnedScalars ≤ L` (a bound on the `δ*`-governing distinct-`γ` count, over all stacks) gives
`epsMCA ≤ L/|F|`.  This is the honest census bound: it consumes the distinct-`γ` count directly, so
future supply bound on distinct alignable scalars plugs in WITHOUT paying the incidence multiplicity
excess (which `epsMCA_le_of_alignableSets_card_le` does pay). -/
theorem epsMCA_le_of_pinnedScalars_card_le (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k)
    (hka : k + 1 ≤ a) {δ : ℝ≥0}
    (hlo : ((a - 1 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (a : ℕ)) (L : ℕ)
    (hL : ∀ u₀ u₁ : Fin n → F, (pinnedScalars dom k a u₀ u₁).card ≤ L) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ (L : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_of_badCount_le
    (((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F))) δ L
    (fun u => le_trans
      (badScalars_card_le_pinnedScalars dom hk hka hlo hhi (u 0) (u 1))
      (hL (u 0) (u 1)))

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.badScalars_eq_pinnedScalars
#print axioms ProximityGap.Ownership.badScalars_card_eq_pinnedScalars_card
#print axioms ProximityGap.Ownership.badScalars_card_le_pinnedScalars
#print axioms ProximityGap.Ownership.badScalars_card_le_alignable_via_pinned
#print axioms ProximityGap.Ownership.epsMCA_le_of_pinnedScalars_card_le
