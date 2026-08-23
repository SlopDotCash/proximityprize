/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.BadScalarsEqPinned

/-!
# The distinct-γ count is the incidence count DIVIDED by the per-scalar multiplicity (#444 §6.4/§6.7)

`BadScalarsEqPinned` identified the bad census with the distinct-γ count `#pinnedScalars`, and
`CensusScalarPartition` gave the exact partition `#alignableSets = Σ_γ mult(γ)` plus the multiplicity
lower bound `mult(γ) ≥ C(s−(k+1), a−(k+1))` for a γ owning a depth-`s` agreement set.

This file supplies the missing **division-tightening**: if EVERY pinned scalar owns at least `M`
aligned `a`-sets, then

  **`#pinnedScalars · M ≤ #alignableSets`**     (`pinnedScalars_card_mul_le_alignable`)
  ⟹ **`#pinnedScalars ≤ #alignableSets / M`**   (`pinnedScalars_card_le_alignable_div`).

This is a genuine tightening of the partition worker's `pinnedScalars_card_le` (`#pinnedScalars ≤
#alignableSets`, the `M = 1` case): the distinct-γ census is the incidence census **deflated by the
per-scalar multiplicity**.  Probe `probe_pinned_div_mult.py` (planted-codeword words on PROPER thin
`μ_n`, prize-regime `p`) measures the inversion to be EXACTLY TIGHT: `#pinnedScalars =
#alignableSets / minMult` to the integer, with `minMult = maxMult = C(s−(k+1), a−(k+1))` (every
pinned scalar owns the same multiplicity for the agreement structure).  E.g. `n=16, k=2, a=6, s=12`:
`#alignable = 3168`, `minMult = 792`, `#pinned = 4 = 3168/792`.

Composed with the partition worker's `mult_ge_choose_of_aligned_superset`, a uniform depth-`s`
agreement structure across all pinned scalars yields `M = C(s−(k+1), a−(k+1))` and hence the explicit
bound `#pinnedScalars ≤ #alignableSets / C(s−(k+1), a−(k+1))` — the mechanism by which the distinct-γ
(δ*-governing) count is sub-incidence at deep bands (the census-partition band-collapse, made into an
axiom-clean inequality on the part-count).

## Scope (rule 3 / rule 6, honesty contract)

NOT a CORE closure, NOT thinness-essential: field-universal combinatorics. It is the reciprocal of
the multiplicity over-count — it bounds the distinct-γ count BY the incidence count divided by `M`,
but it does NOT supply `M` (the uniform multiplicity floor at the prize band) nor a bound on
`#alignableSets`.  It turns "the incidence over-counts distinct-γ by `mult`" into the usable
"distinct-γ ≤ incidence / mult".  CORE (`M(μ_n) ≤ C√(n log(p/n))`) stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The multiplicity-division bound (product form).**  If every pinned scalar owns at least `M`
aligned `a`-sets, then `#pinnedScalars · M ≤ #alignableSets`.  Engine: `#alignableSets =
Σ_{pinned γ} mult(γ)` (the partition restricted to pinned scalars) and each summand is `≥ M`, so the
sum is `≥ #pinnedScalars · M`. -/
theorem pinnedScalars_card_mul_le_alignable (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    {M : ℕ} (hM : ∀ γ ∈ pinnedScalars dom k a u₀ u₁,
      M ≤ (alignedSetsForScalar dom k a u₀ u₁ γ).card) :
    (pinnedScalars dom k a u₀ u₁).card * M ≤ (alignableSets dom k a u₀ u₁).card := by
  classical
  rw [alignableSets_card_eq_sum_pinned]
  calc (pinnedScalars dom k a u₀ u₁).card * M
      = ∑ _γ ∈ pinnedScalars dom k a u₀ u₁, M := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ pinnedScalars dom k a u₀ u₁, (alignedSetsForScalar dom k a u₀ u₁ γ).card :=
        Finset.sum_le_sum hM

open Classical in
/-- **The multiplicity-division bound (quotient form).**  If every pinned scalar owns at least
`M ≥ 1` aligned `a`-sets, then the distinct-γ count is the incidence count deflated by `M`:
`#pinnedScalars ≤ #alignableSets / M`.  This strictly tightens `pinnedScalars_card_le` (the `M = 1`
case) whenever the multiplicities exceed `1` — and probe `probe_pinned_div_mult.py` shows the bound
is exactly tight at the agreement-structured worst case. -/
theorem pinnedScalars_card_le_alignable_div (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    {M : ℕ} (hM1 : 1 ≤ M) (hM : ∀ γ ∈ pinnedScalars dom k a u₀ u₁,
      M ≤ (alignedSetsForScalar dom k a u₀ u₁ γ).card) :
    (pinnedScalars dom k a u₀ u₁).card ≤ (alignableSets dom k a u₀ u₁).card / M := by
  classical
  rw [Nat.le_div_iff_mul_le hM1]
  exact pinnedScalars_card_mul_le_alignable dom k a u₀ u₁ hM

open Classical in
/-- **The bad-scalar census, multiplicity-deflated.**  Combining `badScalars = pinnedScalars` with the
division bound: under the radius hypotheses, if every pinned scalar owns at least `M ≥ 1` aligned
`a`-sets, the MCA bad-scalar count is at most `#alignableSets / M`.  This routes the deployed census
bound through the multiplicity-deflated incidence count — the honest form when the agreement structure
inflates the incidence. -/
theorem badScalars_card_le_alignable_div (dom : Fin n ↪ F) {k a : ℕ} (hk : 1 ≤ k)
    (hka : k + 1 ≤ a) {δ : ℝ≥0}
    (hlo : ((a - 1 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (a : ℕ))
    (u₀ u₁ : Fin n → F) {M : ℕ} (hM1 : 1 ≤ M)
    (hM : ∀ γ ∈ pinnedScalars dom k a u₀ u₁,
      M ≤ (alignedSetsForScalar dom k a u₀ u₁ γ).card) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ (alignableSets dom k a u₀ u₁).card / M :=
  le_trans (badScalars_card_le_pinnedScalars dom hk hka hlo hhi u₀ u₁)
    (pinnedScalars_card_le_alignable_div dom k a u₀ u₁ hM1 hM)

open Classical in
/-- **Explicit depth-`s` deflation via the partition worker's `mult_ge_choose_of_aligned_superset`.**
If every pinned scalar owns a depth-`s` agreement set (size `s`) with a non-degenerate `(k+1)`-tuple
(uniform agreement depth across pinned scalars), then each multiplicity is `≥ C(s−(k+1), a−(k+1))`, so

  `#pinnedScalars ≤ #alignableSets / C(s−(k+1), a−(k+1))`.

This is the explicit form: a deep agreement structure deflates the distinct-γ count below the
incidence count by a binomial factor — the axiom-clean part-count form of the census band-collapse. -/
theorem pinnedScalars_card_le_alignable_div_choose (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    {s : ℕ} (hak : k + 1 ≤ a) (hsc : 1 ≤ (s - (k + 1)).choose (a - (k + 1)))
    (hdepth : ∀ γ ∈ pinnedScalars dom k a u₀ u₁,
      ∃ S₀ : Finset (Fin n), S₀.card = s ∧ Aligned dom k u₀ u₁ γ S₀ ∧
        ∃ t : Fin (k + 1) → Fin n, Function.Injective t ∧ (∀ b, t b ∈ S₀) ∧
          ¬ (residual dom k t u₀ = 0 ∧ residual dom k t u₁ = 0)) :
    (pinnedScalars dom k a u₀ u₁).card
      ≤ (alignableSets dom k a u₀ u₁).card / (s - (k + 1)).choose (a - (k + 1)) := by
  classical
  apply pinnedScalars_card_le_alignable_div dom k a u₀ u₁ hsc
  intro γ hγ
  obtain ⟨S₀, hScard, halign, t, htinj, htmem, hnd⟩ := hdepth γ hγ
  have := mult_ge_choose_of_aligned_superset dom k a u₀ u₁ γ halign htinj htmem hnd hak
  rwa [hScard] at this

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.pinnedScalars_card_mul_le_alignable
#print axioms ProximityGap.Ownership.pinnedScalars_card_le_alignable_div
#print axioms ProximityGap.Ownership.badScalars_card_le_alignable_div
#print axioms ProximityGap.Ownership.pinnedScalars_card_le_alignable_div_choose
