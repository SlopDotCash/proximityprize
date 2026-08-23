/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAStepFunction

/-!
# The finite-table assembly (#357 round 14): `δ*` from finitely many floor values

The band-pin (`mcaDeltaStar_eq_of_band`) requires badness on a continuum of radii; the
step-function law says `ε_mca` only sees the agreement floor. This file welds them:

* **`mcaDeltaStar_eq_of_finite_floor_table`** — `δ* = δ₀` follows from (i) goodness at
  `δ₀`, (ii) badness at a **finite table** `T` of canonical radii, and (iii) a coverage
  condition (every radius beyond `δ₀` shares its floor with a table entry). The
  continuum collapses to `≤ n + 1` checks.

This is the final reduction of the production assembly: for any code and any `ε*`,
`δ*(ε*)` is pinned by finitely many floor-value determinations
`V_t = ε_mca(canonical radius of floor t)` — each of which the campaign's census
machinery (LYM ceiling + supply + the four-family circuit census + the slope
optimization) addresses per cell. The remaining mathematical content of `δ*` at
production scale lives entirely in those finitely many `V_t` values; the assembly
around them is **complete and proven**.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- Issue #357 (round-14); `MCAStepFunction.lean` (step law + band-pin).
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code ProximityGap.MCAThresholdLedger
open ProximityGap.MCAStepFunction

namespace ProximityGap.MCAFiniteTable

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The finite-table assembly.** `δ* = δ₀` from goodness at `δ₀`, badness at a finite
table of canonical radii, and floor-coverage of the band `(δ₀, 1]` by the table. -/
theorem mcaDeltaStar_eq_of_finite_floor_table (C : Set (ι → A)) (εstar : ℝ≥0∞)
    {δ₀ : ℝ≥0} (hδ₀ : δ₀ ≤ 1)
    (hgood : epsMCA (F := F) (A := A) C δ₀ ≤ εstar)
    (T : Finset ℝ≥0)
    (hcover : ∀ δ : ℝ≥0, δ₀ < δ → δ ≤ 1 → ∃ δ' ∈ T,
      ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ = ⌈(1 - δ') * (Fintype.card ι : ℝ≥0)⌉₊)
    (hbadT : ∀ δ' ∈ T, εstar < epsMCA (F := F) (A := A) C δ') :
    mcaDeltaStar (F := F) (A := A) C εstar = δ₀ := by
  apply mcaDeltaStar_eq_of_band C εstar hδ₀ hgood
  intro δ hlt hle
  obtain ⟨δ', hδ'T, hfloor⟩ := hcover δ hlt hle
  rw [epsMCA_eq_of_ceil_eq (F := F) C hfloor]
  exact hbadT δ' hδ'T

/-! ## Source audit -/

#print axioms mcaDeltaStar_eq_of_finite_floor_table

end ProximityGap.MCAFiniteTable
