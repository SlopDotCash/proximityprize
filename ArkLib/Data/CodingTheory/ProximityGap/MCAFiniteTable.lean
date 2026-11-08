/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAStepFunction

/-!
# The finite-table assembly (#357 round 14): `δ*` from finitely many floor values

The step-function law (`MCAStepFunction.epsMCA_eq_of_ceil_eq`) says `ε_mca` only sees the
agreement floor `⌈(1 − δ)·n⌉₊`, and for `1 ≤ t ≤ n` the floor cell of `t` is
`[1 − t/n, 1 − (t − 1)/n)`, open on the right. A threshold assembly therefore tabulates the
**good** side strictly below the boundary and tests the boundary itself for **badness**; a
threshold `δ* < 1` is never itself a good radius
(`MCAStepFunction.lt_epsMCA_mcaDeltaStar_of_lt_one`).

* **`mcaDeltaStar_eq_of_good_floor_table`** — `δ* = δ₀` follows from (i) badness at `δ₀ ≤ 1`,
  (ii) goodness at a **finite table** `T` of radii, and (iii) a coverage condition (every
  radius strictly below `δ₀` shares its agreement floor with a table entry). The continuum
  of good radii collapses to `|T|` checks. `canonical_floor_table_cover` shows that the
  canonical table `{1 − t/n : t₀ ≤ t ≤ n}` (at most `n` entries) meets (iii) at every
  canonical boundary `δ₀ = 1 − (t₀ − 1)/n`; with a good floor value at `t₀` (hence, by
  monotonicity, at every `t ≥ t₀`) and a bad one at `t₀ − 1` all premises hold, so unlike the
  attained form below this interface reaches interior thresholds (e.g. the high-rate RS jump
  at `δ₀ = 1/n`, `MCADeltaStarHighRateFamily.lean`).
* **`exists_mcaDeltaStar_eq_floorRadius`** — for every code and every `ε*`, `δ*` is one of
  the `n + 1` canonical radii `1 − t/n` (`t ≤ n`), determined by the floor values
  `V_t = ε_mca(C, 1 − t/n)`: if `V_0 ≤ ε*` then `δ* = 1`; if `V_n > ε*` then `δ* = 0`;
  otherwise `δ* = 1 − (t₀ − 1)/n` for the least `t₀` with `V_{t₀} ≤ ε*`
  (`MCAStepFunction.mcaDeltaStar_eq_of_floor_values`).

**Correction (audit 2026-10-28, PG-027).** An earlier version of this header presented
`mcaDeltaStar_eq_of_finite_floor_table` (goodness **at** `δ₀`, badness at a table whose floors
cover `(δ₀, 1]`) as the final, complete production assembly. That theorem is valid, but its
premises force `δ₀ = 1` (`eq_one_of_finite_floor_table_premises`): the coverage premise only
transports the band contradiction of `MCAStepFunction.eq_one_of_band_premises` through a
table entry, so it pins only the endpoint `δ* = 1` and cannot reach an interior threshold.

What is proven here is the finite reduction: `δ*` is determined by finitely many floor
values. Those values are **not** computed here for production codes; determining them
(per cell, e.g. by the census machinery: LYM ceiling, supply, circuit census) remains the
open mathematical content of `δ*` at production scale.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- Issue #357 (round-14); `MCAStepFunction.lean` (step law, floor-value pin, endpoint-only
  band form).
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code ProximityGap.MCAThresholdLedger
open ProximityGap.MCAStepFunction

namespace ProximityGap.MCAFiniteTable

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## The good-side finite table -/

/-- **The finite-table assembly.** `δ* = δ₀` from badness at `δ₀ ≤ 1`, goodness at a finite
table `T` of radii, and floor-coverage of the band `[0, δ₀)` by the table (every radius
strictly below `δ₀` shares its agreement floor with a table entry). By the step law every
radius below `δ₀` is then good, and `MCAListBracketInterpolation.mcaDeltaStar_eq_of_jump`
pins the threshold at the bad radius `δ₀`. -/
theorem mcaDeltaStar_eq_of_good_floor_table (C : Set (ι → A)) (εstar : ℝ≥0∞)
    {δ₀ : ℝ≥0} (hδ₀ : δ₀ ≤ 1)
    (T : Finset ℝ≥0)
    (hcover : ∀ δ : ℝ≥0, δ < δ₀ → ∃ δ' ∈ T,
      ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ = ⌈(1 - δ') * (Fintype.card ι : ℝ≥0)⌉₊)
    (hgoodT : ∀ δ' ∈ T, epsMCA (F := F) (A := A) C δ' ≤ εstar)
    (hbad : εstar < epsMCA (F := F) (A := A) C δ₀) :
    mcaDeltaStar (F := F) (A := A) C εstar = δ₀ := by
  refine MCAListBracketInterpolation.mcaDeltaStar_eq_of_jump C εstar hδ₀
    (fun δ hlt => ?_) hbad
  obtain ⟨δ', hδ'T, hfloor⟩ := hcover δ hlt
  rw [epsMCA_eq_of_ceil_eq (F := F) C hfloor]
  exact hgoodT δ' hδ'T

/-- **The coverage premise is satisfiable at interior thresholds.** For `1 ≤ t₀ ≤ n`, the
canonical table `{1 − t/n : t₀ ≤ t ≤ n}` floor-covers every radius strictly below the
canonical boundary `1 − (t₀ − 1)/n`: such a radius has agreement floor `t` with
`t₀ ≤ t ≤ n`, which is the floor of the table entry `1 − t/n`. -/
theorem canonical_floor_table_cover {n t₀ : ℕ} (hn : n ≠ 0) (ht₀ : 1 ≤ t₀) (ht₀n : t₀ ≤ n)
    (δ : ℝ≥0) (hδ : δ < floorRadius n (t₀ - 1)) :
    ∃ δ' ∈ (Finset.Icc t₀ n).image (floorRadius n),
      ⌈(1 - δ) * (n : ℝ≥0)⌉₊ = ⌈(1 - δ') * (n : ℝ≥0)⌉₊ := by
  have hn' : (0 : ℝ≥0) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have htn : ⌈(1 - δ) * (n : ℝ≥0)⌉₊ ≤ n := ceil_one_sub_mul_le n δ
  have ht₀t : t₀ ≤ ⌈(1 - δ) * (n : ℝ≥0)⌉₊ := by
    have hlt : ((t₀ - 1 : ℕ) : ℝ≥0) < (1 - δ) * (n : ℝ≥0) :=
      calc ((t₀ - 1 : ℕ) : ℝ≥0) = (1 - floorRadius n (t₀ - 1)) * (n : ℝ≥0) :=
            (one_sub_floorRadius_mul hn (by omega)).symm
        _ < (1 - δ) * (n : ℝ≥0) :=
            mul_lt_mul_of_pos_right (tsub_lt_tsub_left_of_le (floorRadius_le_one _ _) hδ) hn'
    have := Nat.lt_ceil.mpr hlt
    omega
  exact ⟨floorRadius n ⌈(1 - δ) * (n : ℝ≥0)⌉₊,
    Finset.mem_image.mpr ⟨_, Finset.mem_Icc.mpr ⟨ht₀t, htn⟩, rfl⟩,
    (ceil_floorRadius hn htn).symm⟩

/-! ## `δ*` is one of the `n + 1` canonical radii -/

/-- **Finite determination of `δ*`.** For every code `C` and every target `ε*`, the threshold
`δ*(C, ε*)` is one of the `n + 1` canonical radii `1 − t/n` with `t ≤ n`. Which one is read
off the floor values `V_t = ε_mca(C, 1 − t/n)` (antitone in `t`): `t = n` (`δ* = 0`) when
`V_n > ε*`; `t = 0` (`δ* = 1`) when `V_0 ≤ ε*`; otherwise `t = t₀ − 1` for the least `t₀` with
`V_{t₀} ≤ ε*` (`MCAStepFunction.mcaDeltaStar_eq_of_floor_values`). -/
theorem exists_mcaDeltaStar_eq_floorRadius (C : Set (ι → A)) (εstar : ℝ≥0∞) :
    ∃ t ≤ Fintype.card ι,
      mcaDeltaStar (F := F) (A := A) C εstar = floorRadius (Fintype.card ι) t := by
  classical
  have hn : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  by_cases hzero :
      epsMCA (F := F) (A := A) C (floorRadius (Fintype.card ι) (Fintype.card ι)) ≤ εstar
  · have hex : ∃ t, epsMCA (F := F) (A := A) C (floorRadius (Fintype.card ι) t) ≤ εstar :=
      ⟨_, hzero⟩
    have hspec := Nat.find_spec hex
    have hmin := Nat.find_min' hex hzero
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · refine ⟨0, Nat.zero_le _, ?_⟩
      rw [h0, floorRadius_zero] at hspec
      rw [floorRadius_zero]
      exact le_antisymm (csSup_le' fun δ hδ => hδ.1) (le_mcaDeltaStar_of_good C εstar le_rfl hspec)
    · refine ⟨Nat.find hex - 1, by omega, ?_⟩
      exact mcaDeltaStar_eq_of_floor_values C εstar hpos hmin hspec
        (lt_of_not_ge (Nat.find_min hex (by omega)))
  · refine ⟨Fintype.card ι, le_rfl, ?_⟩
    rw [floorRadius_self hn] at hzero ⊢
    exact le_antisymm (mcaDeltaStar_le_of_bad C εstar (lt_of_not_ge hzero)) zero_le

/-! ## The endpoint-only attained form -/

/-- **The attained table premises force the endpoint.** Goodness at `δ₀ ≤ 1`, badness on a
finite table `T`, and floor-coverage of `(δ₀, 1]` by `T` imply `δ₀ = 1`: through the step law
the table transports badness to all of `(δ₀, 1]`, and `MCAStepFunction.eq_one_of_band_premises`
applies (audit 2026-10-28, PG-027). -/
theorem eq_one_of_finite_floor_table_premises (C : Set (ι → A)) (εstar : ℝ≥0∞)
    {δ₀ : ℝ≥0} (hδ₀ : δ₀ ≤ 1)
    (hgood : epsMCA (F := F) (A := A) C δ₀ ≤ εstar)
    (T : Finset ℝ≥0)
    (hcover : ∀ δ : ℝ≥0, δ₀ < δ → δ ≤ 1 → ∃ δ' ∈ T,
      ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ = ⌈(1 - δ') * (Fintype.card ι : ℝ≥0)⌉₊)
    (hbadT : ∀ δ' ∈ T, εstar < epsMCA (F := F) (A := A) C δ') :
    δ₀ = 1 := by
  refine eq_one_of_band_premises C εstar hδ₀ hgood fun δ hlt hle => ?_
  obtain ⟨δ', hδ'T, hfloor⟩ := hcover δ hlt hle
  rw [epsMCA_eq_of_ceil_eq (F := F) C hfloor]
  exact hbadT δ' hδ'T

/-- **Endpoint-only attained table assembly.** `δ* = δ₀` from goodness at `δ₀`, badness at a
finite table of radii, and floor-coverage of the band `(δ₀, 1]` by the table. The statement is
valid, but its premises force `δ₀ = 1` (`eq_one_of_finite_floor_table_premises`), so it only
covers the endpoint case `δ* = 1`. Interior thresholds are pinned by
`mcaDeltaStar_eq_of_good_floor_table` or `MCAStepFunction.mcaDeltaStar_eq_of_floor_values`. -/
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

#print axioms mcaDeltaStar_eq_of_good_floor_table
#print axioms canonical_floor_table_cover
#print axioms exists_mcaDeltaStar_eq_floorRadius
#print axioms eq_one_of_finite_floor_table_premises
#print axioms mcaDeltaStar_eq_of_finite_floor_table

end ProximityGap.MCAFiniteTable
