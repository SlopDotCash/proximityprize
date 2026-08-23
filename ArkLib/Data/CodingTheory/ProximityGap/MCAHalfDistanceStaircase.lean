/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCABandTwoRS

/-!
# Round 3 (#357): the half-distance staircase law — proven floor, named open surface

The staircase program's discovered law (DISPROOF_LOG, round-3 opening; probe record: 6
collapse rows + 5 boundary rows, one exhaustive):

> On band `b` (`δ·n ∈ [b−1, b)`), `ε_mca(C, δ) = b/|F|` — the spike staircase — **while
> `d ≥ 2b`**; at the boundary `d = 2b−1` it explodes to `~n/|F|`. The staircase is exactly
> linear up to the unique-decoding radius, where the flat-numerator-`n` jump occurs (the
> historical `(12,6)` flat-numerator datum is the band-4 boundary case).

Per the project conventions the law lives here as one **named Prop** per half, with the
proven instances wired and the open bands left as explicit surfaces (never axioms):

* `LinearStaircaseUpper C b` — "every stack has `≤ b` bad scalars on band `≤ b`";
  `linearStaircaseUpper_one` and `linearStaircaseUpper_two` are **theorems** (R1's
  sub-granularity argument; the band-2 collapse). `b ≥ 3` at `d ≥ 2b` is the open
  multi-`c*`-elimination surface — 4 scalars span a 2-dimensional relation space of
  codewords supported on the puncture union, and the band-2 proof's single relation does
  not suffice (the core-free overlapping families realize exactly `b` scalars, so the
  bound, if provable, is sharp).
* `staircase_value_band_one` / `staircase_value_band_two` — the **exact** step values
  `1/|F|` and `2/|F|`, for every proper linear code of distance `≥ 4` (any code for band
  one; both immediate corollaries of the landed theorems, restated here as the staircase's
  first two rungs in one place).

The boundary-explosion half (`d = 2b−1 ⟹ ~n/|F|`) remains probe-verified only
(exhaustively at `(11,6,2)`, band 3); its general construction (core-free puncture families
+ weight-`(2b−1)` codeword corrections) is the round-3 lower-bound target and is *not*
asserted here.

All declarations are `sorry`-free and axiom-clean (`[propext, Classical.choice,
Quot.sound]`); the open surfaces are `def ... : Prop`, consumed hypothetically.

## References
- Issue #357 (the δ* campaign; round 3); DISPROOF_LOG entries of 2026-06-11.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCAHalfDistanceStaircase

open ProximityGap.MCABandTwoCollapse ProximityGap.MCABandTwoExact
open ProximityGap.MCADeltaStarExactPoint

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **The linear-staircase upper surface at band `b`:** every stack has at most `b` bad
scalars at every radius with `δ·n < b`. Proven for `b = 1, 2`; the conjectured regime for
`b ≥ 3` is `d ≥ 2b` (the half-distance law). -/
noncomputable def LinearStaircaseUpper (C : Submodule F (ι → A)) (b : ℕ) : Prop :=
  ∀ (δ : ℝ≥0), δ * (Fintype.card ι : ℝ≥0) < (b : ℝ≥0) →
    ∀ u : WordStack A (Fin 2) ι,
      (Finset.filter (fun γ : F =>
        mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ) Finset.univ).card ≤ b

open Classical in
/-- **Band 1 is a theorem** for every linear code (the R1 sub-granularity argument). -/
theorem linearStaircaseUpper_one (C : Submodule F (ι → A)) :
    LinearStaircaseUpper C 1 := by
  intro δ hδ u
  refine badScalar_card_le_one_of_small_radius C ?_ u
  exact_mod_cast hδ

open Classical in
/-- **Band 2 is a theorem** for every linear code of distance `≥ 4` (the collapse). -/
theorem linearStaircaseUpper_two (C : Submodule F (ι → A)) (hC : NoLowWeight C)
    (hn : 3 ≤ Fintype.card ι) :
    LinearStaircaseUpper C 2 := by
  intro δ hδ u
  refine badScalar_card_le_two_of_dist4 C hC hn ?_ u
  exact_mod_cast hδ

/-- **The first staircase rung, exact** (restating R1's general theorem as the staircase's
band-1 value): every proper linear code has `ε_mca = 1/|F|` on `δ·n < 1`. -/
theorem staircase_value_band_one (C : Submodule F (ι → A)) {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < 1) (hC : (C : Set (ι → A)) ≠ Set.univ) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ = 1 / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_eq_inv_card_of_small_radius C hδ hC

/-- **The second staircase rung, exact** (restating the universal second band): every
linear code of distance `≥ 4` has `ε_mca = 2/|F|` on `1 ≤ δ·n < 2`. -/
theorem staircase_value_band_two (C : Submodule F (ι → A)) (hC : NoLowWeight C)
    (hn : 3 ≤ Fintype.card ι) {δ : ℝ≥0}
    (hδ1 : 1 ≤ δ * (Fintype.card ι : ℝ≥0)) (hδ2 : δ * (Fintype.card ι : ℝ≥0) < 2)
    {i₁ i₂ : ι} (hne : i₁ ≠ i₂) {a : A} (ha : a ≠ 0) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ = 2 / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_eq_two_div_card_of_dist4 C hC hn hδ1 hδ2 hne ha

/-- **The open half-distance surface** (`b ≥ 3`): no nonzero codeword on `< 2b` points
implies the linear-staircase upper at band `b`. The probe record supports it (band 3 at
`d = 6, 7`: max exactly `3`); the band-2 proof's single `c*`-relation does not generalize
(4 scalars span a 2-dimensional relation space of codewords supported on the puncture
union) — this is the round-3 elimination target, stated and never asserted. -/
def HalfDistanceStaircaseConjecture : Prop :=
  ∀ (ι : Type) (inst1 : Fintype ι) (inst2 : Nonempty ι) (inst3 : DecidableEq ι)
    (F : Type) (inst4 : Field F) (inst5 : Fintype F) (inst6 : DecidableEq F)
    (C : Submodule F (ι → F)) (b : ℕ), 3 ≤ b →
    (∀ w ∈ C, (∃ T : Finset ι, T.card < 2 * b ∧ ∀ i ∉ T, w i = 0) → w = 0) →
    LinearStaircaseUpper C b

/-- The conjecture's consumer: under the surface, the spike value caps `ε_mca` on every
sub-half-distance band — the entire unique-decoding staircase becomes linear. -/
theorem epsMCA_le_staircase_of_conjecture (hconj : HalfDistanceStaircaseConjecture)
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (C : Submodule F (ι → F)) (b : ℕ) (hb : 3 ≤ b)
    (hC : ∀ w ∈ C, (∃ T : Finset ι, T.card < 2 * b ∧ ∀ i ∉ T, w i = 0) → w = 0)
    {δ : ℝ≥0} (hδ : δ * (Fintype.card ι : ℝ≥0) < (b : ℝ≥0)) :
    epsMCA (F := F) (A := F) (C : Set (ι → F)) δ
      ≤ (b : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast hconj ι inferInstance inferInstance inferInstance F inferInstance inferInstance
    inferInstance C b hb hC δ hδ u

/-! ## Source audit -/

#print axioms linearStaircaseUpper_one
#print axioms linearStaircaseUpper_two
#print axioms staircase_value_band_one
#print axioms staircase_value_band_two
#print axioms epsMCA_le_staircase_of_conjecture

end ProximityGap.MCAHalfDistanceStaircase
