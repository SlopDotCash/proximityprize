/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpreadExample
import ArkLib.Data.CodingTheory.ProximityGap.MCAGeneralLowerBound

/-!
# Adversarial candidate ledger for the Grand MCA threshold `δ*` (#232)

The Grand MCA Challenge asks for the largest `δ*` with `ε_mca(C, δ*) ≤ ε*` (`ε* = 2^-128`),
**with a matching lower bound** `ε_mca(C, δ) > ε*` for all `δ > δ*`. This file runs the honest
scientific loop the prize demands: state candidate answers, then *prove* or *refute* each.

Every entry below carries a machine-checked verdict. The point is twofold:
* **kill the easy/false candidates** (so no one mistakes a trivial answer for the prize), and
* **bracket `δ*`** with proven inequalities, isolating the genuinely open survivor.

## Verdicts

* `mca_good_set_downward_closed` — **PROVEN (meta).** The set of "good" radii `{δ | ε_mca ≤ ε*}`
  is downward closed (monotonicity of `ε_mca`), so `δ*` is well-defined as its supremum. This is
  the bracketing engine: any proven `ε_mca(C, δ₀) ≤ ε*` gives `δ* ≥ δ₀`, and any proven
  `ε_mca(C, δ₁) > ε*` gives `δ* ≤ δ₁`.
  The API `mcaGoodRadii` / `mcaDeltaStar` / `le_mcaDeltaStar_of_good` /
  `mcaDeltaStar_le_of_bad` makes this `sSup` bracketing explicit inside `[0,1]`.

* `candidate_floor_is_exact_REFUTED` — **REFUTED.** The candidate "`ε_mca` equals its
  unconditional floor `1/|F|` everywhere below capacity" (which would trivialize the prize, making
  `δ* = ` capacity independent of `δ`) is *false*: the constant code over `ZMod 3` has
  `ε_mca(C, 1/3) = 1 > 1/3 = 1/|F|`, with `1/3` strictly below its capacity `2/3`. So `ε_mca`
  genuinely *grows* with `δ` — the prize is non-trivial.

* `candidate_uptocapacity_REFUTED` — **REFUTED (structural).** The candidate "`ε_mca(C, δ) ≤ ε*`
  for every linear code and every `δ <` capacity" is false: the same constant code has
  `ε_mca(C, 1/3) = 1 > 2^-128 = ε*` with `1/3 <` capacity. (This is the *structural / small-field*
  refutation; the deep large-field RS refutations are [CS25],[KK25] — ported, not reproved here.)
  It also shows precisely *why* the prize fixes `|F|` large: smallness of `ε_mca` is impossible
  without it.

* `candidate_exact_delta_star_OPEN` — **OPEN (the survivor).** The exact `δ*` in the interior
  `(1-√ρ, 1-ρ)` for explicit smooth-domain RS at the prize rates is *not* settled here. By
  `MCAWitnessSpread.unique_bad_gamma_common_witness` it reduces to producing an `n^{Ω(1)}`-size
  *spread of distinct witness sets* for such a code — genuine open research. This file does **not**
  assert it; it is recorded as the open survivor, honestly (#141, #171).

All proven verdicts are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAWitnessSpread.Example

namespace ProximityGap.MCAThresholdLedger

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## Meta: the bracketing engine -/

/-- **PROVEN (meta).** The good-radius set `{δ | ε_mca(C, δ) ≤ ε*}` is downward closed: if
`ε_mca(C, δ₀) ≤ ε*` and `δ₁ ≤ δ₀`, then `ε_mca(C, δ₁) ≤ ε*`. Hence `δ*` is the supremum of an
interval and any proven point-bound brackets it. -/
theorem mca_good_set_downward_closed (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ₀ δ₁ : ℝ≥0}
    (hle : δ₁ ≤ δ₀) (hgood : epsMCA (F := F) (A := A) C δ₀ ≤ εstar) :
    epsMCA (F := F) (A := A) C δ₁ ≤ εstar :=
  le_trans (epsMCA_mono C hle) hgood

omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- The good MCA radii inside the meaningful radius interval `[0,1]`: radii whose MCA error is at
most the target `εstar`. Bounding by `1` gives a genuine `sSup` threshold even before the exact
interior answer is known. -/
def mcaGoodRadii (C : Set (ι → A)) (εstar : ℝ≥0∞) : Set ℝ≥0 :=
  {δ | δ ≤ 1 ∧ epsMCA (F := F) (A := A) C δ ≤ εstar}

omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- The formal MCA threshold candidate: the supremum of good radii inside `[0,1]`. This is the
machine-checked object bracketed by pointwise good/bad bounds below. -/
noncomputable def mcaDeltaStar (C : Set (ι → A)) (εstar : ℝ≥0∞) : ℝ≥0 :=
  sSup (mcaGoodRadii (F := F) (A := A) C εstar)

omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- The good-radius set is bounded above by `1`, by construction. -/
theorem mcaGoodRadii_bddAbove (C : Set (ι → A)) (εstar : ℝ≥0∞) :
    BddAbove (mcaGoodRadii (F := F) (A := A) C εstar) :=
  ⟨1, fun _ hδ => hδ.1⟩

omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- **Lower bracket for `δ*`.** Any proven good point `δ ≤ 1` lies below the formal threshold. -/
theorem le_mcaDeltaStar_of_good (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ : ℝ≥0}
    (hδ : δ ≤ 1) (hgood : epsMCA (F := F) (A := A) C δ ≤ εstar) :
    δ ≤ mcaDeltaStar (F := F) (A := A) C εstar := by
  exact le_csSup (mcaGoodRadii_bddAbove (F := F) (A := A) C εstar) ⟨hδ, hgood⟩

omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- A bad point is an upper bound for all good radii: if `εstar < ε_mca(C, δbad)`, monotonicity
prevents any good radius from lying at or above `δbad`. -/
theorem mcaGoodRadii_le_of_bad (C : Set (ι → A)) (εstar : ℝ≥0∞) {δbad δ : ℝ≥0}
    (hbad : εstar < epsMCA (F := F) (A := A) C δbad)
    (hδ : δ ∈ mcaGoodRadii (F := F) (A := A) C εstar) :
    δ ≤ δbad := by
  by_contra hnot
  have hbad_le : δbad ≤ δ := le_of_not_ge hnot
  have hmono : epsMCA (F := F) (A := A) C δbad ≤ epsMCA (F := F) (A := A) C δ :=
    by
      classical
      unfold epsMCA
      apply iSup_mono
      intro u
      apply Pr_le_Pr_of_implies
      intro γ h_event
      obtain ⟨S, hS_card, hline, hpair⟩ := h_event
      exact ⟨S, le_trans
        (mul_le_mul_of_nonneg_right (tsub_le_tsub_left hbad_le 1) (zero_le _)) hS_card,
        hline, hpair⟩
  exact not_le_of_gt hbad (le_trans hmono hδ.2)

omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- **Upper bracket for `δ*`.** Any proven bad point lies above the formal threshold. This version
does not require the good-radius set to be nonempty; it uses the `upperBounds` form of `csSup`. -/
theorem mcaDeltaStar_le_of_bad (C : Set (ι → A)) (εstar : ℝ≥0∞) {δbad : ℝ≥0}
    (hbad : εstar < epsMCA (F := F) (A := A) C δbad) :
    mcaDeltaStar (F := F) (A := A) C εstar ≤ δbad := by
  unfold mcaDeltaStar
  exact csSup_le' (show δbad ∈ upperBounds
      (mcaGoodRadii (F := F) (A := A) C εstar) from
    fun δ hδ => mcaGoodRadii_le_of_bad (F := F) (A := A) C εstar hbad hδ)

/-! ## VERDICT 1 — REFUTED: the MCA error is *not* pinned to its `1/|F|` floor -/

/-- The unconditional floor `ε_mca ≥ 1/|F|` (all codes, below capacity) is *not* tight: a concrete
linear code exceeds it strictly. This refutes the candidate that would trivialize the prize. -/
theorem candidate_floor_is_exact_REFUTED :
    (1 : ℝ≥0∞) / (Fintype.card (ZMod 3) : ℝ≥0∞)
      < epsMCA (F := ZMod 3) (A := ZMod 3) constCode (1/3 : ℝ≥0) := by
  rw [epsMCA_constCode_eq_one]
  have hc : (Fintype.card (ZMod 3) : ℝ≥0∞) = 3 := by simp [ZMod.card]
  rw [hc, ENNReal.div_lt_iff (by norm_num) (by norm_num)]
  norm_num

/-! ## VERDICT 2 — REFUTED: `ε_mca ≤ ε*` cannot hold "up to capacity" for *all* codes/fields -/

/-- The "up-to-capacity" MCA candidate, in its universal form, is false: the constant code over
`ZMod 3` has `ε_mca(C, 1/3) = 1 > 2^-128 = ε*`, with `1/3` strictly below its capacity `2/3`.
This is the structural / small-field refutation; it shows the prize *must* fix `|F|` large. -/
theorem candidate_uptocapacity_REFUTED :
    ((1 : ℝ≥0) / 2 ^ (128 : ℕ) : ℝ≥0∞)
      < epsMCA (F := ZMod 3) (A := ZMod 3) constCode (1/3 : ℝ≥0) := by
  rw [epsMCA_constCode_eq_one,
    ENNReal.div_lt_iff (by norm_num) (by norm_num), one_mul, ENNReal.coe_one]
  calc (1 : ℝ≥0∞) < 2 := by norm_num
    _ = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ (128 : ℕ) := by gcongr <;> norm_num

/-- The capacity `1 - ρ` of the constant code over `Fin 3` is `2/3`, and the tested radius
`1/3` lies strictly below it — so VERDICT 2 really is a below-capacity refutation, not an artifact
of testing above capacity. (`ρ = k/n = 1/3` since `dim = 1`, `n = 3`.) -/
theorem tested_radius_below_capacity :
    (1 / 3 : ℝ≥0) < 1 - (1 / 3 : ℝ≥0) := by
  rw [show (1 : ℝ≥0) - 1 / 3 = 2 / 3 from by
    apply NNReal.coe_injective
    have h13 : (1 : ℝ≥0) / 3 ≤ 1 := by rw [div_le_one (by norm_num : (0 : ℝ≥0) < 3)]; norm_num
    push_cast [NNReal.coe_sub h13]; norm_num]
  rw [div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ≥0) < 3)]
  norm_num

#print axioms mca_good_set_downward_closed
#print axioms le_mcaDeltaStar_of_good
#print axioms mcaGoodRadii_le_of_bad
#print axioms mcaDeltaStar_le_of_bad
#print axioms candidate_floor_is_exact_REFUTED
#print axioms candidate_uptocapacity_REFUTED
#print axioms tested_radius_below_capacity

end ProximityGap.MCAThresholdLedger
