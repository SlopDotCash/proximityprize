/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAListBracketInterpolation
import ArkLib.Data.CodingTheory.ProximityGap.MCAEquivariance

/-!
# The step-function law (#357 round 11): `ε_mca` takes at most `n + 1` values

The `mcaEvent` witness clause `(|S| : ℝ≥0) ≥ (1−δ)·n` sees the radius only through the
integer agreement floor `t = ⌈(1−δ)·n⌉₊`. Hence:

* `mcaEvent_iff_floor` — the event depends on `δ` only through `⌈(1−δ)n⌉₊`;
* **`epsMCA_eq_of_ceil_eq`** — `ε_mca(C, ·)` is a **step function**: radii with equal
  floors have equal MCA error. Since `⌈(1−δ)·n⌉₊ ∈ {0, …, n}`, for every code `C` on `n`
  coordinates `ε_mca(C, ·)` takes at most `n + 1` distinct values along the whole radius axis:
  `epsMCA_eq_floorValue` writes every value as a floor value `V_t = ε_mca(C, 1 − t/n)`, `t ≤ n`;
* `exists_gt_ceil_eq_of_lt_one` / `exists_gt_epsMCA_eq_of_lt_one` — the floor cells are
  **open on the right**: for `1 ≤ t ≤ n` the radii with floor `t` form `[1 − t/n, 1 − (t−1)/n)`,
  so every radius `δ < 1` has a strictly larger radius `δ' ≤ 1` with the same floor and hence
  the same MCA error; consequently a threshold `δ* < 1` is itself a bad radius
  (`lt_epsMCA_mcaDeltaStar_of_lt_one`);
* **`mcaDeltaStar_eq_of_floor_values`** — **the staircase-inverse assembly**: if the
  floor-value at `t₀` is good (`V_{t₀} = ε_mca(C, 1 − t₀/n) ≤ ε*`) and the one at `t₀ − 1` is
  bad (`> ε*`), with `1 ≤ t₀ ≤ n`, then `δ* = 1 − (t₀ − 1)/n` exactly — the threshold is pinned
  by two consecutive floor-values. It is an instance of the jump pin
  `MCAListBracketInterpolation.mcaDeltaStar_eq_of_jump` (goodness at every radius strictly below
  `δ₀`, badness at `δ₀`): the threshold is the excluded right endpoint of the last good floor
  cell, and is itself a **bad** radius. A per-cell census determination converts to an exact
  `δ*` value through this lemma once it supplies such a good/bad pair of adjacent floors.

**The band form is endpoint-only (audit correction, 2026-10-28, PG-027).** An earlier version
of this file presented `mcaDeltaStar_eq_of_band` (goodness **at** `δ₀` and badness at every
`δ ∈ (δ₀, 1]`) as the staircase inverse, and advertised `mcaDeltaStar_eq_of_floor_values`
before it was implemented. The band theorem is valid, but because floor cells are open on the
right its premises force `δ₀ = 1` (`eq_one_of_band_premises`), so it can only record the
endpoint case `δ* = 1`. Likewise the uncapped closed-good premises of
`MCAThresholdLedger.mcaDeltaStar_eq_of_good_of_bad_above` (`MCAExactPin.lean`) are never
jointly satisfiable (`not_good_and_bad_above`).

This explains the measured profiles (the pure step functions of the probes) and makes the
assembly finite: `MCAFiniteTable.exists_mcaDeltaStar_eq_floorRadius` shows that `δ*(ε*)` is
one of the `n + 1` canonical radii `1 − t/n`, determined by the finite vector of floor-values
`(V_n, V_{n−1}, …, V_0)`. Computing those floor values for production codes is not done here
and remains open; only particular cells are bracketed or settled in-tree (e.g. the good/bad jump
at radius `1/n` for high-rate RS in `MCADeltaStarHighRateFamily.lean`, and `V_t = C(n,t)/q`
under an explicit full-layer supply hypothesis in `CrossingPin.lean`).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- Issue #357 (round-11 queue); `MCAListBracketInterpolation.lean` (jump-pin engine).
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code ProximityGap.MCAThresholdLedger
open ProximityGap.MCAListBracketInterpolation ProximityGap.MCAEquivariance

namespace ProximityGap.MCAStepFunction

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The witness-card clause sees only the ceiling floor. -/
theorem card_clause_iff_floor {δ : ℝ≥0} {S : Finset ι} :
    ((S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι : ℝ≥0))
      ↔ ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ ≤ S.card := by
  rw [ge_iff_le, ← Nat.ceil_le]

/-- **The event sees only the floor.** Two radii with equal agreement floors have
identical `mcaEvent`s. -/
theorem mcaEvent_iff_floor (C : Set (ι → A)) {δ δ' : ℝ≥0}
    (hfloor : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊
      = ⌈(1 - δ') * (Fintype.card ι : ℝ≥0)⌉₊)
    (u₀ u₁ : ι → A) (γ : F) :
    mcaEvent (F := F) C δ u₀ u₁ γ ↔ mcaEvent (F := F) C δ' u₀ u₁ γ := by
  constructor
  · rintro ⟨S, hcard, hline, hno⟩
    refine ⟨S, ?_, hline, hno⟩
    rw [card_clause_iff_floor] at hcard ⊢
    rw [← hfloor]
    exact hcard
  · rintro ⟨S, hcard, hline, hno⟩
    refine ⟨S, ?_, hline, hno⟩
    rw [card_clause_iff_floor] at hcard ⊢
    rw [hfloor]
    exact hcard

/-- **The step-function law.** `ε_mca` depends on the radius only through the agreement
floor: it is a step function taking at most `n + 2` values. -/
theorem epsMCA_eq_of_ceil_eq (C : Set (ι → A)) {δ δ' : ℝ≥0}
    (hfloor : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊
      = ⌈(1 - δ') * (Fintype.card ι : ℝ≥0)⌉₊) :
    epsMCA (F := F) (A := A) C δ = epsMCA (F := F) (A := A) C δ' := by
  classical
  unfold epsMCA
  apply iSup_congr
  intro u
  exact Pr_congr_iff _ (fun γ => mcaEvent_iff_floor C hfloor (u 0) (u 1) γ)

/-! ## Floor cells are open on the right -/

/-- Every positive real has a strictly smaller real with the same ceiling. -/
theorem exists_lt_ceil_eq {x : ℝ≥0} (hx : 0 < x) :
    ∃ y : ℝ≥0, y < x ∧ ⌈y⌉₊ = ⌈x⌉₊ := by
  have ht : ⌈x⌉₊ ≠ 0 := (Nat.ceil_pos.mpr hx).ne'
  obtain ⟨hlo, hhi⟩ := (Nat.ceil_eq_iff ht).mp rfl
  obtain ⟨y, hylo, hyx⟩ := exists_between hlo
  exact ⟨y, hyx, (Nat.ceil_eq_iff ht).mpr ⟨hylo, hyx.le.trans hhi⟩⟩

/-- **Right plateau of the agreement floor.** On `n > 0` coordinates every radius `δ < 1` has
a strictly larger radius `δ' ≤ 1` with the same agreement floor `⌈(1 − δ)·n⌉₊`: the floor cell
`[1 − t/n, 1 − (t − 1)/n)` of `t = ⌈(1 − δ)·n⌉₊ ≥ 1` is open on the right. -/
theorem exists_gt_ceil_eq_of_lt_one {n : ℕ} (hn : n ≠ 0) {δ : ℝ≥0} (hδ : δ < 1) :
    ∃ δ' : ℝ≥0, δ < δ' ∧ δ' ≤ 1 ∧
      ⌈(1 - δ') * (n : ℝ≥0)⌉₊ = ⌈(1 - δ) * (n : ℝ≥0)⌉₊ := by
  have hn' : (0 : ℝ≥0) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  obtain ⟨y, hyx, hceil⟩ := exists_lt_ceil_eq (mul_pos (tsub_pos_of_lt hδ) hn')
  have hyn : y / (n : ℝ≥0) < 1 - δ := (div_lt_iff₀ hn').mpr hyx
  have hy1 : y / (n : ℝ≥0) ≤ 1 := hyn.le.trans tsub_le_self
  refine ⟨1 - y / (n : ℝ≥0), lt_tsub_iff_right.mpr (lt_tsub_iff_left.mp hyn), tsub_le_self, ?_⟩
  rw [tsub_tsub_cancel_of_le hy1, div_mul_cancel₀ _ hn'.ne', hceil]

/-- Uncapped right plateau: every radius `δ` has a strictly larger radius with the same
agreement floor (for `δ ≥ 1` both floors are `0`). -/
theorem exists_gt_ceil_eq {n : ℕ} (hn : n ≠ 0) (δ : ℝ≥0) :
    ∃ δ' : ℝ≥0, δ < δ' ∧ ⌈(1 - δ') * (n : ℝ≥0)⌉₊ = ⌈(1 - δ) * (n : ℝ≥0)⌉₊ := by
  rcases lt_or_ge δ 1 with hδ | hδ
  · obtain ⟨δ', hlt, -, hceil⟩ := exists_gt_ceil_eq_of_lt_one hn hδ
    exact ⟨δ', hlt, hceil⟩
  · have h1 : (1 : ℝ≥0) ≤ δ + 1 := hδ.trans (le_add_of_nonneg_right zero_le_one)
    refine ⟨δ + 1, lt_add_one δ, ?_⟩
    rw [tsub_eq_zero_of_le hδ, tsub_eq_zero_of_le h1]

/-- **Right plateau of `ε_mca`.** Every radius `δ < 1` has a strictly larger radius `δ' ≤ 1`
with the same MCA error. In particular no radius `δ < 1` is a largest good radius. -/
theorem exists_gt_epsMCA_eq_of_lt_one (C : Set (ι → A)) {δ : ℝ≥0} (hδ : δ < 1) :
    ∃ δ' : ℝ≥0, δ < δ' ∧ δ' ≤ 1 ∧
      epsMCA (F := F) (A := A) C δ' = epsMCA (F := F) (A := A) C δ := by
  obtain ⟨δ', hlt, hle, hceil⟩ :=
    exists_gt_ceil_eq_of_lt_one (Fintype.card_ne_zero (α := ι)) hδ
  exact ⟨δ', hlt, hle, epsMCA_eq_of_ceil_eq C hceil⟩

/-- Uncapped right plateau of `ε_mca`: every radius has a strictly larger radius with the same
MCA error. -/
theorem exists_gt_epsMCA_eq (C : Set (ι → A)) (δ : ℝ≥0) :
    ∃ δ' : ℝ≥0, δ < δ' ∧
      epsMCA (F := F) (A := A) C δ' = epsMCA (F := F) (A := A) C δ := by
  obtain ⟨δ', hlt, hceil⟩ := exists_gt_ceil_eq (Fintype.card_ne_zero (α := ι)) δ
  exact ⟨δ', hlt, epsMCA_eq_of_ceil_eq C hceil⟩

/-- **A threshold below `1` is a bad radius.** If `δ* < 1` then `ε* < ε_mca(C, δ*)`: were `δ*`
good, the right plateau would give a strictly larger good radius `δ' ≤ 1`. So whenever
`δ* < 1` the good radii form `[0, δ*)` and the supremum is excluded. -/
theorem lt_epsMCA_mcaDeltaStar_of_lt_one (C : Set (ι → A)) (εstar : ℝ≥0∞)
    (h : mcaDeltaStar (F := F) (A := A) C εstar < 1) :
    εstar < epsMCA (F := F) (A := A) C (mcaDeltaStar (F := F) (A := A) C εstar) := by
  by_contra hgood
  obtain ⟨δ', hlt, hle, heq⟩ := exists_gt_epsMCA_eq_of_lt_one (F := F) C h
  exact hlt.not_ge (le_mcaDeltaStar_of_good C εstar hle (heq.trans_le (not_lt.mp hgood)))

/-! ## The staircase-inverse assembly

The inverse of the staircase is the jump pin `MCAListBracketInterpolation.mcaDeltaStar_eq_of_jump`:
goodness at every radius strictly below `δ₀ ≤ 1` and badness at `δ₀` give `δ* = δ₀`. Since
floor cells are open on the right, an interior threshold is the excluded right endpoint of the
last good floor cell and is itself a bad radius; the two-consecutive-floor pin below is the
canonical instance. -/

/-- The canonical radius `1 − t/n` of the agreement floor `t` on `n` coordinates. For `t ≤ n`
its agreement floor `⌈(1 − δ)·n⌉₊` is exactly `t` (`ceil_floorRadius`); for `1 ≤ t ≤ n` it is
the left endpoint of the floor cell `[1 − t/n, 1 − (t − 1)/n)`. -/
noncomputable def floorRadius (n t : ℕ) : ℝ≥0 :=
  1 - (t : ℝ≥0) / (n : ℝ≥0)

theorem floorRadius_le_one (n t : ℕ) : floorRadius n t ≤ 1 :=
  tsub_le_self

theorem floorRadius_zero (n : ℕ) : floorRadius n 0 = 1 := by
  simp [floorRadius]

theorem floorRadius_self {n : ℕ} (hn : n ≠ 0) : floorRadius n n = 0 := by
  have hn' : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn
  simp [floorRadius, div_self hn']

/-- The agreement level of the canonical radius: `(1 − floorRadius n t)·n = t` for `t ≤ n`. -/
theorem one_sub_floorRadius_mul {n t : ℕ} (hn : n ≠ 0) (ht : t ≤ n) :
    (1 - floorRadius n t) * (n : ℝ≥0) = t := by
  have hn' : (0 : ℝ≥0) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hdiv : (t : ℝ≥0) / (n : ℝ≥0) ≤ 1 := by
    rw [div_le_one₀ hn']
    exact_mod_cast ht
  rw [floorRadius, tsub_tsub_cancel_of_le hdiv, div_mul_cancel₀ _ hn'.ne']

/-- The canonical radius of floor `t ≤ n` has agreement floor exactly `t`. -/
theorem ceil_floorRadius {n t : ℕ} (hn : n ≠ 0) (ht : t ≤ n) :
    ⌈(1 - floorRadius n t) * (n : ℝ≥0)⌉₊ = t := by
  rw [one_sub_floorRadius_mul hn ht, Nat.ceil_natCast]

/-- The agreement floor never exceeds the length: `⌈(1 − δ)·n⌉₊ ≤ n`. -/
theorem ceil_one_sub_mul_le (n : ℕ) (δ : ℝ≥0) : ⌈(1 - δ) * (n : ℝ≥0)⌉₊ ≤ n := by
  refine Nat.ceil_le.mpr ?_
  calc (1 - δ) * (n : ℝ≥0) ≤ 1 * (n : ℝ≥0) :=
        mul_le_mul_of_nonneg_right tsub_le_self zero_le
    _ = (n : ℝ≥0) := one_mul _

/-- **Every MCA error is a floor value.** `ε_mca(C, δ) = V_t` with `V_t = ε_mca(C, 1 − t/n)` at
the agreement floor `t = ⌈(1 − δ)·n⌉₊ ≤ n` (`ceil_one_sub_mul_le`). Hence `ε_mca(C, ·)` takes at
most the `n + 1` values `V_0, …, V_n`. -/
theorem epsMCA_eq_floorValue (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) (A := A) C δ = epsMCA (F := F) (A := A) C
      (floorRadius (Fintype.card ι) ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) :=
  epsMCA_eq_of_ceil_eq C
    (ceil_floorRadius (Fintype.card_ne_zero (α := ι)) (ceil_one_sub_mul_le _ δ)).symm

/-- **The two-consecutive-floor pin (staircase inverse).** Write `V_t = ε_mca(C, 1 − t/n)` for
the floor value of floor `t`. If `V_{t₀} ≤ ε*` and `ε* < V_{t₀ − 1}` with `1 ≤ t₀ ≤ n`, then
`δ* = 1 − (t₀ − 1)/n` exactly.

Every radius strictly below `1 − (t₀ − 1)/n` has agreement floor `≥ t₀`, so it is good: below
`1 − t₀/n` by monotonicity, and inside the cell `[1 − t₀/n, 1 − (t₀ − 1)/n)` by the step law.
The threshold itself has floor `t₀ − 1` and is bad, so `δ*` is the excluded supremum of the
good radii (`MCAListBracketInterpolation.mcaDeltaStar_eq_of_jump`). -/
theorem mcaDeltaStar_eq_of_floor_values (C : Set (ι → A)) (εstar : ℝ≥0∞) {t₀ : ℕ}
    (ht₀ : 1 ≤ t₀) (ht₀n : t₀ ≤ Fintype.card ι)
    (hgood : epsMCA (F := F) (A := A) C (floorRadius (Fintype.card ι) t₀) ≤ εstar)
    (hbad : εstar < epsMCA (F := F) (A := A) C (floorRadius (Fintype.card ι) (t₀ - 1))) :
    mcaDeltaStar (F := F) (A := A) C εstar = floorRadius (Fintype.card ι) (t₀ - 1) := by
  have hn : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  have hn' : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by exact_mod_cast Nat.pos_of_ne_zero hn
  refine mcaDeltaStar_eq_of_jump C εstar (floorRadius_le_one _ _) ?_ hbad
  intro δ hδ
  rcases le_or_gt δ (floorRadius (Fintype.card ι) t₀) with hle | hlt
  · exact (epsMCA_mono C hle).trans hgood
  · have hceil : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊
        = ⌈(1 - floorRadius (Fintype.card ι) t₀) * (Fintype.card ι : ℝ≥0)⌉₊ := by
      rw [ceil_floorRadius hn ht₀n]
      refine (Nat.ceil_eq_iff (by omega)).mpr ⟨?_, ?_⟩
      · calc ((t₀ - 1 : ℕ) : ℝ≥0)
            = (1 - floorRadius (Fintype.card ι) (t₀ - 1)) * (Fintype.card ι : ℝ≥0) :=
              (one_sub_floorRadius_mul hn (by omega)).symm
          _ < (1 - δ) * (Fintype.card ι : ℝ≥0) :=
              mul_lt_mul_of_pos_right
                (tsub_lt_tsub_left_of_le (floorRadius_le_one _ _) hδ) hn'
      · calc (1 - δ) * (Fintype.card ι : ℝ≥0)
            ≤ (1 - floorRadius (Fintype.card ι) t₀) * (Fintype.card ι : ℝ≥0) :=
              mul_le_mul_of_nonneg_right (tsub_le_tsub_left hlt.le 1) zero_le
          _ = t₀ := one_sub_floorRadius_mul hn ht₀n
    rw [epsMCA_eq_of_ceil_eq C hceil]
    exact hgood

/-! ## The endpoint-only band form -/

/-- **The band premises force the endpoint.** Goodness at `δ₀ ≤ 1` together with badness at
every `δ ∈ (δ₀, 1]` is satisfiable only for `δ₀ = 1`: for `δ₀ < 1` the right plateau
(`exists_gt_epsMCA_eq_of_lt_one`) supplies some `δ' ∈ (δ₀, 1]` with the same MCA error as
`δ₀`. This is the checked form of the audit observation (2026-10-28, PG-027) that
`mcaDeltaStar_eq_of_band` cannot pin an interior threshold; it shows the premises are
unsatisfiable for `δ₀ < 1`, not that any axiom is inconsistent. -/
theorem eq_one_of_band_premises (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ₀ : ℝ≥0}
    (hδ₀ : δ₀ ≤ 1)
    (hgood : epsMCA (F := F) (A := A) C δ₀ ≤ εstar)
    (hbad : ∀ δ : ℝ≥0, δ₀ < δ → δ ≤ 1 → εstar < epsMCA (F := F) (A := A) C δ) :
    δ₀ = 1 := by
  by_contra hne
  obtain ⟨δ', hlt, hle, heq⟩ :=
    exists_gt_epsMCA_eq_of_lt_one (F := F) C (lt_of_le_of_ne hδ₀ hne)
  exact (hbad δ' hlt hle).not_ge (heq.trans_le hgood)

open Classical in
/-- **Endpoint-only band pin.** Goodness at `δ₀ ≤ 1` and badness at every `δ ∈ (δ₀, 1]` give
`δ* = δ₀` (attained). The statement is valid, but its premises force `δ₀ = 1`
(`eq_one_of_band_premises`), so it only records that a good radius `1` yields `δ* = 1`; it is
**not** a staircase inverse and cannot express an interior threshold. Interior thresholds are
pinned by `MCAListBracketInterpolation.mcaDeltaStar_eq_of_jump` or
`mcaDeltaStar_eq_of_floor_values` (goodness below the boundary, badness at it). -/
theorem mcaDeltaStar_eq_of_band (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ₀ : ℝ≥0}
    (hδ₀ : δ₀ ≤ 1)
    (hgood : epsMCA (F := F) (A := A) C δ₀ ≤ εstar)
    (hbad : ∀ δ : ℝ≥0, δ₀ < δ → δ ≤ 1 → εstar < epsMCA (F := F) (A := A) C δ) :
    mcaDeltaStar (F := F) (A := A) C εstar = δ₀ := by
  apply le_antisymm
  · apply csSup_le'
    intro δ hδ
    by_contra hcon
    push Not at hcon
    exact absurd hδ.2 (not_le_of_gt (hbad δ hcon hδ.1))
  · exact le_mcaDeltaStar_of_good C εstar hδ₀ hgood

/-- **The uncapped closed-good premises are never satisfiable.** No radius `δ₀` is good while
every strictly larger radius is bad: the uncapped right plateau (`exists_gt_epsMCA_eq`) gives
some `δ' > δ₀` with the same MCA error (for `δ₀ = 1`, any `δ' > 1` has the same floor `0`).
These are exactly the premises of `MCAThresholdLedger.mcaDeltaStar_eq_of_good_of_bad_above`
and its alias `mcaDeltaStar_eq_of_good_of_strictMono_bad` (`MCAExactPin.lean`), which are
therefore vacuous for the repository's `ε_mca`. -/
theorem not_good_and_bad_above (C : Set (ι → A)) (εstar : ℝ≥0∞) (δ₀ : ℝ≥0)
    (hgood : epsMCA (F := F) (A := A) C δ₀ ≤ εstar) :
    ¬ ∀ δ : ℝ≥0, δ₀ < δ → εstar < epsMCA (F := F) (A := A) C δ := by
  intro hbad
  obtain ⟨δ', hlt, heq⟩ := exists_gt_epsMCA_eq (F := F) C δ₀
  exact (hbad δ' hlt).not_ge (heq.trans_le hgood)

/-! ## Source audit -/

#print axioms card_clause_iff_floor
#print axioms mcaEvent_iff_floor
#print axioms epsMCA_eq_of_ceil_eq
#print axioms exists_gt_ceil_eq_of_lt_one
#print axioms exists_gt_epsMCA_eq_of_lt_one
#print axioms lt_epsMCA_mcaDeltaStar_of_lt_one
#print axioms epsMCA_eq_floorValue
#print axioms mcaDeltaStar_eq_of_floor_values
#print axioms eq_one_of_band_premises
#print axioms mcaDeltaStar_eq_of_band
#print axioms not_good_and_bad_above

end ProximityGap.MCAStepFunction
