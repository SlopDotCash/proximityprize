/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.RemainingCore
import ArkLib.Data.CodingTheory.ProximityGap.BoundaryThresholdFloorCell
import ArkLib.Data.CodingTheory.ProximityGap.BoundaryLatticeThresholdLeaf

/-!
# The boundary half, assembled: cell-radius reduction + the full Johnson-endpoint dichotomy

This file is the missing glue between the four corrected-boundary bricks of issue #304:

* **O70** (`StrictCoeffLargeReduction.lean`) — the §5 strict-Johnson front door
  `correlatedAgreement_affine_curves_of_largeResidual` from the *large-sector* residual
  `StrictCoeffPolysLargeResidual` (boundary residual vacuous at strict radii);
* **O76** (`BoundaryCardStrictInteriorRefutation.lean`) — both *nonemptiness* leaves of the
  boundary quantization split are refuted; the corrected same-`ε` floor transport
  `correlatedAgreementCurves_boundary_of_floorEq_strict` is the honest replacement;
* **O79** (`BoundaryThresholdFloorCell.lean`) — monotone-`ε` floor-cell transport
  `correlatedAgreementCurves_boundary_of_floorCell_mono`: the §5 machinery is needed at only
  one radius per floor cell;
* **O86** (`BoundaryLatticeThresholdLeaf.lean`) — the genuinely-square lattice branch, reduced
  to the single extraction residual `LatticeCoeffPolyExtraction` with the field-quantitative
  threshold `latticeThresholdEps = (n+1)/|F|`.

## What is added here

1. **The canonical cell radius** `boundaryCellRadius n δ := ⌊δ·n⌋ / n` — the left endpoint of
   `δ`'s `1/n` floor cell — with its lattice/floor calculus: it is floor-matched with `δ`
   (`floor_boundaryCellRadius_mul`), lies at or below `δ` (`boundaryCellRadius_le`), strictly
   below exactly off the lattice (`boundaryCellRadius_lt_of_not_lattice` /
   `boundaryCellRadius_eq_of_lattice`), below every floor-matched radius
   (`boundaryCellRadius_le_of_floor_eq`), and is *itself an exact lattice point*
   (`boundaryCellRadius_isLattice`).
2. **The strict-radius reduction** `correlatedAgreementCurves_iff_boundaryCellRadius`: for every
   radius `δ` and every `ε`, the curve correlated-agreement statement at `δ` is *equivalent* to
   the one at the exact lattice point `⌊δ·n⌋/n`.  This quantifies precisely that the boundary
   half of the keystone is needed **only at exact lattice points** `δ = j/n`: every other radius
   transports there and back with the same `ε`.
3. **The cell-minimum composite** `correlatedAgreementCurves_boundary_of_largeResidual_cellMin`:
   O70 ∘ O79 ∘ O76 pinned at the canonical cell radius — a single `StrictCoeffPolysLargeResidual`
   supply at `⌊δ·n⌋/n` yields the closed statement at `δ` with `ε = errorBound δ'` for *every*
   floor-matched `δ' < 1 − √ρ`.  This discharges in Lean the floor-matching side conditions that
   `correlatedAgreement_of_remainingCore` leaves to the caller (previously only probe-checked).
4. **The Johnson-endpoint dichotomy capstone**
   `correlatedAgreementCurves_johnsonClosed_of_leaves`: at the exact closed boundary
   `δ = 1 − √ρ` (with `√ρ ≤ 1`, `deg ≤ n`), the keystone statement holds with the explicit
   positive error `ε = max (errorBound (⌊δ·n⌋/n)) ((n+1)/|F|)` from exactly the two genuine
   open leaves, split by the perfect-square arithmetic of `deg · n`:
   * `¬ IsSquare (deg·n)` (non-lattice bulk) — `StrictCoeffPolysLargeResidual` at the cell
     radius (BCIKS20 §5 Steps 5–7 content at a strict radius);
   * `IsSquare (deg·n)` (lattice endpoint) — `LatticeCoeffPolyExtraction` at `δ` (BCIKS20 §5
     extraction at the endpoint).
   The error is strictly positive (`johnsonClosed_eps_pos`) — never the refuted nonemptiness
   shapes, never the vacuous `errorBound (1 − √ρ) = 0`.  Adapters consume
   `BCIKS20RemainingCore` directly, and an `∃ ε > 0` form is provided.
5. **End-to-end witness** (`JohnsonClosedWitness`): the capstone fires at the O76 witness point
   (`ZMod 5`, `n = 4`, `deg = 2`, `k = 1`, non-square endpoint `deg·n = 8`), reusing the
   in-tree satisfiability witness `remainingCore_boundary_witness` — no hypothesis of this
   file is unsatisfiable.

The hypotheses `hLarge`/`hExt` of the capstone are *named open inputs* (the genuine BCIKS20 §5
content), never goals.  `#print axioms` of every declaration here rests only on
`[propext, Classical.choice, Quot.sound]`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (list-decoding agreement chain), §6.2 (closed Johnson boundary at `1 − √ρ`).
-/

open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace BoundaryHalfState

/-! ## The canonical cell radius `⌊δ·n⌋ / n` and its lattice/floor calculus -/

/-- **The canonical cell radius**: the left endpoint `⌊δ · n⌋ / n` of the `1/n` floor cell
containing `δ`.  This is the unique exact lattice point of the cell, and the deepest radius
sharing `δ`'s integer distance level. -/
noncomputable def boundaryCellRadius (n : ℕ) (δ : ℝ≥0) : ℝ≥0 :=
  (Nat.floor (δ * n) : ℝ≥0) / n

/-- Clearing the denominator: `boundaryCellRadius n δ · n = ⌊δ · n⌋`. -/
theorem boundaryCellRadius_mul_self {n : ℕ} (hn : 0 < n) (δ : ℝ≥0) :
    boundaryCellRadius n δ * n = (Nat.floor (δ * n) : ℝ≥0) := by
  have hnne : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  rw [boundaryCellRadius, div_mul_cancel₀ _ hnne]

/-- **The cell radius is floor-matched with `δ`**: `⌊boundaryCellRadius n δ · n⌋ = ⌊δ · n⌋`.
This is the hypothesis shape consumed by the O76/O79 step-function transports. -/
theorem floor_boundaryCellRadius_mul {n : ℕ} (hn : 0 < n) (δ : ℝ≥0) :
    Nat.floor (boundaryCellRadius n δ * n) = Nat.floor (δ * n) := by
  rw [boundaryCellRadius_mul_self hn, Nat.floor_natCast]

/-- **The cell radius is itself an exact lattice point**: `⌊r · n⌋ = r · n` for
`r = boundaryCellRadius n δ`.  Combined with the transport equivalence below, this shows the
boundary half of the keystone is needed *only* at exact lattice points `δ = j/n`. -/
theorem boundaryCellRadius_isLattice {n : ℕ} (hn : 0 < n) (δ : ℝ≥0) :
    (Nat.floor (boundaryCellRadius n δ * n) : ℝ≥0) = boundaryCellRadius n δ * n := by
  rw [floor_boundaryCellRadius_mul hn, boundaryCellRadius_mul_self hn]

/-- The cell radius never exceeds `δ`. -/
theorem boundaryCellRadius_le {n : ℕ} (hn : 0 < n) (δ : ℝ≥0) :
    boundaryCellRadius n δ ≤ δ := by
  have hnpos : (0 : ℝ≥0) < n := by exact_mod_cast hn
  rw [boundaryCellRadius, div_le_iff₀ hnpos]
  exact Nat.floor_le (zero_le _)

/-- Off the `1/n` lattice (`⌊δ·n⌋ < δ·n`), the cell radius is *strictly* below `δ`: the
canonical strict floor-matched sub-radius of the quantization split. -/
theorem boundaryCellRadius_lt_of_not_lattice {n : ℕ} {δ : ℝ≥0} (hn : 0 < n)
    (hfrac : (Nat.floor (δ * n) : ℝ≥0) < δ * n) :
    boundaryCellRadius n δ < δ := by
  have hnpos : (0 : ℝ≥0) < n := by exact_mod_cast hn
  rw [boundaryCellRadius, div_lt_iff₀ hnpos]
  exact hfrac

/-- At a `1/n` lattice point (`⌊δ·n⌋ = δ·n`), the cell radius *is* `δ`: the two branches of the
boundary dichotomy are exactly `boundaryCellRadius n δ < δ` and `boundaryCellRadius n δ = δ`. -/
theorem boundaryCellRadius_eq_of_lattice {n : ℕ} {δ : ℝ≥0} (hn : 0 < n)
    (hlat : (Nat.floor (δ * n) : ℝ≥0) = δ * n) :
    boundaryCellRadius n δ = δ := by
  have hnne : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  rw [boundaryCellRadius, hlat, mul_div_cancel_right₀ _ hnne]

/-- The cell radius of `δ` lies at or below every radius floor-matched with `δ`: it is the
*minimum* of the floor cell. -/
theorem boundaryCellRadius_le_of_floor_eq {n : ℕ} {δ δ' : ℝ≥0} (hn : 0 < n)
    (hfloor : Nat.floor (δ' * n) = Nat.floor (δ * n)) :
    boundaryCellRadius n δ ≤ δ' := by
  have hnpos : (0 : ℝ≥0) < n := by exact_mod_cast hn
  rw [boundaryCellRadius, div_le_iff₀ hnpos, ← hfloor]
  exact Nat.floor_le (zero_le _)

/-! ## The strict-radius reduction: the boundary half lives only at lattice points `j/n` -/

/-- **The strict-radius reduction.**  For every radius `δ` and error `ε`, the curve
correlated-agreement statement at `δ` is *equivalent* to the statement at the exact lattice
point `boundaryCellRadius n δ = ⌊δ·n⌋/n` with the same `ε` (O76 floor transport, both ways).
Since the cell radius is an exact lattice point (`boundaryCellRadius_isLattice`), this
quantifies precisely: the boundary half of the [BCIKS20] keystone is needed **only at exact
lattice points** `δ = j/n` — all other radii, including every non-lattice Johnson endpoint
`1 − √ρ` with `deg·n` non-square, transport there and back. -/
theorem correlatedAgreementCurves_iff_boundaryCellRadius
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k deg : ℕ} {domain : ι ↪ F} {δ ε : ℝ≥0} :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := (ReedSolomon.code domain deg : Set (ι → F)))
      (δ := boundaryCellRadius (Fintype.card ι) δ) (ε := ε)
      ↔ δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
        (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ) (ε := ε) := by
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  constructor
  · exact
      ArkLib.BoundaryQuantizationCorrected.correlatedAgreementCurves_boundary_of_floorEq_strict
        (floor_boundaryCellRadius_mul hn δ)
  · exact
      ArkLib.BoundaryQuantizationCorrected.correlatedAgreementCurves_boundary_of_floorEq_strict
        ((floor_boundaryCellRadius_mul hn δ).symm)

/-! ## The cell-minimum composite: O70 ∘ O79 ∘ O76 pinned at `⌊δ·n⌋/n` -/

/-- **The cell-minimum composite.**  A single `StrictCoeffPolysLargeResidual` supply at the
canonical cell radius `⌊δ·n⌋/n` yields the closed correlated-agreement statement at `δ` with
`ε = errorBound δ'` for *every* floor-matched `δ' < 1 − √ρ`:

* the O70 front door turns the large-sector residual at the cell radius into the full §5
  statement there (the §6.2 boundary residual is vacuous at strict radii, since
  `⌊δ·n⌋/n ≤ δ' < 1 − √ρ`);
* the O79 monotone-`ε` floor-cell transport raises it to `δ'` with `errorBound δ'`;
* the O76 same-`ε` floor transport carries it to the target `δ`.

Compared with `ProximityGap.correlatedAgreement_of_remainingCore`, the floor-matching of the
working radius is *proved* here (`boundaryCellRadius_le_of_floor_eq`,
`floor_boundaryCellRadius_mul`) rather than left as caller-supplied side conditions. -/
theorem correlatedAgreementCurves_boundary_of_largeResidual_cellMin
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k deg : ℕ} [NeZero deg] {domain : ι ↪ F} {δ δ' : ℝ≥0}
    (hdeg : 0 < deg)
    (hδ' : δ' < 1 - ReedSolomon.sqrtRate deg domain)
    (hfloor' : Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι))
    (hLarge : ProximityGap.StrictCoeffPolysLargeResidual (k := k) (deg := deg)
      (domain := domain) (δ := boundaryCellRadius (Fintype.card ι) δ)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)
      (ε := errorBound δ' deg domain) := by
  classical
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  have hcell_le : boundaryCellRadius (Fintype.card ι) δ ≤ δ' :=
    boundaryCellRadius_le_of_floor_eq hn hfloor'
  have hcell_lt :
      boundaryCellRadius (Fintype.card ι) δ < 1 - ReedSolomon.sqrtRate deg domain :=
    lt_of_le_of_lt hcell_le hδ'
  have hfloor'' :
      Nat.floor (boundaryCellRadius (Fintype.card ι) δ * Fintype.card ι)
        = Nat.floor (δ' * Fintype.card ι) :=
    (floor_boundaryCellRadius_mul hn δ).trans hfloor'.symm
  have hcellCA := ProximityGap.correlatedAgreement_affine_curves_of_largeResidual
    (k := k) (deg := deg) (domain := domain)
    (δ := boundaryCellRadius (Fintype.card ι) δ)
    hLarge (fun _hk _u _hprob _hJ hnot => absurd hcell_lt hnot) hcell_lt.le
  exact ArkLib.BoundaryThresholdFloorCell.correlatedAgreementCurves_boundary_of_floorCell_mono
    (deg := deg) (domain := domain) hdeg hcell_le hδ' hfloor'' hfloor' hcellCA

/-! ## The Johnson-endpoint dichotomy capstone -/

/-- **The closed Johnson endpoint, assembled from the two genuine leaves.**  At the exact
boundary `δ = 1 − √ρ` (with `√ρ ≤ 1` and `deg ≤ n`), the [BCIKS20] Theorem 1.5 keystone
statement holds with the explicit error `ε = max (errorBound (⌊δ·n⌋/n)) ((n+1)/|F|)` from:

* `hLarge` — at *non-square* `deg·n` (the non-lattice bulk): the §5 large-sector extraction
  residual `StrictCoeffPolysLargeResidual` at the canonical cell radius `⌊δ·n⌋/n`, which is
  then *strictly* interior (`boundaryCellRadius_lt_of_not_lattice` via
  `boundary_not_lattice_of_not_isSquare_deg_mul_card`), where `errorBound > 0` and the §5
  machinery is genuinely applicable;
* `hExt` — at *square* `deg·n` (the exact lattice endpoint): the O86 extraction residual
  `LatticeCoeffPolyExtraction` at `δ`, carried by the field-quantitative threshold
  `(n+1)/|F|`.

Both inputs are honest named open obligations (BCIKS20 §5 Steps 5–7 content); the refuted
nonemptiness surfaces (`BoundaryCardResidual`, `BoundaryCardLatticeResidual`,
`BoundaryCardStrictInteriorFalseAsStated`) appear nowhere, and the export error is strictly
positive (`johnsonClosed_eps_pos`) — never the vacuous `errorBound (1 − √ρ) = 0`. -/
theorem correlatedAgreementCurves_johnsonClosed_of_leaves
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k deg : ℕ} [NeZero deg] {domain : ι ↪ F} {δ : ℝ≥0}
    (hk : 0 < k)
    (hδeq : δ = 1 - ReedSolomon.sqrtRate deg domain)
    (hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1)
    (hdeg_le : deg ≤ Fintype.card ι)
    (hLarge : ¬ IsSquare (deg * Fintype.card ι) →
      ProximityGap.StrictCoeffPolysLargeResidual (k := k) (deg := deg) (domain := domain)
        (δ := boundaryCellRadius (Fintype.card ι) δ))
    (hExt : IsSquare (deg * Fintype.card ι) →
      ArkLib.BoundaryLatticeThresholdLeaf.LatticeCoeffPolyExtraction
        (k := k) (deg := deg) domain δ) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)
      (ε := max (errorBound (boundaryCellRadius (Fintype.card ι) δ) deg domain)
        (ArkLib.BoundaryLatticeThresholdLeaf.latticeThresholdEps ι F)) := by
  classical
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  by_cases hSq : IsSquare (deg * Fintype.card ι)
  · exact ProximityGap.correlatedAgreementCurves_mono_eps (le_max_right _ _)
      (ArkLib.BoundaryLatticeThresholdLeaf.correlatedAgreementCurves_of_latticeExtraction
        hk (hExt hSq))
  · have hNotLat : (Nat.floor (δ * Fintype.card ι) : ℝ≥0) < δ * Fintype.card ι :=
      ArkLib.BoundaryCardResidual.boundary_not_lattice_of_not_isSquare_deg_mul_card
        (domain := domain) hδeq hsqrt_le hdeg_le hSq
    have hcell_lt_δ : boundaryCellRadius (Fintype.card ι) δ < δ :=
      boundaryCellRadius_lt_of_not_lattice hn hNotLat
    have hcell_lt :
        boundaryCellRadius (Fintype.card ι) δ < 1 - ReedSolomon.sqrtRate deg domain := by
      rw [← hδeq]
      exact hcell_lt_δ
    have hdeg0 : 0 < deg := Nat.pos_of_ne_zero (NeZero.ne deg)
    exact ProximityGap.correlatedAgreementCurves_mono_eps (le_max_left _ _)
      (correlatedAgreementCurves_boundary_of_largeResidual_cellMin
        (deg := deg) (domain := domain) hdeg0 hcell_lt
        (floor_boundaryCellRadius_mul hn δ) (hLarge hSq))

/-- The capstone's export error is strictly positive: the lattice threshold `(n+1)/|F|`
dominates it from below.  This certifies the closed-boundary export is never the refuted
vacuous `ε = 0` shape. -/
theorem johnsonClosed_eps_pos {ι : Type} [Fintype ι] {F : Type} [Field F] [Fintype F]
    (e : ℝ≥0) :
    0 < max e (ArkLib.BoundaryLatticeThresholdLeaf.latticeThresholdEps ι F) :=
  lt_of_lt_of_le ArkLib.BoundaryLatticeThresholdLeaf.latticeThresholdEps_pos
    (le_max_right _ _)

/-- The `∃ ε > 0` form of the dichotomy capstone: at the exact closed Johnson endpoint, the
two genuine leaves produce the keystone statement at *some* strictly positive error. -/
theorem exists_pos_eps_correlatedAgreementCurves_johnsonClosed
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k deg : ℕ} [NeZero deg] {domain : ι ↪ F} {δ : ℝ≥0}
    (hk : 0 < k)
    (hδeq : δ = 1 - ReedSolomon.sqrtRate deg domain)
    (hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1)
    (hdeg_le : deg ≤ Fintype.card ι)
    (hLarge : ¬ IsSquare (deg * Fintype.card ι) →
      ProximityGap.StrictCoeffPolysLargeResidual (k := k) (deg := deg) (domain := domain)
        (δ := boundaryCellRadius (Fintype.card ι) δ))
    (hExt : IsSquare (deg * Fintype.card ι) →
      ArkLib.BoundaryLatticeThresholdLeaf.LatticeCoeffPolyExtraction
        (k := k) (deg := deg) domain δ) :
    ∃ ε : ℝ≥0, 0 < ε ∧
      δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
        (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ) (ε := ε) :=
  ⟨_, johnsonClosed_eps_pos _,
    correlatedAgreementCurves_johnsonClosed_of_leaves hk hδeq hsqrt_le hdeg_le hLarge hExt⟩

/-- Adapter: the dichotomy capstone consuming the packaged `BCIKS20RemainingCore` (with the
working radius pinned at the canonical cell radius) on the non-square branch.  Only the second
conjunct is used — the first conjunct (the large residual at the boundary radius itself) is
not needed for the closed-boundary export. -/
theorem correlatedAgreementCurves_johnsonClosed_of_remainingCore
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k deg : ℕ} [NeZero deg] {domain : ι ↪ F} {δ : ℝ≥0}
    (hk : 0 < k)
    (hδeq : δ = 1 - ReedSolomon.sqrtRate deg domain)
    (hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1)
    (hdeg_le : deg ≤ Fintype.card ι)
    (hCore : ¬ IsSquare (deg * Fintype.card ι) →
      ProximityGap.BCIKS20RemainingCore k deg domain δ
        (boundaryCellRadius (Fintype.card ι) δ))
    (hExt : IsSquare (deg * Fintype.card ι) →
      ArkLib.BoundaryLatticeThresholdLeaf.LatticeCoeffPolyExtraction
        (k := k) (deg := deg) domain δ) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)
      (ε := max (errorBound (boundaryCellRadius (Fintype.card ι) δ) deg domain)
        (ArkLib.BoundaryLatticeThresholdLeaf.latticeThresholdEps ι F)) :=
  correlatedAgreementCurves_johnsonClosed_of_leaves hk hδeq hsqrt_le hdeg_le
    (fun h => (hCore h).2) hExt

end BoundaryHalfState

/-! ## End-to-end witness: the capstone fires at the O76 witness point

The hypothesis spine of the dichotomy capstone is simultaneously satisfiable: at the O76
refutation witness (`ι = Fin 4`, `F = ZMod 5`, `deg = 2`, `k = 1`, the non-square endpoint
`deg·n = 8`), the non-square leaf is the in-tree satisfiability witness
`remainingCore_boundary_witness.2` (its cell radius is exactly `1/4`), and the square leaf is
vacuous (`¬ IsSquare 8`).  The honest caveat of `RemainingCore.lean` applies verbatim: at toy
field size the §5 conjunct holds vacuously, so the witness certifies *consistency*, not
large-`q` content. -/

namespace JohnsonClosedWitness

open ArkLib.BoundaryHalfState ArkLib.BoundaryCardResidualRefutation
  ArkLib.BoundaryCardStrictInteriorRefutation ArkLib.RemainingCoreWitness
open ProximityGap NNReal

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- At the O76 witness point, the canonical cell radius of the Johnson endpoint is exactly the
unique-decoding edge `1/4`: `⌊(1 − √(1/2)) · 4⌋ / 4 = 1/4`. -/
theorem boundaryCellRadius_witness_eq_quarter :
    boundaryCellRadius (Fintype.card I) (1 - ReedSolomon.sqrtRate 2 domain)
      = (1 / 4 : ℝ≥0) := by
  rw [boundaryCellRadius, boundary_floor_eq_one]
  have hcard : ((Fintype.card I : ℕ) : ℝ≥0) = 4 := by norm_num [I]
  rw [hcard]
  norm_num

/-- **The dichotomy capstone, instantiated end-to-end.**  An in-tree, hypothesis-free
closed-boundary correlated-agreement statement at the non-square Johnson endpoint of the O76
witness, with the explicit positive error `max (errorBound (1/4)) (5/5) = max (4/5) 1`. -/
theorem johnsonClosed_witness :
    δ_ε_correlatedAgreementCurves (k := 1) (A := F) (F := F) (ι := I)
      (C := (ReedSolomon.code domain 2 : Set (I → F)))
      (δ := 1 - ReedSolomon.sqrtRate 2 domain)
      (ε := max (errorBound (boundaryCellRadius (Fintype.card I)
          (1 - ReedSolomon.sqrtRate 2 domain)) 2 domain)
        (ArkLib.BoundaryLatticeThresholdLeaf.latticeThresholdEps I F)) :=
  correlatedAgreementCurves_johnsonClosed_of_leaves Nat.one_pos rfl sqrtRate_le_one
    (by norm_num [I])
    (fun _ => by
      rw [boundaryCellRadius_witness_eq_quarter]
      exact remainingCore_boundary_witness.2)
    (fun h => absurd h not_isSquare_deg_mul_card)

end JohnsonClosedWitness

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.BoundaryHalfState.boundaryCellRadius
#print axioms ArkLib.BoundaryHalfState.boundaryCellRadius_mul_self
#print axioms ArkLib.BoundaryHalfState.floor_boundaryCellRadius_mul
#print axioms ArkLib.BoundaryHalfState.boundaryCellRadius_isLattice
#print axioms ArkLib.BoundaryHalfState.boundaryCellRadius_le
#print axioms ArkLib.BoundaryHalfState.boundaryCellRadius_lt_of_not_lattice
#print axioms ArkLib.BoundaryHalfState.boundaryCellRadius_eq_of_lattice
#print axioms ArkLib.BoundaryHalfState.boundaryCellRadius_le_of_floor_eq
#print axioms ArkLib.BoundaryHalfState.correlatedAgreementCurves_iff_boundaryCellRadius
#print axioms
  ArkLib.BoundaryHalfState.correlatedAgreementCurves_boundary_of_largeResidual_cellMin
#print axioms ArkLib.BoundaryHalfState.correlatedAgreementCurves_johnsonClosed_of_leaves
#print axioms ArkLib.BoundaryHalfState.johnsonClosed_eps_pos
#print axioms
  ArkLib.BoundaryHalfState.exists_pos_eps_correlatedAgreementCurves_johnsonClosed
#print axioms ArkLib.BoundaryHalfState.correlatedAgreementCurves_johnsonClosed_of_remainingCore
#print axioms ArkLib.JohnsonClosedWitness.boundaryCellRadius_witness_eq_quarter
#print axioms ArkLib.JohnsonClosedWitness.johnsonClosed_witness
