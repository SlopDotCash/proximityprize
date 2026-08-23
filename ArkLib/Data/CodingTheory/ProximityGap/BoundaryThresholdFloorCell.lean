/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BoundaryCardStrictInteriorRefutation

/-!
# Floor-cell threshold transport: the monotone-ε strengthening of the corrected boundary route

`BoundaryCardStrictInteriorRefutation` (O76) refuted both *nonemptiness* leaves of the boundary
quantization split and identified the corrected obligation: the closed-boundary export must carry
the §5 *probability threshold* `Pr[good at δ'] > k · errorBound δ'` at a floor-matched strict
radius `δ' < δ = 1 − √ρ`.  Its proven piece, `correlatedAgreementCurves_boundary_of_floorEq_strict`,
transports the full `δ_ε_correlatedAgreementCurves` statement across equal floors with the **same**
error parameter `ε`.

This file supplies the *probability-threshold monotonicity* piece the full corrected route needs:

* `prob_threshold_floorCell_mono` — **threshold transport within a floor cell**: if the §5
  threshold holds at a floor-matched radius `δ'`, it holds at every smaller radius `δ'' ≤ δ'` with
  the same floor.  The probability side is *constant* on the cell (the good-coefficient set is a
  step function of `⌊δ·n⌋`, in-tree `goodCoeffsCurve_eq_of_floor_eq`), while the error side is
  *monotone nondecreasing* below the Johnson boundary (in-tree `DivergenceOfSets.errorBound_mono`;
  the hypothesis `0 < deg` is load-bearing — at `deg = 0` the Johnson value degenerates to `0`
  and monotonicity fails, probe-checked).
* `correlatedAgreementCurves_floorCell_mono` — the consumer-shaped corollary: within a floor cell,
  the `δ_ε_correlatedAgreementCurves` statement at the *smaller* radius with **its own**
  `errorBound` implies the statement at any floor-matched larger radius with **its** `errorBound`.
  This strengthens the O76 transport from same-`ε` to monotone-`ε`: the corrected boundary route
  needs the §5 machinery only at a single (e.g. the deepest available) floor-matched radius.
* `correlatedAgreementCurves_boundary_of_floorCell_mono` — the composite boundary export: a
  strict-interior `δ_ε_correlatedAgreementCurves` at `δ''` (with `errorBound δ''`) plus a
  floor-matched chain `δ'' ≤ δ' < δ` yields the closed-boundary statement at `δ` with
  `ε = errorBound δ'` — for *every* floor-matched `δ'`, not only the one where the machinery runs.

The witness namespace instantiates the whole hypothesis spine at the O76 refutation witness
(`ZMod 5`, `n = 4`, `deg = 2`, the genuinely non-lattice endpoint `deg·n = 8` non-square) with the
**cross-branch** pair `δ'' = 1/4` (unique-decoding branch of `errorBound`) and `δ' = 7/25`
(Johnson branch), certifying the hypotheses are simultaneously satisfiable — no leaf of this file
is guarded by an unsatisfiable assumption.

Falsify-first probe: `scripts/probes/probe_boundary_threshold_floorcell.py` — the corrected
threshold statement survives 4 parameter points (exhaustive 390,625-stack census at
`q=5, n=4, deg=2, k=1`; sampled `q=13`/`q=257`, `k=2`), the floor-cell monotonicity is clean on
4 grids including the UDR→Johnson seam, and the `deg = 0` negative control confirms `0 < deg`
is load-bearing.  Measured saturation: the no-`jointAgreement` maximum good count equals `k·n`
exactly at three of the four points — the transported threshold is tight at the cell minimum.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (quantitative threshold), §6.2 (closed Johnson boundary).
-/

namespace ArkLib

namespace BoundaryThresholdFloorCell

open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Threshold transport within a floor cell (downward).**  If the §5 probability threshold
`Pr[curve δ'-close] > k · errorBound δ'` holds at a radius `δ'` strictly below the Johnson
boundary, it holds at every smaller radius `δ'' ≤ δ'` with the same distance floor: the
probability is constant on the cell (the good set is a step function of `⌊δ·n⌋`), and
`errorBound` is monotone nondecreasing below the boundary, so the threshold only tightens
upward along the cell.  `0 < deg` is load-bearing for the monotonicity (probe-checked). -/
theorem prob_threshold_floorCell_mono {k deg : ℕ} {domain : ι ↪ F} {δ'' δ' : ℝ≥0}
    (hdeg : 0 < deg) (hle : δ'' ≤ δ')
    (hδ' : δ' < 1 - ReedSolomon.sqrtRate deg domain)
    (hfloor : Nat.floor (δ'' * Fintype.card ι) = Nat.floor (δ' * Fintype.card ι))
    (u : WordStack F (Fin (k + 1)) ι)
    (hprob : Pr_{let r ← $ᵖ F}[ δᵣ(∑ i : Fin (k + 1), (r ^ (i : ℕ)) • u i,
        (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ' ]
      > k * errorBound δ' deg domain) :
    Pr_{let r ← $ᵖ F}[ δᵣ(∑ i : Fin (k + 1), (r ^ (i : ℕ)) • u i,
        (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ'' ]
      > k * errorBound δ'' deg domain := by
  classical
  have hPrδ' := prob_close_curve_eq_card_goodCoeffsCurve_div_card
    (k := k) (deg := deg) (domain := domain) (δ := δ') u
  have hPrδ'' := prob_close_curve_eq_card_goodCoeffsCurve_div_card
    (k := k) (deg := deg) (domain := domain) (δ := δ'') u
  have hgood :
      RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ''
        = RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ' :=
    ArkLib.BoundaryCardResidual.goodCoeffsCurve_eq_of_floor_eq (deg := deg)
      (domain := domain) u hfloor
  have hmono : errorBound δ'' deg domain ≤ errorBound δ' deg domain :=
    DivergenceOfSets.errorBound_mono hdeg hle hδ'
  rw [hPrδ'', hgood, ← hPrδ']
  refine lt_of_le_of_lt ?_ hprob
  exact mul_le_mul_right (by exact_mod_cast hmono) _

/-- **Monotone-ε transport of the curve correlated-agreement statement within a floor cell.**
If `δ_ε_correlatedAgreementCurves` holds at the smaller radius `δ''` with its own
`errorBound δ''`, it holds at every floor-matched `δ' ≥ δ''` strictly below the Johnson boundary
with **its** `errorBound δ'`.  This strengthens the O76 same-`ε` transport
(`correlatedAgreementCurves_boundary_of_floorEq_strict`): the corrected boundary route needs the
§5 machinery at only one radius per cell. -/
theorem correlatedAgreementCurves_floorCell_mono {k deg : ℕ} {domain : ι ↪ F} {δ'' δ' : ℝ≥0}
    (hdeg : 0 < deg) (hle : δ'' ≤ δ')
    (hδ' : δ' < 1 - ReedSolomon.sqrtRate deg domain)
    (hfloor : Nat.floor (δ'' * Fintype.card ι) = Nat.floor (δ' * Fintype.card ι))
    (hCA : δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ'')
      (ε := errorBound δ'' deg domain)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ')
      (ε := errorBound δ' deg domain) := by
  classical
  intro u hprob
  refine (ArkLib.BoundaryCardResidual.jointAgreement_iff_of_floor_eq
    (deg := deg) (domain := domain) u hfloor).mp (hCA u ?_)
  exact prob_threshold_floorCell_mono (deg := deg) (domain := domain)
    hdeg hle hδ' hfloor u hprob

/-- **The composite corrected boundary export.**  A strict-interior
`δ_ε_correlatedAgreementCurves` at a single floor-matched radius `δ''` (with `errorBound δ''`)
yields the closed-boundary statement at `δ` with `ε = errorBound δ'` for *every* floor-matched
intermediate `δ'` — composing the monotone-ε cell transport with the O76 floor transport.
Taking `δ = 1 − √ρ` non-lattice, this is the honest boundary export shape: never the refuted
nonemptiness leaves, never the vacuous `errorBound (1 − √ρ) = 0`. -/
theorem correlatedAgreementCurves_boundary_of_floorCell_mono {k deg : ℕ} {domain : ι ↪ F}
    {δ δ' δ'' : ℝ≥0}
    (hdeg : 0 < deg) (hle : δ'' ≤ δ')
    (hδ' : δ' < 1 - ReedSolomon.sqrtRate deg domain)
    (hfloor'' : Nat.floor (δ'' * Fintype.card ι) = Nat.floor (δ' * Fintype.card ι))
    (hfloor' : Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι))
    (hCA : δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ'')
      (ε := errorBound δ'' deg domain)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)
      (ε := errorBound δ' deg domain) :=
  ArkLib.BoundaryQuantizationCorrected.correlatedAgreementCurves_boundary_of_floorEq_strict
    hfloor'
    (correlatedAgreementCurves_floorCell_mono (deg := deg) (domain := domain)
      hdeg hle hδ' hfloor'' hCA)

end BoundaryThresholdFloorCell

namespace BoundaryThresholdFloorCellWitness

open ArkLib.BoundaryCardResidualRefutation ArkLib.BoundaryCardStrictInteriorRefutation
  ArkLib.BoundaryThresholdFloorCell
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- `√8 < 72/25` (i.e. `8 < (72/25)² = 5184/625`): the arithmetic placing `7/25` strictly
below the non-lattice boundary `1 − √(1/2)` of the O76 witness. -/
theorem sqrt_eight_lt_seventyTwoDivTwentyFive : NNReal.sqrt 8 < 72 / 25 := by
  rw [← not_le, NNReal.le_sqrt_iff_sq_le]
  rw [div_pow, not_le, lt_div_iff₀ (by norm_num : (0 : ℝ≥0) < 25 ^ 2)]
  norm_num

theorem sqrtRate_lt_eighteenDivTwentyFive :
    ReedSolomon.sqrtRate 2 domain < 18 / 25 := by
  refine lt_of_mul_lt_mul_right ?_ (zero_le (4 : ℝ≥0))
  have hcard : ((Fintype.card I : ℕ) : ℝ≥0) = 4 := by norm_num [I]
  have h4 : ReedSolomon.sqrtRate 2 domain * (4 : ℝ≥0) = NNReal.sqrt 8 := by
    rw [← hcard]
    exact sqrtRate_mul_card_eq_sqrt_eight
  rw [h4, show (18 / 25 : ℝ≥0) * 4 = 72 / 25 by norm_num]
  exact sqrt_eight_lt_seventyTwoDivTwentyFive

/-- `δ' = 7/25` lies strictly below the (non-lattice) boundary `δ = 1 − √(1/2) ≈ 0.293`,
and strictly above the unique-decoding edge `1/4`: a genuinely Johnson-branch radius. -/
theorem sevenDivTwentyFive_lt_boundary :
    (7 / 25 : ℝ≥0) < 1 - ReedSolomon.sqrtRate 2 domain := by
  rw [lt_tsub_iff_right]
  calc (7 / 25 : ℝ≥0) + ReedSolomon.sqrtRate 2 domain
      < 7 / 25 + 18 / 25 :=
        add_lt_add_of_le_of_lt le_rfl sqrtRate_lt_eighteenDivTwentyFive
    _ = 1 := by norm_num

/-- `⌊(7/25)·4⌋ = ⌊28/25⌋ = 1`: same floor cell as `δ'' = 1/4` and as the boundary. -/
theorem floor_sevenDivTwentyFive_eq_one :
    Nat.floor ((7 / 25 : ℝ≥0) * Fintype.card I) = 1 := by
  have h : (7 / 25 : ℝ≥0) * (Fintype.card I : ℝ≥0) = 28 / 25 := by
    norm_num [I]
  rw [h, Nat.floor_eq_iff (zero_le _)]
  constructor
  · rw [Nat.cast_one, le_div_iff₀ (by norm_num : (0 : ℝ≥0) < 25)]
    norm_num
  · rw [div_lt_iff₀ (by norm_num : (0 : ℝ≥0) < 25)]
    norm_num

/-- **Cross-branch satisfiability of the monotonicity hypothesis spine** at the O76 witness:
`errorBound` at the unique-decoding edge `1/4` is dominated by `errorBound` at the
Johnson-branch radius `7/25` in the same floor cell.  This instantiates
`DivergenceOfSets.errorBound_mono` across the UDR→Johnson seam at a concrete non-lattice
endpoint. -/
theorem errorBound_quarter_le_sevenDivTwentyFive :
    errorBound (1 / 4 : ℝ≥0) 2 domain ≤ errorBound (7 / 25 : ℝ≥0) 2 domain :=
  DivergenceOfSets.errorBound_mono (by norm_num)
    (by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ≥0) < 4)
        (by norm_num : (0 : ℝ≥0) < 25)]
      norm_num)
    sevenDivTwentyFive_lt_boundary

/-- **The full composite at the O76 witness**: the boundary export with `ε = errorBound (7/25)`
follows from the strict-interior statement at the single cell radius `δ'' = 1/4` — the entire
hypothesis spine of `correlatedAgreementCurves_boundary_of_floorCell_mono` is simultaneously
satisfiable at a genuinely non-lattice endpoint (`deg·n = 8` non-square), with the cell chain
`1/4 ≤ 7/25 < 1 − √(1/2)` crossing the UDR→Johnson branch seam. -/
theorem boundary_export_witness
    (hCA : δ_ε_correlatedAgreementCurves (k := 1) (A := F) (F := F) (ι := I)
      (C := (ReedSolomon.code domain 2 : Set (I → F))) (δ := (1 / 4 : ℝ≥0))
      (ε := errorBound (1 / 4 : ℝ≥0) 2 domain)) :
    δ_ε_correlatedAgreementCurves (k := 1) (A := F) (F := F) (ι := I)
      (C := (ReedSolomon.code domain 2 : Set (I → F)))
      (δ := 1 - ReedSolomon.sqrtRate 2 domain)
      (ε := errorBound (7 / 25 : ℝ≥0) 2 domain) :=
  correlatedAgreementCurves_boundary_of_floorCell_mono (by norm_num)
    (by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ≥0) < 4)
        (by norm_num : (0 : ℝ≥0) < 25)]
      norm_num)
    sevenDivTwentyFive_lt_boundary
    (by rw [quarter_floor_eq_one, floor_sevenDivTwentyFive_eq_one])
    (by rw [floor_sevenDivTwentyFive_eq_one, boundary_floor_eq_one])
    hCA

end BoundaryThresholdFloorCellWitness

end ArkLib

/-! ## Axiom audit -/
#print axioms ArkLib.BoundaryThresholdFloorCell.prob_threshold_floorCell_mono
#print axioms ArkLib.BoundaryThresholdFloorCell.correlatedAgreementCurves_floorCell_mono
#print axioms ArkLib.BoundaryThresholdFloorCell.correlatedAgreementCurves_boundary_of_floorCell_mono
#print axioms ArkLib.BoundaryThresholdFloorCellWitness.sqrt_eight_lt_seventyTwoDivTwentyFive
#print axioms ArkLib.BoundaryThresholdFloorCellWitness.sevenDivTwentyFive_lt_boundary
#print axioms ArkLib.BoundaryThresholdFloorCellWitness.floor_sevenDivTwentyFive_eq_one
#print axioms ArkLib.BoundaryThresholdFloorCellWitness.errorBound_quarter_le_sevenDivTwentyFive
#print axioms ArkLib.BoundaryThresholdFloorCellWitness.boundary_export_witness
