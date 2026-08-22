/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G249CartesianRowSelectionBarrier

/-!
# G250: sponsor-scale calibration of the Cartesian row-selection barrier (#466)

G249 proves the finite obstruction: a Cartesian exceptional set of density exactly `1/m` can contain
one whole row.  This file records the sponsor-scale arithmetic consumer of that obstruction.

The published Lu--Zheng--Zheng-style Cartesian discrepancy available in G248 is around `2^-15` at
both sponsor moduli.  Even the idealized stronger budget `2^-15` is far above the one-row threshold:
at `m = 2^128 + 192` it permits more than `2^113` complete rows, and at
`m = 2^129 + 13` it permits more than `2^114` complete rows.  Thus the 113--114 bit
quantifier gap is not a prose estimate: it is a kernel-checked cardinal arithmetic obstruction.

This is a calibrated no-go for importing a two-dimensional Cartesian discrepancy theorem as
fixed-row control.  It is not a Jacobi-sum estimate and not a prize closure.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G250SponsorRowDiscrepancyCalibration

open ArkLib.ProximityGap.Frontier.G249CartesianRowSelectionBarrier

/-- P1 quotient size from the G248 sponsor audit. -/
def sponsorP1M : ℕ := 2 ^ 128 + 192

/-- P2 quotient size from the G248 sponsor audit. -/
def sponsorP2M : ℕ := 2 ^ 129 + 13

/--
The idealized `2^-15` Cartesian discrepancy scale is still above the P1 row-density threshold.
-/
theorem p1_two_pow15_below_row_length : 2 ^ 15 < sponsorP1M := by
  norm_num [sponsorP1M]

/--
The idealized `2^-15` Cartesian discrepancy scale is still above the P2 row-density threshold.
-/
theorem p2_two_pow15_below_row_length : 2 ^ 15 < sponsorP2M := by
  norm_num [sponsorP2M]

/-- At P1, a `2^-15` Cartesian budget contains more than `2^113` full row-lengths. -/
theorem p1_two_pow_neg15_budget_allows_gt_2pow113_rows :
    2 ^ 15 * (2 ^ 113 * sponsorP1M) < sponsorP1M * sponsorP1M := by
  norm_num [sponsorP1M]

/-- At P2, a `2^-15` Cartesian budget contains more than `2^114` full row-lengths. -/
theorem p2_two_pow_neg15_budget_allows_gt_2pow114_rows :
    2 ^ 15 * (2 ^ 114 * sponsorP2M) < sponsorP2M * sponsorP2M := by
  norm_num [sponsorP2M]

/-- The P1 one-row counterexample from G249 has exactly the sponsor row length. -/
theorem p1_rowBad_card :
    (rowBad (sponsorP1M - 1)).card = sponsorP1M := by
  rw [rowBad_card]
  norm_num [sponsorP1M]

/-- The P2 one-row counterexample from G249 has exactly the sponsor row length. -/
theorem p2_rowBad_card :
    (rowBad (sponsorP2M - 1)).card = sponsorP2M := by
  rw [rowBad_card]
  norm_num [sponsorP2M]

/-- Honest scope marker: this is only a sponsor-scale calibration of a Cartesian-to-row no-go. -/
def isPrizeClosure : Bool := false

theorem not_prizeClosure : isPrizeClosure = false := rfl

#print axioms p1_two_pow15_below_row_length
#print axioms p2_two_pow15_below_row_length
#print axioms p1_two_pow_neg15_budget_allows_gt_2pow113_rows
#print axioms p2_two_pow_neg15_budget_allows_gt_2pow114_rows
#print axioms p1_rowBad_card
#print axioms p2_rowBad_card
#print axioms not_prizeClosure

end ArkLib.ProximityGap.Frontier.G250SponsorRowDiscrepancyCalibration
