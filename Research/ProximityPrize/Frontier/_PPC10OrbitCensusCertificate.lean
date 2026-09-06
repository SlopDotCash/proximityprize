/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# PPC10: weighted-orbit certificates for exact Paley relation censuses

`scripts/probes/probe_ppc10_orbit_census.py` enumerates nondecreasing subgroup words and gives each
word its permutation-orbit size.  This file proves the small checker kernel behind that
compression: replacing a representative `a` by `w a` labeled copies turns the exact equal-sum and
fully-disjoint pair censuses into weighted bucket sums.

The exact matched-regime probe gives the first `r = 3` onset:

* `n = 128`: characteristic-zero excess `= 0`, fully-disjoint census `D = 0`;
* `n = 256`: excess `= D = 184320`;
* `n = 512`: excess `= D = 368640`.

Thus the proposed finite-anchor shortcut "the characteristic-zero depth-three formula persists at
`p ≍ n^4`" is false already at `n = 256`.  At `(n,r)=(128,4)` the exact energy is
`27110661760`, with positive characteristic-`p` excess `222781440` and fully-disjoint census
`2454783744`, but it still lies below the Wick ceiling by `1075061120`.

The large numerical equalities below kernel-check the arithmetic interpretation of the emitted
summary.  They do **not** make Lean replay the 11.7-million-record `n=128,r=4` sort: reproducibility
is supplied by the exact deterministic probe and its canonical SHA-256 record digest.  The generic
weighted-orbit identities are fully proved here.  This is a falsifier/anchor interface, not a
production algorithm: its record count is `binomial (n+r-1) r`, exponential at the live
`(n,r)=(2^30,110)` gate.

Issues #466 and #505.  No Paley maximum or proximity-gap closure claim.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.PPC10OrbitCensusCertificate

open Finset

section WeightedBuckets

variable {R K V : Type*} [Fintype R] [DecidableEq R] [Fintype K] [DecidableEq K]
  [DecidableEq V]

/-- Total ordered mass in one sum bucket. -/
def bucketMass (bucket : R → K) (weight : R → ℕ) (k : K) : ℕ :=
  ∑ a : R, if bucket a = k then weight a else 0

/-- Weighted equal-bucket pair census on orbit representatives. -/
def weightedEnergy (bucket : R → K) (weight : R → ℕ) : ℕ :=
  ∑ a : R, ∑ b : R, if bucket a = bucket b then weight a * weight b else 0

/-- Exact row expansion used by the checker: every left representative pays its orbit weight times
the total ordered mass in its sum bucket. -/
theorem weightedEnergy_eq_rows (bucket : R → K) (weight : R → ℕ) :
    weightedEnergy bucket weight =
      ∑ a : R, weight a * bucketMass bucket weight (bucket a) := by
  classical
  unfold weightedEnergy bucketMass
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : bucket a = bucket b
  · simp [h]
  · have h' : bucket b ≠ bucket a := fun hba => h hba.symm
    simp [h, h']

/-- Ordered mass in the bucket of `a` whose support is disjoint from the support of `a`. -/
def disjointBucketMass (bucket : R → K) (support : R → Finset V) (weight : R → ℕ)
    (a : R) : ℕ :=
  ∑ b : R,
    if bucket a = bucket b ∧ Disjoint (support a) (support b) then weight b else 0

/-- Weighted fully-disjoint equal-bucket pair census. -/
def weightedDisjoint (bucket : R → K) (support : R → Finset V) (weight : R → ℕ) : ℕ :=
  ∑ a : R, ∑ b : R,
    if bucket a = bucket b ∧ Disjoint (support a) (support b)
    then weight a * weight b else 0

/-- Exact row expansion for the fully-disjoint census. -/
theorem weightedDisjoint_eq_rows (bucket : R → K) (support : R → Finset V)
    (weight : R → ℕ) :
    weightedDisjoint bucket support weight =
      ∑ a : R, weight a * disjointBucketMass bucket support weight a := by
  classical
  unfold weightedDisjoint disjointBucketMass
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : bucket a = bucket b ∧ Disjoint (support a) (support b)
  · simp [h]
  · simp [h]

/-- Representatives expanded into `weight a` labeled copies.  This is the abstract permutation
orbit expansion used by the exact probe. -/
abbrev Expanded (weight : R → ℕ) := Σ a : R, Fin (weight a)

/-- Unweighted equal-bucket census on a finite type. -/
def unweightedEnergy {Q : Type*} [Fintype Q] (bucket : Q → K) : ℕ :=
  ∑ a : Q, ∑ b : Q, if bucket a = bucket b then 1 else 0

/-- Unweighted fully-disjoint equal-bucket census on a finite type. -/
def unweightedDisjoint {Q : Type*} [Fintype Q] (bucket : Q → K)
    (support : Q → Finset V) : ℕ :=
  ∑ a : Q, ∑ b : Q,
    if bucket a = bucket b ∧ Disjoint (support a) (support b) then 1 else 0

/-- Expanding every representative into its labeled orbit copies gives exactly the weighted energy.
This is the proof-producing justification for storing one nondecreasing word plus an orbit size. -/
theorem expanded_energy_eq_weighted (bucket : R → K) (weight : R → ℕ) :
    unweightedEnergy (fun x : Expanded weight => bucket x.1) = weightedEnergy bucket weight := by
  classical
  unfold unweightedEnergy weightedEnergy
  simp only [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : bucket a = bucket b
  · simp [h, Nat.mul_comm]
  · simp [h]

/-- The same orbit expansion is exact for the support-sensitive fully-disjoint census. -/
theorem expanded_disjoint_eq_weighted (bucket : R → K) (support : R → Finset V)
    (weight : R → ℕ) :
    unweightedDisjoint (fun x : Expanded weight => bucket x.1)
        (fun x : Expanded weight => support x.1) =
      weightedDisjoint bucket support weight := by
  classical
  unfold unweightedDisjoint weightedDisjoint
  simp only [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : bucket a = bucket b ∧ Disjoint (support a) (support b)
  · simp [h, Nat.mul_comm]
  · simp [h]

end WeightedBuckets

section Centering

/-- Ordinary nonprincipal centered contribution of one left-support stratum. -/
def ordinaryCentered (p n r A E : ℕ) : ℤ := p * E - A * n ^ r

/-- Fully-disjoint centered contribution of one left-support stratum. -/
def disjointCentered (p n r s A D : ℕ) : ℤ := p * D - A * (n - s) ^ r

/-- Signed puncture correction in one support stratum. -/
def punctureCorrection (p n r s A E D : ℕ) : ℤ :=
  disjointCentered p n r s A D - ordinaryCentered p n r A E

/-- The G133 support-stratum decomposition is an exact integer identity. -/
theorem disjointCentered_eq_ordinary_add_correction (p n r s A E D : ℕ) :
    disjointCentered p n r s A D =
      ordinaryCentered p n r A E + punctureCorrection p n r s A E D := by
  simp only [punctureCorrection]
  ring

end Centering

/-! ## Kernel-checked arithmetic summaries from the deterministic exact census -/

def charZeroEnergyThree (n : ℕ) : ℕ := 15 * n ^ 3 - 45 * n ^ 2 + 40 * n

def charZeroEnergyFour (n : ℕ) : ℕ :=
  105 * n ^ 4 - 630 * n ^ 3 + 1435 * n ^ 2 - 1155 * n

/-- Exact matched-regime depth-three onset printed by the probe.  The external enumerator supplies
the three energy/disjoint values; Lean checks that their interpretation is arithmetically exact:
the excess is zero at 128 and equals the fully-disjoint census at 256 and 512. -/
theorem matched_depth_three_onset_arithmetic :
    30725120 = charZeroEnergyThree 128 ∧
    248903680 = charZeroEnergyThree 256 + 184320 ∧
    2001858560 = charZeroEnergyThree 512 + 368640 ∧
    (0 : ℕ) < 184320 ∧ (0 : ℕ) < 368640 := by
  norm_num [charZeroEnergyThree]

/-- Consequently the finite-anchor rule asserting persistence of the characteristic-zero formula
at all three matched cells is refuted by either of the last two exact summaries. -/
theorem not_charZero_persistence_on_matched_anchors :
    ¬(30725120 = charZeroEnergyThree 128 ∧
      248903680 = charZeroEnergyThree 256 ∧
      2001858560 = charZeroEnergyThree 512) := by
  norm_num [charZeroEnergyThree]

/-- The `n=128,r=4` summary: positive characteristic-p excess, nonzero fully-disjoint sector, and a
strictly surviving Wick slack. -/
theorem n128_depth_four_anchor_arithmetic :
    27110661760 = charZeroEnergyFour 128 + 222781440 ∧
    27110661760 + 1075061120 = 105 * 128 ^ 4 ∧
    (0 : ℕ) < 2454783744 ∧
    (7205544091668307584 : ℤ) + (-6610141054032283136 : ℤ) =
      595403037636024448 := by
  norm_num [charZeroEnergyFour]

/-- All four concrete anchors remain below their corresponding Wick ceilings.  Computation detects
the onset but does not by itself break the Gaussian-energy budget. -/
theorem anchor_energies_lt_wick :
    30725120 < 15 * 128 ^ 3 ∧
    248903680 < 15 * 256 ^ 3 ∧
    2001858560 < 15 * 512 ^ 3 ∧
    27110661760 < 105 * 128 ^ 4 := by
  norm_num

end ArkLib.ProximityGap.Frontier.PPC10OrbitCensusCertificate

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.PPC10OrbitCensusCertificate
#print axioms weightedEnergy_eq_rows
#print axioms weightedDisjoint_eq_rows
#print axioms expanded_energy_eq_weighted
#print axioms expanded_disjoint_eq_weighted
#print axioms disjointCentered_eq_ordinary_add_correction
#print axioms matched_depth_three_onset_arithmetic
#print axioms not_charZero_persistence_on_matched_anchors
#print axioms n128_depth_four_anchor_arithmetic
#print axioms anchor_energies_lt_wick
