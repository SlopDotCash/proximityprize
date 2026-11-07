/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BoundaryLatticeThresholdLeaf
import Mathlib.Algebra.Field.ZMod

/-!
# Counterexample to the threshold-only lattice residual

`BoundaryLatticeThresholdLeaf.BoundaryCardLatticeThresholdResidual` asks for `jointAgreement`
from the field-quantitative threshold `Pr > k·(n+1)/|F|` at a square lattice endpoint.  The
leaf records that the threshold alone is not enough, but only through an unverified probe.
This file kernel-checks a smaller endpoint instead:

* coordinate domain `ι = Fin 4`;
* field `F = ZMod 7`;
* Reed-Solomon degree `deg = 1`, so codewords are constant functions on the four points;
* curve dimension parameter `k = 1`;
* exact Johnson endpoint `δ = 1 - sqrt(1/4) = 1/2`, with `δ·n = 2` integral;
* stack `u 0 = (0, 0, 1, 4)`, `u 1 = (0, 1, 2, 3)`.

The good set contains `{0, 1, 3, 4, 5, 6}`: six of the seven parameters place the curve
within distance `1/2` of a constant word, so `Pr ≥ 6/7 > 5/7 = k·(n+1)/|F|`.  But
`jointAgreement` needs a common agreement set of size at least `(1-δ)·4 = 2`, and `u 1` is
injective, so no constant codeword can agree with it on two coordinates.  Hence the residual is
false as stated.  Moreover the extraction-only surface `LatticeCoeffPolyExtraction` is itself
refuted at this endpoint (`not_latticeCoeffPolyExtraction`): the extraction is load-bearing, but
the all-decoded-family formulation of it is too strong — it also fails on ambiguous decodings
where correlated agreement holds (see the module header of `BoundaryLatticeThresholdLeaf`), so
the surviving frontier is an existence / selection-compatible extraction statement.

## Verification
`./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/BoundaryLatticeThresholdRefutation.lean`

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (list-decoding extraction), §6.2 (closed Johnson boundary at `1 − √ρ`).
-/

namespace ArkLib

namespace BoundaryLatticeThresholdRefutation

open ArkLib BoundaryLatticeThresholdLeaf ProximityGap Code NNReal
open scoped BigOperators NNReal ENNReal ProbabilityTheory LinearCode

private instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

abbrev I : Type := Fin 4
abbrev F : Type := ZMod 7

/-- Four distinct evaluation points in `ZMod 7`. -/
def domain : I ↪ F where
  toFun i := (i : ℕ)
  inj' := by
    intro a b h
    apply Fin.ext
    have h' : (((a : ℕ) : ZMod 7) = ((b : ℕ) : ZMod 7)) := h
    have hmod := (ZMod.natCast_eq_natCast_iff' (a : ℕ) (b : ℕ) 7).mp h'
    have ha7 : (a : ℕ) < 7 := by omega
    have hb7 : (b : ℕ) < 7 := by omega
    rwa [Nat.mod_eq_of_lt ha7, Nat.mod_eq_of_lt hb7] at hmod

/-- The bad stack: `u 0 = (0, 0, 1, 4)` and `u 1 = (0, 1, 2, 3)`. -/
def u : WordStack F (Fin 2) I :=
  ![![0, 0, 1, 4], ![0, 1, 2, 3]]

theorem sqrtRate_mul_card_eq_two :
    ReedSolomon.sqrtRate 1 domain * Fintype.card I = (2 : ℝ≥0) := by
  obtain ⟨m, hm⟩ :=
    ArkLib.BoundaryCardResidual.sqrtRate_mul_card_mem_of_isSquare_deg_mul_card
      (domain := domain) (deg := 1) (by decide) ⟨2, by norm_num⟩
  have hm_sq : m * m = 4 := by
    apply Nat.cast_injective (R := ℝ≥0)
    calc
      ((m * m : ℕ) : ℝ≥0) = (m : ℝ≥0) ^ 2 := by norm_num [pow_two]
      _ = (ReedSolomon.sqrtRate 1 domain * Fintype.card I) ^ 2 := by rw [hm]
      _ = ((1 * Fintype.card I : ℕ) : ℝ≥0) := by
        rw [ArkLib.BoundaryCardResidual.sqrtRate_mul_card_sq_eq_deg_mul_card
          (domain := domain) (deg := 1) (by decide)]
      _ = (4 : ℝ≥0) := by norm_num [I]
  have hm_le : m ≤ 4 := by
    by_contra h
    have h5 : 5 ≤ m := Nat.succ_le_of_lt (Nat.lt_of_not_ge h)
    have h25 : 25 ≤ m * m := Nat.mul_le_mul h5 h5
    omega
  have hm_two : m = 2 := by
    interval_cases m <;> first | rfl | omega
  simpa [hm_two] using hm

theorem boundary_mul_card_eq_two :
    (1 - ReedSolomon.sqrtRate 1 domain) * Fintype.card I = (2 : ℝ≥0) := by
  have hle : ReedSolomon.sqrtRate 1 domain * Fintype.card I ≤ (Fintype.card I : ℝ≥0) := by
    rw [sqrtRate_mul_card_eq_two]
    norm_num [I]
  calc
    (1 - ReedSolomon.sqrtRate 1 domain) * Fintype.card I
        = (Fintype.card I : ℝ≥0) - ReedSolomon.sqrtRate 1 domain * Fintype.card I := by
          rw [tsub_mul, one_mul]
    _ = (2 : ℝ≥0) := by
      rw [sqrtRate_mul_card_eq_two]
      norm_num [I]
      apply Subtype.ext
      change ((((4 : ℝ≥0) - (2 : ℝ≥0) : ℝ≥0) : ℝ) = (2 : ℝ))
      rw [NNReal.coe_sub (by norm_num : (2 : ℝ≥0) ≤ 4)]
      norm_num

theorem boundary_eq_half :
    1 - ReedSolomon.sqrtRate 1 domain = (1 : ℝ≥0) / 2 := by
  apply Subtype.ext
  have h := congrArg (fun x : ℝ≥0 => (x : ℝ)) boundary_mul_card_eq_two
  change (((1 - ReedSolomon.sqrtRate 1 domain) : ℝ≥0) : ℝ) *
      ((Fintype.card I : ℝ≥0) : ℝ) = (2 : ℝ) at h
  norm_num [I] at h
  change (((1 - ReedSolomon.sqrtRate 1 domain) : ℝ≥0) : ℝ) = ((1 : ℝ≥0) / 2 : ℝ)
  norm_num
  linarith

theorem boundary_floor_eq_two :
    Nat.floor ((1 - ReedSolomon.sqrtRate 1 domain) * Fintype.card I) = 2 := by
  rw [boundary_mul_card_eq_two]
  norm_num

theorem boundary_floor_cast :
    (Nat.floor ((1 - ReedSolomon.sqrtRate 1 domain) * Fintype.card I) : ℝ≥0)
      = (1 - ReedSolomon.sqrtRate 1 domain) * Fintype.card I := by
  rw [boundary_floor_eq_two, boundary_mul_card_eq_two]
  norm_num

/-- A word agreeing with a constant on two distinct coordinates is within relative distance
`1/2` of it. -/
theorem relDist_half_of_agree {w : I → F} {c : F} {i j : I} (hij : i ≠ j)
    (hi : w i = c) (hj : w j = c) :
    δᵣ(w, ReedSolomon.constantCode c I) ≤ (1 : ℝ≥0) / 2 := by
  rw [Code.relCloseToWord_iff_exists_agreementCols]
  refine ⟨{i, j}, ?_, ?_⟩
  · rw [Finset.card_pair hij]
    norm_num [I]
  · intro k
    constructor
    · intro hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · simpa [ReedSolomon.constantCode] using hi
      · simpa [ReedSolomon.constantCode] using hj
    · intro hne hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hne (by simpa [ReedSolomon.constantCode] using hi)
      · exact hne (by simpa [ReedSolomon.constantCode] using hj)

/-- Membership in the good set from an explicit two-coordinate agreement with a constant. -/
theorem good_of_pair (z c : F) (i j : I) (hij : i ≠ j)
    (hi : (∑ t : Fin (1 + 1), (z ^ (t : ℕ)) • u t) i = c)
    (hj : (∑ t : Fin (1 + 1), (z ^ (t : ℕ)) • u t) j = c) :
    z ∈ RS_goodCoeffsCurve (k := 1) (deg := 1) (domain := domain) u ((1 : ℝ≥0) / 2) := by
  simp only [RS_goodCoeffsCurve, Finset.mem_filter, Finset.mem_univ, true_and]
  refine le_trans
    (Code.relDistFromCode_le_relDist_to_mem _ (ReedSolomon.constantCode c I) (by simp)) ?_
  have hpair := relDist_half_of_agree hij hi hj
  exact_mod_cast hpair

theorem good_card_ge_six :
    6 ≤ (RS_goodCoeffsCurve (k := 1) (deg := 1) (domain := domain) u
      ((1 : ℝ≥0) / 2)).card := by
  have hsub : ({0, 1, 3, 4, 5, 6} : Finset F) ⊆
      RS_goodCoeffsCurve (k := 1) (deg := 1) (domain := domain) u ((1 : ℝ≥0) / 2) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · exact good_of_pair 0 0 0 1 (by decide) (by decide) (by decide)
    · exact good_of_pair 1 0 0 3 (by decide) (by decide) (by decide)
    · exact good_of_pair 3 0 0 2 (by decide) (by decide) (by decide)
    · exact good_of_pair 4 2 2 3 (by decide) (by decide) (by decide)
    · exact good_of_pair 5 5 1 3 (by decide) (by decide) (by decide)
    · exact good_of_pair 6 6 1 2 (by decide) (by decide) (by decide)
  calc (6 : ℕ) = ({0, 1, 3, 4, 5, 6} : Finset F).card := by decide
    _ ≤ _ := Finset.card_le_card hsub

theorem latticeThresholdEps_eq :
    latticeThresholdEps I F = (5 : ℝ≥0) / 7 := by
  unfold latticeThresholdEps
  norm_num [I, F]

theorem prob_hypothesis :
    Pr_{
      let z ← $ᵖ F}[δᵣ(∑ t : Fin (1 + 1), (z ^ (t : ℕ)) • u t,
        ReedSolomon.code domain 1) ≤
          ((1 - ReedSolomon.sqrtRate 1 domain : ℝ≥0) : ENNReal)] >
      (1 : ENNReal) * (latticeThresholdEps I F : ENNReal) := by
  have hPr := prob_close_curve_eq_card_goodCoeffsCurve_div_card
    (k := 1) (deg := 1) (domain := domain)
    (δ := 1 - ReedSolomon.sqrtRate 1 domain) u
  rw [hPr]
  rw [boundary_eq_half]
  rw [latticeThresholdEps_eq]
  have hcard :
      (6 : ENNReal) ≤
        ((RS_goodCoeffsCurve (k := 1) (deg := 1) (domain := domain) u
          ((1 : ℝ≥0) / 2)).card : ENNReal) := by
    exact_mod_cast good_card_ge_six
  rw [show ((Fintype.card F : ℝ≥0) : ENNReal) = 7 by norm_num [F]]
  have hcard' : (5 : ENNReal) <
      ((RS_goodCoeffsCurve (k := 1) (deg := 1) (domain := domain) u
        ((1 : ℝ≥0) / 2)).card : ENNReal) :=
    lt_of_lt_of_le (by norm_num : (5 : ENNReal) < 6) hcard
  have hlt := ENNReal.div_lt_div_right (a := (5 : ENNReal))
    (b := ((RS_goodCoeffsCurve (k := 1) (deg := 1) (domain := domain) u
      ((1 : ℝ≥0) / 2)).card : ENNReal)) (c := 7)
    (by norm_num) (by norm_num) hcard'
  simpa using hlt

theorem code_deg_one_constant {v : I → F}
    (hv : v ∈ (ReedSolomon.code domain 1 : Set (I → F))) :
    ∀ i j : I, v i = v j := by
  change v ∈ ReedSolomon.code domain 1 at hv
  rw [ReedSolomon.mem_code_iff_exists_polynomial_of_ne_zero] at hv
  rcases hv with ⟨p, hpdeg, hv_eval⟩
  have hpconst : p = Polynomial.C (p.coeff 0) :=
    Polynomial.eq_C_of_natDegree_le_zero (by omega)
  intro i j
  rw [hv_eval, ReedSolomon.evalOnPoints, hpconst]
  simp

theorem u_one_injective : Function.Injective (u 1) := by
  decide

theorem not_jointAgreement :
    ¬ jointAgreement (C := ReedSolomon.code domain 1)
      (δ := 1 - ReedSolomon.sqrtRate 1 domain) (W := u) := by
  classical
  rintro ⟨S, hS, v, hv⟩
  have hS_two : 2 ≤ S.card := by
    rw [ge_iff_le,
      ← Code.relDist_floor_bound_iff_complement_bound
        (Fintype.card I) S.card (1 - ReedSolomon.sqrtRate 1 domain)] at hS
    rw [boundary_floor_eq_two] at hS
    norm_num [I] at hS
    exact hS
  have hS_one : S.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    have hvconst := code_deg_one_constant (hv 1).1 a b
    have ha_eq := (Finset.mem_filter.mp ((hv 1).2 ha)).2
    have hb_eq := (Finset.mem_filter.mp ((hv 1).2 hb)).2
    apply u_one_injective
    rw [← ha_eq, hvconst, hb_eq]
  omega

/-- The threshold-only lattice surface is false at the `ZMod 7`, `n = 4`, `deg = 1`,
`k = 1` lattice endpoint. -/
theorem not_boundaryCardLatticeThresholdResidual :
    ¬ BoundaryCardLatticeThresholdResidual (k := 1) (deg := 1) (domain := domain)
      (δ := 1 - ReedSolomon.sqrtRate 1 domain) := by
  intro h
  exact not_jointAgreement
    (h (by norm_num) u rfl boundary_floor_cast (by simpa using prob_hypothesis))

/-- The extraction-only residual is also false at this endpoint: extraction at the count
threshold would yield `BoundaryCardLatticeThresholdResidual` through
`boundaryCardLatticeThresholdResidual_of_extraction`, and that surface is refuted above.  So the
unconditional extraction hypothesis is not merely open — it is unsatisfiable here. -/
theorem not_latticeCoeffPolyExtraction :
    ¬ LatticeCoeffPolyExtraction (k := 1) (deg := 1) (domain := domain)
      (δ := 1 - ReedSolomon.sqrtRate 1 domain) :=
  fun hExt =>
    not_boundaryCardLatticeThresholdResidual
      (boundaryCardLatticeThresholdResidual_of_extraction hExt)

/-- The canonical-family form is refuted at the same endpoint: it implies the all-families
extraction, which is false here. -/
theorem not_latticeCanonicalCoeffPolyExtraction :
    ¬ LatticeCanonicalCoeffPolyExtraction (k := 1) (deg := 1) (domain := domain)
      (δ := 1 - ReedSolomon.sqrtRate 1 domain) :=
  fun hCanon => not_latticeCoeffPolyExtraction
    (latticeCoeffPolyExtraction_of_canonical hCanon)

end BoundaryLatticeThresholdRefutation

end ArkLib

/-! ## Axiom audit -/
#print axioms ArkLib.BoundaryLatticeThresholdRefutation.relDist_half_of_agree
#print axioms ArkLib.BoundaryLatticeThresholdRefutation.good_card_ge_six
#print axioms ArkLib.BoundaryLatticeThresholdRefutation.prob_hypothesis
#print axioms ArkLib.BoundaryLatticeThresholdRefutation.not_jointAgreement
#print axioms ArkLib.BoundaryLatticeThresholdRefutation.not_boundaryCardLatticeThresholdResidual
#print axioms ArkLib.BoundaryLatticeThresholdRefutation.not_latticeCoeffPolyExtraction
#print axioms ArkLib.BoundaryLatticeThresholdRefutation.not_latticeCanonicalCoeffPolyExtraction
