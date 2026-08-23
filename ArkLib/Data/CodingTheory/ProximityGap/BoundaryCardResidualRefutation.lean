/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BoundaryCardResidual
import Mathlib.Algebra.Field.ZMod

/-!
# Counterexample to the bare closed-boundary cardinality residual

The original `ProximityGap.BoundaryCardResidual` asks for `jointAgreement` from a **merely
nonempty** good-coefficient set at the exact square-root boundary.  This file exhibits a small
square-endpoint instance where the good set is nonempty but `jointAgreement` is false.

The witness is:

* coordinate domain `ι = Fin 4`;
* field `F = ZMod 5`;
* Reed-Solomon degree `deg = 1`, so codewords are constant functions on the four evaluation points;
* curve dimension parameter `k = 2`;
* exact Johnson endpoint `δ = 1 - sqrt(1 / 4) = 1 / 2`;
* stack `uBad` with `uBad 0 = 0`, `uBad 1 = domain`, and `uBad 2 = 0`.

The curve parameter `z = 0` gives the zero codeword, so the good set is nonempty.  But
`jointAgreement` would require a two-coordinate set on which `uBad 1` agrees with a constant
codeword.  Since `uBad 1 = domain` is injective, any such agreement set has cardinality at most
one.  Thus the bare residual is false as stated; boundary work must keep a genuinely stronger
threshold, cardinality, or coefficient-polynomial hypothesis rather than trying to discharge
`BoundaryCardResidual` from nonemptiness alone.  The same witness also shows that the current
`BoundaryCardLatticeData` package cannot be derived in small fields: it would require
`(Fintype.card I + 1) * k = 10` good coefficients in `ZMod 5`.

The same witness also refutes `BoundaryProbabilityResidual` and the corresponding exported
`δ_ε_correlatedAgreementCurves` conclusion with `ε = errorBound`: at the exact Johnson endpoint,
`errorBound = 0`, so the probability premise is only `Pr[good] > 0`.
-/

namespace ArkLib

namespace BoundaryCardResidualRefutation

open ArkLib ArkLib.BoundaryCardResidual ProximityGap Code
open scoped BigOperators NNReal ENNReal ProbabilityTheory LinearCode

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

abbrev I : Type := Fin 4
abbrev F : Type := ZMod 5

/-- Four distinct evaluation points in `ZMod 5`. -/
def domain : I ↪ F where
  toFun i := (i : ℕ)
  inj' := by
    intro a b h
    apply Fin.ext
    have h' : (((a : ℕ) : ZMod 5) = ((b : ℕ) : ZMod 5)) := h
    have hmod := (ZMod.natCast_eq_natCast_iff' (a : ℕ) (b : ℕ) 5).mp h'
    have ha5 : (a : ℕ) < 5 := by omega
    have hb5 : (b : ℕ) < 5 := by omega
    rwa [Nat.mod_eq_of_lt ha5, Nat.mod_eq_of_lt hb5] at hmod

/-- Bad stack: `u 0` is the zero codeword, while `u 1` separates all four coordinates. -/
def uBad : WordStack F (Fin 3) I :=
  fun t i => if t = 1 then domain i else 0

theorem sqrtRate_le_one : ReedSolomon.sqrtRate 1 domain ≤ 1 := by
  simp only [ReedSolomon.sqrtRate]
  have hrate : (LinearCode.rate (ReedSolomon.code domain 1) : ℝ≥0) ≤ 1 := by
    exact_mod_cast
      (DivergenceOfSets.reedSolomon_rate_le_one (deg := 1) (domain := domain))
  simpa using NNReal.sqrt_le_sqrt.mpr hrate

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

theorem rate_eq_quarter :
    (LinearCode.rate (ReedSolomon.code domain 1) : ℝ≥0) = (1 : ℝ≥0) / 4 := by
  simpa [I, NNRat.cast_div, NNRat.cast_natCast] using
    congrArg (fun x : ℚ≥0 => (x : ℝ≥0))
      (ReedSolomon.rateOfLinearCode_eq_div' (F := F) (α := domain) (n := 1) (by decide))

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

theorem johnson_side_lower :
    (1 - (LinearCode.rate (ReedSolomon.code domain 1) : ℝ≥0)) / 2
      < 1 - ReedSolomon.sqrtRate 1 domain := by
  rw [rate_eq_quarter, boundary_eq_half]
  rw [← NNReal.coe_lt_coe]
  have hquarter_le_one : (1 / 4 : ℝ≥0) ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    norm_num
  rw [NNReal.coe_div, NNReal.coe_div, NNReal.coe_sub hquarter_le_one]
  norm_num

theorem boundary_floor_eq_two :
    Nat.floor ((1 - ReedSolomon.sqrtRate 1 domain) * Fintype.card I) = 2 := by
  rw [boundary_mul_card_eq_two]
  norm_num

theorem boundary_floor_cast :
    (Nat.floor ((1 - ReedSolomon.sqrtRate 1 domain) * Fintype.card I) : ℝ≥0)
      = (1 - ReedSolomon.sqrtRate 1 domain) * Fintype.card I := by
  rw [boundary_floor_eq_two, boundary_mul_card_eq_two]
  norm_num

theorem good_nonempty :
    0 < (RS_goodCoeffsCurve (k := 2) (deg := 1) (domain := domain) uBad
      (1 - ReedSolomon.sqrtRate 1 domain)).card := by
  classical
  refine Finset.card_pos.mpr ⟨0, ?_⟩
  have hzero_mem :
      (0 : I → F) ∈ (ReedSolomon.code domain 1 : Set (I → F)) := by
    exact (ReedSolomon.code domain 1).zero_mem
  have hrel :
      δᵣ((0 : I → F), (ReedSolomon.code domain 1 : Set (I → F))) ≤
        (1 - ReedSolomon.sqrtRate 1 domain : ℝ≥0) := by
    rw [Code.relDistFromCode_eq_distFromCode_div,
      Code.distFromCode_of_mem (ReedSolomon.code domain 1 : Set (I → F)) hzero_mem]
    simp
  have hsum :
      (∑ t : Fin 3, (0 : F) ^ (t : ℕ) • uBad t) = (0 : I → F) := by
    funext i
    fin_cases i <;> simp [uBad]
  simpa [RS_goodCoeffsCurve, hsum] using hrel

theorem good_probability_pos :
    Pr_{
      let z ← $ᵖ F}[δᵣ(∑ t : Fin (2 + 1), (z ^ (t : ℕ)) • uBad t,
        ReedSolomon.code domain 1) ≤ 1 - ReedSolomon.sqrtRate 1 domain] > (0 : ENNReal) := by
  classical
  change
    Pr_{
      let z ← $ᵖ F}[δᵣ(∑ t : Fin (2 + 1), (z ^ (t : ℕ)) • uBad t,
        ReedSolomon.code domain 1) ≤
          ((1 - ReedSolomon.sqrtRate 1 domain : ℝ≥0) : ENNReal)] > (0 : ENNReal)
  have hPr := prob_close_curve_eq_card_goodCoeffsCurve_div_card
    (k := 2) (deg := 1) (domain := domain)
    (δ := 1 - ReedSolomon.sqrtRate 1 domain) uBad
  rw [hPr]
  have hcard : (0 : ℝ≥0) <
      ((RS_goodCoeffsCurve (k := 2) (deg := 1) (domain := domain) uBad
        (1 - ReedSolomon.sqrtRate 1 domain)).card : ℝ≥0) := by
    exact_mod_cast good_nonempty
  exact_mod_cast
    (div_pos hcard (by norm_num [F] : (0 : ℝ≥0) < (Fintype.card F : ℝ≥0)))

theorem boundary_errorBound_eq_zero :
    errorBound (1 - ReedSolomon.sqrtRate 1 domain) 1 domain = 0 := by
  exact errorBound_eq_zero_of_johnson_not_lt_sqrt
    (deg := 1) (domain := domain)
    johnson_side_lower (not_lt.mpr le_rfl)

theorem boundary_probability_hypothesis :
    Pr_{
      let z ← $ᵖ F}[δᵣ(∑ t : Fin (2 + 1), (z ^ (t : ℕ)) • uBad t,
        ReedSolomon.code domain 1) ≤ 1 - ReedSolomon.sqrtRate 1 domain] >
      ((2 : ENNReal) *
        (errorBound (1 - ReedSolomon.sqrtRate 1 domain) 1 domain : ENNReal)) := by
  simpa [boundary_errorBound_eq_zero] using good_probability_pos

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

theorem not_jointAgreement :
    ¬ jointAgreement (C := ReedSolomon.code domain 1)
      (δ := 1 - ReedSolomon.sqrtRate 1 domain) (W := uBad) := by
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
    have ha_dom : v 1 a = domain a := by simpa [uBad] using ha_eq
    have hb_dom : v 1 b = domain b := by simpa [uBad] using hb_eq
    have hdom : domain a = domain b := by
      rw [← ha_dom, hvconst, hb_dom]
    exact domain.injective hdom
  omega

theorem not_boundaryCardResidual :
    ¬ BoundaryCardResidual (k := 2) (deg := 1) (domain := domain)
      (δ := 1 - ReedSolomon.sqrtRate 1 domain) := by
  intro h
  exact not_jointAgreement (h (by norm_num) uBad rfl good_nonempty)

theorem not_boundaryCardLatticeResidual :
    ¬ ArkLib.BoundaryCardResidual.BoundaryCardLatticeResidual
      (k := 2) (deg := 1) (domain := domain)
      (δ := 1 - ReedSolomon.sqrtRate 1 domain) := by
  intro h
  exact not_jointAgreement (h (by norm_num) uBad rfl boundary_floor_cast good_nonempty)

theorem not_boundaryCardLatticeData :
    ¬ ArkLib.BoundaryCardResidual.BoundaryCardLatticeData
      (k := 2) (deg := 1) (domain := domain)
      (δ := 1 - ReedSolomon.sqrtRate 1 domain) := by
  exact ArkLib.BoundaryCardResidual.BoundaryCardLatticeData.not_of_field_card_lt_of_pos
    (F := F) (ι := I) (domain := domain)
    (hfield := by norm_num [I, F]) (by norm_num) uBad rfl boundary_floor_cast good_nonempty

theorem not_boundaryCardQuantizationResiduals :
    ¬ ArkLib.BoundaryCardResidual.BoundaryCardQuantizationResiduals
      (k := 2) (deg := 1) (domain := domain)
      (δ := 1 - ReedSolomon.sqrtRate 1 domain) := by
  intro h
  exact not_boundaryCardLatticeResidual h.lattice

theorem not_boundaryProbabilityResidual :
    ¬ BoundaryProbabilityResidual (k := 2) (deg := 1) (domain := domain)
      (δ := 1 - ReedSolomon.sqrtRate 1 domain) := by
  intro h
  exact not_jointAgreement
    (h (by norm_num) uBad boundary_probability_hypothesis johnson_side_lower
      (not_lt.mpr le_rfl))

theorem not_delta_epsilon_correlatedAgreementCurves_boundary :
    ¬ δ_ε_correlatedAgreementCurves (k := 2) (A := F) (F := F) (ι := I)
      (C := ReedSolomon.code domain 1)
      (δ := 1 - ReedSolomon.sqrtRate 1 domain)
      (ε := errorBound (1 - ReedSolomon.sqrtRate 1 domain) 1 domain) := by
  intro h
  exact not_jointAgreement (h uBad (by simpa using boundary_probability_hypothesis))

end BoundaryCardResidualRefutation

end ArkLib

/-! ## Axiom audit -/
#print axioms ArkLib.BoundaryCardResidualRefutation.not_boundaryCardResidual
#print axioms ArkLib.BoundaryCardResidualRefutation.not_boundaryCardLatticeResidual
#print axioms ArkLib.BoundaryCardResidualRefutation.not_boundaryCardLatticeData
#print axioms ArkLib.BoundaryCardResidualRefutation.not_boundaryCardQuantizationResiduals
#print axioms ArkLib.BoundaryCardResidualRefutation.not_boundaryProbabilityResidual
#print axioms ArkLib.BoundaryCardResidualRefutation.not_delta_epsilon_correlatedAgreementCurves_boundary
