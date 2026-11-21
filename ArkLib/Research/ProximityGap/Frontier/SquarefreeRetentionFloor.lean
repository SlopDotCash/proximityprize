/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Profile
import ArkLib.Research.ProximityGap.Frontier.FirstOrderDegreeOneBoundary

/-! # Necessary costs of the retained squarefree curve certificate

The ordinary and regular parts each charge accidental agreements. Keeping both
excludes both production budgets at each of the four test radii, even in the
numerical relaxation where the common Taylor exponent is set to zero.
-/
set_option autoImplicit false
namespace ProximityGap.SquarefreeRetentionFloor
open ReedSolomon ReedSolomon.HiddenDerivative ReedSolomon.FirstOrder.Squarefree
open ReedSolomon.HiddenDerivative.CurveProfile PolynomialDifferential MvPolynomial

/-- The smallest generally sufficient first-order Taylor exponent is attained by the
last chart coordinate. Enlarging the chart preserves this necessary lower bound. -/
theorem taylor_floor {D K τ : ℕ} (hk : D < K) (ht : TaylorExponentSufficient 1 K τ) :
    regularTaylorExponent D ≤ τ := by
  have := ht ⟨D,hk⟩
  unfold regularTaylorExponent
  dsimp at this
  omega

/-- For positive derivative degree and nonlinear total degree, the mixed volume
also charges the derivative coordinates, beyond the common denominator itself. -/
theorem fiber_floor {K B M τ : ℕ} (hB : 2 ≤ B) (hM : 1 ≤ M) (hMB : M ≤ B) :
    1 + τ + min (1+τ) (K-1) ≤ firstOrderCurveFiberStageOne K B M τ := by
  apply le_trans _ ((firstOrderCurveFiberStageOne_mono_total (r := 1) hB).trans
    (firstOrderCurveFiberStageOne_mono_derivative hM hMB))
  simp [firstOrderCurveFiberStageOne,cappedDegreeMixedVolume_eq,
    firstOrderTaylorTotalCap,firstOrderTaylorDerivativeCap,Nat.add_comm]

/-- The regular fiber term retains the incidence ratio even if the Taylor
exponent is allowed to be zero. The bound holds for every permitted split. -/
theorem regular_floor {n D K L A ℓ B M H τ : ℕ}
    (hDL : D < L) (hLA : L ≤ A) (hℓ : 1 ≤ ℓ) :
    ((n-A : ℕ) : ℚ) * ((n-D : ℕ) : ℚ) / ((A-D : ℕ) : ℚ) *
        firstOrderCurveFiberStageOne K B M τ ≤
      regularPowerBatchedDerivativeCappedBoundTwo n ℓ K (D+1) L A B M H τ := by
  have hnum : n - (D+1) + 1 ≥ n-D := by omega
  have hden : L - (D+1) + 1 = L-D := by omega
  have hℓn : n-A ≤ ℓ*(n-L) := (Nat.sub_le_sub_left hLA n).trans
    (Nat.le_mul_of_pos_left _ hℓ)
  have hrat : ((n-D : ℕ) : ℚ) / ((A-D : ℕ) : ℚ) ≤
      ((n-(D+1)+1 : ℕ) : ℚ) / ((L-D : ℕ) : ℚ) := by
    apply div_le_div₀ (by positivity) (by exact_mod_cast hnum) (by exact_mod_cast (show 0 < L-D by omega))
    exact_mod_cast Nat.sub_le_sub_right hLA D
  unfold regularPowerBatchedDerivativeCappedBoundTwo
  rw [hden, mul_div_assoc, mul_right_comm _ (firstOrderCurveFiberStageOne .. : ℚ)]
  apply le_trans _ (le_add_of_nonneg_left (by positivity))
  gcongr

/-- At generally sufficient exponents the regular cost alone is at least
the incidence ratio times the discarded sites and the degree factor 3D−2.
This allows any chart length at least the recovery dimension. -/
theorem quadratic_regular_floor {n D K L A ℓ B M H τ : ℕ}
    (hD : 2 ≤ D) (hDK : D < K) (hDL : D < L) (hLA : L ≤ A) (hℓ : 1 ≤ ℓ)
    (hB : 2 ≤ B) (hM : 1 ≤ M) (hMB : M ≤ B) (ht : TaylorExponentSufficient 1 K τ) :
    ((n-A : ℕ) : ℚ) * ((n-D : ℕ) : ℚ) / ((A-D : ℕ) : ℚ) * ((3*D-2 : ℕ) : ℚ) ≤
      regularPowerBatchedDerivativeCappedBoundTwo n ℓ K (D+1) L A B M H τ := by
  apply le_trans _ (regular_floor hDL hLA hℓ)
  have hτ := taylor_floor hDK ht
  unfold regularTaylorExponent at hτ
  have hf := fiber_floor (K:=K) (τ:=τ) hB hM hMB
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast (show 3*D-2 ≤ firstOrderCurveFiberStageOne K B M τ by omega)

/-- Minimizing the ordinary threshold leaves a cost for the discarded sites. -/
theorem ordinary_floor {n D A B M H ℓ : ℕ} (hDA : D < A) (hℓ : 1 ≤ ℓ) :
    ((n-A : ℕ) : ℝ) * B ≤ curveRetentionMinimum D A
      (retainedSquarefreeOrdinaryCurveChargeAt n D ℓ · A B M H) := by
  obtain ⟨L,_,hLA,he⟩ := exists_curveRetentionMinimum
    (retainedSquarefreeOrdinaryCurveChargeAt n D ℓ · A B M H) hDA
  rw [← he]
  unfold retainedSquarefreeOrdinaryCurveChargeAt ordinaryUnifiedPowerFactorAt
    ordinaryUnifiedPowerFactorRawAt
  have hl : (n-A)*B ≤ ℓ*((n-L)*ordinaryDegreeEnvelope B M) :=
    (Nat.mul_le_mul (Nat.sub_le_sub_left hLA _) (self_le_ordinaryDegreeEnvelope B M)).trans
      (Nat.le_mul_of_pos_left _ hℓ)
  push_cast
  apply le_trans _ (le_add_of_nonneg_left (by positivity))
  exact_mod_cast hl

/-- The same numerical obstruction applies if an equation-specific argument
could completely remove the common Taylor denominator. -/
theorem retention_floor {n D K L A ℓ B M H τ : ℕ}
    (hDL : D < L) (hLA : L ≤ A) (hK : 2 ≤ K) (hℓ : 1 ≤ ℓ) :
    ((n-A : ℕ) : ℝ) * B + ((n-A : ℕ) : ℝ) * ((n-D : ℕ) : ℝ) /
        ((A-D : ℕ) : ℝ) * B ≤
      curveRetentionMinimum D A (retainedSquarefreeOrdinaryCurveChargeAt n D ℓ · A B M H) +
        (regularPowerBatchedDerivativeCappedBoundTwo n ℓ K (D+1) L A B M H τ : ℝ) := by
  apply add_le_add (ordinary_floor (hDL.trans_le hLA) hℓ)
  have h := regular_floor (n:=n) (K:=K) (B:=B) (M:=M) (H:=H) (τ:=τ) hDL hLA hℓ
  have h' := le_firstOrderCurveFiberStageOne (j:=B) (r:=M) (τ:=τ) hK
  have hQ : ((n-A : ℕ) : ℚ) * ((n-D : ℕ) : ℚ) / ((A-D : ℕ) : ℚ) * (B : ℚ) ≤
      regularPowerBatchedDerivativeCappedBoundTwo n ℓ K (D+1) L A B M H τ :=
    le_trans (mul_le_mul_of_nonneg_left (by exact_mod_cast h') (by positivity)) h
  have hR := (Rat.cast_le (K:=ℝ)).mpr hQ
  push_cast at hR
  exact hR

/-- Every verified beyond-Johnson first-order profile with positive derivative
cap obeys the two discarded-site charges, independently of the threshold. -/
theorem profile_floor {p : LineProfile} {L : ℕ} (hp : p.CurveVerification)
    (hDL : p.candidateDegree < L) (hLA : L ≤ p.agreement) (hAn : p.agreement ≤ p.n)
    (hJ : p.agreement^2 < p.n*p.candidateDegree)
    (hℓ : 1 ≤ p.batchingDegree) (hM : 1 ≤ p.firstDerivativeCap) :
    ((p.n-p.agreement : ℕ) : ℝ)*2 +
        ((p.n-p.agreement : ℕ) : ℝ)*((p.n-p.candidateDegree : ℕ) : ℝ) /
          ((p.agreement-p.candidateDegree : ℕ) : ℝ)*2 ≤
      squarefreeSharpOptimizedCurveEnvelope p L := by
  have hD := hp.1
  have hm : 0 < p.multiplicity := Nat.pos_of_mul_pos_right hp.2.1
  have hB := FirstOrderDegreeOneBoundary.two_le_degree_of_beyond_johnson
    (hDL.trans_le hLA) hAn hm hM hJ hp.2.2.1
  apply le_trans _ (retention_floor (K:=p.candidateDegree+1) (τ:=regularTaylorExponent _)
    (B:=p.totalJetCap) (M:=p.firstDerivativeCap) (H:=p.height) hDL hLA (by omega) hℓ)
  gcongr <;> exact_mod_cast hB

/-- Both named production fields have budget at most twice the block length.
All four universal lower bounds from the split-free profile test exceed it. -/
theorem four_rates_exceed_two_budgets :
    let n : ℕ := 2^30
    let blocked := fun (k A : ℕ) =>
      (2*n : ℝ) < ((n-A : ℕ) : ℝ)*2 + ((n-A : ℕ) : ℝ)*((n-(k-1) : ℕ) : ℝ) /
        ((A-(k-1) : ℕ) : ℝ)*2
    blocked (2^29) (89*2^23) ∧ blocked (2^28) (61*2^23) ∧
      blocked (2^27) (42*2^23) ∧ blocked (2^26) (29*2^23) := by
  norm_num

/-- With the jet caps of the four known certificates, the regular part alone
exceeds respectively 46n, 114n, 193n and 349n, even at zero Taylor cost. -/
theorem four_regular_zero_exponent_costs :
    let n : ℕ := 2^30
    let blocked := fun (k A B C : ℕ) =>
      (C*n : ℚ) < ((n-A : ℕ) : ℚ)*((n-(k-1) : ℕ) : ℚ) / ((A-(k-1) : ℕ) : ℚ)*B
    blocked (2^29) (89*2^23) 59 46 ∧ blocked (2^28) (61*2^23) 66 114 ∧
      blocked (2^27) (42*2^23) 67 193 ∧ blocked (2^26) (29*2^23) 79 349 := by
  norm_num

#print axioms quadratic_regular_floor
#print axioms four_regular_zero_exponent_costs
#print axioms taylor_floor
#print axioms fiber_floor
#print axioms retention_floor
#print axioms profile_floor
#print axioms four_rates_exceed_two_budgets
end ProximityGap.SquarefreeRetentionFloor
