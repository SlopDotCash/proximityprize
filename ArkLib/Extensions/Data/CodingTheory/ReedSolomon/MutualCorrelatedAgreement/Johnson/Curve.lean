/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude

Ported from mitschabaude-bot/ArkLib:reduced-rate (commit 93fd4833b88fb0b964a29d9ca8cbbcd7ca781ba4).
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
import ArkLib.Extensions.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.CurveSlots

/-!
# Exact Johnson correlated agreement for power curves in every characteristic

A message polynomial has degree at most `D`, the agreement fraction is `a = √(D / n) + η` with
slack `η > 0`, and `w₀, …, w_ℓ` are received words. One set of at most
`ℓ · johnsonExceptionCount n D A η` challenges, fixed before the challenge and the candidate, has
the following property: outside it, every polynomial `P` of degree at most `D` agreeing with the
power-batched word `∑ t, z ^ t w_t` on at least `A ≥ a n` points is `∑ t, z ^ t P_t` with
`Agr(∑ t, z ^ t w_t, P) = ⋂ t, Agr(w_t, P_t)`. The field may be infinite and have any
characteristic, and the evaluation points are arbitrary.

## Proof sketch

The argument is the line argument of `exists_johnson_line_exactCorrelatedPair` with the received
line `f + Z g` replaced by the received curve `R_i(Z) = ∑ t, Z ^ t w_t(i)` of challenge degree
`ℓ`. Write `m, μ, h, X` for the Johnson multiplicity, candidate degree, challenge height and
weighted cutoff of the line (`johnsonM`, `johnsonMu`, `johnsonH`, `johnsonXCutoff`).

1. *Interpolation.* Look for `Q(X, Y) = ∑_{j ≤ μ, i + D j < X} q_{ij}(Z) X^i Y^j` over `F[Z]`
   vanishing to order `m` at every `(x_i, R_i(Z))`, with `deg q_{ij} ≤ ℓ h - ℓ j`. The local
   constraint of jet grade `e` at a point has entries of challenge degree at most `ℓ (j - e)`
   (`johnsonFinMatrix_degree_le`), so it is `ℓ h + 1 - ℓ e` scalar equations. There are
   `∑_{j ≤ μ} (X - D j)(ℓ h + 1 - ℓ j)` scalar unknowns and
   `n ∑_{e < m} (m - e)(ℓ h + 1 - ℓ e)` scalar equations: `ℓ` times the line counts at the real
   height `z = h + 1 / ℓ` in place of `h + 1`. The line comparison has slack at the height
   `t² / (3ρ₋)` exceeding one unit of height, and `z > h ≥ t² / (3ρ₋) - 1`, so there are more
   unknowns than equations (`johnson_curve_interpolation_slot_surplus`). A nonzero solution with
   coprime coefficients exists (`exists_primitive_interpolant_of_shifted_height`), so every
   challenge specialization of `Q` is nonzero, its challenge height is at most `ℓ h` and its
   `Y`-degree at most `μ`.
2. *Soundness.* For every challenge `z` and every `P` of degree at most `D` with `A` agreements
   with `R(z)`, `Q(X, P(X))` at `z` has weighted degree below `X ≤ m A` and `m A` zeros with
   multiplicity, so it vanishes
   (`differentialSpecialization_curve_interpolant_eq_zero_of_agreements`).
3. *Exceptional challenges.* The ordinary-equation theorem of [DKT26]
   (`exists_baseExceptional_ordinaryPowerEquation`), which is already stated for power curves of
   any degree `ℓ`, gives one exceptional set of at most `ordinaryCurveFactorRaw θ n D ℓ μ (ℓ h)`
   challenges outside which every such root has exact power agreement. At height `ℓ h` this
   charge is at most `ℓ` times the line charge `ordinaryFactorRaw θ n D μ h`
   (`ordinaryCurveFactorRaw_le_line_mul`), which is `johnsonExceptionCount n D A η`.

The count is therefore exactly `ℓ` times the line count, and the closed form is
`ℓ · (8/3) n t³ / ρ₋` with `t = m + 1/2` (`johnsonExceptionCount_lt_closed`). This is half the
`2ℓ` times the line count of `exists_johnson_curve_exactPowerAgreement`, which interpolates at the
challenge height `ℓ (h + 1) - 1` instead of `ℓ h`.

## Main statements

* `ReedSolomon.exists_johnson_curve_equation`: the interpolated equation for a received curve.
* `ReedSolomon.exists_johnson_curve_exactPowerAgreement_line_mul`: the exceptional-set bound
  `ℓ · johnsonExceptionCount n D A η`.
* `ReedSolomon.exists_johnson_curve_exactPowerAgreement_closed`: the closed bound
  `ℓ · (8/3) n t³ / ρ₋`.

## References

* [BCHKS25]
* [DKT26]
-/


namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative
open HiddenDerivative.SymbolicReceivedInterpolation

/-- The agreement threshold `(√ρ₋ + η) n ≤ A ≤ n` forces the agreement fraction to be at most `1`
when `n > 0`. -/
theorem johnsonAgreement_le_one_of_threshold {n D A : ℕ} {eta : ℝ} (hn : 0 < n)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) (hAn : A ≤ n) :
    johnsonAgreement n D eta ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hAnR : (A : ℝ) ≤ n := by exact_mod_cast hAn
  by_contra hlt
  nlinarith [lt_of_not_ge hlt]

open Classical in
/-- **Johnson interpolation for a received curve.** For distinct evaluation points and received
words `values t`, `0 ≤ t ≤ ℓ`, with `ℓ ≥ 1`, there is a nonzero order-zero equation `Q` over
`F[Z]` with challenge height at most `ℓ h` and `Y`-degree at most `μ`, whose specialization at
every challenge `z` vanishes on every polynomial of degree at most `D` agreeing with the batched
word `∑ t, z ^ t values t` on at least `A ≥ (√ρ₋ + η) n` points. -/
theorem exists_johnson_curve_equation
    {F : Type*} [Field F] {n D A ℓ : ℕ} {eta : ℝ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta) (hℓ : 0 < ℓ)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) (hAn : A ≤ n) :
    ∃ Q : DifferentialPolynomial F[X] 0, Q ≠ 0 ∧
      CoeffNatDegreeLE Q (ℓ * johnsonH n D eta) ∧
      Q.degreeOf (some 0) ≤ johnsonMu n D eta ∧
      ∀ z : F, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
          differentialSpecialization (challengeSpecialization Q z) P = 0 := by
  classical
  have hDlt : D < n := by omega
  have hDpos : 0 < D := by omega
  have ha : johnsonAgreement n D eta ≤ 1 :=
    johnsonAgreement_le_one_of_threshold (by omega) hthreshold hAn
  let m := johnsonM n D eta
  let μ := johnsonMu n D eta
  let h := johnsonH n D eta
  let Xc := johnsonXCutoff n D eta
  let columns := johnsonColumns Xc D μ
  let w : Fin n → F[X] := fun i ↦ powerBatchedCoordinate fun t ↦ values t i
  have hw : ∀ i, (w i).natDegree ≤ ℓ := fun i ↦ powerBatchedCoordinate_natDegree_le _
  have hcut : Xc ≤ m * A := johnsonXCutoff_le_mul_agreement heta hthreshold
  have hbudget : 0 < m * A := by
    have hDA := johnson_degree_succ_le_agreement hDlt heta hthreshold
    have hm := johnsonM_ge_three n D eta
    exact Nat.mul_pos (by omega) (by omega)
  obtain ⟨v, _hv, hvdegree, _hprimitive, hnonzero, hconstraints⟩ :=
    exists_primitive_interpolant_of_shifted_height m ℓ (ℓ * h) (fun i ↦ domain i) w columns
      (johnsonColumns_injective Xc D μ)
      (johnsonFinMatrix Xc D μ m (fun i ↦ domain i) w) (fun i ↦ ℓ * johnsonFinRowWeight m i)
      (fun v hv ↦ (johnsonFinMatrix_kernel_iff Xc D μ m (fun i ↦ domain i) w v).mp hv)
      (by
        intro i j _
        have hh := johnsonFinMatrix_curve_degree_le Xc D μ m ℓ (fun i ↦ domain i) w hw i j
        rw [johnsonColumns_totalJetDegree, ← Nat.mul_sub]
        exact hh)
      (by
        intro i j hweight
        apply johnsonFinMatrix_eq_zero_of_grade_lt Xc D μ m (fun i ↦ domain i) w i j
        rw [johnsonColumns_totalJetDegree] at hweight
        exact Nat.lt_of_mul_lt_mul_left hweight)
      (by
        simp only [columns, johnsonColumns_totalJetDegree]
        rw [sum_johnsonFinRowWeight_curveSlots, sum_johnsonColumns_curveSlots]
        exact johnson_curve_interpolation_slot_surplus hD hDlt heta ha hℓ)
  let Q : DifferentialPolynomial F[X] 0 := SourceColumn.interpolant columns v
  have hvheight : ∀ j, (v j).natDegree ≤ ℓ * h := by
    intro j
    by_cases hz : v j = 0
    · simp [hz]
    · have hlt : (v j).natDegree < ℓ * h + 1 - ℓ * totalJetDegree (columns j).exponent :=
        (Polynomial.natDegree_lt_iff_degree_lt hz).mpr (Polynomial.mem_degreeLT.mp (hvdegree j))
      omega
  refine ⟨Q, ?_, SourceColumn.coeff_interpolant_natDegree_le columns v hvheight, johnsonInterpolant_jetDegree_le v, ?_⟩
  · intro hzero
    apply hnonzero (RingHom.id F) 0
    change MvPolynomial.map _ Q = 0
    rw [hzero, map_zero]
  · intro z P hdegree hagree
    have hPnat : P.natDegree ≤ D := by
      by_cases hPzero : P = 0
      · simp [hPzero]
      · have hlt : P.natDegree < D + 1 := by
          exact_mod_cast (Polynomial.natDegree_lt_iff_degree_lt hPzero).mpr hdegree
        omega
    have hsound := differentialSpecialization_curve_interpolant_eq_zero_of_agreements
      (by exact_mod_cast hcut) (fun i ↦ domain i) w columns
      (fun j ↦ johnsonColumns_weightedSupportEligible j) v hconstraints (RingHom.id F) z
      (polynomialAgreementSet domain (powerBatchedWord values z) P) P hPnat
      domain.injective.injOn hagree (by
        intro i hi
        rw [eval₂_powerBatchedCoordinate_eq_powerBatchedWord]
        exact (Finset.mem_filter.mp hi).2)
    have heval : Polynomial.eval₂RingHom (RingHom.id F) z = (Polynomial.aeval z).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro a
        simp
      · simp
    simpa only [heval, challengeSpecialization] using hsound

open Classical in
/-- **Johnson exact power agreement for curves.** For distinct evaluation points and received
words `values t`, `0 ≤ t ≤ ℓ`, with `ℓ ≥ 1`, one set of at most
`ℓ · johnsonExceptionCount n D A η` challenges is chosen before the challenge and candidate.
Outside it, every polynomial of degree at most `D` agreeing with `∑ t, z ^ t values t` on at least
`A ≥ (√(D / n) + η) n` points has exact power agreement: it is `∑ t, z ^ t P_t` for polynomials
`P_t` of degree at most `D`, and its agreement set is the common agreement set of the `P_t`. -/
theorem exists_johnson_curve_exactPowerAgreement_line_mul
    {F : Type*} [Field F] {n D A ℓ : ℕ} {eta : ℝ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta) (hℓ : 0 < ℓ)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) (hAn : A ≤ n) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ ℓ * johnsonExceptionCount n D A eta ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) (D + 1) z P := by
  classical
  have hDlt : D < n := by omega
  have hDA := johnson_degree_succ_le_agreement hDlt heta hthreshold
  have hmu := johnsonMu_pos (eta := eta) hD hDlt
  obtain ⟨Q, hQ, hheight, hdegree, hsound⟩ :=
    exists_johnson_curve_equation domain values hD hDn heta hℓ hthreshold hAn
  obtain ⟨ex, hcard, hgood⟩ := exists_baseExceptional_ordinaryPowerEquation domain values Q D
    (ℓ * johnsonH n D eta) (johnsonMu n D eta) (D + 1) A hQ (by omega) (by omega) hDA
    hheight hdegree
  rw [ordinaryUnifiedPowerFactorAtOrHeight_of_pos n D ℓ _ _ A (D + 1) hmu,
    ordinaryUnifiedPowerFactorAt_succ_eq n D ℓ _ _ A hDA hAn] at hcard
  have htheta : (0 : ℚ) ≤ ((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ) := by positivity
  have hcurve := (ordinaryUnifiedPowerFactorRaw_le_ordinaryCurveFactorRaw n ℓ
    (johnsonMu n D eta) (ℓ * johnsonH n D eta) htheta hD).trans
      (ordinaryCurveFactorRaw_le_line_mul _ n D ℓ (johnsonMu n D eta) (ℓ * johnsonH n D eta)
        (johnsonH n D eta) htheta le_rfl)
  have hcardQ := hcard.trans hcurve
  have hcardReal : (ex.card : ℝ) ≤
      ((ℓ * ordinaryFactorRaw (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D
        (johnsonMu n D eta) (johnsonH n D eta) : ℚ) : ℝ) := by exact_mod_cast hcardQ
  refine ⟨ex, ?_, fun z hz P hdeg hagree ↦ hgood z hz P hdeg (hsound z P hdeg hagree) hagree⟩
  simpa only [ordinaryFactorRaw, johnsonExceptionCount, johnsonTheta, Rat.cast_add,
    Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat] using hcardReal

open Classical in
/-- **Johnson exact power agreement, closed bound.** Under the hypotheses of
`exists_johnson_curve_exactPowerAgreement_line_mul`, fewer than `ℓ · (8/3) n t³ / ρ₋`
challenges are exceptional, with `t = johnsonT n D η` and `ρ₋ = D / n`. -/
theorem exists_johnson_curve_exactPowerAgreement_closed
    {F : Type*} [Field F] {n D A ℓ : ℕ} {eta : ℝ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta) (hℓ : 0 < ℓ)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) (hAn : A ≤ n) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) <
        ℓ * ((8 / 3 : ℝ) * n * johnsonT n D eta ^ 3 / johnsonRhoMinus n D) ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) (D + 1) z P := by
  obtain ⟨ex, hcard, hgood⟩ :=
    exists_johnson_curve_exactPowerAgreement_line_mul domain values hD hDn heta hℓ hthreshold hAn
  refine ⟨ex, hcard.trans_lt ?_, hgood⟩
  exact mul_lt_mul_of_pos_left (johnsonExceptionCount_lt_closed hD hDn heta hthreshold)
    (by exact_mod_cast hℓ)

end ReedSolomon

#print axioms ReedSolomon.johnsonAgreement_le_one_of_threshold
#print axioms ReedSolomon.exists_johnson_curve_equation
#print axioms ReedSolomon.exists_johnson_curve_exactPowerAgreement_line_mul
#print axioms ReedSolomon.exists_johnson_curve_exactPowerAgreement_closed
