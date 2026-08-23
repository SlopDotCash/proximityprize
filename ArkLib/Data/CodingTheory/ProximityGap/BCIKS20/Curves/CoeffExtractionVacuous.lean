/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.CoeffExtractionResidual

/-!
# Issue #304 — vacuous-regime discharges of the BCIKS20 §5 strict coefficient-extraction core

`CurveCommonAgreementResidual` (the geometric form of the strict Johnson-branch
coefficient-polynomial residual `StrictCoeffPolysResidual`, the open core of #304 gating
STIR/WHIR/FRI soundness) carries the probability hypothesis `Pr > k · errorBound`. Since every
probability is `≤ 1`, the residual holds **unconditionally** whenever `1 ≤ k · errorBound`.

Composing with the existing bound `errorBound_ge_const : n/q ≤ errorBound` (valid for `0 < deg`
and `δ < 1 − √ρ`), this discharges the residual — and through the proven bivariate-Lagrange
reduction `strictCoeffPolysResidual_of_commonAgreement`, the full `StrictCoeffPolysResidual` —
for **every field with `q ≤ k·n`**. In particular every full-domain Reed–Solomon code
(`ι = F`, `n = q`) satisfies this at any curve dimension `k ≥ 1`.

## Honest scope

These are *vacuous-regime* discharges: they show the BCIKS20 probability threshold is
unsatisfiable when the field is at most `k` times the evaluation domain (`errorBound ≥ n/q ≥ 1/k`),
so the conditional content is empty there. The genuinely open content of #304 is the
**large-field regime `q > k·n`** (the deployed FRI/STIR setting, smooth subdomain `n ≪ q`),
where the §5 Guruswami–Sudan/Hensel counting must produce the common agreement. Axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/
namespace ProximityGap

open NNReal Finset Function ProbabilityTheory Code Polynomial
open scoped BigOperators LinearCode ProbabilityTheory ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Vacuous-regime discharge (abstract form).** If `1 ≤ k · errorBound`, then the probability
hypothesis `Pr > k·errorBound` of the geometric common-agreement residual is unsatisfiable
(every probability is `≤ 1`), so `CurveCommonAgreementResidual` holds. -/
theorem curveCommonAgreementResidual_of_one_le_mul {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (h : (1 : ENNReal) ≤ (k : ENNReal) * (errorBound δ deg domain : ENNReal)) :
    CurveCommonAgreementResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro _hk u hprob _hJ _hsqrt _P _hP
  exact absurd (lt_of_le_of_lt h hprob) (not_lt.mpr (PMF.coe_le_one _ _))

/-- **Vacuous-regime discharge (small-field form).** If `q ≤ k · n` (field at most `k` times the
evaluation-domain size — e.g. any full-domain RS code with `k ≥ 1`), then `1 ≤ k·errorBound`
via `errorBound_ge_const : n/q ≤ errorBound`, and the residual holds. -/
theorem curveCommonAgreementResidual_of_card_le {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg : 0 < deg)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hq : (Fintype.card F : ℝ≥0) ≤ (k : ℝ≥0) * (Fintype.card ι : ℝ≥0)) :
    CurveCommonAgreementResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  refine curveCommonAgreementResidual_of_one_le_mul (k := k) ?_
  have hconst : (Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0) ≤ errorBound δ deg domain :=
    DivergenceOfSets.errorBound_ge_const (deg := deg) (domain := domain) hdeg hδ
  -- 1 ≤ k·(n/q) since q ≤ k·n, and k·(n/q) ≤ k·errorBound.
  have hqpos : (0 : ℝ≥0) < (Fintype.card F : ℝ≥0) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hone : (1 : ℝ≥0) ≤ (k : ℝ≥0) * ((Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0)) := by
    rw [mul_div_assoc', le_div_iff₀ hqpos, one_mul]
    exact hq
  have hstep : (1 : ℝ≥0) ≤ (k : ℝ≥0) * errorBound δ deg domain :=
    le_trans hone (mul_le_mul_left' hconst _)
  exact_mod_cast hstep

/-- **Vacuous-regime `StrictCoeffPolysResidual` (abstract form).** Composes the vacuous
common-agreement discharge through the proven bivariate-Lagrange reduction. -/
theorem strictCoeffPolysResidual_of_one_le_mul {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (h : (1 : ENNReal) ≤ (k : ENNReal) * (errorBound δ deg domain : ENNReal)) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  strictCoeffPolysResidual_of_commonAgreement
    (curveCommonAgreementResidual_of_one_le_mul h)

/-- **Vacuous-regime `StrictCoeffPolysResidual` (small-field form, `q ≤ k·n`).** -/
theorem strictCoeffPolysResidual_of_card_le {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hdeg : 0 < deg)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hq : (Fintype.card F : ℝ≥0) ≤ (k : ℝ≥0) * (Fintype.card ι : ℝ≥0)) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  strictCoeffPolysResidual_of_commonAgreement
    (curveCommonAgreementResidual_of_card_le hdeg hδ hq)

/-! ## The sharp interior regime: `q ≤ k · deg² · 10⁷` -/

/-- In the strict Johnson interior, the BCIKS20 error bound is at least `deg² · 10⁷ / q`:
the minimum `m = min(1−√ρ−δ, √ρ/20)` is `≤ 1/20`, so `(2m)⁷ ≤ 10⁻⁷`. -/
theorem errorBound_ge_e7 {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg : 0 < deg)
    (hJ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ)
    (hsqrt : δ < 1 - ReedSolomon.sqrtRate deg domain) :
    ((deg ^ 2 * 10 ^ 7 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) ≤ errorBound δ deg domain := by
  classical
  set r : ℝ≥0 := (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) with hr
  have hUD : ¬ δ ≤ (1 - r) / 2 := not_le.mpr (by simpa [← hr] using hJ)
  have hδ' : δ < 1 - r.sqrt := by
    simpa [ReedSolomon.sqrtRate, ← hr] using hsqrt
  have hmem2 : (1 - r) / 2 < δ ∧ δ < 1 - r.sqrt := ⟨lt_of_not_ge hUD, hδ'⟩
  simp only [errorBound, ← hr, Set.mem_Icc, zero_le, hUD, and_false,
    ↓reduceIte, Set.mem_Ioo, hmem2, and_self, coe_pow, NNReal.coe_natCast,
    coe_min, NNReal.coe_div, Real.coe_sqrt, NNReal.coe_ofNat, ge_iff_le]
  change ((deg ^ 2 * 10 ^ 7 : ℕ) : ℝ) / (Fintype.card F : ℝ) ≤
    (↑deg ^ 2 : ℝ) /
      ((2 * min (↑(1 - sqrt r - δ) : ℝ) (Real.sqrt (r : ℝ) / 20)) ^ 7 *
        (Fintype.card F : ℝ))
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  set m : ℝ := min (↑(1 - sqrt r - δ) : ℝ) (Real.sqrt (r : ℝ) / 20) with hm
  have hm_le : m ≤ Real.sqrt (r : ℝ) / 20 := by simp [hm]
  have hm_nonneg : 0 ≤ m := by
    have h1 : (0 : ℝ) ≤ (↑(1 - sqrt r - δ) : ℝ) := by
      exact_mod_cast (show (0 : ℝ≥0) ≤ (1 - sqrt r - δ) from zero_le _)
    have h2 : (0 : ℝ) ≤ Real.sqrt (r : ℝ) / 20 := by positivity
    simpa [hm] using le_min h1 h2
  have hr_le_one : r ≤ 1 := by
    have h := DivergenceOfSets.reedSolomon_rate_le_one (deg := deg) (domain := domain)
    have : (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) ≤ 1 := by exact_mod_cast h
    simpa [hr] using this
  have h_sqrt_le_one : Real.sqrt (r : ℝ) ≤ 1 := by
    have hr1 : (r : ℝ) ≤ 1 := by exact_mod_cast hr_le_one
    calc Real.sqrt (r : ℝ) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hr1
      _ = 1 := Real.sqrt_one
  -- 2m ≤ 1/10
  have h2m : 2 * m ≤ 1 / 10 := by
    have : m ≤ 1 / 20 := le_trans hm_le (by linarith)
    linarith
  have h2m_nonneg : 0 ≤ 2 * m := by linarith
  -- (2m)^7 ≤ (1/10)^7
  have hpow : (2 * m) ^ 7 ≤ (1 / 10 : ℝ) ^ 7 := by
    exact pow_le_pow_left₀ h2m_nonneg h2m 7
  have hpow_nonneg : 0 ≤ (2 * m) ^ 7 := by positivity
  -- m > 0 (strict interior + positive rate)
  have hr_pos : (0 : ℝ) < (r : ℝ) := by
    have hrate_posQ : (0 : ℚ≥0) < LinearCode.rate (ReedSolomon.code domain deg) :=
      DivergenceOfSets.reedSolomon_rate_pos (deg := deg) (domain := domain) hdeg
    have hrate_pos :
        (0 : ℝ≥0) < (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) := by
      exact_mod_cast hrate_posQ
    have : (0 : ℝ≥0) < r := by simpa [hr] using hrate_pos
    exact_mod_cast this
  have hm_pos : 0 < m := by
    have hA_nnreal : (0 : ℝ≥0) < (1 - sqrt r - δ) := tsub_pos_of_lt hδ'
    have hA : (0 : ℝ) < (↑(1 - sqrt r - δ) : ℝ) := by exact_mod_cast hA_nnreal
    have hB : (0 : ℝ) < Real.sqrt (r : ℝ) / 20 := by
      have hsqrt_pos : (0 : ℝ) < Real.sqrt (r : ℝ) := (Real.sqrt_pos).2 hr_pos
      nlinarith
    have : 0 < min (↑(1 - sqrt r - δ) : ℝ) (Real.sqrt (r : ℝ) / 20) := lt_min hA hB
    simpa [hm] using this
  have hden_pos : (0 : ℝ) < (2 * m) ^ 7 * (Fintype.card F : ℝ) := by positivity
  rw [div_le_div_iff₀ hqpos hden_pos]
  push_cast
  have key : ((deg : ℝ) ^ 2 * 10 ^ 7) * (2 * m) ^ 7 ≤ (deg : ℝ) ^ 2 := by
    nlinarith [hpow, sq_nonneg ((deg : ℝ))]
  have hmulq := mul_le_mul_of_nonneg_right key (le_of_lt hqpos)
  nlinarith [hmulq]

/-- **Sharp vacuous-regime discharge: `q ≤ k · deg² · 10⁷`.** Inside the strict interior
(both regime bounds available from the residual's own hypotheses), the error bound is
`≥ deg²·10⁷/q ≥ 1/k`, making the probability threshold unsatisfiable. -/
theorem curveCommonAgreementResidual_of_card_le_e7 {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg : 0 < deg)
    (hq : (Fintype.card F : ℝ≥0) ≤ (k : ℝ≥0) * ((deg ^ 2 * 10 ^ 7 : ℕ) : ℝ≥0)) :
    CurveCommonAgreementResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro _hk u hprob hJ hsqrt _P _hP
  exfalso
  have hconst := errorBound_ge_e7 (deg := deg) (domain := domain) (δ := δ) hdeg hJ hsqrt
  have hqpos : (0 : ℝ≥0) < (Fintype.card F : ℝ≥0) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hone : (1 : ℝ≥0) ≤ (k : ℝ≥0) * (((deg ^ 2 * 10 ^ 7 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)) := by
    rw [mul_div_assoc', le_div_iff₀ hqpos, one_mul]
    exact hq
  have hstep : (1 : ℝ≥0) ≤ (k : ℝ≥0) * errorBound δ deg domain :=
    le_trans hone (mul_le_mul_left' hconst _)
  have h : (1 : ENNReal) ≤ (k : ENNReal) * (errorBound δ deg domain : ENNReal) := by
    exact_mod_cast hstep
  exact absurd (lt_of_le_of_lt h hprob) (not_lt.mpr (PMF.coe_le_one _ _))

/-- **Sharp vacuous-regime `StrictCoeffPolysResidual` (`q ≤ k·deg²·10⁷`).** -/
theorem strictCoeffPolysResidual_of_card_le_e7 {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (hq : (Fintype.card F : ℝ≥0) ≤ (k : ℝ≥0) * ((deg ^ 2 * 10 ^ 7 : ℕ) : ℝ≥0)) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  strictCoeffPolysResidual_of_commonAgreement
    (curveCommonAgreementResidual_of_card_le_e7 (Nat.pos_of_ne_zero (NeZero.ne deg)) hq)

end ProximityGap

#print axioms ProximityGap.curveCommonAgreementResidual_of_one_le_mul
#print axioms ProximityGap.curveCommonAgreementResidual_of_card_le
#print axioms ProximityGap.strictCoeffPolysResidual_of_one_le_mul
#print axioms ProximityGap.strictCoeffPolysResidual_of_card_le
#print axioms ProximityGap.errorBound_ge_e7
#print axioms ProximityGap.curveCommonAgreementResidual_of_card_le_e7
#print axioms ProximityGap.strictCoeffPolysResidual_of_card_le_e7
